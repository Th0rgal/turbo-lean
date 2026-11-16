import Lean.Elab.Command
import Lean.Elab.App
import Lean.Elab.PreDefinition.Structural.Main
import Lean.Elab.PreDefinition.WF.Main
import Lean.Elab.PreDefinition.PartialFixpoint.Main
import Lean.Data.Json
import Lean.Util.CollectAxioms
import Lean.Replay
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr
import Lean.Compiler.InlineAttrs
import Lean.Compiler.Specialize
import Lean.Compiler.ExportAttr
import Lean.Compiler.NoncomputableAttr
import Lean.Compiler.ModPkgExt
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.ToDecl
import Lean.Compiler.LCNF.Main
import Lean.Compiler.LCNF.Passes
import Lean.Compiler.LCNF.AlphaEqv
import Lean.Compiler.LCNF.SpecInfo
import Lean.Compiler.LCNF.Simp.ConstantFold
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.IR.CompilerM
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Instances
import Lean.Meta.CoeAttr
import Lean.Meta.Tactic.Ext
import Lean.Meta.Tactic.Grind.Attr
import Lean.Meta.Match.MatchPatternAttr
import Lean.Meta.CompletionName
import Lean.Meta.RecExt
import Lean.Compiler.LCNF.MonoTypes
import Lean.Compiler.LCNF.ToImpureType
import Lean.Linter.Deprecated
import Lean.DeprecatedModule
import Lake.Load.Lean.Elab
import Std.Data.HashMap
import TurboLean.Blake3
import TurboLean.StatementHash
import TurboLean.ZygoteFork

import TurboLean.ZygoteWorker.Env
import TurboLean.ZygoteWorker.Wire
import TurboLean.ZygoteWorker.KernelAudit
import TurboLean.ZygoteWorker.StatementHashing
import TurboLean.ZygoteWorker.Signature
import TurboLean.ZygoteWorker.Replay
import TurboLean.ZygoteWorker.Compiler

open Lean Elab

namespace TurboLean.ZygoteWorker

structure TimeoutHotspotEntry where
  kind : String
  label : String
  line : Nat
  elapsedMs : Nat
  heartbeats : Nat

structure SimpHotspotEntry where
  lemmaName : String
  attempts : Nat
  succeeded : Nat

private partial def walkHotspotMessageData
    (md : MessageData)
    (cmdLine : Nat)
    (traceOut : IO.Ref (Array TimeoutHotspotEntry))
    (simpOut : IO.Ref (Std.HashMap String (Nat × Nat)))
    (visitedNodes : IO.Ref Nat) : IO Unit := do
  let n ← visitedNodes.get
  if n >= 8192 then
    return
  visitedNodes.set (n + 1)
  match md with
  | .trace data hdr children =>
    let clsStr := data.cls.toString
    if clsStr.startsWith "Meta.Tactic.simp." then
      let hdrTxt ← (hdr.toString : IO String)
      let firstLine := ((hdrTxt.splitOn "\n").headD hdrTxt).trimAscii.toString
      let rawLemma := ((firstLine.splitOn ":").headD firstLine).trimAscii.toString
      let cleanLemma := if rawLemma.startsWith "[" then
          match rawLemma.splitOn "]" with
          | _ :: rest => (String.intercalate "]" rest).trimAscii.toString
          | [] => rawLemma
        else rawLemma
      if !cleanLemma.isEmpty && !cleanLemma.startsWith "==" && cleanLemma.length <= 160 then
        let isRewrite := clsStr == "Meta.Tactic.simp.rewrite"
        let isSuccess := isRewrite || (match data.result? with | some .success => true | _ => false)
        let curMap ← simpOut.get
        let (att, succ) := curMap[cleanLemma]?.getD (0, 0)
        simpOut.set (curMap.insert cleanLemma (att + 1, succ + (if isSuccess then 1 else 0)))
    if data.stopTime > data.startTime then
      let durSec := data.stopTime - data.startTime
      let durMsFloat := durSec * 1000.0
      let durMs := durMsFloat.toUInt64.toNat
      if durMs >= 1 && (clsStr.startsWith "Elab." || clsStr == "Kernel" || clsStr.startsWith "Meta.Tactic") then
        let hdrTxt ← (hdr.toString : IO String)
        let firstLine := ((hdrTxt.splitOn "\n").headD hdrTxt).trimAscii.toString
        let clipped := if firstLine.length > 120 then (firstLine.take 120).toString else firstLine
        let label := if clipped.isEmpty then clsStr else s!"[{clsStr}] {clipped}"
        let arr ← traceOut.get
        if arr.size < 256 then
          traceOut.set (arr.push { kind := "trace", label := label, line := cmdLine, elapsedMs := durMs, heartbeats := 0 })
    for child in children do
      walkHotspotMessageData child cmdLine traceOut simpOut visitedNodes
  | .withContext _ inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .withNamingContext _ inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .nest _ inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .group inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .compose a b =>
    walkHotspotMessageData a cmdLine traceOut simpOut visitedNodes
    walkHotspotMessageData b cmdLine traceOut simpOut visitedNodes
  | .tagged _ inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .ofWidget _ inner => walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | .ofLazy fn _ =>
    let dyn ← (fn none : BaseIO Dynamic)
    if let some inner := dyn.get? MessageData then
      walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes
  | other =>
    if let some inner := originatingMessage? other then
      walkHotspotMessageData inner cmdLine traceOut simpOut visitedNodes

/-- Bounded command-by-command diagnostic pass executed ONLY after a timeout or heartbeat/recursion
    exhaustion failure. Enables `profiler` + `trace.Meta.Tactic.simp.*` on an isolated state, records
    per-command wall-clock / heartbeat consumption and `simp` lemma rewrite/unify counts, and formats
    additive `,"timeout_hotspots":[...],"simp_hotspots":[...]` JSON fields (never `ok: true`). -/
def diagnoseShardHotspots
    (baseEnv : Environment)
    (code : String)
    (fileName : String := "<zygote-shard>")
    (encodedLeanArgs : String := "") : IO (Nat × Nat × List String × List String × String) := do
  let initOpts ← applyEncodedLeanArgs {} encodedLeanArgs
  let profOpts0 := initOpts.setBool `profiler true
  let profOpts1 := profOpts0.set `profiler.threshold (1 : Nat)
  let profOpts2 := profOpts1.setBool `trace.Meta.Tactic.simp.rewrite true
  let profOpts3 := profOpts2.setBool `trace.Meta.Tactic.simp.unify true
  let profOpts := profOpts3.setBool `trace.Meta.Tactic.simp.discharge true
  let curHb := profOpts.get `maxHeartbeats (200000 : Nat)
  let diagHb := if curHb == 0 || curHb > 250000 then 250000 else curHb
  let opts ← withToolchainSatSolver (profOpts.set `maxHeartbeats diagHb)
  let ictx := Parser.mkInputContext code fileName
  let initState := Command.mkState baseEnv {} opts
  let mut fstate : Frontend.State := {
    commandState := initState
    parserState := {}
    cmdPos := 0
  }
  let cmdHotspotsRef ← IO.mkRef (#[] : Array TimeoutHotspotEntry)
  let traceHotspotsRef ← IO.mkRef (#[] : Array TimeoutHotspotEntry)
  let simpMapRef ← IO.mkRef ({} : Std.HashMap String (Nat × Nat))
  let visitedRef ← IO.mkRef (0 : Nat)
  let mut allMsgs : List String := []
  let mut allErrs : List String := []
  let mut prevMsgCount : Nat := 0
  let tStart ← IO.monoNanosNow
  let hbStart ← IO.getNumHeartbeats
  let mut done := false
  let mut stepCount : Nat := 0
  while !done && stepCount < 512 do
    stepCount := stepCount + 1
    let cmdPosBefore := fstate.parserState.pos
    let cmdLine := (ictx.fileMap.toPosition cmdPosBefore).line
    let cT0 ← IO.monoNanosNow
    let cHb0 ← IO.getNumHeartbeats
    let (_, (_, fstate')) ← IO.FS.withIsolatedStreams ((Frontend.processCommand.run { inputCtx := ictx }).run fstate) (isolateStderr := false)
    let cT1 ← IO.monoNanosNow
    let cHb1 ← IO.getNumHeartbeats
    let cmdMs := (cT1 - cT0) / 1000000
    let cmdHbs := cHb1 - cHb0
    let cmdStx? := fstate'.commands.back?
    let isTerm := cmdStx?.any Parser.isTerminalCommand
    if !isTerm then
      let kindStr := match cmdStx? with | some stx => stx.getKind.toString | none => "command"
      let rawSlice := (String.Pos.Raw.extract code cmdPosBefore fstate'.parserState.pos).trimAscii.toString
      let firstLine := ((rawSlice.splitOn "\n").headD rawSlice).trimAscii.toString
      let snippet := if firstLine.length > 100 then (firstLine.take 100).toString else firstLine
      let label := if snippet.isEmpty then kindStr else snippet
      let curCmds ← cmdHotspotsRef.get
      cmdHotspotsRef.set (curCmds.push {
        kind := "command"
        label := label
        line := cmdLine
        elapsedMs := cmdMs
        heartbeats := cmdHbs
      })
    let msgList := fstate'.commandState.messages.toList
    let newMsgs := msgList.drop prevMsgCount
    prevMsgCount := msgList.length
    for msg in newMsgs do
      walkHotspotMessageData msg.data msg.pos.line traceHotspotsRef simpMapRef visitedRef
      let txt ← msg.data.toString
      let sevStr := match msg.severity with
        | .error => "error"
        | .warning => "warning"
        | .information => "info"
      let formatted := s!"{msg.fileName}:{msg.pos.line}:{msg.pos.column}: {sevStr}: {txt.trimAsciiEnd.toString}"
      allMsgs := allMsgs ++ [formatted]
      if msg.severity == .error then
        allErrs := allErrs ++ [formatted]
    for td in fstate'.commandState.traceState.traces do
      walkHotspotMessageData td.msg cmdLine traceHotspotsRef simpMapRef visitedRef
    fstate := fstate'
    let nowNs ← IO.monoNanosNow
    if isTerm || ((nowNs - tStart) / 1000000) >= 3500 then
      done := true
  if allMsgs.any isRuntimePanicText then
    allErrs := allErrs ++ [runtimePanicErr]
  if allErrs.isEmpty then
    allErrs := ["[TurboLean.Diagnostics] diagnostic hotspot pass completed"]
  let cmdArr ← cmdHotspotsRef.get
  let traceArr ← traceHotspotsRef.get
  let combined := (cmdArr ++ traceArr).qsort fun a b =>
    if a.heartbeats != b.heartbeats then a.heartbeats > b.heartbeats
    else a.elapsedMs > b.elapsedMs
  let topTimeout := combined.extract 0 (Nat.min 8 combined.size)
  let simpMap ← simpMapRef.get
  let simpArr := (simpMap.toArray.map fun (k, (att, succ)) =>
    ({ lemmaName := k, attempts := att, succeeded := succ } : SimpHotspotEntry)).qsort fun a b =>
      if a.attempts != b.attempts then a.attempts > b.attempts
      else a.succeeded > b.succeeded
  let topSimp := simpArr.extract 0 (Nat.min 8 simpArr.size)
  let timeoutJsonItems := topTimeout.toList.map fun e =>
    s!"\{\"kind\":\"{jsonEscape e.kind}\",\"label\":\"{jsonEscape e.label}\",\"line\":{e.line},\"elapsed_ms\":{e.elapsedMs},\"heartbeats\":{e.heartbeats}}"
  let simpJsonItems := topSimp.toList.map fun e =>
    s!"\{\"lemma\":\"{jsonEscape e.lemmaName}\",\"attempts\":{e.attempts},\"succeeded\":{e.succeeded}}"
  let suffix := s!",\"timeout_hotspots\":[{String.intercalate "," timeoutJsonItems}],\"simp_hotspots\":[{String.intercalate "," simpJsonItems}]"
  let tEnd ← IO.monoNanosNow
  let hbEnd ← IO.getNumHeartbeats
  return ((tEnd - tStart) / 1000, hbEnd - hbStart, allMsgs, allErrs, suffix)

end TurboLean.ZygoteWorker
