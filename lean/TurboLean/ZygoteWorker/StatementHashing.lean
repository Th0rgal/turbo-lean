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

open Lean Elab

namespace TurboLean.ZygoteWorker

/-- 256-bit cryptographic BLAKE3 content digest over raw artifact bytes. -/
def hashBytesBlake3Hex (bs : ByteArray) : String :=
  TurboLean.Blake3.blake3Bytes bs

/-- Canonical BLAKE3 digest of `(c.levelParams, c.type)` under the `statement-v1` schema,
    normalizing module-local private constant names so probe, shard, and module elaborations match. -/
def kernelStatementHash (c : ConstantInfo) (localMod? : Option Name := none) : String :=
  let j := TurboLean.StatementHash.statement c (TurboLean.StatementHash.normalizeLocalPrivateName localMod?)
  TurboLean.Blake3.blake3Bytes j.compress.toUTF8

end TurboLean.ZygoteWorker
