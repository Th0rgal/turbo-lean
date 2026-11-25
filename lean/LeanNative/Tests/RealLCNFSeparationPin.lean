import LeanNative.IR.RealLCNFSemantics

/-!
# H1.1 Separation Pin: `RealLCNFSemantics` must not (transitively) import the lowerer

This module imports ONLY `LeanNative.IR.RealLCNFSemantics` and asserts, against the
elaboration environment, that the lowerer module `LeanNative.IR.RealLCNFBridge` is not among
the transitively imported modules, while the shared-definitions module
`LeanNative.IR.RealLCNFShared` is (the positive control proving the module-index lookup
works). An edit that re-introduces `import LeanNative.IR.RealLCNFBridge` anywhere in the
semantics' import closure turns this module red at build time.
-/

namespace LeanNative.Tests.RealLCNFSeparationPin

open Lean

#eval show CoreM Unit from do
  let env ← getEnv
  if (env.getModuleIdx? `LeanNative.IR.RealLCNFShared).isNone then
    throwError "separation pin: positive control failed — LeanNative.IR.RealLCNFShared is not an imported module (the module-index lookup itself is broken)"
  if (env.getModuleIdx? `LeanNative.IR.RealLCNFBridge).isSome then
    throwError "separation pin: LeanNative.IR.RealLCNFSemantics transitively imports the lowerer module LeanNative.IR.RealLCNFBridge (H1.1 separation regressed)"
  IO.println "[real-lcnf-separation-pin] OK: RealLCNFSemantics imports RealLCNFShared and not RealLCNFBridge"

end LeanNative.Tests.RealLCNFSeparationPin
