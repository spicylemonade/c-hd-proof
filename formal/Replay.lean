import Lean
open Lean

/-!
agent-09 independent kernel-replay tool (lean4checker-style), for the acceptance audit.
Usage: lake env lean --run /path/Replay.lean <RootModule> [prefix]
Imports <RootModule>, collects every constant whose defining module starts with <prefix>
(default `Frontier`), builds a base environment from ALL other transitively imported modules,
and re-sends each collected constant to the kernel via `Kernel.Environment.replay`.
Mathlib/Lean core constants are trusted (from their .olean files); Frontier constants are re-checked.
-/

unsafe def main (args : List String) : IO UInt32 := do
  let root := args.headD "Frontier"
  let pfx := (args.drop 1).headD "Frontier"
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let rootName := root.toName
  let env ← importModules #[{ module := rootName }] {} 0 (loadExts := true)
  let modNames := env.header.moduleNames
  let isTarget (m : Name) : Bool := (pfx.toName).isPrefixOf m
  let baseMods := modNames.filter (fun m => !isTarget m)
  let targetMods := modNames.filter isTarget
  IO.println s!"root={root} modules={modNames.size} target modules={targetMods.size}: {targetMods.toList}"
  -- collect target constants
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := modNames[idx.toNat]!
      if isTarget m then newConsts := newConsts.insert n ci
    | none => pure ()
  IO.println s!"target constants to replay: {newConsts.size}"
  let env0 ← importModules (baseMods.map fun m => ({ module := m } : Import)) {} 0 (loadExts := false)
  let t0 ← IO.monoMsNow
  try
    let _ ← env0.toKernelEnv.replay newConsts
    let t1 ← IO.monoMsNow
    IO.println s!"KERNEL REPLAY OK: {newConsts.size} constants re-checked in {t1 - t0} ms"
    return 0
  catch e =>
    IO.println s!"KERNEL REPLAY FAILED: {e}"
    return 1
