/-
agent-07 (reviewer #1) independent kernel replay, in the style of lean4checker, using core `Lean.Kernel.Environment.replay`.
Usage (from a Lake project root):  lake env lean --run Replay07.lean <RootModule> <theorem> [<theorem> ...]
1. Imports <RootModule>. Collects every constant whose defining module is in the `Frontier` namespace.
2. Builds a base environment from the NON-Frontier modules those Frontier modules import directly (Mathlib/core).
3. Replays all Frontier constants into the base environment. The kernel re-checks every definition and theorem.
4. Prints the axioms of each given theorem, collected on the replayed environment.
Read-only: it never writes .olean files.
-/
import Lean
open Lean

def isFrontier (m : Name) : Bool := (`Frontier).isPrefixOf m

partial def collectAxiomsKernel (env : Kernel.Environment) (n : Name) : StateM (NameSet × Array Name) Unit := do
  let (seen, _) ← get
  if seen.contains n then return
  modify fun (s, a) => (s.insert n, a)
  match env.find? n with
  | some (.axiomInfo _) => modify fun (s, a) => (s, a.push n)
  | some ci => for c in ci.getUsedConstantsAsSet do collectAxiomsKernel env c
  | none => pure ()

def main (args : List String) : IO UInt32 := do
  match args with
  | [] => IO.eprintln "usage: Replay07 <RootModule> [theorems...]"; return 2
  | root :: thms =>
  initSearchPath (← findSysroot)
  let rootName := root.toName
  let env ← importModules #[{ module := rootName }] {} (trustLevel := 0) (loadExts := false)
  let header := env.header
  -- modules of the import closure, with their direct imports
  let mods := header.moduleNames
  let frontierMods := mods.filter isFrontier
  IO.println s!"import closure: {mods.size} modules, Frontier modules: {frontierMods.size}"
  IO.println s!"Frontier modules in closure: {frontierMods.toList}"
  let nonStd := mods.filter fun m => !(isFrontier m) && !((`Mathlib).isPrefixOf m) && !((`Lean).isPrefixOf m) && !((`Init).isPrefixOf m)
    && !((`Std).isPrefixOf m) && !((`Batteries).isPrefixOf m) && !((`Aesop).isPrefixOf m) && !((`Qq).isPrefixOf m)
    && !((`ProofWidgets).isPrefixOf m) && !((`Plausible).isPrefixOf m) && !((`LeanSearchClient).isPrefixOf m) && !((`ImportGraph).isPrefixOf m)
  IO.println s!"modules outside Frontier/Mathlib/Lean/Init/Std/Batteries/Aesop/Qq/ProofWidgets/Plausible/LeanSearchClient/ImportGraph: {nonStd.toList}"
  -- base imports: non-Frontier modules imported directly by some Frontier module
  let mut baseImports : NameSet := {}
  for i in [0:mods.size] do
    if isFrontier mods[i]! then
      for imp in header.moduleData[i]!.imports do
        if !isFrontier imp.module then baseImports := baseImports.insert imp.module
  IO.println s!"base (non-Frontier) direct imports: {baseImports.toList.length}"
  -- constants defined in Frontier modules
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  for i in [0:mods.size] do
    if isFrontier mods[i]! then
      for n in header.moduleData[i]!.constNames, ci in header.moduleData[i]!.constants do
        newConsts := newConsts.insert n ci
  IO.println s!"Frontier constants to replay: {newConsts.size}"
  let baseEnv ← importModules (baseImports.toList.map fun m => { module := m }).toArray {} (trustLevel := 0) (loadExts := false)
  let t0 ← IO.monoMsNow
  let kenv ← baseEnv.toKernelEnv.replay newConsts
  let t1 ← IO.monoMsNow
  IO.println s!"REPLAY OK: all {newConsts.size} Frontier constants re-checked by the kernel in {t1 - t0} ms"
  for t in thms do
    let n := t.toName
    match kenv.find? n with
    | none => IO.println s!"{t}: NOT FOUND in replayed environment"
    | some _ =>
      let ((), (_, axs)) := (collectAxiomsKernel kenv n).run ({}, #[])
      IO.println s!"{t}: axioms = {axs.toList}"
  return 0
