import Frontier.CHD.FPBind
import Frontier.CHD.PartitionMap

/-!
# Frontier.CHD.FPBridge — from the RAM FindPivots output to the call relation's FindPivots conjunct (owner agent-03)

**NON-GATE** (Layer A glue).  `fpFull_spec` (Layer B) ends in agent-05's pinned `FindPivotsC … trees cost` and the groups
`(forestGroups S Q k trees).map (map Fin.val)` in `GrpOut`.  Here:
* `fpC_of_findPivotsC`: that is exactly the first conjunct of `BMLazy.CallD` for `FPC = fpC out k hins hext`, with
  `p = |groups|`, `P j = (groups[j]).toFinset`, `ω = ⟨lxOf B S d0, trees, Din, Dout⟩`;
* `grpP_val`: the ℕ-groups stored by the RAM (agent-01's `copyGrp`, `grpP Gs j = Gs[j].toFinset`) are `(P j).image Fin.val`.
-/

namespace Frontier
namespace CHD

open Frontier Graph Frontier.CHD.Partition

variable {G : Graph} {s : Fin G.n}

/-- **The FindPivots conjunct of the call relation**, from the pinned relation. -/
theorem fpC_of_findPivotsC {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ} {lv : ℕ} {Blow B : WLab G s}
    {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {Din Dout : Finset (Fin G.m)} {Q W : Finset (Fin G.n)}
    {trees : List (TreeRec (Fin G.n))} {c : ℕ}
    (h : FindPivotsC out k hins hext B S d0 Din d1 Dout Q W trees c) :
    fpC G s out k hins hext lv Blow B S d0 Din d1 (forestGroups S Q k trees).length
      (fun j => ((forestGroups S Q k trees).get j).toFinset) Q W Dout ⟨lxOf B S d0, trees, Din, Dout⟩ c :=
  ⟨h, rfl, ⟨rfl, fun _ => rfl⟩, rfl, rfl⟩

/-- The RAM's word groups are the Layer-A groups relabelled by `Fin.val`. -/
theorem grpP_val (Gs : List (List (Fin G.n))) (j : ℕ) (hj : j < Gs.length) :
    ((Gs.map (List.map Fin.val))[j]'(by simpa using hj)).toFinset = (Gs[j].toFinset).image Fin.val := by
  simp only [List.getElem_map]
  exact toFinset_map' Fin.val _

end CHD
end Frontier
