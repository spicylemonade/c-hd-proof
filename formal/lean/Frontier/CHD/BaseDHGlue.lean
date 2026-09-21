import Frontier.CHD.BMLazy
import Frontier.CHD.BaseGlue

/-!
# Frontier.CHD.BaseDHGlue — the literal base case plus the leftover conversion is `BaseDH` (owner agent-03)

**NON-GATE** (Layer A glue).  agent-08's RAM base case (`baseBody_spec`) refines the literal `BaseC` with the store in
the shape `Dof T' d'` (keys = labels on the heap set `T'`); agent-03's `baseConv_spec` inserts a duplicate-free
enumeration `lK` of `T'` into `newC M₀ B`.  `baseDH_of_baseC`: together they are agent-01's `BaseDH` (the base case of
`BMSSPD`), with the result's structure `(insManyC … lK g0 (newC M₀ B)).2.1`, the global state `.1`, and a log whose cost
is the literal log's cost plus the conversion's.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

theorem baseDH_of_baseC (ops : DOps G s) {Φ Ω : Type} {DC : DCost} {T M0 : ℕ} {Blow B : WLab G s}
    {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 : Φ} {g0 : DGl G s} {τ : ℕ} {res : Result G s}
    {lg : Log G s Ω} (h : BaseC G s DC Blow B S d0 φ0 τ res φ0 lg) {T' : Finset (Fin G.n)}
    (hT' : res.2.2.1 = Dof T' res.2.2.2) {lK : List (Fin G.n)} (hnd : lK.Nodup) (hset : lK.toFinset = T') :
    ∃ lgD : Log G s Ω, BaseDH G s ops DC T M0 Blow B S d0 φ0 g0 τ
        (res.1, res.2.1, (insManyC ops T res.2.2.2 lK g0 (newC M0 B)).2.1, res.2.2.2) φ0
        (insManyC ops T res.2.2.2 lK g0 (newC M0 B)).1 lgD ∧
      Log.cost lgD = Log.cost lg + (insManyC ops T res.2.2.2 lK g0 (newC M0 B)).2.2 := by
  obtain ⟨st, c, hloop, hU, hD, hd, hemp, hne, -, rfl⟩ := h
  refine ⟨_, ⟨st, c, lK, hloop, hnd, fun y => ?_, hU, hd, by rw [hd], by rw [hd], hemp, hne, rfl, rfl⟩, ?_⟩
  · rw [← hD, hT', Dof_apply]
    have e : y ∈ lK ↔ y ∈ T' := by rw [← hset, List.mem_toFinset]
    by_cases hy : y ∈ T' <;> simp [hy, e]
  · rw [hd]
    simp [Log.cost]

end BM
end CHD
end Frontier
