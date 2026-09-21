import Frontier.CHD.BMCost
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Frontier.CHD.BaseCostDeg — the base loop's cost index pays each returned vertex's out-degree (owner agent-03)

**NON-GATE** (Layer A).  Every step of `BaseLoopC` extracts `u` and charges `1 + bext + |L|(1 + bins)` with `L` the full
out-list of `u` (`Enumerates G L {u}`).  `baseLoopC_deg_le`: the vertices added to the returned set pay
`Σ (outdeg u + 1) ≤ c`.  This pays for the base case's pointer pass (agent-02's `ptrSet`, `25·deg u + 30` per
returned `u`) and the heap clear.
-/

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- The out-degree of `u`. -/
def outdeg (u : Fin G.n) : ℕ := (Finset.univ.filter (fun e : Fin G.m => G.src e = u)).card

theorem Enumerates.length_eq {L : List (Fin G.m)} {u : Fin G.n} (h : Enumerates G L {u}) :
    L.length = outdeg u := by
  classical
  obtain ⟨hnd, hmem⟩ := h
  rw [← List.toFinset_card_of_nodup hnd]
  unfold outdeg
  congr 1
  ext e
  simp [hmem e]

theorem baseLoopC_deg_le {DC : DCost} {B : WLab G s} {τ : ℕ} :
    ∀ {st st' : Labels G s × DS G s × Finset (Fin G.n)} {c : ℕ}, BaseLoopC G s DC B τ st st' c →
      (∑ u ∈ st'.2.2 \ st.2.2, (outdeg u + 1)) ≤ c := by
  classical
  intro st st' c h
  induction h with
  | stop st _ => simp
  | step d D U u val L st' c _ _ _ hL _ ih =>
    have hsub : st'.2.2 \ U ⊆ insert u (st'.2.2 \ insert u U) := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      by_cases hxu : x = u
      · exact Finset.mem_insert.mpr (Or.inl hxu)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx.1, fun h => hx.2 (by
          rcases Finset.mem_insert.mp h with h | h
          · exact absurd h hxu
          · exact h)⟩))
    have h1 := Finset.sum_le_sum_of_subset (f := fun u => outdeg u + 1) hsub
    have hun : u ∉ st'.2.2 \ insert u U := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self u U)
    have h2 := Finset.sum_insert (f := fun u => outdeg u + 1) hun
    have hLl := hL.length_eq
    have : L.length * (1 + DC.bins) ≥ L.length := Nat.le_mul_of_pos_right _ (by omega)
    simp only at ih ⊢
    omega

end BM
end CHD
end Frontier
