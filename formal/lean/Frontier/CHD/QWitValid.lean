import Frontier.CHD.CostLe
import Frontier.CHD.QWitProv

/-!
# Frontier.CHD.QWitValid — the `Q`-witness fields of `Valid` for the traced counters (tracker O22; owner agent-03)

**NON-GATE** (Layer A).  Restates `QWitProv.bmsspC_qwit` in the shape of `CostAggregate.Valid.wit_mem`,
`Valid.wit_inj`, `Valid.src_once` and `Valid.inE_card` for `tracedCounters`, with `inE v` the in-edges of `v`.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- The in-edges of a vertex. -/
def inEdges (G : Graph) (v : Fin G.n) : Finset (Fin G.m) := Finset.univ.filter (fun e => G.dst e = v)

/-- `Valid.inE_card`. -/
theorem inEdges_card : ∑ v, (inEdges G v).card ≤ Fintype.card (Fin G.m) := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro v _ w _ hvw
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    simp only [inEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    exact hvw (he.symm.trans he')

variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s (FPData G s)} (hL : LogInv τ L0 lg)

/-- **The witness fields of `Valid` for `tracedCounters`**, from any witness with the three properties of
`bmsspC_qwit`. -/
theorem tracedCounters_wit (wit : lg.Call → Fin G.n → Fin G.m)
    (h1 : ∀ X, (lg.recOf X).B' = (lg.recOf X).B → ∀ v ∈ (lg.recOf X).Q, v ≠ s → G.dst (wit X v) = v)
    (h2 : ∀ v X X', (lg.recOf X).B' = (lg.recOf X).B → (lg.recOf X').B' = (lg.recOf X').B →
      v ∈ (lg.recOf X).Q → v ∈ (lg.recOf X').Q → wit X v = wit X' v → X = X')
    (h3 : ∀ X X', (lg.recOf X).B' = (lg.recOf X).B → (lg.recOf X').B' = (lg.recOf X').B →
      s ∈ (lg.recOf X).Q → s ∈ (lg.recOf X').Q → X = X') :
    (∀ X, (tracedCounters hL).full X = true → ∀ v ∈ (tracedCounters hL).Q X, v ≠ s →
      wit X v ∈ inEdges G v) ∧
    (∀ v X X', (tracedCounters hL).full X = true → (tracedCounters hL).full X' = true →
      v ∈ (tracedCounters hL).Q X → v ∈ (tracedCounters hL).Q X' → wit X v = wit X' v → X = X') ∧
    (∀ X X', (tracedCounters hL).full X = true → (tracedCounters hL).full X' = true →
      s ∈ (tracedCounters hL).Q X → s ∈ (tracedCounters hL).Q X' → X = X') := by
  have hfull : ∀ X, (tracedCounters hL).full X = true → (lg.recOf X).B' = (lg.recOf X).B :=
    fun X h => of_decide_eq_true h
  refine ⟨fun X hX v hv hvs => ?_, fun v X X' hX hX' hv hv' heq => h2 v X X' (hfull X hX) (hfull X' hX') hv hv' heq,
    fun X X' hX hX' hs hs' => h3 X X' (hfull X hX) (hfull X' hX') hs hs'⟩
  simp only [inEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h1 X (hfull X hX) v hv hvs

end BM
end CHD
end Frontier
