import Frontier.CostModel
import Frontier.GateCCalc

/-!
# Frontier.GateC — top-level Gate-C target statement (owner: agent-10)

**Status: STATEMENT ONLY. `CHDTarget` is NOT proved.** This file fixes the exact theorem the C-HD
candidate (theorem card by agent-09, board 10:47) must establish, in the CostModel v2 deep-embedded
RAM + comparison-addition machine, and proves (kernel-checked, no gap) that it would imply
`Frontier.GateC`. Proving `CHDTarget` requires the complete costed algorithm, its exactness and its
running-time bound; none of that exists yet.

`CHDTarget F`: one uniform program `P` (a finite `Stmt` tree), exact on every graph and source, whose
unique terminating run costs at most `C * Tchd n m` whenever `m ≤ n * F n` (and `C (n+1)(m+1)`
otherwise), where `Tchd n m = n + m + m log(m/(n+1) + 2) + m^(1/3) (n log(n+2))^(2/3)`.
-/

open Real Filter Topology

namespace Frontier.GateCTarget

open Frontier Frontier.RAM Frontier.GateCCalc

/-- The cost bound claimed for a program that runs C-HD on graphs with `m ≤ n * F n` and any exact
fallback (e.g. agent-08's verified Bellman-Ford) with an `O((n+1)(m+1))` bound on all other graphs.
`F` is the program's own (integer-computable) density threshold. -/
noncomputable def Tdisp (F : ℕ → ℕ) (n m : ℕ) : ℝ :=
  if m ≤ n * F n then Tchd n m else ((n : ℝ) + 1) * ((m : ℝ) + 1)

/-- The Gate-C target for the C-HD candidate, parametrized by the dispatch threshold `F`
(NOT proved). -/
def CHDTarget (F : ℕ → ℕ) : Prop :=
  ∃ P : Program, P.Exact ∧ ∃ C : ℝ, ∀ (G : Graph) (s : Fin G.n),
    P.RunsWithin G s (C * Tdisp F G.n G.m)

/-- If the threshold eventually dominates the profile multiplier `s n = ⌊log(n+2)^(3/4)⌋₊`,
the target implies CostModel's Gate C along `μ n = n * s n`. -/
theorem chdTarget_imp_gateC (F : ℕ → ℕ) (hF : ∀ᶠ n : ℕ in atTop, s n ≤ F n) :
    CHDTarget F → GateC := by
  rintro ⟨P, hP, C, hC⟩
  refine ⟨P, hP, fun n m => C * Tdisp F n m, fun G s => hC G s, μ, mu_window, ?_⟩
  have h1 := tendsto_Tchd_mu.const_mul C
  simp only [mul_zero] at h1
  refine h1.congr' ?_
  filter_upwards [hF] with n hn
  have hle : μ n ≤ n * F n := by
    unfold μ; exact Nat.mul_le_mul_left n hn
  simp [Tdisp, hle, mul_div_assoc]

/-- Uniform variant (agent-09's draft `CHD_Target`, 11:13, with natural logs): the C-HD bound for EVERY
graph, no dispatch.  (A base-2-log version implies this one with a larger constant.) -/
def CHDTargetU : Prop :=
  ∃ P : Program, P.Exact ∧ ∃ C : ℝ, ∀ (G : Graph) (s : Fin G.n),
    P.RunsWithin G s (C * Tchd G.n G.m)

theorem chdTargetU_imp_gateC : CHDTargetU → GateC := by
  rintro ⟨P, hP, C, hC⟩
  refine ⟨P, hP, fun n m => C * Tchd n m, fun G s => hC G s, μ, mu_window, ?_⟩
  have := tendsto_Tchd_mu.const_mul C
  simpa [mul_div_assoc] using this

/-- The concrete corollary for the integer-computable threshold `F n = ⌊(log₂ n)^(3/4)⌋`
(`Frontier.GateCCalc.F`): proving `CHDTarget GateCCalc.F` establishes CostModel's Gate C. -/
theorem chdTarget_F_imp_gateC : CHDTarget GateCCalc.F → GateC :=
  chdTarget_imp_gateC GateCCalc.F F_dominates

end Frontier.GateCTarget

#print axioms Frontier.GateCTarget.chdTarget_imp_gateC
#print axioms Frontier.GateCTarget.chdTarget_F_imp_gateC
#print axioms Frontier.GateCTarget.chdTargetU_imp_gateC
#print axioms Frontier.GateCCalc.tendsto_Tchd_mu
#print axioms Frontier.GateCCalc.mu_window
