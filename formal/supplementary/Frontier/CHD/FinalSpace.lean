import Frontier.CHD.Final
import Frontier.AuditBridge

/-!
# Space corollary for the C-HD witness (agent-05, NON-GATE; a NEW file outside Final's closure)

`chd_space_within`: on every graph and source, the unique terminating run of `Final.chdProgram`
solves the instance, and its allocated SPACE is at most its cost, hence at most the same bound
`C · Tdisp F n m` as its time.  (From `Final.chd_exact_within`, `exec_det` and the model invariant
`Frontier.Audit.RAMAudit.run_space_le_cost`.)  No `O(n+m)` space claim is made: the program preallocates the
D-structure arrays with `Θ(Tnat)` cells.
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.FinalSpace

open Frontier Frontier.RAM Frontier.CHD Frontier.CHD.Final

/-- **Time and space of the C-HD witness.** -/
theorem chd_space_within : ∀ (G : Graph) (s : Fin G.n), ∃ (fuel : ℕ) (r : State ℝ≥0),
    chdProgram.run fuel G s = some r ∧ r.Solves G s ∧
      (r.space : ℝ) ≤ (r.cost : ℝ) ∧
      (r.cost : ℝ) ≤ (L6.bodyC KcC + 65536 * 9 + 100) * GateCTarget.Tdisp GateCCalc.F G.n G.m := by
  intro G s
  obtain ⟨f, r, hr, hsol⟩ := chd_exact_within.1 G s
  obtain ⟨f', r', hr', hc⟩ := chd_exact_within.2 G s
  have hrr : r = r' := exec_det realOps hr hr'
  subst hrr
  refine ⟨f, r, hr, hsol, ?_, hc⟩
  exact_mod_cast Frontier.Audit.RAMAudit.run_space_le_cost chdProgram f G s r hr

end Frontier.CHD.FinalSpace

#print axioms Frontier.CHD.FinalSpace.chd_space_within
