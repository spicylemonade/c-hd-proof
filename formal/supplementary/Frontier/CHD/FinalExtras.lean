import Frontier.CHD.Final
import Frontier.AuditGateC

/-!
# Frontier.CHD.FinalExtras — space and the strong-form gate for the C-HD witness (agent-01)

**NON-GATE** (corollaries of the frozen `Frontier.CHD.Final`; this file is outside its import
closure).
* `chd_space`: on every graph and source, the unique terminating run of `Final.chdProgram` solves
  the instance and its cost AND its allocated space are both at most `C · Tdisp F n m`
  (space ≤ cost in the RAM model, `RAMAudit.run_space_le_cost`).
* `chd_auditGateC`: agent-09's independent strong-form gate `Audit.GateC ramModel` (exact, and
  `o(n lg n)` worst case on ALL graphs with `m ≤ n · max 1 (F n)`) for the same witness, via
  `AuditGateC.chdTarget_imp_auditGateC`.
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.FinalExtras

open Frontier Frontier.RAM Frontier.CHD.Final

/-- **Time and space of the C-HD witness**: the unique terminating run solves the instance, and its
cost and allocated space are both at most `C · Tdisp F n m`. -/
theorem chd_space (G : Graph) (s : Fin G.n) :
    ∃ fuel r, chdProgram.run fuel G s = some r ∧ r.Solves G s ∧
      (r.cost : ℝ) ≤ (L6.bodyC KcC + 65536 * 9 + 100) * GateCTarget.Tdisp GateCCalc.F G.n G.m ∧
      (r.space : ℝ) ≤ (L6.bodyC KcC + 65536 * 9 + 100) * GateCTarget.Tdisp GateCCalc.F G.n G.m := by
  obtain ⟨f, r, hr, hsol⟩ := chd_exact_within.1 G s
  have hc := Program.runsWithin_unique (chd_exact_within.2 G s) hr
  have h := Frontier.Audit.RAMAudit.run_space_le_cost chdProgram f G s r hr
  have h' : (r.space : ℝ) ≤ r.cost := by exact_mod_cast h
  exact ⟨f, r, hr, hsol, hc, le_trans h' hc⟩

/-- **The strong-form audit gate** (agent-09's `Audit.GateC` for the RAM machine) for the C-HD
witness: exact, and `o(n lg n)` on every graph with `m ≤ n · max 1 (F n)`. -/
theorem chd_auditGateC : Frontier.Audit.GateC Frontier.Audit.ramModel :=
  Frontier.AuditGateC.chdTarget_imp_auditGateC chd_CHDTarget

end Frontier.CHD.FinalExtras

#print axioms Frontier.CHD.FinalExtras.chd_space
#print axioms Frontier.CHD.FinalExtras.chd_auditGateC
