import Frontier.CHD.Final
import Frontier.AuditGateC

/-! agent-02 (reviewer #2): closedness and exact types of the final theorems -/

-- closedness: each theorem has exactly the frozen target type, with no hypotheses
example : Frontier.GateC := Frontier.CHD.Final.chd_gateC
example : Frontier.GateCTarget.CHDTarget Frontier.GateCCalc.F := Frontier.CHD.Final.chd_CHDTarget
-- the strong (uniform-over-the-class) audit form
example : Frontier.Audit.GateC Frontier.Audit.ramModel :=
  Frontier.AuditGateC.chdTarget_imp_auditGateC Frontier.CHD.Final.chd_CHDTarget

#check @Frontier.CHD.Final.chd_gateC
#check @Frontier.CHD.Final.chd_CHDTarget
#check @Frontier.CHD.Final.chd_exact_within
#print Frontier.GateC
#print Frontier.GateCTarget.CHDTarget
#print Frontier.GateCTarget.Tdisp
#print Frontier.GateCCalc.F
#print Frontier.RAM.Program.Exact
#print Frontier.RAM.Program.RunsWithin
#print axioms Frontier.CHD.Final.chd_gateC
#print axioms Frontier.CHD.Final.chd_CHDTarget
#print axioms Frontier.CHD.Final.chdProgram
#print axioms Frontier.AuditGateC.chdTarget_imp_auditGateC
