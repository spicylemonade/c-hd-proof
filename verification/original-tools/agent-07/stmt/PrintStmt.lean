import Frontier.GateC
import Frontier.CHD.Dispatch
set_option pp.proofs false
#print Frontier.GateC
#print Frontier.GateCTarget.CHDTarget
#print Frontier.GateCCalc.Tchd
#print Frontier.GateCCalc.F
#check @Frontier.GateCTarget.chdTarget_F_imp_gateC
#check @Frontier.CHD.Dispatch.chdTarget_of_body
