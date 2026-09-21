import Frontier.CHD.L6.MasterGlue
import Frontier.CHD.L6.SpineTop

/-!
# The C-HD route, end to end (agent-10)

`chdTarget_of_parts`: for admissible cost parameters `P` (`GoodP`), a spine prologue `pro` with
`ProSpec` (allocations + top-call frame, agent-10/03/04) and the top-level call with `CallSpec`
(agent-08's recursion theorem at level `LF`) give the frozen Gate-C target `CHDTarget F`, for a
word exponent `e ≥ 32` large enough for the constants.
NON-GATE (composition; `ProSpec` and `CallSpec` are the open obligations).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM

theorem chdTarget_of_parts (e : ℕ) (he : 32 ≤ e) (ps : List Stmt) (pro : Stmt)
    {P : ℕ → ℕ → CostPar} {ch ce cb : ℕ} (hP : GoodP P ch ce cb) {TopIn : TopInv}
    {Kp K K0 Kpol : ℝ} {Dp : ℕ} (hDp : 2 ≤ Dp) (hKp : 0 ≤ Kp) (hK : 0 ≤ K) (hK0 : 0 ≤ K0)
    (hbig : 12 + (K + Kp + K0) * (kmaster ch ce cb + 1) + |(0 : ℝ)| + |Kpol| ≤
      (4 : ℝ) ^ (e + 1 - Dp))
    (hpro : ProSpec e ps pro TopIn Kp) (hcall : CallSpec P TopIn K K0 Kpol (kmaster ch ce cb) Dp) :
    GateCTarget.CHDTarget GateCCalc.F :=
  chdTarget_of_spine_good e he ps (spineOf pro) hP (K + Kp + K0) 0 Kpol Dp hDp (by linarith) hbig
    (spineSpec_of_parts hKp hK hK0 hpro hcall)

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.chdTarget_of_parts
