import Frontier.CHD.L6.SpineIface
import Frontier.CHD.MasterCost

/-!
# `MasterSpec` from the Layer-A master cost theorem (agent-06, COORD G2-8 (b); NON-GATE)

For every choice `P` of cost parameters in the class `GoodP P ch ce cb` (FindPivots' insertion charge `≤ ch`,
extraction charge `≤ ce (k+1)`, base heap costs `≤ cb (log₂(t+1) + log₂(dd+1) + 2)`), every Layer-A top-level
run `TopRun` on a graph with at least one edge has `lg.cost ≤ Km · Tchd cn cm` with the explicit constant
`kmaster ch ce cb = 5100 · cMaster (2 (scanC + ch) + ce + 2) cb · 56` (`BM.master_cost_D`).

`masterSpec_of_goodP` is `MasterSpec` itself under the extra graph fact `1 ≤ H.m` (`MasterInM`): the cost chain's
`Valid.wit` needs an edge type.  The core wrapper has to treat `H.m = 0` separately (only `src` is reachable).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.CHD Frontier.CHD.BM

/-- The class of cost parameters covered by the master cost theorem. -/
structure GoodP (P : ℕ → ℕ → CostPar) (ch ce cb : ℕ) : Prop where
  hins : ∀ cn cm, (P cn cm).hins ≤ ch
  hext : ∀ cn cm, (P cn cm).hext ≤ ce * (CostSkeleton.kF cn cm + 1)
  bins : ∀ cn cm, (P cn cm).DCb.bins ≤
    cb * (Nat.log 2 (CostSkeleton.tF cn cm + 1) + Nat.log 2 (CostSkeleton.dd cn cm + 1) + 1 + 1)
  bext : ∀ cn cm, (P cn cm).DCb.bext ≤
    cb * (Nat.log 2 (CostSkeleton.tF cn cm + 1) + Nat.log 2 (CostSkeleton.dd cn cm + 1) + 1 + 1)

/-- The explicit master constant. -/
noncomputable def kmaster (ch ce cb : ℕ) : ℝ :=
  5100 * (cMaster (2 * (scanC + ch) + ce + 2) cb : ℕ) * ((56 : ℕ) : ℝ)

/-- **The master cost theorem in `MasterSpec` form** (with `1 ≤ H.m`). -/
theorem masterSpec_of_goodP {P : ℕ → ℕ → CostPar} {ch ce cb : ℕ} (hP : GoodP P ch ce cb) :
    ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ), MasterIn H src cn cm → 1 ≤ H.m →
    ∀ (T : ℕ → ℕ) (Blow : WLab H src), Blow ≤ BM.initLabels src src →
    ∀ (res : BM.ResultD H src) (φ' : Finset (Fin H.m)) (gE : BM.DGl H src)
      (lg : BM.Log H src (FPData H src)), TopRun H src cn cm (P cn cm) T Blow res φ' gE lg →
      (lg.cost : ℝ) ≤ kmaster ch ce cb * GateCCalc.Tchd cn cm := by
  intro H src cn cm hM hm1 T Blow hlow res φ' gE lg hrun
  have ha := fpA_le_of (k := CostSkeleton.kF cn cm) (hP.hins cn cm) (hP.hext cn cm)
  have hI : DelInv H src (∅ : Finset (Fin H.m)) := fun e he => absurd he (Finset.notMem_empty e)
  exact master_cost_D (fun _ _ => outL_mem) hM.sorted hM.simple hM.cn_pos hM.cm_pos hM.cn_le hM.sizeN
    hM.sizeM hm1 hM.deg le_rfl hM.dens ha (hP.bins cn cm) (hP.bext cn cm) hlow hI hrun

end Frontier.CHD.L6
