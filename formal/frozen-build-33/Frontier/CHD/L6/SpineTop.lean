import Frontier.CHD.L6.SpineIface

/-!
# The spine as prologue + top-level call (agent-10, COORD G2-9)

`spineOf pro = seq pro (call P_bmssp)`.  `spineSpec_of_parts` derives `SpineSpec` from

* `ProSpec`: the prologue (`n := gN`, the allocations, the top-call frame) reaches a state of the
  spine's top-call invariant `TopIn` at cost `≤ Kp Tchd`, keeping the frame;
* `CallSpec`: from `TopIn` and the budget, `call P_bmssp` ends with the label table of a Layer-A
  top-level run (`TopRun`), the frame, and cost `≤ K lg.cost + K0`.

`TopIn` is a parameter: it is the spine team's representation of the top call's arguments
(frontier `{src}`, bound `⊤`, `Blow`, level `LF`, empty `D`, …).  NON-GATE (composition).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab WExpr Stmt

/-- The procedure number of the BMSSP body (agent-08's `RamSpine.P_bmssp`). -/
def pBmssp : ℕ := 0

/-- The spine: a prologue, then the top-level call. -/
def spineOf (pro : Stmt) : Stmt := seq pro (call pBmssp)

/-- The top-call invariant: a predicate on the state, indexed by the instance and the label-clock
origin `c0`. -/
abbrev TopInv := ∀ (H : Graph) (src : Fin H.n) (cn cm c0 : ℕ), State ℝ≥0 → Prop

/-- **The prologue specification**: from `SpineIn`, reach `TopIn` at cost `≤ Kp Tchd`, keeping
the frame. -/
def ProSpec (e : ℕ) (ps : List Stmt) (pro : Stmt) (TopIn : TopInv) (Kp : ℝ) : Prop :=
  ∀ (H : Graph) (src : Fin H.n) (cn cm c0 : ℕ) (t : State ℝ≥0), SpineIn e ps H src cn cm c0 t →
    Runs realOps pro t (fun r => TopIn H src cn cm c0 r ∧ SpineFrame t r ∧
      (r.cost : ℝ) ≤ t.cost + Kp * GateCCalc.Tchd cn cm)

/-- **The top-level call specification** (agent-08's recursion theorem at the top level): from
`TopIn` and the budget, `call P_bmssp` ends with the label table of a `TopRun`, the frame, and
cost `≤ K lg.cost + K0` above the start. -/
def CallSpec (P : ℕ → ℕ → CostPar) (TopIn : TopInv) (K K0 Kpol Km : ℝ) (Dp : ℕ) : Prop :=
  ∀ (H : Graph) (src : Fin H.n) (cn cm c0 : ℕ) (r : State ℝ≥0), TopIn H src cn cm c0 r →
    (∀ (T : ℕ → ℕ) (Blow : WLab H src), Blow ≤ BM.initLabels src src →
      ∀ (res : BM.ResultD H src) (φ' : Finset (Fin H.m)) (gE : BM.DGl H src)
        (lg : BM.Log H src (FPData H src)), TopRun H src cn cm (P cn cm) T Blow res φ' gE lg →
        (r.cost : ℝ) + K * (lg.cost : ℝ) + K0 + Kpol * ((cn : ℝ) + cm + 2) ^ Dp ≤ c0 + r.cap) →
    MasterBound H src cn cm (P cn cm) Km →
    Runs realOps (call pBmssp) r (fun r' => ∃ (T : ℕ → ℕ) (Blow : WLab H src)
      (res : BM.ResultD H src) (φ' : Finset (Fin H.m)) (gE : BM.DGl H src)
      (lg : BM.Log H src (FPData H src)) (Hh : Fin H.n → ℕ → List (Fin H.m)) (c1 : ℕ),
      Blow ≤ BM.initLabels src src ∧ TopRun H src cn cm (P cn cm) T Blow res φ' gE lg ∧
      LabAt (s := src) r' res.2.2.2 Hh c1 ∧ SpineFrame r r' ∧
      (r'.cost : ℝ) ≤ r.cost + K * (lg.cost : ℝ) + K0)

theorem SpineFrame.trans {t r r' : State ℝ≥0} (h1 : SpineFrame t r) (h2 : SpineFrame r r') :
    SpineFrame t r' :=
  ⟨⟨h2.keep.1.trans h1.keep.1, h2.keep.2.trans h1.keep.2⟩,
   ⟨h2.rep.1.trans h1.rep.1, h2.rep.2.trans h1.rep.2⟩,
   h2.n.trans h1.n, h2.s.trans h1.s, h2.m.trans h1.m, h2.cap.trans h1.cap⟩

/-- **`SpineSpec` from the prologue and the top-level call.**  The constants: `Ks = K + Kp + K0`
(using `1 ≤ Tchd`), `Kb = 0`. -/
theorem spineSpec_of_parts {e : ℕ} {ps : List Stmt} {pro : Stmt} {P : ℕ → ℕ → CostPar}
    {TopIn : TopInv} {Kp K K0 Kpol Km : ℝ} {Dp : ℕ} (hKp : 0 ≤ Kp) (hK : 0 ≤ K) (hK0 : 0 ≤ K0)
    (hpro : ProSpec e ps pro TopIn Kp) (hcall : CallSpec P TopIn K K0 Kpol Km Dp) :
    SpineSpec e ps (spineOf pro) P (K + Kp + K0) 0 Kpol Km Dp := by
  intro H src cn cm c0 t hS hbud hmas
  have hTn : (cn : ℝ) ≤ GateCCalc.Tchd cn cm := CostSkeleton.n_le_Tchd cn cm
  have hcn1 : (1 : ℝ) ≤ cn := by exact_mod_cast hS.core.cn_pos
  have hT1 : (1 : ℝ) ≤ GateCCalc.Tchd cn cm := le_trans hcn1 hTn
  unfold spineOf
  refine runs_seq ((hpro H src cn cm c0 t hS).mono ?_)
  rintro r ⟨hTop, hF1, hc1⟩
  have hbud' : ∀ (T : ℕ → ℕ) (Blow : WLab H src), Blow ≤ BM.initLabels src src →
      ∀ (res : BM.ResultD H src) (φ' : Finset (Fin H.m)) (gE : BM.DGl H src)
        (lg : BM.Log H src (FPData H src)), TopRun H src cn cm (P cn cm) T Blow res φ' gE lg →
        (r.cost : ℝ) + K * (lg.cost : ℝ) + K0 + Kpol * ((cn : ℝ) + cm + 2) ^ Dp ≤
          c0 + r.cap := by
    intro T Blow hlow res φ' gE lg hrun
    have h := hbud T Blow hlow res φ' gE lg hrun
    have hcap : (r.cap : ℝ) = t.cap := by rw [hF1.cap]
    have hlg : (0 : ℝ) ≤ lg.cost := Nat.cast_nonneg _
    have e1 : K * (lg.cost : ℝ) ≤ (K + Kp + K0) * lg.cost := by nlinarith
    have e2 : Kp * GateCCalc.Tchd cn cm + K0 ≤ (K + Kp + K0) * GateCCalc.Tchd cn cm := by
      nlinarith
    rw [hcap]
    nlinarith
  refine (hcall H src cn cm c0 r hTop hbud' hmas).mono ?_
  rintro r' ⟨T, Blow, res, φ', gE, lg, Hh, c1, hlow, hrun, hLab, hF2, hc2⟩
  refine ⟨T, Blow, res, φ', gE, lg, Hh, c1, hlow, hrun, hLab, hF1.trans hF2, ?_⟩
  have hlg : (0 : ℝ) ≤ lg.cost := Nat.cast_nonneg _
  have e1 : K * (lg.cost : ℝ) ≤ (K + Kp + K0) * lg.cost := by nlinarith
  have e2 : Kp * GateCCalc.Tchd cn cm + K0 ≤ (K + Kp + K0) * GateCCalc.Tchd cn cm := by
    nlinarith
  nlinarith

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.spineSpec_of_parts
