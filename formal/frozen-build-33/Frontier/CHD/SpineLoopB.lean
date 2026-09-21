import Frontier.CHD.SpinePostA
import Frontier.CHD.SpinePostProof
import Frontier.CHD.RamBody

/-!
# SpineLoopB — the main loop as the level body's loop interface (agent-08, B-L4, NON-GATE)

`loop2_spec`, with agent-06's second half (`postSpec`, through `postHalf_of_stmt`), is the loop
interface of agent-01's level body: a projection with the cost sums reordered.  The interface is
stated here as `LoopSpecB2` (agent-01's `LoopSpecB` with the factor-2 use of `CallSpec` and the frame
`LFrame`); `loopSpecB_of_loop2` / `loopSpecB_of_postSpec` give agent-01's `RamBody.LoopSpecB` itself
(its `LoopFrame` has the fields of `LFrame`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab WExpr Stmt

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ Ω : Type}

/-- **The main loop of a call at level `l + 1`**, as the level body uses it: from `LoopRep ∧ ALoop`,
the budget and the room of every Layer-A run, `mainLoop dsEmpty iterB` realizes one `LoopD` run at
RAM cost `≤ K · lg.cost + Ko · (cc + cm)` and use `≤ 2 · (cc + cm + lg.cost)`. -/
def LoopSpecB2 (DL : DLayer G s T) (PI : PhiI Φ) (Inv : Φ → Prop) (FPC : FPRelC G s Φ Ω)
    (DCb : DCost) (Mf τ : ℕ → ℕ) (LF : ℕ) (body dsEmpty iterB : Stmt) (K Ko Sl : ℕ) (Sb : ℕ → ℕ)
    (l : ℕ) : Prop :=
  ∀ (st : State ℝ≥0) (B : WLab G s) (S : Finset (Fin G.n)) (d0 d1 : Labels G s) (p : ℕ)
    (P0 : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n)) (B'0 : WLab G s) (f0 : ℕ)
    (L0 : LiveM G s) (c : LoopCfgD G s Φ p) (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ),
    CallPre B S d0 → FPContract B S d0 d1 p P0 Q W →
    LoopRep DL PI LF body τ Mf st (l + 1) B (τ (l + 1)) Ds H c0 c →
    ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 c →
    (∀ c', ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 c' → ¬ LoopDoneD (τ (l + 1)) c' →
      ∀ ks Bi g1 Dc1 cp, pullC (dlOps G s) (T (l + 1)) c'.cs.g c'.cs.Dc = (ks, Bi, g1, Dc1, cp) →
      (BM.expand c'.cs.lit ks.toFinset Bi).card ≤ Sb l) →
    (∀ cs' φ' lg J cm cc, LoopD G s (dlOps G s) (T (l + 1)) (BMSSPD G s (dlOps G s) FPC DCb T Mf τ l)
      B (τ (l + 1)) c.i c.cs c.φ cs' φ' lg J cm cc →
      st.cost + K * lg.cost + Ko * (cc + cm) + Sl ≤ c0 + st.cap) →
    (∀ cs' φ' lg J cm cc, LoopD G s (dlOps G s) (T (l + 1)) (BMSSPD G s (dlOps G s) FPC DCb T Mf τ l)
      B (τ (l + 1)) c.i c.cs c.φ cs' φ' lg J cm cc → DL.use st + 2 * (cc + cm + lg.cost) ≤ DL.ucap) →
    Runs realOps (mainLoop dsEmpty iterB) st (fun r => ∃ (cs' : CSt G s p) (φ' : Φ) (lg : Log G s Ω)
      (J : Finset (Fin G.m)) (cm cc : ℕ) (H' : Hist G),
      LoopD G s (dlOps G s) (T (l + 1)) (BMSSPD G s (dlOps G s) FPC DCb T Mf τ l)
        B (τ (l + 1)) c.i c.cs c.φ cs' φ' lg J cm cc ∧
      LoopRep DL PI LF body τ Mf r (l + 1) B (τ (l + 1)) Ds H' c0 ⟨c.i, cs', φ'⟩ ∧
      ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 ⟨c.i, cs', φ'⟩ ∧
      HExt H (vc st) H' (vc r) ∧ LFrame st r G.n l ∧
      (∀ x : Fin G.n, x ∉ cs'.U → x ∉ c.cs.U → r.wa "sp.ptr" x = st.wa "sp.ptr" x) ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + K * lg.cost + Ko * (cc + cm) ∧
      DL.use r ≤ DL.use st + 2 * (cc + cm + lg.cost))

/-- **`loop2_spec` is the loop interface** of the level body, for any second half `PostHalf`. -/
theorem loopSpecB2_of_loop2 (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt}
    {τf Mf : ℕ → ℕ} {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} {DCb : DCost} {K Ko Sl : ℕ}
    {Sb : ℕ → ℕ} {l : ℕ}
    (hIH : CallSpec DL PI.PhiR Inv FPC DCb Mf τf LF body K Sl Sb l)
    {ltBi : Stmt} {CL : ℕ} {LW LV : List String}
    (hLt : ∀ (d : Labels G s) (H : Hist G) (c0 : ℕ) (Bi : WLab G s),
      LtI realOps ltBi (fun st => LabAt st d H c0 ∧ WHolds st KBi "sp.bif" H (vc st) Bi ∧
          1 < st.cap ∧ st.w "n" = G.n)
        (fun v => ∃ h : v < G.n, d ⟨v, h⟩ < Bi) CL LW LV)
    (hLWd : ∀ a ∈ LW, a ∉ DL.dWR) (hLWp : ∀ a ∈ LW, a ∉ PI.pWR)
    (hLWs : ∀ a ∈ LW, a ∉ ["gN", "hp_n", "core.n", "core.s", "core.m"])
    (hDP : ∀ a ∈ DL.dWA, a ∉ PI.pWA) (hDPr : ∀ a ∈ DL.dWR, a ∉ PI.pWR)
    {postI : Stmt} {Kp : ℕ}
    (hpost : PostHalf DL PI LF body τf Mf Inv FPC DCb l (seq postI DL.empty) Kp Sl)
    (hMf : ∀ l, (dlOps G s).mergeM (Mf (l + 1)) (Mf l)) {DC : DCost} {subC : SubRelC G s Φ Ω}
    (hsimsub : SimSub G s (dlOps G s) τf Inv Mf l (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) subC)
    (hsubC : GoodSub G s τf Inv l subC) (hDC : DC.M (l + 1) = Mf (l + 1)) (hτ1 : 1 ≤ τf l)
    (hsubT : TotalSub G s Inv (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l))
    (hKo : DL.K + CL + 71 + Kp + 1 ≤ Ko) (hKoD : DL.K + 1 ≤ Ko) :
    LoopSpecB2 DL PI Inv FPC DCb Mf τf LF body DL.empty (seq (firstHalf DL.pull ltBi) postI) K Ko Sl
      Sb l := by
  intro st B S d0 d1 p P0 Q W B'0 f0 L0 c Ds H c0 hpre hfp hrep hA hSb hbud hubud
  refine (loop2_spec DL PI hIH hLt hLWd hLWp hLWs hDP hDPr hpost hMf (DC := DC) hsimsub hsubC hDC hτ1
    hsubT hKo hKoD st B S d0 d1 p P0 Q W B'0 f0 L0 c Ds H c0 hpre hfp hrep hA hSb
    (fun cs' φ' lg J cm cc h => by have := hbud cs' φ' lg J cm cc h; omega) hubud).mono ?_
  rintro r ⟨cs', φ', lg, J, cm, cc, H', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact ⟨cs', φ', lg, J, cm, cc, H', h1, h2, h3, h4, h5, fun x hx _ => h6 x hx, h7, by omega, h9⟩

/-- The second half of an iteration before its final emptiness bit (agent-06's `postProg`). -/
def postI (merge delB ins cmp : Stmt) : Stmt :=
  seq merge (seq (removeU delB gDel) (seq (scanP ins) (seq (reselect cmp ins) (appendU copyBp))))

theorem postProg_eq (merge delB ins empty cmp : Stmt) :
    postProg merge delB ins empty cmp = seq (postI merge delB ins cmp) empty := rfl

/-- **The loop interface with agent-06's second half**: `loop2_spec` + `postSpec`. -/
theorem loopSpecB2_of_postSpec (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt}
    {τf Mf : ℕ → ℕ} {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} {DCb : DCost} {K Ko Sl : ℕ}
    {Sb : ℕ → ℕ} {l : ℕ}
    (hIH : CallSpec DL PI.PhiR Inv FPC DCb Mf τf LF body K Sl Sb l)
    {ltBi : Stmt} {CL : ℕ} {LW LV : List String}
    (hLt : ∀ (d : Labels G s) (H : Hist G) (c0 : ℕ) (Bi : WLab G s),
      LtI realOps ltBi (fun st => LabAt st d H c0 ∧ WHolds st KBi "sp.bif" H (vc st) Bi ∧
          1 < st.cap ∧ st.w "n" = G.n)
        (fun v => ∃ h : v < G.n, d ⟨v, h⟩ < Bi) CL LW LV)
    (hLWd : ∀ a ∈ LW, a ∉ DL.dWR) (hLWp : ∀ a ∈ LW, a ∉ PI.pWR)
    (hLWs : ∀ a ∈ LW, a ∉ ["gN", "hp_n", "core.n", "core.s", "core.m"])
    (hDP : ∀ a ∈ DL.dWA, a ∉ PI.pWA) (hDPr : ∀ a ∈ DL.dWR, a ∉ PI.pWR)
    {cmp : Stmt} {C : ℕ} {CW CV : List String}
    (hy : PostHyg DL PI CW) (hcmp : ∀ c0, CmpFam DL cmp C CW CV c0) (hsort : WinScan.CSRSorted G s)
    (hSl : postS DL.K C G.n G.m (2 * DL.NB) ≤ Sl) (hLT : LF ≤ DL.LT)
    (hMf : ∀ l, (dlOps G s).mergeM (Mf (l + 1)) (Mf l)) {DC : DCost} {subC : SubRelC G s Φ Ω}
    (hsimsub : SimSub G s (dlOps G s) τf Inv Mf l (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) subC)
    (hsubC : GoodSub G s τf Inv l subC) (hDC : DC.M (l + 1) = Mf (l + 1)) (hτ1 : 1 ≤ τf l)
    (hsubT : TotalSub G s Inv (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l))
    (hKo : DL.K + CL + 71 + postK DL.K C + 1 ≤ Ko) (hKoD : DL.K + 1 ≤ Ko) :
    LoopSpecB2 DL PI Inv FPC DCb Mf τf LF body DL.empty
      (seq (firstHalf DL.pull ltBi) (postI DL.merge DL.delB DL.ins cmp)) K Ko Sl Sb l :=
  loopSpecB2_of_loop2 DL PI hIH hLt hLWd hLWp hLWs hDP hDPr
    (postHalf_of_stmt DL PI (postSpec DL PI LF body τf Mf cmp C CW CV Ω) hy hcmp hsort hsimsub hsubC
      hSl hLT) hMf (DC := DC) hsimsub hsubC hDC hτ1 hsubT hKo hKoD

/-! ## agent-01's `LoopSpecB` -/

theorem loopFrame_of_lframe {st r : State ℝ≥0} {l : ℕ} (h : LFrame st r G.n l) :
    RamBody.LoopFrame (G := G) st r l :=
  ⟨h.S, h.Slen, h.W, h.Wlen, h.above, h.stArr⟩

/-- `LoopSpecB2` is agent-01's `LoopSpecB` (the frame is the same). -/
theorem loopSpecB_of_B2 {DL : DLayer G s T} {PI : PhiI Φ} {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω}
    {DCb : DCost} {Mf τ : ℕ → ℕ} {LF : ℕ} {body dsEmpty iterB : Stmt} {K Ko Sl : ℕ} {Sb : ℕ → ℕ}
    {l : ℕ} (h : LoopSpecB2 DL PI Inv FPC DCb Mf τ LF body dsEmpty iterB K Ko Sl Sb l) :
    RamBody.LoopSpecB DL PI Inv FPC DCb Mf τ LF body dsEmpty iterB K Ko Sl Sb l := by
  intro st B S d0 d1 p P0 Q W B'0 f0 L0 c Ds H c0 hpre hfp hrep hA hSb hbud hubud
  refine (h st B S d0 d1 p P0 Q W B'0 f0 L0 c Ds H c0 hpre hfp hrep hA hSb hbud hubud).mono ?_
  rintro r ⟨cs', φ', lg, J, cm, cc, H', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  exact ⟨cs', φ', lg, J, cm, cc, H', h1, h2, h3, h4, loopFrame_of_lframe h5, h6, h7, h8, h9⟩

/-- **`loop2_spec` gives agent-01's `LoopSpecB`**, for any second half `PostHalf`. -/
theorem loopSpecB_of_loop2 (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt}
    {τf Mf : ℕ → ℕ} {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} {DCb : DCost} {K Ko Sl : ℕ}
    {Sb : ℕ → ℕ} {l : ℕ}
    (hIH : CallSpec DL PI.PhiR Inv FPC DCb Mf τf LF body K Sl Sb l)
    {ltBi : Stmt} {CL : ℕ} {LW LV : List String}
    (hLt : ∀ (d : Labels G s) (H : Hist G) (c0 : ℕ) (Bi : WLab G s),
      LtI realOps ltBi (fun st => LabAt st d H c0 ∧ WHolds st KBi "sp.bif" H (vc st) Bi ∧
          1 < st.cap ∧ st.w "n" = G.n)
        (fun v => ∃ h : v < G.n, d ⟨v, h⟩ < Bi) CL LW LV)
    (hLWd : ∀ a ∈ LW, a ∉ DL.dWR) (hLWp : ∀ a ∈ LW, a ∉ PI.pWR)
    (hLWs : ∀ a ∈ LW, a ∉ ["gN", "hp_n", "core.n", "core.s", "core.m"])
    (hDP : ∀ a ∈ DL.dWA, a ∉ PI.pWA) (hDPr : ∀ a ∈ DL.dWR, a ∉ PI.pWR)
    {postI : Stmt} {Kp : ℕ}
    (hpost : PostHalf DL PI LF body τf Mf Inv FPC DCb l (seq postI DL.empty) Kp Sl)
    (hMf : ∀ l, (dlOps G s).mergeM (Mf (l + 1)) (Mf l)) {DC : DCost} {subC : SubRelC G s Φ Ω}
    (hsimsub : SimSub G s (dlOps G s) τf Inv Mf l (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) subC)
    (hsubC : GoodSub G s τf Inv l subC) (hDC : DC.M (l + 1) = Mf (l + 1)) (hτ1 : 1 ≤ τf l)
    (hsubT : TotalSub G s Inv (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l))
    (hKo : DL.K + CL + 71 + Kp + 1 ≤ Ko) (hKoD : DL.K + 1 ≤ Ko) :
    RamBody.LoopSpecB DL PI Inv FPC DCb Mf τf LF body DL.empty (seq (firstHalf DL.pull ltBi) postI)
      K Ko Sl Sb l :=
  loopSpecB_of_B2 (loopSpecB2_of_loop2 DL PI hIH hLt hLWd hLWp hLWs hDP hDPr hpost hMf (DC := DC)
    hsimsub hsubC hDC hτ1 hsubT hKo hKoD)

/-- **agent-01's `LoopSpecB` from `loop2_spec` and agent-06's `postSpec`** (`iterB` = the first
half, then `postI`). -/
theorem loopSpecB_of_postSpec (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt}
    {τf Mf : ℕ → ℕ} {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} {DCb : DCost} {K Ko Sl : ℕ}
    {Sb : ℕ → ℕ} {l : ℕ}
    (hIH : CallSpec DL PI.PhiR Inv FPC DCb Mf τf LF body K Sl Sb l)
    {ltBi : Stmt} {CL : ℕ} {LW LV : List String}
    (hLt : ∀ (d : Labels G s) (H : Hist G) (c0 : ℕ) (Bi : WLab G s),
      LtI realOps ltBi (fun st => LabAt st d H c0 ∧ WHolds st KBi "sp.bif" H (vc st) Bi ∧
          1 < st.cap ∧ st.w "n" = G.n)
        (fun v => ∃ h : v < G.n, d ⟨v, h⟩ < Bi) CL LW LV)
    (hLWd : ∀ a ∈ LW, a ∉ DL.dWR) (hLWp : ∀ a ∈ LW, a ∉ PI.pWR)
    (hLWs : ∀ a ∈ LW, a ∉ ["gN", "hp_n", "core.n", "core.s", "core.m"])
    (hDP : ∀ a ∈ DL.dWA, a ∉ PI.pWA) (hDPr : ∀ a ∈ DL.dWR, a ∉ PI.pWR)
    {cmp : Stmt} {C : ℕ} {CW CV : List String}
    (hy : PostHyg DL PI CW) (hcmp : ∀ c0, CmpFam DL cmp C CW CV c0) (hsort : WinScan.CSRSorted G s)
    (hSl : postS DL.K C G.n G.m (2 * DL.NB) ≤ Sl) (hLT : LF ≤ DL.LT)
    (hMf : ∀ l, (dlOps G s).mergeM (Mf (l + 1)) (Mf l)) {DC : DCost} {subC : SubRelC G s Φ Ω}
    (hsimsub : SimSub G s (dlOps G s) τf Inv Mf l (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l) subC)
    (hsubC : GoodSub G s τf Inv l subC) (hDC : DC.M (l + 1) = Mf (l + 1)) (hτ1 : 1 ≤ τf l)
    (hsubT : TotalSub G s Inv (BMSSPD G s (dlOps G s) FPC DCb T Mf τf l))
    (hKo : DL.K + CL + 71 + postK DL.K C + 1 ≤ Ko) (hKoD : DL.K + 1 ≤ Ko) :
    RamBody.LoopSpecB DL PI Inv FPC DCb Mf τf LF body DL.empty
      (seq (firstHalf DL.pull ltBi) (postI DL.merge DL.delB DL.ins cmp)) K Ko Sl Sb l :=
  loopSpecB_of_B2 (loopSpecB2_of_postSpec DL PI hIH hLt hLWd hLWp hLWs hDP hDPr hy hcmp hsort hSl
    hLT hMf (DC := DC) hsimsub hsubC hDC hτ1 hsubT hKo hKoD)

end Frontier.CHD.RamSpine
