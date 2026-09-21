import Frontier.CHD.RamBodyPro
import Frontier.CHD.SynFrame
import Frontier.CHD.SpineLevels

/-!
# Frontier.CHD.RamBodySpec — the level body: `CallSpec l → CallSpec (l+1)` (owner: agent-01)

**NON-GATE** (B-L4, the spine's level body).  Composition of the phases of one recursive call at
level `l + 1` (`bodyProg`):
* FindPivots (`FPB`, agent-09's `fpB_inst`);
* the prologue (`pro_spec`, `RamBodyPro`);
* the main loop (`LoopSpecB`, agent-08);
* the finalization (`FinB`, agent-03's `fin_spec`);
and the Layer-A assembly of the call's outcome (`callD_mk`), at ONE constant `K`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBody

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine
  Frontier.CHD.RamInit WExpr Stmt

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ Ω : Type}

/-- `B'f` of a loop exit (BM.24a, FIX-EMPTY). -/
noncomputable def bpfB (B : WLab G s) {p : ℕ} (cs : CSt G s p) : WLab G s := by
  classical exact if (cs.g.view cs.Dc).IsEmpty then B else cs.B'

theorem bpfB_empty {B : WLab G s} {p : ℕ} {cs : CSt G s p} (h : (cs.g.view cs.Dc).IsEmpty) :
    bpfB B cs = B := by
  unfold bpfB; simp [h]

theorem bpfB_ne {B : WLab G s} {p : ℕ} {cs : CSt G s p} (h : ¬ (cs.g.view cs.Dc).IsEmpty) :
    bpfB B cs = cs.B' := by
  unfold bpfB; simp [h]

/-- **The facts after the finalization** (as agent-03's `FinPost`): the tail data of `CallD` and
the `CallOut` facts at level `l + 1`, relative to the loop-exit state `st`. -/
structure FinOut (DL : DLayer G s T) (PI : PhiI Φ) (LF : ℕ) (body : Stmt) (τ Mf : ℕ → ℕ)
    (st r : State ℝ≥0) (l : ℕ) (B : WLab G s) (S W : Finset (Fin G.n)) (Ds : ℕ → DStrM G s)
    (H : Hist G) (c0 : ℕ) {p : ℕ} (c : LoopCfgD G s Φ p) (lT6 : List (Fin G.n))
    (W' : Finset (Fin G.n)) (lW' : List (Fin G.n)) (L : List (Fin G.m)) (H' : Hist G)
    (Kf C : ℕ) : Prop where
  t6nd : lT6.Nodup
  t6mem : ∀ x, x ∈ lT6 ↔ x ∈ S ∧ bpfB B c.cs ≤ c.cs.d x ∧ c.cs.d x < B
  wmem : ∀ x, x ∈ W' ↔ (x ∈ W ∧ x ∉ c.cs.U) ∧ c.cs.d x < bpfB B c.cs
  enum : Enumerates G L W'
  wnd : lW'.Nodup
  wset : lW'.toFinset = W'
  lab : LabAt r (finD (dlOps G s) (T (l + 1)) B (bpfB B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').1 H' c0
  hext : HExt H (vc st) H' (vc r)
  D : DL.DR r H' (finD (dlOps G s) (T (l + 1)) B (bpfB B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.1
    (Function.update Ds (l + 1)
      (finD (dlOps G s) (T (l + 1)) B (bpfB B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.1) (l + 1)
  phi : PI.PhiR r c.φ
  U : SetRow r "U" "U.len" (l + 1) (c.cs.U ∪ W')
  sBp : SlotHolds r (slotBp (l + 1)) H' (vc r) (bpfB B c.cs)
  ptr : ∀ u ∈ c.cs.U ∪ W',
    PtrOK r (finD (dlOps G s) (T (l + 1)) B (bpfB B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').1 B u
  ptrFr : ∀ x : Fin G.n, x ∉ W' → r.wa "sp.ptr" x = st.wa "sp.ptr" x
  clr : Clear r G.n (l + 1)
  above : Above st r G.n (l + 1)
  stArr : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "gKeep", "gRep"], r.wa a = st.wa a
  stat : Static r G LF body τ Mf
  lvl : r.w "lvl" = l + 1
  cost1 : st.cost ≤ r.cost
  cost2 : r.cost ≤ st.cost + Kf * (1 + S.card + W.card + W'.card +
    (finD (dlOps G s) (T (l + 1)) B (bpfB B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.2) +
    3 * c.cs.U.card + C
  use : DL.use r ≤ DL.use st + 2 * (S.card +
    (finD (dlOps G s) (T (l + 1)) B (bpfB B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.2)

/-- **The finalization** (BM.24a–31, agent-03's `fin_spec`) as an interface of the level body:
from the loop exit (`LoopRep`, the `S`/`W` rows, the Layer-A exit facts) and the budgets, the
finalization program `finP` ends in `FinOut`. -/
def FinB (DL : DLayer G s T) (PI : PhiI Φ) (LF : ℕ) (body : Stmt) (τ Mf : ℕ → ℕ) (finP : Stmt)
    (Kf C Cst : ℕ) (l : ℕ) : Prop :=
  ∀ (st : State ℝ≥0) (B : WLab G s) (S W : Finset (Fin G.n)) (wl : List (Fin G.n))
    (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ) {p : ℕ} (c : LoopCfgD G s Φ p),
    LoopRep DL PI LF body τ Mf st (l + 1) B (τ (l + 1)) Ds H c0 c →
    SetRow st "S" "S.len" (l + 1) S → RowRep st "W" "W.len" G.n (l + 1) (wl.map Fin.val) →
    wl.Nodup → wl.toFinset = W →
    WalkInv c.cs.d → (∀ u ∈ c.cs.U, c.cs.d u = dis (s := s) u) →
    (∀ x ∈ W, x ∉ c.cs.U → c.cs.d x < bpfB B c.cs → c.cs.d x = dis (s := s) x) →
    (∀ j, ∀ x ∈ c.cs.P j, x ∈ S) → c.cs.Dc.Bd = B →
    st.cost + Kf * (1 + S.card + W.card) + 3 * c.cs.U.card + Cst ≤ c0 + st.cap →
    (∀ (lT6 : List (Fin G.n)) (L : List (Fin G.m)) (lW' : List (Fin G.n)),
      lT6.Nodup → (∀ x, x ∈ lT6 ↔ x ∈ S ∧ bpfB B c.cs ≤ c.cs.d x ∧ c.cs.d x < B) →
      Enumerates G L lW'.toFinset → lW'.Nodup →
      (∀ x, x ∈ lW'.toFinset ↔ (x ∈ W ∧ x ∉ c.cs.U) ∧ c.cs.d x < bpfB B c.cs) →
      DL.use st + 2 * (S.card +
        (finD (dlOps G s) (T (l + 1)) B (bpfB B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.2) ≤
          DL.ucap) →
    Runs realOps finP st (fun r => ∃ (lT6 : List (Fin G.n)) (W' : Finset (Fin G.n))
      (lW' : List (Fin G.n)) (L : List (Fin G.m)) (H' : Hist G),
      FinOut DL PI LF body τ Mf st r l B S W Ds H c0 c lT6 W' lW' L H' Kf C)

/-! ## Arithmetic of the uniform constant -/

/-- **The whole body at one constant `K`**: every Layer-A term of the call record (and the sub-log)
pays its RAM work, and the leading `1 +` pays all additive constants. -/
theorem body_arith {K Kf Cf Ko Kfin Cfin KD : ℕ}
    (hK : Kf + Cf + Ko + Kfin + Cfin + 2 * KD + 60 ≤ K)
    (cfp I σ p cl cm Lg nS nW nW' F nU : ℕ) (hU : nU ≤ cl) :
    Kf * cfp + Cf + (KD + 28 + (KD + 53) * p + 41 * σ) + KD * I + K * Lg + Ko * (cl + cm) +
      (Kfin * (1 + nS + nW + nW' + F) + 3 * nU + Cfin) + 2 ≤
    K * (cfp + (I + σ + 2 * p) + cl + cm + (1 + nS + nW + nW' + σ + F) + Lg) := by
  have h1 : Kf * cfp ≤ K * cfp := Nat.mul_le_mul_right _ (by omega)
  have h2 : (KD + 53) * p ≤ K * (2 * p) := by nlinarith
  have h3 : 41 * σ ≤ K * (2 * σ) := by nlinarith
  have h4 : KD * I ≤ K * I := Nat.mul_le_mul_right _ (by omega)
  have h5 : Ko * (cl + cm) + 3 * nU ≤ K * (cl + cm) := by nlinarith
  have h6 : Kfin * (1 + nS + nW + nW' + F) ≤ K * (nS + nW + nW' + F) + Kfin := by nlinarith
  have e : K * (cfp + (I + σ + 2 * p) + cl + cm + (1 + nS + nW + nW' + σ + F) + Lg) =
      K * cfp + K * (2 * p) + K * (2 * σ) + K * I + K * (cl + cm) + K * (nS + nW + nW' + F) + K +
        K * Lg := by ring
  rw [e]
  omega

/-- A partial budget is dominated by the whole. -/
theorem body_arith_fp {K Kf Cf Ko Kfin Cfin KD : ℕ}
    (hK : Kf + Cf + Ko + Kfin + Cfin + 2 * KD + 60 ≤ K) (cfp σ p Lt : ℕ)
    (hLt : cfp + σ + 2 * p + 1 ≤ Lt) :
    Kf * cfp + Cf + 5 + 15 * p + 41 * σ + 2 ≤ K * Lt := by
  have h0 : K * (cfp + σ + 2 * p + 1) ≤ K * Lt := Nat.mul_le_mul_left _ hLt
  have h1 : Kf * cfp ≤ K * cfp := Nat.mul_le_mul_right _ (by omega)
  have h2 : 15 * p ≤ K * (2 * p) := by nlinarith
  have h3 : 41 * σ ≤ K * σ := by nlinarith
  have e : K * (cfp + σ + 2 * p + 1) = K * cfp + K * σ + K * (2 * p) + K := by ring
  omega

/-- The loop's budget is dominated by the whole. -/
theorem body_arith_loop {K Kf Cf Ko Kfin Cfin KD : ℕ}
    (hK : Kf + Cf + Ko + Kfin + Cfin + 2 * KD + 60 ≤ K) (cfp I σ p cl cm Lg Lt : ℕ)
    (hLt : cfp + I + σ + 2 * p + cl + cm + 1 + Lg ≤ Lt) :
    Kf * cfp + Cf + (KD + 28 + (KD + 53) * p + 41 * σ) + KD * I + K * Lg + Ko * (cl + cm) + 2 ≤
      K * Lt := by
  have h0 : K * (cfp + I + σ + 2 * p + cl + cm + 1 + Lg) ≤ K * Lt := Nat.mul_le_mul_left _ hLt
  have h1 : Kf * cfp ≤ K * cfp := Nat.mul_le_mul_right _ (by omega)
  have h2 : (KD + 53) * p ≤ K * (2 * p) := by nlinarith
  have h3 : 41 * σ ≤ K * σ := by nlinarith
  have h4 : KD * I ≤ K * I := Nat.mul_le_mul_right _ (by omega)
  have h5 : Ko * (cl + cm) ≤ K * (cl + cm) := Nat.mul_le_mul_right _ (by omega)
  have e : K * (cfp + I + σ + 2 * p + cl + cm + 1 + Lg) =
      K * cfp + K * I + K * σ + K * (2 * p) + K * (cl + cm) + K + K * Lg := by ring
  omega

/-- The finalization's budget is dominated by the whole. -/
theorem body_arith_fin {K Kf Cf Ko Kfin Cfin KD : ℕ}
    (hK : Kf + Cf + Ko + Kfin + Cfin + 2 * KD + 60 ≤ K) (cfp I σ p cl cm Lg nS nW nU Lt : ℕ)
    (hU : nU ≤ cl) (hLt : cfp + I + σ + 2 * p + cl + cm + 1 + nS + nW + Lg ≤ Lt) :
    Kf * cfp + Cf + (KD + 28 + (KD + 53) * p + 41 * σ) + KD * I + K * Lg + Ko * (cl + cm) +
      Kfin * (1 + nS + nW) + 3 * nU + 2 ≤ K * Lt := by
  have h0 : K * (cfp + I + σ + 2 * p + cl + cm + 1 + nS + nW + Lg) ≤ K * Lt :=
    Nat.mul_le_mul_left _ hLt
  have h1 : Kf * cfp ≤ K * cfp := Nat.mul_le_mul_right _ (by omega)
  have h2 : (KD + 53) * p ≤ K * (2 * p) := by nlinarith
  have h3 : 41 * σ ≤ K * σ := by nlinarith
  have h4 : KD * I ≤ K * I := Nat.mul_le_mul_right _ (by omega)
  have h5 : Ko * (cl + cm) + 3 * nU ≤ K * (cl + cm) := by nlinarith
  have h6 : Kfin * (1 + nS + nW) ≤ K * (nS + nW) + Kfin := by nlinarith
  have e : K * (cfp + I + σ + 2 * p + cl + cm + 1 + nS + nW + Lg) =
      K * cfp + K * I + K * σ + K * (2 * p) + K * (cl + cm) + K + K * (nS + nW) + K * Lg := by ring
  omega

/-- The pivots of disjoint groups are distinct. -/
theorem piv_list {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
    {P : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} (hfp : FPContract B S d0 d1 p P Q W)
    {piv : Fin p → Fin G.n} (hpiv : ∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x) :
    (List.ofFn piv).Nodup ∧ (List.ofFn piv).toFinset = Finset.univ.image piv := by
  classical
  refine ⟨List.nodup_ofFn.mpr (fun i j hij => ?_), by ext x; simp [List.mem_ofFn]⟩
  by_contra hne
  exact Finset.disjoint_left.mp (hfp.gdisj i j hne) (hpiv i).1 (hij ▸ (hpiv j).1)

/-! ## The level body -/

set_option maxHeartbeats 8000000 in
/-- **The level body** (BM.1–31 at level `l + 1`): from a call entry at level `l + 1` whose every
Layer-A outcome fits the cost and resource budgets, the body realizes one `CallD` outcome (built
by `callD_mk`), ends in `CallOut`, and costs at most `K` per unit of its log cost — the SAME `K` as
the main loop's sub-calls. -/
theorem body_spec (DL : DLayer G s T) (PI : PhiI Φ) {RW : List String} (hNm : BodyNames DL PI RW)
    {LF : ℕ} {body : Stmt} {τ Mf : ℕ → ℕ} {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω} {DCb : DCost}
    {K Ko Sl : ℕ} {Sb : ℕ → ℕ} {l : ℕ} {fp iterB finP : Stmt} {Kf Cf Kfin Cfin Cst : ℕ}
    (hFP : FPB DL PI Inv FPC LF body fp τ Mf Kf Cf (l + 1))
    (hLoop : LoopSpecB DL PI Inv FPC DCb Mf τ LF body DL.empty iterB K Ko Sl Sb l)
    (hFin : FinB DL PI LF body τ Mf finP Kfin Cfin Cst l)
    (hFPC : FPCSound G s FPC Inv) (hFPCt : FPCTotal G s FPC Inv) (hτ : ∀ l, 1 ≤ τ l)
    (hMf : ∀ l, (dlOps G s).mergeM (Mf (l + 1)) (Mf l)) (hM1 : ∀ l, 1 ≤ Mf l)
    (hSbA : ∀ (Blow B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (φ : Φ)
      (d1 : Labels G s) (p : ℕ) (P0 : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n)) (φ1 : Φ)
      (ω : Ω) (cfp : ℕ) (B'0 : WLab G s) (f0 : ℕ) (L0 : LiveM G s) (c' : LoopCfgD G s Φ p),
      FPC (l + 1) Blow B S d0 φ d1 p P0 Q W φ1 ω cfp → CallPre B S d0 → Inv φ →
      (∀ x ∈ S, Blow ≤ d0 x) →
      ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 c' → ¬ LoopDoneD (τ (l + 1)) c' →
      ∀ ks Bi g1 Dc1 cp, pullC (dlOps G s) (T (l + 1)) c'.cs.g c'.cs.Dc = (ks, Bi, g1, Dc1, cp) →
      (BM.expand c'.cs.lit ks.toFinset Bi).card ≤ Sb l)
    (hK : Kf + Cf + Ko + Kfin + Cfin + 2 * DL.K + 60 ≤ K) (hSl : Cst + 2 ≤ Sl) :
    ∀ (st : State ℝ≥0) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (φ : Φ)
      (g : DGl G s) (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ),
      CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B →
      DB.KeyInj g.L (kof G s) → (∀ v i a, g.L v = some (i, a) → B ≤ a) →
      CallIn DL PI.PhiR LF body τ Mf st (l + 1) Blow B S d φ g Ds H c0 →
      (∀ res φ' g' lg, BMSSPD G s (dlOps G s) FPC DCb T Mf τ (l + 1) Blow B S d φ g res φ' g' lg →
        st.cost + K * Log.cost lg + Sl ≤ c0 + st.cap + 2) →
      (∀ res φ' g' lg, BMSSPD G s (dlOps G s) FPC DCb T Mf τ (l + 1) Blow B S d φ g res φ' g' lg →
        DL.use st + 2 * Log.cost lg ≤ DL.ucap) →
      Runs realOps (seq fp (seq copyGrp (seq (pivProg cmpTTc) (seq (pivIns DL.new DL.ins)
        (seq b8Setup (seq SpineLab.b8Prog (seq (rowReset "U.len")
          (seq (mainLoop DL.empty iterB) finP)))))))) st (fun r =>
        ∃ (res : ResultD G s) (φ' : Φ) (g' : DGl G s) (lg : Log G s Ω) (H' : Hist G),
          BMSSPD G s (dlOps G s) FPC DCb T Mf τ (l + 1) Blow B S d φ g res φ' g' lg ∧
          HExt H (vc st) H' (vc r) ∧
          CallOut DL PI.PhiR LF body τ Mf st r (l + 1) B res φ' g' Ds H' c0 ∧
          st.cost ≤ r.cost ∧ r.cost + 2 ≤ st.cost + K * Log.cost lg ∧
          DL.use r ≤ DL.use st + 2 * Log.cost lg) := by
  intro st Blow B S d φ g Ds H c0 hpre hI hlow hBlow hK0 hab hIn hbud hubud
  classical
  have hlow' : ∀ x ∈ S, Blow ≤ d x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
  -- (1) FindPivots
  have hbudF : ∀ d1 p P Q W φ1 ω cfp, FPC (l + 1) Blow B S d φ d1 p P Q W φ1 ω cfp →
      st.cost + Kf * cfp + Cf ≤ c0 + st.cap := by
    intro d1 p P Q W φ1 ω cfp hf
    obtain ⟨hfp, -⟩ := hFPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hf
    obtain ⟨piv, lpiv, hpiv, hlpnd, hlp⟩ := exists_piv hfp
    obtain ⟨res, φ2, gE, lg, hrel, hc⟩ :=
      callD_ext_fp (DCb := DCb) hFPC hFPCt hτ hMf hM1 hpre hI hlow hK0 hab hf hpiv hlpnd hlp
    have h1 := hbud _ _ _ _ hrel
    have h2 := body_arith_fp hK cfp (∑ j, (P j).card) p (Log.cost lg) (by omega)
    omega
  refine runs_seq ((Runs.frame rfl (hFP st Blow B S d φ g Ds H c0 hIn hpre hI hlow hbudF)).mono ?_)
  rintro r1 ⟨⟨d1, p, P, Q, W, φ1, ω, cfp, Gs, wl, H1, hfprel, hp, hPG, hGnd, hGO, hGl, hW1, hwnd,
    hwset, hL1, hext1, hPhi1, hD1, hF, hc1a, hc1b, hu1⟩, hU1⟩
  have hcap1 : r1.cap = st.cap := hU1.cap
  obtain ⟨hfp, hI1⟩ := hFPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
  have hsB1 : SlotHolds r1 (slotB (l + 1)) H1 (vc r1) B :=
    (hIn.sB.of_slot_eq (hF.slots _).1 (hF.slots _).2).ext hext1
  have hbudP : r1.cost + 5 + 15 * p + 41 * (∑ j, (P j).card) ≤ c0 + r1.cap := by
    obtain ⟨piv, lpiv, hpiv, hlpnd, hlp⟩ := exists_piv hfp
    obtain ⟨res, φ2, gE, lg, hrel, hc⟩ :=
      callD_ext_fp (DCb := DCb) hFPC hFPCt hτ hMf hM1 hpre hI hlow hK0 hab hfprel hpiv hlpnd hlp
    have h1 := hbud _ _ _ _ hrel
    have h2 := body_arith_fp hK cfp (∑ j, (P j).card) p (Log.cost lg) (by omega)
    rw [hcap1]; omega
  have hUb1 : ∀ piv : Fin p → Fin G.n, (∀ j, piv j ∈ P j ∧ ∀ x ∈ P j, d1 (piv j) ≤ d1 x) →
      DL.use r1 + 1 + (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 (List.ofFn piv) g).2.2 + p ≤
        DL.ucap := by
    intro piv hpiv
    obtain ⟨hlpnd, hlp⟩ := piv_list hfp hpiv
    obtain ⟨res, φ2, gE, lg, hrel, hc⟩ :=
      callD_ext_fp (DCb := DCb) hFPC hFPCt hτ hMf hM1 hpre hI hlow hK0 hab hfprel hpiv hlpnd hlp
    have h1 := hubud _ _ _ _ hrel
    rw [hu1]; omega
  -- (2) the prologue
  refine pro_spec DL PI hNm hpre hfp hp hPG hGnd hGO hGl hW1 hL1 hPhi1 hD1 hF hIn.lvl_le hsB1 hbudP
    (hF.stat.MCap (l + 1) (by have := hIn.lvl_le; omega)) hUb1 ?_
  intro r7 piv lpiv hpiv hlpnd hlp hPP hvc7 hc7a hc7b hu7 hcap71
  have hA := aloop_init (Inv := Inv) (Mf := Mf) (T := T (l + 1)) (l := l) (lpiv := lpiv) hM1 hpre
    hfp hI1 hpiv hlp hK0 hab
  have hc7 : r7.cost ≤ st.cost + Kf * cfp + Cf +
      (DL.K + 28 + (DL.K + 53) * p + 41 * ∑ j, (P j).card) +
      DL.K * (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g).2.2 := by
    unfold Kpro at hc7b; omega
  -- (3) the main loop
  refine runs_seq ((Runs.frame rfl (hLoop r7 B S d d1 p P Q W (initB' B d1 piv) g.fresh g.L
    ⟨0, cs0 (T (l + 1)) (Mf (l + 1)) B d1 P piv lpiv g, φ1⟩ Ds H1 c0 hpre hfp hPP.loop hA
    (fun c' hA' hnd ks Bi g1 Dc1 cp hpull =>
      hSbA Blow B S d φ d1 p P Q W φ1 ω cfp _ _ _ c' hfprel hpre hI hlow' hA' hnd ks Bi g1 Dc1 cp
        hpull)
    ?_ ?_)).mono ?_)
  · intro cs' φ' lgc J cm cc hloop
    obtain ⟨res, gE, lg, hrel, hc⟩ := callD_ext_loop (DCb := DCb) hfprel hpiv hlpnd hlp hloop
    have h1 := hbud _ _ _ _ hrel
    have h2 := body_arith_loop hK cfp (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g).2.2
      (∑ j, (P j).card) p cc cm (Log.cost lgc) (Log.cost lg) (by omega)
    rw [hcap71, hcap1]; omega
  · intro cs' φ' lgc J cm cc hloop
    obtain ⟨res, gE, lg, hrel, hc⟩ := callD_ext_loop (DCb := DCb) hfprel hpiv hlpnd hlp hloop
    have h1 := hubud _ _ _ _ hrel
    omega
  rintro r8 ⟨⟨cs', φ', lgc, J, cm, cl, H2, hloop, hLR8, hA8, hext2, hLF8, hptr8, hc8a, hc8b, hu8⟩,
    hU8⟩
  have hcap8 : r8.cap = r7.cap := hU8.cap
  have hU0 : cs'.U.card ≤ cl := by
    have := loopD_card_le hloop
    simpa [cs0] using this
  -- (4) the finalization
  obtain ⟨resC, gEC, lgC, hrelC, hcC⟩ := callD_ext_loop (DCb := DCb) hfprel hpiv hlpnd hlp hloop
  have hbudFin : r8.cost + Kfin * (1 + S.card + W.card) + 3 * cs'.U.card + Cst ≤ c0 + r8.cap := by
    have h1 := hbud _ _ _ _ hrelC
    have h2 := body_arith_fin hK cfp (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g).2.2
      (∑ j, (P j).card) p cl cm (Log.cost lgc) S.card W.card cs'.U.card (Log.cost lgC) hU0 (by omega)
    rw [hcap8, hcap71, hcap1]; omega
  have huFin : ∀ (lT6 : List (Fin G.n)) (L : List (Fin G.m)) (lW' : List (Fin G.n)),
      lT6.Nodup → (∀ x, x ∈ lT6 ↔ x ∈ S ∧ bpfB B cs' ≤ cs'.d x ∧ cs'.d x < B) →
      Enumerates G L lW'.toFinset → lW'.Nodup →
      (∀ x, x ∈ lW'.toFinset ↔ (x ∈ W ∧ x ∉ cs'.U) ∧ cs'.d x < bpfB B cs') →
      DL.use r8 + 2 * (S.card +
        (finD (dlOps G s) (T (l + 1)) B (bpfB B cs') cs'.d cs'.g cs'.Dc lT6 L lW').2.2.2) ≤
          DL.ucap := by
    intro lT6 L lW' h1 h2 h3 h4 h5
    have hrel := callD_mk (DCb := DCb) hfprel hpiv hlpnd hlp hloop (fun h => bpfB_empty h)
      (fun h => bpfB_ne h) h1 h2 h5 h3 h4 rfl
    have h6 := hubud _ _ _ _ hrel
    rw [logCost_cons] at h6
    simp only [recD] at h6
    omega
  have hn2 : (l + 1 + 1) * G.n = (l + 1) * G.n + G.n := Nat.succ_mul _ _
  have hn3 : (l + 2) * G.n = (l + 1) * G.n + G.n := by ring
  have hS8 : SetRow r8 "S" "S.len" (l + 1) S :=
    setRow_of_eq hPP.S (by rw [hLF8.above.wlen]) (by rw [hLF8.above.wlen]) hLF8.Slen
      (fun i hi => hLF8.S _ (by omega) (by omega))
  have hW8 : RowRep r8 "W" "W.len" G.n (l + 1) (wl.map Fin.val) :=
    hPP.W.of_eq (by rw [hLF8.above.wlen]) (by rw [hLF8.above.wlen]) hLF8.Wlen
      (fun i hi => hLF8.W _ (by omega) (by omega))
  refine (Runs.frame rfl (hFin r8 B S W wl Ds H2 c0 ⟨0, cs', φ'⟩ hLR8 hS8 hW8 hwnd hwset
    hA8.linv.walk (fun u hu => hA8.linv.U_complete u hu)
    (fun x hxW hxU hxlt => wp_complete hpre hfp hA8.linv (fun h => bpfB_empty h)
      (fun h => bpfB_ne h) hxW hxU hxlt)
    (fun j x hx => (hfp.groups j).2 (hA8.linv.Psub j hx)) hA8.sinv.Bd hbudFin huFin)).mono ?_
  rintro r9 ⟨⟨lT6, W', lW', L, H3, hFO⟩, hU9⟩
  -- (5) the call's outcome
  refine ⟨(bpfB B cs', cs'.U ∪ W',
      (finD (dlOps G s) (T (l + 1)) B (bpfB B cs') cs'.d cs'.g cs'.Dc lT6 L lW').2.2.1,
      (finD (dlOps G s) (T (l + 1)) B (bpfB B cs') cs'.d cs'.g cs'.Dc lT6 L lW').1), φ',
    (finD (dlOps G s) (T (l + 1)) B (bpfB B cs') cs'.d cs'.g cs'.Dc lT6 L lW').2.1,
    ([], recD T Mf l Blow B S g d1 p P Q W ω cfp lpiv cs' J cm cl L (bpfB B cs') lT6 W' lW') :: lgc,
    H3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact callD_mk (DCb := DCb) hfprel hpiv hlpnd hlp hloop (fun h => bpfB_empty h)
      (fun h => bpfB_ne h) hFO.t6nd hFO.t6mem hFO.wmem hFO.enum hFO.wnd hFO.wset
  · rw [hvc7] at hext2
    exact (hext1.trans hext2).trans hFO.hext
  · have hpf : ∀ x : Fin G.n, x ∉ cs'.U ∪ W' → r9.wa "sp.ptr" x = st.wa "sp.ptr" x := by
      intro x hx
      rw [Finset.mem_union, not_or] at hx
      rw [hFO.ptrFr x hx.2, hptr8 x hx.1 (by simp [cs0]), hPP.ptr x]
    exact ⟨hFO.lvl, hFO.stat, hFO.lab, hFO.D, hFO.phi, hFO.U, hFO.sBp, hFO.ptr, hpf, hFO.clr,
      hPP.above.trans (hLF8.above.trans hFO.above),
      fun a ha => (hFO.stArr a ha).trans ((hLF8.stArr a ha).trans (hPP.stArr a ha))⟩
  · have := hFO.cost1; omega
  · rw [logCost_cons]
    simp only [recD]
    have h2 := body_arith hK cfp (initD (dlOps G s) (T (l + 1)) (Mf (l + 1)) B d1 lpiv g).2.2
      (∑ j, (P j).card) p cl cm (Log.cost lgc) S.card W.card W'.card
      (finD (dlOps G s) (T (l + 1)) B (bpfB B cs') cs'.d cs'.g cs'.Dc lT6 L lW').2.2.2
      cs'.U.card hU0
    have h3 := hFO.cost2
    dsimp only at h3
    omega
  · rw [logCost_cons]
    simp only [recD]
    have h3 := hFO.use
    dsimp only at h3
    omega

/-! ## The dispatch: `CallSpec (l+1)` -/

theorem unch_enter_charge (st : State ℝ≥0) (k : ℕ) (wa va wr vr : List String) :
    Unchanged st ((st.enter).charge k) wa va wr vr :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- A call entry survives the call's own `enter` and dispatch test (cost only). -/
theorem callIn_enter (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt} {τ Mf : ℕ → ℕ}
    {st : State ℝ≥0} {l : ℕ} {Blow B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s} {φ : Φ}
    {g : DGl G s} {Ds : ℕ → DStrM G s} {H : Hist G} {c0 : ℕ}
    (h : CallIn DL PI.PhiR LF body τ Mf st l Blow B S d φ g Ds H c0) :
    CallIn DL PI.PhiR LF body τ Mf ((st.enter).charge 1) l Blow B S d φ g Ds H c0 := by
  have hU := unch_enter_charge st 1 [] [] [] []
  have hvc : vc (G := G) ((st.enter).charge 1) = vc st := rfl
  exact ⟨h.lvl, h.lvl_le,
    static_of_unch h.stat hU (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
    h.lab.of_unchanged hU (by simp) (by simp) (by simp <;> omega),
    DL.frame st _ H H g Ds (l + 1) [] [] [] [] h.D hU (by simp) (by simp) (by simp)
      (by rw [hvc]; exact HExt.refl _ _),
    PI.frame st _ φ [] [] [] [] h.phi hU (by simp) (by simp),
    setRow_of_unch h.S hU (by simp) (by simp),
    by rw [hvc]; exact h.sB.of_unchanged hU (by simp) (by simp),
    by rw [hvc]; exact h.sBlow.of_unchanged hU (by simp) (by simp),
    clear_of_unch h.clr hU (by simp) (by simp) (by simp)⟩

set_option maxHeartbeats 4000000 in
/-- **The level step**: with the procedure body `ite (lvl = 0) body0 (bodyProg …)`, the level body
gives agent-08's `CallSpec (l+1)` at the same constant `K` (cost, resource budget with factor 2). -/
theorem callSpec_succ (DL : DLayer G s T) (PI : PhiI Φ) {RW : List String}
    (hNm : BodyNames DL PI RW)
    {LF : ℕ} {body body0 : Stmt} {τ Mf : ℕ → ℕ} {Inv : Φ → Prop} {FPC : FPRelC G s Φ Ω}
    {DCb : DCost} {K Ko Sl : ℕ} {Sb : ℕ → ℕ} {l : ℕ} {fp iterB finP : Stmt}
    {Kf Cf Kfin Cfin Cst : ℕ}
    (hbody : body = bmsspProc body0 (seq fp (seq copyGrp (seq (pivProg cmpTTc)
      (seq (pivIns DL.new DL.ins) (seq b8Setup (seq SpineLab.b8Prog (seq (rowReset "U.len")
        (seq (mainLoop DL.empty iterB) finP)))))))))
    (hFP : FPB DL PI Inv FPC LF body fp τ Mf Kf Cf (l + 1))
    (hLoop : LoopSpecB DL PI Inv FPC DCb Mf τ LF body DL.empty iterB K Ko Sl Sb l)
    (hFin : FinB DL PI LF body τ Mf finP Kfin Cfin Cst l)
    (hFPC : FPCSound G s FPC Inv) (hFPCt : FPCTotal G s FPC Inv) (hτ : ∀ l, 1 ≤ τ l)
    (hMf : ∀ l, (dlOps G s).mergeM (Mf (l + 1)) (Mf l)) (hM1 : ∀ l, 1 ≤ Mf l)
    (hSbA : ∀ (Blow B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (φ : Φ)
      (d1 : Labels G s) (p : ℕ) (P0 : Fin p → Finset (Fin G.n)) (Q W : Finset (Fin G.n)) (φ1 : Φ)
      (ω : Ω) (cfp : ℕ) (B'0 : WLab G s) (f0 : ℕ) (L0 : LiveM G s) (c' : LoopCfgD G s Φ p),
      FPC (l + 1) Blow B S d0 φ d1 p P0 Q W φ1 ω cfp → CallPre B S d0 → Inv φ →
      (∀ x ∈ S, Blow ≤ d0 x) →
      ALoop (dlOps G s) Inv Mf l B S d0 d1 P0 B'0 f0 L0 c' → ¬ LoopDoneD (τ (l + 1)) c' →
      ∀ ks Bi g1 Dc1 cp, pullC (dlOps G s) (T (l + 1)) c'.cs.g c'.cs.Dc = (ks, Bi, g1, Dc1, cp) →
      (BM.expand c'.cs.lit ks.toFinset Bi).card ≤ Sb l)
    (hK : Kf + Cf + Ko + Kfin + Cfin + 2 * DL.K + 60 ≤ K) (hSl : Cst + 2 ≤ Sl) :
    CallSpec DL PI.PhiR Inv FPC DCb Mf τ LF body K Sl Sb (l + 1) := by
  intro st Blow B S d φ g Ds H c0 hpre hI hlow hBlow hK0 hab _ hIn hbud hubud
  have hproc : st.procs[P_bmssp]? = some body := hIn.stat.proc
  rw [hbody] at hproc
  refine runs_call_rec hproc hIn.lvl ?_
  have hU := unch_enter_charge st 1 [] [] [] []
  refine ((body_spec DL PI hNm hFP hLoop hFin hFPC hFPCt hτ hMf hM1 hSbA hK hSl
    ((st.enter).charge 1) Blow B S d φ g Ds H c0 hpre hI hlow hBlow hK0 hab (callIn_enter DL PI hIn)
    (fun res φ' g' lg h => by have := hbud res φ' g' lg h; simp; omega)
    (fun res φ' g' lg h => by
      rw [DL.use_frame st _ [] [] [] [] hU (by simp)]; exact hubud res φ' g' lg h)).mono ?_)
  rintro r ⟨res, φ', g', lg, H', hrel, hext, hout, hc1', hc2', hu'⟩
  have hus : DL.use ((st.enter).charge 1) = DL.use st := DL.use_frame st _ [] [] [] [] hU (by simp)
  refine ⟨res, φ', g', lg, H', hrel, hext, ⟨hout.lvl, hout.stat, hout.lab, hout.D, hout.phi, hout.U,
    hout.sBp, hout.ptr, fun x hx => hout.ptrFr x hx, hout.clr, ?_, fun a ha => hout.stArr a ha⟩,
    by simp at hc1'; omega, by simp at hc2'; omega, by rw [← hus]; exact hu'⟩
  exact ⟨fun a ha i hi => hout.above.rows a ha i hi, fun a ha j hj => hout.above.lens a ha j hj,
    fun i hi => hout.above.slots i hi, hout.above.wlen, hout.above.vlen⟩

end Frontier.CHD.RamBody
