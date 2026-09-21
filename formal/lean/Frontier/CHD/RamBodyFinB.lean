import Frontier.CHD.RamBodySpec
import Frontier.CHD.RamBodyFinDefs

/-!
# Frontier.CHD.RamBodyFinB — agent-03's finalization statement gives the level body's `FinB`
(owner: agent-01)

**NON-GATE** (B-L4).  `FinSpecStmt` is the statement of agent-03's `fin_spec` (RamBodyFin) for the
finalization `finProg DL.empty tstT6 DL.ins tstWp (relW DL.ins) delW`; `finB_of_finSpec` turns it
into `FinB` with `Kf = Kfin DL.K`, `C = 100` and the static constant `finCst`: the premises of
`FinB` imply those of `fin_spec` (the `Wp` row lengths come from `Static`, the use budget with
factor 2 implies the factor-1 one, and `|S|, |W| ≤ n` bound the static budget).  `FinB.mono`
(monotone in the constants) and `finB_uniform` give `hFin` of `L6.hs_of_parts` with closed texts
and one uniform constant `Kfin KD`; the `W'`-deletion `delW` is `DDelW.dsDelW` (`delWBU_mkDL`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBody

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine
  Frontier.CHD.WinScan WExpr Stmt

variable {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} {Φ : Type}

/-- The static constant of the finalization's budget (agent-02's `relW_spec` and the T6 inserts). -/
def finCst (G : Graph) (K NB : ℕ) : ℕ :=
  K * (G.n * (Nat.log 2 NB + 4)) + (G.n + 1) * ((G.m + 1) * CED K NB + 101)

/-- **The statement of agent-03's `fin_spec`.** -/
def FinSpecStmt (DL : DLayer G s T) (PI : PhiI Φ) (LF : ℕ) (body : Stmt) (τ Mf : ℕ → ℕ)
    (delW : Stmt) : Prop :=
  ∀ (st : State ℝ≥0) (l : ℕ) (B : WLab G s) (S W : Finset (Fin G.n)) (wl : List (Fin G.n))
    (Ds : ℕ → DStrM G s) (H : Hist G) (c0 : ℕ) {p : ℕ} (c : LoopCfgD G s Φ p),
    LoopRep DL PI LF body τ Mf st (l + 1) B (τ (l + 1)) Ds H c0 c →
    SetRow st "S" "S.len" (l + 1) S →
    RowRep st "W" "W.len" G.n (l + 1) (wl.map Fin.val) → wl.Nodup → wl.toFinset = W →
    ((l + 2) * G.n ≤ st.wlen "Wp" ∧ l + 1 < st.wlen "Wp.len") →
    WalkInv c.cs.d → (∀ u ∈ c.cs.U, c.cs.d u = dis (s := s) u) →
    (∀ x ∈ W, x ∉ c.cs.U → c.cs.d x < bpfB B c.cs → c.cs.d x = dis (s := s) x) →
    (∀ j, ∀ x ∈ c.cs.P j, x ∈ S) → c.cs.Dc.Bd = B →
    (∀ (lT6 : List (Fin G.n)) (L : List (Fin G.m)) (lW' : List (Fin G.n)), lT6.Nodup →
      (∀ x, x ∈ lT6 ↔ x ∈ S ∧ bpfB B c.cs ≤ c.cs.d x ∧ c.cs.d x < B) → lW'.Nodup →
      (∀ x, x ∈ lW' ↔ (x ∈ W ∧ x ∉ c.cs.U) ∧ c.cs.d x < bpfB B c.cs) →
      Enumerates G L lW'.toFinset →
      DL.use st + S.card +
        (finD (dlOps G s) (T (l + 1)) B (bpfB B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.2 ≤
          DL.ucap) →
    st.cost + Kfin DL.K * (1 + S.card + W.card) + DL.K * (S.card * (Nat.log 2 DL.NB + 4)) +
      (W.card + 1) * ((G.m + 1) * CED DL.K DL.NB + 101) ≤ c0 + st.cap →
    Runs realOps (finProg DL.empty tstT6 DL.ins tstWp (relW DL.ins) delW) st (fun r =>
      ∃ (lT6 : List (Fin G.n)) (W' : Finset (Fin G.n)) (lW' : List (Fin G.n)) (L : List (Fin G.m))
        (H' : Hist G), FinOut DL PI LF body τ Mf st r l B S W Ds H c0 c lT6 W' lW' L H' (Kfin DL.K) 100)

/-- **`fin_spec` gives `FinB`.** -/
theorem finB_of_finSpec (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt} {τ Mf : ℕ → ℕ}
    {delW : Stmt} (hfs : FinSpecStmt DL PI LF body τ Mf delW) (l : ℕ) (hl : l + 1 ≤ LF) :
    FinB DL PI LF body τ Mf (finProg DL.empty tstT6 DL.ins tstWp (relW DL.ins) delW) (Kfin DL.K) 100
      (finCst G DL.K DL.NB) l := by
  intro st B S W wl Ds H c0 p c hloop hS hW hwnd hwset hwalk hUc hW'c hPS hBd hbud hUse
  have hst := hloop.stat
  have hWp : (l + 2) * G.n ≤ st.wlen "Wp" ∧ l + 1 < st.wlen "Wp.len" := by
    refine ⟨le_trans (Nat.mul_le_mul_right _ (by omega)) (hst.rows "Wp" (by simp [rowArrs])), ?_⟩
    have := hst.lens "Wp.len" (by simp [lenArrs]); omega
  have hSn : S.card ≤ G.n := (Finset.card_le_univ S).trans (by simp)
  have hWn : W.card ≤ G.n := (Finset.card_le_univ W).trans (by simp)
  refine hfs st l B S W wl Ds H c0 c hloop hS hW hwnd hwset hWp hwalk hUc hW'c hPS hBd
    (fun lT6 L lW' h1 h2 h3 h4 h5 => by
      have := hUse lT6 L lW' h1 h2 h5 h3 (fun x => by rw [List.mem_toFinset]; exact h4 x)
      omega) ?_
  have e1 : DL.K * (S.card * (Nat.log 2 DL.NB + 4)) ≤ DL.K * (G.n * (Nat.log 2 DL.NB + 4)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hSn)
  have e2 : (W.card + 1) * ((G.m + 1) * CED DL.K DL.NB + 101) ≤
      (G.n + 1) * ((G.m + 1) * CED DL.K DL.NB + 101) := Nat.mul_le_mul_right _ (by omega)
  unfold finCst at hbud
  omega

/-- `FinOut` is monotone in its cost constants. -/
theorem FinOut.mono {DL : DLayer G s T} {PI : PhiI Φ} {LF : ℕ} {body : Stmt} {τ Mf : ℕ → ℕ}
    {st r : State ℝ≥0} {l : ℕ} {B : WLab G s} {S W : Finset (Fin G.n)} {Ds : ℕ → DStrM G s}
    {H : Hist G} {c0 : ℕ} {p : ℕ} {c : LoopCfgD G s Φ p} {lT6 : List (Fin G.n)}
    {W' : Finset (Fin G.n)} {lW' : List (Fin G.n)} {L : List (Fin G.m)} {H' : Hist G}
    {Kf C Kf' C' : ℕ} (h : FinOut DL PI LF body τ Mf st r l B S W Ds H c0 c lT6 W' lW' L H' Kf C)
    (hK : Kf ≤ Kf') (hC : C ≤ C') :
    FinOut DL PI LF body τ Mf st r l B S W Ds H c0 c lT6 W' lW' L H' Kf' C' :=
  { h with
    cost2 := le_trans h.cost2 (by
      have := Nat.mul_le_mul_right (1 + S.card + W.card + W'.card +
        (finD (dlOps G s) (T (l + 1)) B (bpfB B c.cs) c.cs.d c.cs.g c.cs.Dc lT6 L lW').2.2.2) hK
      omega) }

/-- `FinB` is monotone in its constants (a larger `Kf` / `Cst` strengthens the budget premise and
weakens the cost bound; a larger `C` weakens the cost bound). -/
theorem FinB.mono {DL : DLayer G s T} {PI : PhiI Φ} {LF : ℕ} {body : Stmt} {τ Mf : ℕ → ℕ}
    {finP : Stmt} {Kf C Cst Kf' C' Cst' l : ℕ} (h : FinB DL PI LF body τ Mf finP Kf C Cst l)
    (hK : Kf ≤ Kf') (hC : C ≤ C') (hCst : Cst ≤ Cst') :
    FinB DL PI LF body τ Mf finP Kf' C' Cst' l := by
  intro st B S W wl Ds H c0 p c hloop hS hW hwnd hwset hwalk hUc hW'c hPS hBd hbud hUse
  have hb : st.cost + Kf * (1 + S.card + W.card) + 3 * c.cs.U.card + Cst ≤ c0 + st.cap := by
    have := Nat.mul_le_mul_right (1 + S.card + W.card) hK
    omega
  refine (h st B S W wl Ds H c0 c hloop hS hW hwnd hwset hwalk hUc hW'c hPS hBd hb hUse).mono ?_
  rintro r ⟨lT6, W', lW', L, H', hF⟩
  exact ⟨lT6, W', lW', L, H', hF.mono hK hC⟩

/-- **`hFin` of the level step** (`L6.hs_of_parts`) from `fin_spec`: closed texts `emptyS`/`insS`
for the D operations and one uniform own-work constant `Kfin KD` for every instance with
`DL.K ≤ KD`. -/
theorem finB_uniform (DL : DLayer G s T) (PI : PhiI Φ) {LF : ℕ} {body : Stmt} {τ Mf : ℕ → ℕ}
    {emptyS insS delW : Stmt} (hemp : DL.empty = emptyS) (hins : DL.ins = insS)
    (hfs : FinSpecStmt DL PI LF body τ Mf delW) {KD : ℕ} (hKD : DL.K ≤ KD) (l : ℕ) (hl : l < LF) :
    FinB DL PI LF body τ Mf (finProg emptyS tstT6 insS tstWp (relW insS) delW) (Kfin KD) 100
      (finCst G DL.K DL.NB) l := by
  have h := finB_of_finSpec DL PI hfs l (by omega)
  rw [hemp, hins] at h
  exact h.mono (by unfold Kfin; omega) le_rfl le_rfl

end Frontier.CHD.RamBody
