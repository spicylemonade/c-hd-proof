import Frontier.CHD.L6.Keep
import Frontier.CHD.L6.CSort
import Frontier.CHD.L6.Dedup

/-!
# L6 pass A (agent-10, scratch): dedup + kept flags + degrees + offsets for every vertex
-/

open scoped NNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt Finset

/-- The input of L6 as functions (read from the RAM input arrays). -/
structure L6In where
  n : ℕ
  m : ℕ
  s : ℕ
  src : ℕ → ℕ
  dst : ℕ → ℕ
  wt : ℕ → ℝ≥0

namespace L6In

variable (I : L6In)

noncomputable def keep (v : ℕ) : ℕ := keepF I.src I.dst I.m I.s v
def grp (u : ℕ) : List ℕ := grpk I.src I.m u
def kept (u e : ℕ) : Prop := keptP I.dst I.wt u (I.grp u) e
noncomputable instance (u e : ℕ) : Decidable (I.kept u e) := by unfold kept; infer_instance
noncomputable def deg (u : ℕ) : ℕ :=
  if I.keep u = 0 then 0 else ((I.grp u).filter (fun e => decide (I.kept u e))).length
def δ : ℕ := deltaF I.n I.m
noncomputable def cc (u : ℕ) : ℕ :=
  if I.keep u = 0 then 0 else max 1 ((I.deg u + (I.δ - 2)) / (I.δ - 1))
noncomputable def off (u : ℕ) : ℕ := ∑ i ∈ range u, I.cc i
/-- number of slots of `u` -/
noncomputable def ns (u : ℕ) : ℕ := if I.keep u = 0 then 0 else I.deg u + I.cc u - 1
noncomputable def sl (u : ℕ) : ℕ := ∑ i ∈ range u, I.ns i
def keptE (e : ℕ) : Prop := I.keep (I.src e) ≠ 0 ∧ I.kept (I.src e) e
open Classical in
noncomputable def keptArr (u : ℕ) : ℕ → ℕ :=
  fun e => if e < I.m ∧ I.src e < u ∧ I.keptE e then 1 else 0

theorem off_succ (u : ℕ) : I.off (u + 1) = I.off u + I.cc u := by simp [off, sum_range_succ]
theorem sl_succ (u : ℕ) : I.sl (u + 1) = I.sl u + I.ns u := by simp [sl, sum_range_succ]

theorem mem_grp {u e : ℕ} : e ∈ I.grp u ↔ e < I.m ∧ I.src e = u := by
  simp [grp, grpk]

theorem keptArr_zero : I.keptArr 0 = fun _ => 0 := by funext e; simp [keptArr]

theorem keptArr_succ_skip {u : ℕ} (hk : I.keep u = 0) : I.keptArr (u + 1) = I.keptArr u := by
  funext e
  unfold keptArr
  by_cases h : e < I.m ∧ I.src e < u + 1 ∧ I.keptE e
  · have hne : I.src e ≠ u := by rintro rfl; exact h.2.2.1 hk
    rw [if_pos h, if_pos ⟨h.1, by omega, h.2.2⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1, by omega, h'.2.2⟩)]

theorem keptArr_succ_kept {u : ℕ} (hk : I.keep u ≠ 0) :
    I.keptArr (u + 1) = fun e => if e ∈ I.grp u ∧ I.kept u e then 1 else I.keptArr u e := by
  funext e
  simp only [I.mem_grp]
  unfold keptArr keptE
  by_cases hs : I.src e = u
  · subst hs
    by_cases he : e < I.m
    · simp [he, hk]
    · simp [he]
  · have : I.src e < u + 1 ↔ I.src e < u := by omega
    simp [hs, this]

end L6In

def passAWA : List String := ["g_mark", "g_best", "g_deg", "g_off", "g_sl", "g_kept"]
def passAWR : List String := ["g_u", "g_x", "g_y", "g_z", "g_j", "g_e", "g_v", "g_b", "g_d", "g_c"]

/-- The read-only environment of pass A (outputs of keep/params/csort and the input). -/
structure AEnv (I : L6In) (t : State ℝ≥0) : Prop where
  n : t.w "n" = I.n
  m : t.w "m" = I.m
  gD : t.w "gD" = I.δ
  src : ∀ e < I.m, t.wa "src" e = I.src e
  srcL : I.m ≤ t.wlen "src"
  dst : ∀ e < I.m, t.wa "dst" e = I.dst e
  dstL : I.m ≤ t.wlen "dst"
  w : ∀ e < I.m, t.va "w" e = I.wt e
  wL : I.m ≤ t.vlen "w"
  hsrc : ∀ e < I.m, I.src e < I.n
  hdst : ∀ e < I.m, I.dst e < I.n
  keep : WSeg t "gKeep" 0 I.n I.keep
  cnt : WSeg t "g_cnt" 0 (I.n + 1) (pfx I.src I.m)
  ord : OrdK I.src I.m I.n I.m t
  ordL : t.wlen "g_ord" = I.m

theorem AEnv.of_unchanged {I : L6In} {t t' : State ℝ≥0} (h : AEnv I t)
    (hU : Unchanged t t' passAWA [] passAWR []) : AEnv I t' where
  n := by rw [hU.wreg _ (by simp [passAWR])]; exact h.n
  m := by rw [hU.wreg _ (by simp [passAWR])]; exact h.m
  gD := by rw [hU.wreg _ (by simp [passAWR])]; exact h.gD
  src e he := by rw [(hU.warr _ (by simp [passAWA])).1]; exact h.src e he
  srcL := by rw [(hU.warr _ (by simp [passAWA])).2]; exact h.srcL
  dst e he := by rw [(hU.warr _ (by simp [passAWA])).1]; exact h.dst e he
  dstL := by rw [(hU.warr _ (by simp [passAWA])).2]; exact h.dstL
  w e he := by rw [(hU.varr _ (by simp)).1]; exact h.w e he
  wL := by rw [(hU.varr _ (by simp)).2]; exact h.wL
  hsrc := h.hsrc
  hdst := h.hdst
  keep := h.keep.of_unchanged hU (by simp [passAWA])
  cnt := h.cnt.of_unchanged hU (by simp [passAWA])
  ord u hu i hi := by rw [(hU.warr _ (by simp [passAWA])).1]; exact h.ord u hu i hi
  ordL := by rw [(hU.warr _ (by simp [passAWA])).2]; exact h.ordL

namespace L6In

variable (I : L6In)

theorem grp_length (u : ℕ) : (I.grp u).length = cntk I.src I.m u := grpk_length _ _ _

theorem deg_le (u : ℕ) : I.deg u ≤ (I.grp u).length := by
  unfold deg; split_ifs
  · exact Nat.zero_le _
  · exact List.length_filter_le _ _

theorem cc_le (u : ℕ) (hδ : 3 ≤ I.δ) : I.cc u ≤ I.deg u + 1 := by
  unfold cc; split_ifs
  · exact Nat.zero_le _
  · apply max_le (by omega)
    apply Nat.div_le_of_le_mul
    have h1 : I.deg u ≤ (I.δ - 1) * I.deg u := Nat.le_mul_of_pos_left _ (by omega)
    have h2 : (I.δ - 1) * (I.deg u + 1) = (I.δ - 1) * I.deg u + (I.δ - 1) := by ring
    omega

theorem ns_le (u : ℕ) (hδ : 3 ≤ I.δ) : I.ns u ≤ 2 * I.deg u := by
  unfold ns; split_ifs with h
  · exact Nat.zero_le _
  · have hc := I.cc_le u hδ
    by_cases hd : I.deg u = 0
    · have h0 : (0 + (I.δ - 2)) / (I.δ - 1) = 0 := Nat.div_eq_of_lt (by omega)
      have : I.cc u = 1 := by simp only [cc, if_neg h, hd, h0]; rfl
      omega
    · omega

end L6In

/-- Frame of `passAKept`. -/
def kWA : List String := ["g_mark", "g_best", "g_kept", "g_deg"]
def kWR : List String := ["g_z", "g_j", "g_e", "g_v", "g_b", "g_d", "g_c", "g_x", "g_y"]

/-- Postcondition of `passAKept` for vertex `u` from state `t`. -/
structure KPost (I : L6In) (u : ℕ) (t r : State ℝ≥0) : Prop where
  gx : r.w "g_x" = t.w "g_x" + I.cc u
  gy : r.w "g_y" = t.w "g_y" + I.ns u
  deg : r.wa "g_deg" = Function.update (t.wa "g_deg") u (I.deg u)
  kept : r.wa "g_kept" = fun e => if e ∈ I.grp u ∧ I.kept u e then 1 else t.wa "g_kept" e
  mark : ∀ v < I.n, r.wa "g_mark" v ≤ u + 1
  mL : r.wlen "g_mark" = I.n
  bL : r.wlen "g_best" = I.n
  kL : r.wlen "g_kept" = t.wlen "g_kept"
  dL : r.wlen "g_deg" = t.wlen "g_deg"
  U : Unchanged t r kWA [] kWR []
  c : r.cost ≤ t.cost + 17 * (I.grp u).length + 14

theorem passAKept_runs (I : L6In) (t : State ℝ≥0) (u : ℕ) (hE : AEnv I t) (hu : t.w "g_u" = u)
    (hun : u < I.n) (hk : I.keep u ≠ 0) (hδ : 3 ≤ I.δ)
    (hmark : ∀ v < I.n, t.wa "g_mark" v ≤ u)
    (hmL : t.wlen "g_mark" = I.n) (hbL : t.wlen "g_best" = I.n) (hkL : I.m ≤ t.wlen "g_kept")
    (hdL : u < t.wlen "g_deg")
    (hx : t.w "g_x" + I.n + I.m + 2 < t.cap) (hy : t.w "g_y" + 2 * I.m + 2 < t.cap)
    (hcap : 4 * (I.n + I.m) + 8 < t.cap) :
    Runs realOps passAKept t (KPost I u t) := by
  set L := I.grp u with hLdef
  have hcntL : u + 1 < t.wlen "g_cnt" := by have := hE.cnt.1; omega
  have hcnt0 : t.wa "g_cnt" u = pfx I.src I.m u := by
    have := hE.cnt.2 u (by omega); simpa using this
  have hcnt1 : t.wa "g_cnt" (u + 1) = pfx I.src I.m u + L.length := by
    have := hE.cnt.2 (u + 1) (by omega); simp at this; rw [this, pfx_succ, I.grp_length]
  have hpm : pfx I.src I.m u + L.length ≤ I.m := by
    have h1 : pfx I.src I.m (u + 1) ≤ pfx I.src I.m I.n := pfx_mono _ _ (by omega)
    rw [pfx_total _ _ _ hE.hsrc, pfx_succ, ← I.grp_length] at h1; exact h1
  have hordL : pfx I.src I.m u + L.length ≤ t.wlen "g_ord" := by rw [hE.ordL]; exact hpm
  have hord : ∀ i < L.length, t.wa "g_ord" (pfx I.src I.m u + i) = L.getD i 0 := by
    intro i hi; rw [I.grp_length] at hi; exact hE.ord u hun i hi
  have hLm : ∀ e ∈ L, e < I.m := fun e he => (I.mem_grp.mp he).1
  have hLd : ∀ e ∈ L, I.dst e < I.n := fun e he => hE.hdst e (hLm e he)
  unfold passAKept
  -- g_z := u + 1
  refine runs_seq (runs_wset (a := u + 1) (evalW_add_of (by rw [evalW_var, hu])
    (evalW_lit_of (by omega)) (by omega)) ?_)
  -- g_j := g_cnt[u]
  refine runs_seq (runs_wset (a := pfx I.src I.m u) (by
    rw [evalW_load_of (j := u) (by simp [hu]) (by simp; omega)]; simp [hcnt0]) ?_)
  set s2 := (((t.setW "g_z" (u + 1)).charge 1).setW "g_j" (pfx I.src I.m u)).charge 1 with hs2
  refine runs_seq ((dedupLoop_runs s2 I.n I.m u (pfx I.src I.m u) I.dst I.wt L
    (by simp [hs2, hu]) (by simp [hs2]) (by simp [hs2]) (by simpa [hs2] using hcntL)
    (by simpa [hs2] using hcnt1) (by simpa [hs2] using hordL) (by simpa [hs2] using hord)
    hLm hLd (by simpa [hs2] using hE.dst) (by simpa [hs2] using hE.dstL)
    (by simpa [hs2] using hE.w) (by simpa [hs2] using hE.wL) (by simpa [hs2] using hmL)
    (by simpa [hs2] using hbL)
    ⟨fun v hv _ => by have := hmark v hv; simp [hs2]; omega, fun v _ b h => by simp at h⟩
    (by simp [hs2]; omega)).mono ?_)
  rintro r1 ⟨hR1, hmL1, hbL1, hU1, hc1⟩
  have hU1' : Unchanged t r1 kWA [] kWR [] := by
    have h := (show Unchanged t s2 kWA [] kWR [] by simp [hs2, kWR]).trans
      (hU1.mono (by simp [dedupWA, kWA]) (by simp) (by simp [dedupWR, kWR]) (by simp))
    exact h
  have hr1u : r1.w "g_u" = u := by rw [hU1'.wreg _ (by simp [kWR])]; exact hu
  have hE1 : AEnv I r1 := hE.of_unchanged (hU1'.mono (by simp [kWA, passAWA]) (by simp)
    (by simp [kWR, passAWR]) (by simp))
  -- g_d := 0 ; g_j := g_cnt[u]
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hU1'.cap]; omega)) ?_)
  refine runs_seq (runs_wset (a := pfx I.src I.m u) (by
    rw [evalW_load_of (j := u) (by simp [hr1u]) (by simp; have := hE1.cnt.1; omega)]
    have := hE1.cnt.2 u (by omega); simp at this; simp [this]) ?_)
  set s4 := (((r1.setW "g_d" 0).charge 1).setW "g_j" (pfx I.src I.m u)).charge 1 with hs4
  have hkL1 : I.m ≤ r1.wlen "g_kept" := by
    rw [(hU1.warr "g_kept" (by simp [dedupWA])).2]; simpa [hs2] using hkL
  refine runs_seq ((flagLoop_runs s4 I.n I.m u (pfx I.src I.m u) I.dst I.wt L
    (by simp [hs4, hr1u]) (by simp [hs4]) (by simp [hs4])
    (by simpa [hs4] using (show u + 1 < r1.wlen "g_cnt" by have := hE1.cnt.1; omega))
    (by have := hE1.cnt.2 (u + 1) (by omega); simp at this
        simp only [hs4, State.charge_wa, State.setW_wa]; rw [this, pfx_succ, hLdef, I.grp_length])
    (by simpa [hs4, hE1.ordL] using hpm)
    (by intro i hi; simp [hs4]; rw [I.grp_length] at hi; exact hE1.ord u hun i hi)
    hLm hLd (by simpa [hs4] using hE1.dst) (by simpa [hs4] using hE1.dstL)
    (by simpa [hs4] using hbL1) (by simpa [hs4] using hkL1)
    (by simpa [hs4, DRep] using hR1) (by simp [hs4]; rw [hU1'.cap]; omega)).mono ?_)
  rintro r2 ⟨hd2, hk2, hkL2, hU2, hc2⟩
  have hU2' : Unchanged t r2 kWA [] kWR [] :=
    hU1'.trans ((show Unchanged r1 s4 kWA [] kWR [] by simp [hs4, kWR]).trans
      (hU2.mono (by simp [flagWA, kWA]) (by simp) (by simp [flagWR, kWR]) (by simp)))
  have hr2u : r2.w "g_u" = u := by rw [hU2'.wreg _ (by simp [kWR])]; exact hu
  have hE2 : AEnv I r2 := hE.of_unchanged (hU2'.mono (by simp [kWA, passAWA]) (by simp)
    (by simp [kWR, passAWR]) (by simp))
  have hdeg : r2.w "g_d" = I.deg u := by rw [hd2]; simp [L6In.deg, hk, L6In.kept, hLdef]
  have hδ2 : r2.w "gD" = I.δ := hE2.gD
  have hr2x : r2.w "g_x" = t.w "g_x" := by
    rw [hU2.wreg _ (by simp [flagWR]), hs4]; simp
    rw [hU1.wreg _ (by simp [dedupWR]), hs2]; simp
  have hr2y : r2.w "g_y" = t.w "g_y" := by
    rw [hU2.wreg _ (by simp [flagWR]), hs4]; simp
    rw [hU1.wreg _ (by simp [dedupWR]), hs2]; simp
  have hr2cap : r2.cap = t.cap := hU2'.cap
  have hdegb : I.deg u ≤ I.m := le_trans (I.deg_le u) (by rw [← hLdef]; omega)
  have hdL2 : u < r2.wlen "g_deg" := by
    rw [(hU2.warr "g_deg" (by simp [flagWA])).2, hs4]; simp
    rw [(hU1.warr "g_deg" (by simp [dedupWA])).2, hs2]; simp; exact hdL
  have hccE : I.cc u = max 1 ((I.deg u + (I.δ - 2)) / (I.δ - 1)) := by simp [L6In.cc, hk]
  have hcle := I.cc_le u hδ
  have hδm : I.δ ≤ 2 * I.m + I.n + 3 := by
    simp only [L6In.δ, deltaF]
    apply max_le (by omega)
    exact le_trans (Nat.div_le_self _ _) (by omega)
  -- facts about r2 relative to t
  have hr2deg : r2.wa "g_deg" = t.wa "g_deg" := by
    rw [(hU2.warr "g_deg" (by simp [flagWA])).1, hs4]; simp
    rw [(hU1.warr "g_deg" (by simp [dedupWA])).1, hs2]; simp
  have hr2dL : r2.wlen "g_deg" = t.wlen "g_deg" := by
    rw [(hU2.warr "g_deg" (by simp [flagWA])).2, hs4]; simp
    rw [(hU1.warr "g_deg" (by simp [dedupWA])).2, hs2]; simp
  have hr2mark : r2.wa "g_mark" = r1.wa "g_mark" := by
    rw [(hU2.warr "g_mark" (by simp [flagWA])).1, hs4]; simp
  have hr2mL : r2.wlen "g_mark" = I.n := by
    rw [(hU2.warr "g_mark" (by simp [flagWA])).2, hs4]; simpa using hmL1
  have hr2bL : r2.wlen "g_best" = I.n := by
    rw [(hU2.warr "g_best" (by simp [flagWA])).2, hs4]; simpa using hbL1
  have hs4kept : s4.wa "g_kept" = t.wa "g_kept" := by
    rw [hs4]; simp; rw [(hU1.warr "g_kept" (by simp [dedupWA])).1, hs2]; simp
  have hr2kL : r2.wlen "g_kept" = t.wlen "g_kept" := by
    rw [hkL2, hs4]; simp; rw [(hU1.warr "g_kept" (by simp [dedupWA])).2, hs2]; simp
  have hr2kept : r2.wa "g_kept" = fun e => if e ∈ I.grp u ∧ I.kept u e then 1 else t.wa "g_kept" e := by
    rw [hk2, hs4kept]; rfl
  have hmark1 : ∀ v < I.n, r1.wa "g_mark" v ≤ u + 1 := by
    intro v hv
    cases h : bst I.dst I.wt u L v with
    | none => have := hR1.1 v hv h; omega
    | some b => exact le_of_eq (hR1.2 v hv b h).1
  have hcost2 : r2.cost ≤ t.cost + 17 * (I.grp u).length + 6 := by
    have e1 : s2.cost = t.cost + 2 := by simp [hs2]
    have e2 : s4.cost = r1.cost + 2 := by simp [hs4]
    rw [← hLdef]; omega
  apply wp_sound
  by_cases hc0 : (I.deg u + (I.δ - 2)) / (I.δ - 1) = 0
  · have hcc1 : I.cc u = 1 := by rw [hccE, hc0]; rfl
    simp [wp, hr2u, hdeg, hδ2, hdL2, fit, hr2cap, hr2x, hr2y, hc0,
      show u < t.cap by omega, show I.deg u + (I.δ - 2) < t.cap by omega,
      show 2 < t.cap by omega, show 1 < t.cap by omega, show 0 < t.cap by omega,
      show t.w "g_x" + 1 < t.cap by omega, show I.deg u + 1 < t.cap by omega,
      show t.w "g_y" + (I.deg u + 1) < t.cap by omega, show (1 : ℕ) ≤ I.δ by omega,
      show I.δ - 1 ≠ 0 by omega]
    refine ⟨by simp [hcc1], by simp [L6In.ns, hk, hcc1] <;> omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by simpa [kWA, kWR] using hU2', by simp; omega⟩
    · funext i; simp [Function.update, hr2deg]
    · funext e; simp [hr2kept]
    · intro v hv; simp [hr2mark]; exact hmark1 v hv
    · simpa using hr2mL
    · simpa using hr2bL
    · simpa using hr2kL
    · simpa using hr2dL
  · have hccE' : I.cc u = (I.deg u + (I.δ - 2)) / (I.δ - 1) := by
      rw [hccE]; exact max_eq_right (Nat.one_le_iff_ne_zero.mpr hc0)
    have hc0le : (I.deg u + (I.δ - 2)) / (I.δ - 1) ≤ I.deg u + 1 := by rw [← hccE']; exact hcle
    simp [wp, hr2u, hdeg, hδ2, hdL2, fit, hr2cap, hr2x, hr2y, hc0,
      show u < t.cap by omega, show I.deg u + (I.δ - 2) < t.cap by omega,
      show 2 < t.cap by omega, show 1 < t.cap by omega, show 0 < t.cap by omega,
      show t.w "g_x" + (I.deg u + (I.δ - 2)) / (I.δ - 1) < t.cap by omega,
      show I.deg u + (I.deg u + (I.δ - 2)) / (I.δ - 1) < t.cap by omega,
      show t.w "g_y" + (I.deg u + (I.deg u + (I.δ - 2)) / (I.δ - 1)) < t.cap by omega,
      show (1 : ℕ) ≤ I.δ by omega, show I.δ - 1 ≠ 0 by omega]
    refine ⟨by simp [hccE'], by simp [L6In.ns, hk, hccE'] <;> omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by simpa [kWA, kWR] using hU2', by simp; omega⟩
    · funext i; simp [Function.update, hr2deg]
    · funext e; simp [hr2kept]
    · intro v hv; simp [hr2mark]; exact hmark1 v hv
    · simpa using hr2mL
    · simpa using hr2bL
    · simpa using hr2kL
    · simpa using hr2dL

namespace L6In

variable (I : L6In)

theorem off_le (hδ : 3 ≤ I.δ) (u : ℕ) : I.off u ≤ u + pfx I.src I.m u := by
  induction u with
  | zero => simp [off, pfx]
  | succ u ih =>
    rw [I.off_succ, pfx_succ]
    have h1 := I.cc_le u hδ
    have h2 := I.deg_le u
    rw [I.grp_length] at h2
    omega

theorem sl_le (hδ : 3 ≤ I.δ) (u : ℕ) : I.sl u ≤ 2 * pfx I.src I.m u := by
  induction u with
  | zero => simp [sl, pfx]
  | succ u ih =>
    rw [I.sl_succ, pfx_succ]
    have h1 := I.ns_le u hδ
    have h2 := I.deg_le u
    rw [I.grp_length] at h2
    omega

theorem cc_zero {u : ℕ} (hk : I.keep u = 0) : I.cc u = 0 := by simp [cc, hk]
theorem ns_zero {u : ℕ} (hk : I.keep u = 0) : I.ns u = 0 := by simp [ns, hk]
theorem deg_zero {u : ℕ} (hk : I.keep u = 0) : I.deg u = 0 := by simp [deg, hk]

end L6In

/-- Outer invariant of pass A after `u` vertices. -/
structure AInv (I : L6In) (st : State ℝ≥0) (u : ℕ) (t : State ℝ≥0) : Prop where
  E : AEnv I t
  gu : t.w "g_u" = u
  gx : t.w "g_x" = I.off u
  gy : t.w "g_y" = I.sl u
  offA : ∀ i < u, t.wa "g_off" i = I.off i
  slA : ∀ i < u, t.wa "g_sl" i = I.sl i
  degA : ∀ i < I.n, t.wa "g_deg" i = if i < u then I.deg i else 0
  keptA : t.wa "g_kept" = I.keptArr u
  markA : ∀ v < I.n, t.wa "g_mark" v ≤ u
  mL : t.wlen "g_mark" = I.n
  bL : t.wlen "g_best" = I.n
  dL : t.wlen "g_deg" = I.n
  oL : t.wlen "g_off" = I.n + 1
  sL : t.wlen "g_sl" = I.n + 1
  kL : t.wlen "g_kept" = I.m
  U : Unchanged st t passAWA [] passAWR []
  c : t.cost ≤ st.cost + 25 * u + 17 * pfx I.src I.m u

theorem passALoop_runs (I : L6In) (st : State ℝ≥0) (hδ : 3 ≤ I.δ)
    (hcap : 4 * (I.n + I.m) + 8 < st.cap) (h0 : AInv I st 0 st) :
    Runs realOps passALoop st (fun r => ∃ t, AInv I st I.n t ∧ r = t.charge 1) := by
  refine runs_while (fun u t => AInv I st u t) I.n _ ?_ ?_ st h0
  · intro u hun t hI
    have hE := hI.E
    have htcap : t.cap = st.cap := hI.U.cap
    have hkeepL : u < t.wlen "gKeep" := by have := hE.keep.1; omega
    have hkeepv : t.wa "gKeep" u = I.keep u := by have := hE.keep.2 u hun; simpa using this
    have hxb : t.w "g_x" + I.n + I.m + 2 < t.cap := by
      rw [hI.gx, htcap]; have := I.off_le hδ u
      have h2 : pfx I.src I.m u ≤ I.m := by
        have := pfx_mono I.src I.m (show u ≤ I.n by omega); rw [pfx_total _ _ _ hE.hsrc] at this; exact this
      omega
    have hyb : t.w "g_y" + 2 * I.m + 2 < t.cap := by
      rw [hI.gy, htcap]; have := I.sl_le hδ u
      have h2 : pfx I.src I.m u ≤ I.m := by
        have := pfx_mono I.src I.m (show u ≤ I.n by omega); rw [pfx_total _ _ _ hE.hsrc] at this; exact this
      omega
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := u) (y := I.n) (by rw [evalW_var, hI.gu]) (by rw [evalW_var, hE.n])
        (by omega)]
      simp [hun]
    · unfold passABody
      set t0 := t.charge 1 with ht0
      refine runs_seq (runs_wstore (j := u) (a := I.off u) (by simp [ht0, hI.gu])
        (by simp [ht0, hI.gx]) (by simp [ht0, hI.oL]; omega) ?_)
      set t1 := (t0.storeW "g_off" u (I.off u)).charge 1 with ht1
      refine runs_seq (runs_wstore (j := u) (a := I.sl u) (by simp [ht1, ht0, hI.gu])
        (by simp [ht1, ht0, hI.gy]) (by simp [ht1, ht0, hI.sL]; omega) ?_)
      set t2 := (t1.storeW "g_sl" u (I.sl u)).charge 1 with ht2
      have ht2u : t2.w "g_u" = u := by simp [ht2, ht1, ht0, hI.gu]
      have ht2cap : t2.cap = st.cap := by simp [ht2, ht1, ht0, htcap]
      have hkev : evalW t2 (eq (load "gKeep" (var "g_u")) (lit 0)) =
          some (if I.keep u = 0 then 1 else 0) := by
        rw [evalW_eq_of (x := I.keep u) (y := 0)
          (evalW_load_of (j := u) (by simp [ht2u]) (by simp [ht2, ht1, ht0]; omega) |>.trans
            (by simp [ht2, ht1, ht0, hkeepv]))
          (evalW_lit_of (by omega)) (by omega)]
      have hU2 : Unchanged st t2 passAWA [] passAWR [] := by
        simpa [ht2, ht1, ht0, passAWA] using hI.U
      have hE2 : AEnv I t2 := hE.of_unchanged (by simp [ht2, ht1, ht0, passAWA])
      have hoff2 : ∀ i < u + 1, t2.wa "g_off" i = I.off i := by
        intro i hi; simp [ht2, ht1, ht0]
        by_cases hiu : i = u
        · simp [hiu]
        · simp [hiu]; exact hI.offA i (by omega)
      have hsl2 : ∀ i < u + 1, t2.wa "g_sl" i = I.sl i := by
        intro i hi; simp [ht2, ht1, ht0]
        by_cases hiu : i = u
        · simp [hiu]
        · simp [hiu]; exact hI.slA i (by omega)
      refine runs_seq ?_
      by_cases hk : I.keep u = 0
      · -- not kept: skip
        refine runs_ite_true (x := 1) (by rw [hkev, if_pos hk]) one_ne_zero (runs_skip ?_)
        set t3 := (t2.charge 1).charge 1 with ht3
        refine runs_wset (a := u + 1) (evalW_add_of (by simp [ht3, ht2u])
          (evalW_lit_of (by simp [ht3, ht2cap]; omega)) (by simp [ht3, ht2cap]; omega)) ?_
        refine ⟨hE2.of_unchanged (by simp [ht3, passAWR]), by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [ht3, ht2, ht1, ht0, hI.gx, I.off_succ, I.cc_zero hk]
        · simp [ht3, ht2, ht1, ht0, hI.gy, I.sl_succ, I.ns_zero hk]
        · intro i hi; simpa [ht3] using hoff2 i hi
        · intro i hi; simpa [ht3] using hsl2 i hi
        · intro i hi
          have hd := hI.degA i hi
          have e : ((t3.setW "g_u" (u + 1)).charge 1).wa "g_deg" i = t.wa "g_deg" i := by
            simp [ht3, ht2, ht1, ht0]
          rw [e, hd]
          by_cases hiu : i = u
          · subst hiu; simp [I.deg_zero hk]
          · by_cases h : i < u
            · simp [h, show i < u + 1 by omega]
            · simp [h, show ¬ i < u + 1 by omega]
        · funext e; have := congrFun hI.keptA e
          simp [ht3, ht2, ht1, ht0, I.keptArr_succ_skip hk]; exact this
        · intro v hv; have := hI.markA v hv; simp [ht3, ht2, ht1, ht0]; omega
        · simp [ht3, ht2, ht1, ht0, hI.mL]
        · simp [ht3, ht2, ht1, ht0, hI.bL]
        · simp [ht3, ht2, ht1, ht0, hI.dL]
        · simp [ht3, ht2, ht1, ht0, hI.oL]
        · simp [ht3, ht2, ht1, ht0, hI.sL]
        · simp [ht3, ht2, ht1, ht0, hI.kL]
        · simpa [ht3, passAWR] using hU2
        · have := hI.c
          simp [ht3, ht2, ht1, ht0, pfx_succ]; omega
      · -- kept: passAKept
        refine runs_ite_false (by rw [hkev, if_neg hk]) ?_
        have hmark2 : ∀ v < I.n, (t2.charge 1).wa "g_mark" v ≤ u := by
          intro v hv; have := hI.markA v hv; simpa [ht2, ht1, ht0] using this
        refine (passAKept_runs I (t2.charge 1) u (hE2.of_unchanged (by simp [passAWA]))
          (by simp [ht2u]) hun hk hδ hmark2 (by simp [ht2, ht1, ht0, hI.mL])
          (by simp [ht2, ht1, ht0, hI.bL]) (by simp [ht2, ht1, ht0, hI.kL])
          (by simp [ht2, ht1, ht0, hI.dL]; omega)
          (by simp [ht2, ht1, ht0]; rw [htcap] at hxb; simpa [htcap] using hxb)
          (by simp [ht2, ht1, ht0]; rw [htcap] at hyb; simpa [htcap] using hyb)
          (by simp [ht2cap]; omega)).mono ?_
        intro r hK
        have hrcap : r.cap = st.cap := by rw [hK.U.cap]; simp [ht2cap]
        have hru : r.w "g_u" = u := by rw [hK.U.wreg _ (by simp [kWR])]; simp [ht2u]
        refine runs_wset (a := u + 1) (evalW_add_of (by rw [evalW_var, hru])
          (evalW_lit_of (by rw [hrcap]; omega)) (by rw [hrcap]; omega)) ?_
        have hUr : Unchanged (t2.charge 1) r passAWA [] passAWR [] :=
          hK.U.mono (by simp [kWA, passAWA]) (by simp) (by simp [kWR, passAWR]) (by simp)
        refine ⟨(hE2.of_unchanged (by simp [passAWA])).of_unchanged hUr |>.of_unchanged
            (by simp [passAWR]), by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hK.gx, ht2, ht1, ht0, hI.gx, I.off_succ]
        · simp [hK.gy, ht2, ht1, ht0, hI.gy, I.sl_succ]
        · intro i hi
          have h1 : r.wa "g_off" = (t2.charge 1).wa "g_off" := (hK.U.warr _ (by simp [kWA])).1
          simp [h1]; simpa using hoff2 i hi
        · intro i hi
          have h1 : r.wa "g_sl" = (t2.charge 1).wa "g_sl" := (hK.U.warr _ (by simp [kWA])).1
          simp [h1]; simpa using hsl2 i hi
        · intro i hi
          have hd := hK.deg
          simp only [State.charge_wa, State.setW_wa, hd]
          have hdi := hI.degA i hi
          by_cases hiu : i = u
          · subst hiu; simp
          · rw [Function.update_of_ne hiu]
            have e : t2.wa "g_deg" i = t.wa "g_deg" i := by simp [ht2, ht1, ht0]
            rw [e, hdi]
            by_cases h : i < u
            · simp [h, show i < u + 1 by omega]
            · simp [h, show ¬ i < u + 1 by omega]
        · simp only [State.charge_wa, State.setW_wa, hK.kept]
          rw [I.keptArr_succ_kept hk]
          funext e; have := congrFun hI.keptA e
          simp [ht2, ht1, ht0]; rw [this]
        · intro v hv; simpa using hK.mark v hv
        · simpa using hK.mL
        · simpa using hK.bL
        · simp [hK.dL, ht2, ht1, ht0, hI.dL]
        · have h1 := (hK.U.warr "g_off" (by simp [kWA])).2
          simp [h1, ht2, ht1, ht0, hI.oL]
        · have h1 := (hK.U.warr "g_sl" (by simp [kWA])).2
          simp [h1, ht2, ht1, ht0, hI.sL]
        · simp [hK.kL, ht2, ht1, ht0, hI.kL]
        · have h := hU2.trans ((Unchanged.charge _ _ _ _ _ _).trans hUr)
          simpa [passAWR] using h
        · have h1 := hK.c
          have h2 := hI.c
          have e1 : (t2.charge 1).cost = t.cost + 4 := by simp [ht2, ht1, ht0]
          have h3 : (I.grp u).length = cntk I.src I.m u := I.grp_length u
          simp only [State.charge_cost, State.setW_cost]
          rw [pfx_succ]
          omega
  · intro t hI
    have htcap : t.cap = st.cap := hI.U.cap
    refine ⟨?_, t, hI, rfl⟩
    rw [evalW_lt_of (x := I.n) (y := I.n) (by rw [evalW_var, hI.gu]) (by rw [evalW_var, hI.E.n])
      (by omega)]
    simp

theorem AEnv.of_frame {I : L6In} {t t' : State ℝ≥0} {wa va wr vr : List String} (h : AEnv I t)
    (hU : Unchanged t t' wa va wr vr)
    (ha : "src" ∉ wa ∧ "dst" ∉ wa ∧ "gKeep" ∉ wa ∧ "g_cnt" ∉ wa ∧ "g_ord" ∉ wa)
    (hv : "w" ∉ va) (hr : "n" ∉ wr ∧ "m" ∉ wr ∧ "gD" ∉ wr) : AEnv I t' where
  n := by rw [hU.wreg _ hr.1]; exact h.n
  m := by rw [hU.wreg _ hr.2.1]; exact h.m
  gD := by rw [hU.wreg _ hr.2.2]; exact h.gD
  src e he := by rw [(hU.warr _ ha.1).1]; exact h.src e he
  srcL := by rw [(hU.warr _ ha.1).2]; exact h.srcL
  dst e he := by rw [(hU.warr _ ha.2.1).1]; exact h.dst e he
  dstL := by rw [(hU.warr _ ha.2.1).2]; exact h.dstL
  w e he := by rw [(hU.varr _ hv).1]; exact h.w e he
  wL := by rw [(hU.varr _ hv).2]; exact h.wL
  hsrc := h.hsrc
  hdst := h.hdst
  keep := h.keep.of_unchanged hU ha.2.2.1
  cnt := h.cnt.of_unchanged hU ha.2.2.2.1
  ord u hu i hi := by rw [(hU.warr _ ha.2.2.2.2).1]; exact h.ord u hu i hi
  ordL := by rw [(hU.warr _ ha.2.2.2.2).2]; exact h.ordL

/-- Result of pass A. -/
structure APost (I : L6In) (st r : State ℝ≥0) : Prop where
  E : AEnv I r
  off : WSeg r "g_off" 0 (I.n + 1) I.off
  sl : WSeg r "g_sl" 0 (I.n + 1) I.sl
  deg : WSeg r "g_deg" 0 I.n I.deg
  kept : r.wa "g_kept" = I.keptArr I.n
  kL : r.wlen "g_kept" = I.m
  gN : r.w "gN" = I.off I.n
  gM : r.w "gM" = I.sl I.n
  U : Unchanged st r passAWA [] (passAWR ++ ["gN", "gM"]) []
  c : r.cost ≤ st.cost + 30 * I.n + 18 * I.m + 20

theorem passAProg_runs (I : L6In) (st : State ℝ≥0) (hE : AEnv I st) (hδ : 3 ≤ I.δ)
    (hcap : 4 * (I.n + I.m) + 8 < st.cap) :
    Runs realOps passAProg st (APost I st) := by
  have hpm : pfx I.src I.m I.n = I.m := pfx_total _ _ _ hE.hsrc
  apply wp_sound
  simp only [passAProg, wp]
  simp [hE.n, hE.m, fit, show I.n + 1 < st.cap by omega, show 1 < st.cap by omega,
    show 0 < st.cap by omega]
  set s9 := (((((((((((((((((st.allocW "g_mark" I.n).charge (I.n + 1)).allocW "g_best" I.n).charge
    (I.n + 1)).allocW "g_deg" I.n).charge (I.n + 1)).allocW "g_off" (I.n + 1)).charge
    (I.n + 1 + 1)).allocW "g_sl" (I.n + 1)).charge (I.n + 1 + 1)).allocW "g_kept" I.m).charge
    (I.m + 1)).setW "g_x" 0).charge 1).setW "g_y" 0).charge 1).setW "g_u" 0).charge 1 with hs9
  have hU9 : Unchanged st s9 passAWA [] passAWR [] := by simp [hs9, passAWA, passAWR]
  have hE9 : AEnv I s9 := hE.of_unchanged hU9
  have h0 : AInv I s9 0 s9 := by
    refine ⟨hE9, by simp [hs9], by simp [hs9, L6In.off], by simp [hs9, L6In.sl],
      fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i _ => by simp [hs9], by funext e; simp [hs9, I.keptArr_zero],
      fun v _ => by simp [hs9], by simp [hs9], by simp [hs9], by simp [hs9], by simp [hs9],
      by simp [hs9], by simp [hs9], by simp, by simp [pfx]⟩
  refine (passALoop_runs I s9 hδ (by simp [hs9]; omega) h0).mono ?_
  rintro _ ⟨t, hI, rfl⟩
  have htcap : t.cap = st.cap := by rw [hI.U.cap]; simp [hs9]
  have hoffn : I.off I.n ≤ I.n + I.m := by have := I.off_le hδ I.n; omega
  have hsln : I.sl I.n ≤ 2 * I.m := by have := I.sl_le hδ I.n; omega
  simp [wp, hI.gx, hI.gy, hI.E.n, hI.oL, hI.sL, fit, htcap, show I.off I.n < st.cap by omega,
    show I.sl I.n < st.cap by omega]
  have hUt : Unchanged st t passAWA [] passAWR [] := hU9.trans hI.U
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hI.E.of_frame (wa := ["g_off", "g_sl"]) (va := []) (wr := ["gN", "gM"]) (vr := [])
      (by simp) (by simp) (by simp) (by simp)
  · refine ⟨by simp [hI.oL], fun i hi => ?_⟩
    simp
    by_cases hin : i = I.n
    · simp [hin]
    · simp [hin]; exact hI.offA i (by omega)
  · refine ⟨by simp [hI.sL], fun i hi => ?_⟩
    simp
    by_cases hin : i = I.n
    · simp [hin]
    · simp [hin]; exact hI.slA i (by omega)
  · refine ⟨by simp [hI.dL], fun i hi => ?_⟩
    have := hI.degA i hi; simp [hi] at this; simpa using this
  · funext e; have := congrFun hI.keptA e; simpa using this
  · simpa using hI.kL
  · simp
  · simp
  · have := hUt.mono (List.Subset.refl _) (List.Subset.refl _)
      (show passAWR ⊆ passAWR ++ ["gN", "gM"] by simp) (List.Subset.refl _)
    simpa [passAWA, passAWR] using this
  · have h1 := hI.c
    have e9 : s9.cost ≤ st.cost + 5 * I.n + I.m + 11 := by simp [hs9]; omega
    rw [hpm] at h1
    simp; omega

end Frontier.CHD.L6
