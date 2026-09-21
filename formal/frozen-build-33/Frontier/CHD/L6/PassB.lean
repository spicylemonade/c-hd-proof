import Frontier.CHD.L6.PassA

/-!
# L6 pass B (agent-10, scratch): CSR layout, chain edges, live lists
-/

open scoped NNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt Finset

namespace L6In

variable (I : L6In)

/-- The kept list of `u` (in group order). -/
noncomputable def KL (u : ℕ) : List ℕ := (I.grp u).filter (fun e => decide (I.kept u e))

/-- Length of the slot range of the `q`-th chunk of `u`. -/
noncomputable def lenF (u q : ℕ) : ℕ := if q + 1 < I.cc u then I.δ else I.deg u - q * (I.δ - 1)

/-- Initial live-list head of the `q`-th chunk of `u` (`M` = end marker). -/
noncomputable def hdF (u q : ℕ) : ℕ := if I.lenF u q = 0 then I.sl I.n else I.sl u + q * I.δ

theorem KL_length {u : ℕ} (hk : I.keep u ≠ 0) : (I.KL u).length = I.deg u := by
  simp [KL, deg, hk]

variable {I}

theorem cc_pos {u : ℕ} (hk : I.keep u ≠ 0) : 1 ≤ I.cc u := by simp [cc, hk]

theorem cc_eq {u : ℕ} (hk : I.keep u ≠ 0) :
    I.cc u = max 1 ((I.deg u + (I.δ - 2)) / (I.δ - 1)) := by simp [cc, hk]

/-- ceiling property: `d ≤ c (δ-1)` -/
theorem deg_le_cc {u : ℕ} (hk : I.keep u ≠ 0) (hδ : 3 ≤ I.δ) : I.deg u ≤ I.cc u * (I.δ - 1) := by
  rw [cc_eq hk]
  have h1 : 0 < I.δ - 1 := by omega
  have h2 := Nat.div_add_mod (I.deg u + (I.δ - 2)) (I.δ - 1)
  have h3 := Nat.mod_lt (I.deg u + (I.δ - 2)) h1
  have h4 : I.deg u ≤ (I.deg u + (I.δ - 2)) / (I.δ - 1) * (I.δ - 1) := by
    have : (I.δ - 1) * ((I.deg u + (I.δ - 2)) / (I.δ - 1)) =
        (I.deg u + (I.δ - 2)) / (I.δ - 1) * (I.δ - 1) := by ring
    omega
  calc I.deg u ≤ (I.deg u + (I.δ - 2)) / (I.δ - 1) * (I.δ - 1) := h4
    _ ≤ max 1 ((I.deg u + (I.δ - 2)) / (I.δ - 1)) * (I.δ - 1) :=
        Nat.mul_le_mul_right _ (le_max_right _ _)

/-- `(c - 1)(δ - 1) ≤ d` (strict when `d > 0`) -/
theorem cc_pred_le {u : ℕ} (hk : I.keep u ≠ 0) (hδ : 3 ≤ I.δ) :
    (I.cc u - 1) * (I.δ - 1) ≤ I.deg u := by
  rw [cc_eq hk]
  have h1 : 0 < I.δ - 1 := by omega
  by_cases h0 : (I.deg u + (I.δ - 2)) / (I.δ - 1) = 0
  · rw [h0]; simp
  · rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr h0)]
    have h2 : (I.deg u + (I.δ - 2)) / (I.δ - 1) * (I.δ - 1) ≤ I.deg u + (I.δ - 2) :=
      Nat.div_mul_le_self _ _
    have h3 : ((I.deg u + (I.δ - 2)) / (I.δ - 1) - 1) * (I.δ - 1) =
        (I.deg u + (I.δ - 2)) / (I.δ - 1) * (I.δ - 1) - (I.δ - 1) := by
      rw [Nat.sub_mul, one_mul]
    omega

theorem lenF_last {u q : ℕ} (hq : ¬ q + 1 < I.cc u) : I.lenF u q = I.deg u - q * (I.δ - 1) := by
  simp [lenF, hq]

theorem lenF_mid {u q : ℕ} (hq : q + 1 < I.cc u) : I.lenF u q = I.δ := by simp [lenF, hq]

theorem lenF_le {u q : ℕ} (hk : I.keep u ≠ 0) (hδ : 3 ≤ I.δ) (hq : q < I.cc u) :
    I.lenF u q ≤ I.δ := by
  unfold lenF; split_ifs with h
  · exact le_rfl
  · have := deg_le_cc hk hδ
    have hq' : q = I.cc u - 1 := by omega
    subst hq'
    have h2 : I.cc u * (I.δ - 1) = (I.cc u - 1) * (I.δ - 1) + (I.δ - 1) := by
      have : I.cc u = (I.cc u - 1) + 1 := by have := cc_pos hk; omega
      conv_lhs => rw [this]
      ring
    omega

/-- The `q`-th range lies inside `u`'s slot block. -/
theorem range_le {u q : ℕ} (hk : I.keep u ≠ 0) (hδ : 3 ≤ I.δ) (hq : q < I.cc u) :
    q * I.δ + I.lenF u q ≤ I.ns u := by
  have hc := cc_pos hk
  have hp := cc_pred_le hk hδ
  have hns : I.ns u = I.deg u + I.cc u - 1 := by simp [ns, hk]
  by_cases hmid : q + 1 < I.cc u
  · rw [lenF_mid hmid, hns]
    have h1 : (q + 1) * I.δ ≤ (I.cc u - 1) * I.δ := Nat.mul_le_mul_right _ (by omega)
    have h2 : (I.cc u - 1) * I.δ = (I.cc u - 1) * (I.δ - 1) + (I.cc u - 1) := by
      have : I.δ = (I.δ - 1) + 1 := by omega
      conv_lhs => rw [this]
      ring
    have h3 : (q + 1) * I.δ = q * I.δ + I.δ := by ring
    omega
  · rw [lenF_last hmid, hns]
    have hq' : q = I.cc u - 1 := by omega
    subst hq'
    have h2 : (I.cc u - 1) * I.δ = (I.cc u - 1) * (I.δ - 1) + (I.cc u - 1) := by
      have : I.δ = (I.δ - 1) + 1 := by omega
      conv_lhs => rw [this]
      ring
    omega

/-- The ranges of the chunks of `u` add up to its slot count. -/
theorem lsum_eq {u : ℕ} (hk : I.keep u ≠ 0) (hδ : 3 ≤ I.δ) :
    ∑ q ∈ range (I.cc u), I.lenF u q = I.ns u := by
  have hc := cc_pos hk
  have hp := cc_pred_le hk hδ
  have hns : I.ns u = I.deg u + I.cc u - 1 := by simp [ns, hk]
  obtain ⟨c, hcdef⟩ : ∃ c, I.cc u = c + 1 := ⟨I.cc u - 1, by omega⟩
  rw [hcdef, sum_range_succ]
  have hmid : ∀ q ∈ range c, I.lenF u q = I.δ := fun q hq => lenF_mid (by simp at hq; omega)
  rw [sum_congr rfl hmid, sum_const, card_range, smul_eq_mul, lenF_last (by omega), hns, hcdef]
  rw [hcdef] at hp
  simp only [Nat.add_sub_cancel] at hp
  have h2 : c * I.δ = c * (I.δ - 1) + c := by
    have : I.δ = (I.δ - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  omega

end L6In

/-! ## The slot loop -/

def slotWA : List String := ["gSrc", "gNxt"]
def slotWR : List String := ["g_k"]

structure SInv (st : State ℝ≥0) (P R X : ℕ) (k : ℕ) (t : State ℝ≥0) : Prop where
  gk : t.w "g_k" = k
  src : t.wa "gSrc" = fun p => if P ≤ p ∧ p < P + k then X else st.wa "gSrc" p
  nxt : t.wa "gNxt" = fun p => if P ≤ p ∧ p < P + k then p + 1 else st.wa "gNxt" p
  sL : t.wlen "gSrc" = st.wlen "gSrc"
  nL : t.wlen "gNxt" = st.wlen "gNxt"
  U : Unchanged st t slotWA [] slotWR []
  c : t.cost = st.cost + 4 * k

theorem slotLoop_runs (st : State ℝ≥0) (P R X : ℕ) (hk : st.w "g_k" = 0) (hp : st.w "g_p" = P)
    (hr : st.w "g_r" = R) (hx : st.w "g_x" = X) (hsL : P + R ≤ st.wlen "gSrc")
    (hnL : P + R ≤ st.wlen "gNxt") (hcap : P + R + 1 < st.cap) :
    Runs realOps slotLoop st (fun r => ∃ t, SInv st P R X R t ∧ r = t.charge 1) := by
  refine runs_while (fun k t => SInv st P R X k t) R _ ?_ ?_ st
    ⟨hk, by funext p; simp, by funext p; simp, rfl, rfl, by simp, by simp⟩
  · intro k hkR t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htp : t.w "g_p" = P := by rw [hI.U.wreg _ (by simp [slotWR])]; exact hp
    have htr : t.w "g_r" = R := by rw [hI.U.wreg _ (by simp [slotWR])]; exact hr
    have htx : t.w "g_x" = X := by rw [hI.U.wreg _ (by simp [slotWR])]; exact hx
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := k) (y := R) (by rw [evalW_var, hI.gk]) (by rw [evalW_var, htr])
        (by omega)]
      simp [hkR]
    · apply wp_sound
      simp [slotBody, inc, wp, hI.gk, htp, htx, fit, htcap, hI.sL, hI.nL,
        show 1 < st.cap by omega, show P + k < st.cap by omega, show P + k + 1 < st.cap by omega,
        show k + 1 < st.cap by omega, show P + k < st.wlen "gSrc" by omega,
        show P + k < st.wlen "gNxt" by omega]
      refine ⟨by simp, ?_, ?_, by simp [hI.sL], by simp [hI.nL], by simpa [slotWA, slotWR] using hI.U,
        by simp [hI.c]; ring⟩
      · funext p; simp [hI.src]
        by_cases hpk : p = P + k
        · simp [hpk]
        · simp [hpk]
          by_cases h : P ≤ p ∧ p < P + k
          · simp [h, show P ≤ p ∧ p < P + (k + 1) by omega]
          · simp [h]; intro h1; omega
      · funext p; simp [hI.nxt]
        by_cases hpk : p = P + k
        · simp [hpk]
        · simp [hpk]
          by_cases h : P ≤ p ∧ p < P + k
          · simp [h, show P ≤ p ∧ p < P + (k + 1) by omega]
          · simp [h]; intro h1; omega
  · intro t hI
    have htcap : t.cap = st.cap := hI.U.cap
    have htr : t.w "g_r" = R := by rw [hI.U.wreg _ (by simp [slotWR])]; exact hr
    refine ⟨?_, t, hI, rfl⟩
    rw [evalW_lt_of (x := R) (y := R) (by rw [evalW_var, hI.gk]) (by rw [evalW_var, htr])
      (by omega)]
    simp

/-! ## Read-only environment of pass B -/

structure BEnv (I : L6In) (t : State ℝ≥0) : Prop where
  A : AEnv I t
  off : WSeg t "g_off" 0 (I.n + 1) I.off
  sl : WSeg t "g_sl" 0 (I.n + 1) I.sl
  deg : WSeg t "g_deg" 0 I.n I.deg
  kept : t.wa "g_kept" = I.keptArr I.n
  kL : t.wlen "g_kept" = I.m
  gN : t.w "gN" = I.off I.n
  gM : t.w "gM" = I.sl I.n

theorem BEnv.of_frame {I : L6In} {t t' : State ℝ≥0} {wa va wr vr : List String} (h : BEnv I t)
    (hU : Unchanged t t' wa va wr vr)
    (ha : ∀ a ∈ ["src", "dst", "gKeep", "g_cnt", "g_ord", "g_off", "g_sl", "g_deg", "g_kept"],
      a ∉ wa)
    (hv : "w" ∉ va) (hr : ∀ x ∈ ["n", "m", "gD", "gN", "gM"], x ∉ wr) : BEnv I t' where
  A := h.A.of_frame hU ⟨ha _ (by simp), ha _ (by simp), ha _ (by simp), ha _ (by simp),
    ha _ (by simp)⟩ hv ⟨hr _ (by simp), hr _ (by simp), hr _ (by simp)⟩
  off := h.off.of_unchanged hU (ha _ (by simp))
  sl := h.sl.of_unchanged hU (ha _ (by simp))
  deg := h.deg.of_unchanged hU (ha _ (by simp))
  kept := by rw [(hU.warr _ (ha _ (by simp))).1]; exact h.kept
  kL := by rw [(hU.warr _ (ha _ (by simp))).2]; exact h.kL
  gN := by rw [hU.wreg _ (hr _ (by simp))]; exact h.gN
  gM := by rw [hU.wreg _ (hr _ (by simp))]; exact h.gM

/-! ## The chunk loop -/

def vertWA : List String := ["gOwn", "gSt", "gHd", "gSrc", "gNxt", "gHead"]
def vertWR : List String := ["g_x", "g_q", "g_p", "g_r", "g_k"]

/-- Invariant of the chunk loop of kept `u` after `q` chunks. -/
structure VInv (I : L6In) (u : ℕ) (t0 : State ℝ≥0) (q : ℕ) (t : State ℝ≥0) : Prop where
  gx : t.w "g_x" = I.off u + q
  own : t.wa "gOwn" = fun y => if I.off u ≤ y ∧ y < I.off u + q then u else t0.wa "gOwn" y
  st : t.wa "gSt" = fun y =>
    if I.off u ≤ y ∧ y < I.off u + q then I.sl u + (y - I.off u) * I.δ else t0.wa "gSt" y
  hd : t.wa "gHd" = fun y =>
    if I.off u ≤ y ∧ y < I.off u + q then I.hdF u (y - I.off u) else t0.wa "gHd" y
  src : ∀ q' < q, ∀ o < I.lenF u q', t.wa "gSrc" (I.sl u + q' * I.δ + o) = I.off u + q'
  nxt : ∀ q' < q, ∀ o < I.lenF u q', t.wa "gNxt" (I.sl u + q' * I.δ + o) =
    if o + 1 = I.lenF u q' then I.sl I.n else I.sl u + q' * I.δ + o + 1
  chain : ∀ q' < q, q' + 1 < I.cc u →
    t.wa "gHead" (I.sl u + q' * I.δ + (I.δ - 1)) = I.off u + q' + 1 ∧
    t.va "gW" (I.sl u + q' * I.δ + (I.δ - 1)) = 0
  frS : ∀ p < I.sl u, t.wa "gSrc" p = t0.wa "gSrc" p ∧ t.wa "gNxt" p = t0.wa "gNxt" p ∧
    t.wa "gHead" p = t0.wa "gHead" p ∧ t.va "gW" p = t0.va "gW" p
  lens : t.wlen "gOwn" = t0.wlen "gOwn" ∧ t.wlen "gSt" = t0.wlen "gSt" ∧
    t.wlen "gHd" = t0.wlen "gHd" ∧ t.wlen "gSrc" = t0.wlen "gSrc" ∧
    t.wlen "gNxt" = t0.wlen "gNxt" ∧ t.wlen "gHead" = t0.wlen "gHead" ∧
    t.vlen "gW" = t0.vlen "gW"
  U : Unchanged t0 t vertWA ["gW"] vertWR []
  c : t.cost ≤ t0.cost + 4 * (∑ q' ∈ range q, I.lenF u q') + 20 * q

theorem off_mono (I : L6In) {a b : ℕ} (h : a ≤ b) : I.off a ≤ I.off b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [I.off_succ]; omega

theorem sl_mono (I : L6In) {a b : ℕ} (h : a ≤ b) : I.sl a ≤ I.sl b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [I.sl_succ]; omega

theorem vertLoop_runs (I : L6In) (t0 : State ℝ≥0) (u : ℕ) (hB : BEnv I t0) (hu : t0.w "g_u" = u)
    (hun : u < I.n) (hk : I.keep u ≠ 0) (hδ : 3 ≤ I.δ) (hx : t0.w "g_x" = I.off u)
    (hlOwn : I.off I.n ≤ t0.wlen "gOwn") (hlSt : I.off I.n ≤ t0.wlen "gSt")
    (hlHd : I.off I.n ≤ t0.wlen "gHd") (hlSrc : I.sl I.n ≤ t0.wlen "gSrc")
    (hlNxt : I.sl I.n ≤ t0.wlen "gNxt") (hlHead : I.sl I.n ≤ t0.wlen "gHead")
    (hlW : I.sl I.n ≤ t0.vlen "gW")
    (hoffn : I.off I.n ≤ I.n + I.m) (hsln : I.sl I.n ≤ 2 * I.m) (hδm : I.δ ≤ 2 * I.m + I.n + 3)
    (hcap : 8 * (I.n + I.m) + 16 < t0.cap) :
    Runs realOps vertLoop t0 (fun r => ∃ t, VInv I u t0 (I.cc u) t ∧ r = t.charge 1) := by
  have hoffu1 : I.off (u + 1) = I.off u + I.cc u := I.off_succ u
  have hslu1 : I.sl (u + 1) = I.sl u + I.ns u := I.sl_succ u
  have hoffle : I.off (u + 1) ≤ I.off I.n := off_mono I (by omega)
  have hslle : I.sl (u + 1) ≤ I.sl I.n := sl_mono I (by omega)
  have hoffv : t0.wa "g_off" u = I.off u := by have := hB.off.2 u (by omega); simpa using this
  have hoffv1 : t0.wa "g_off" (u + 1) = I.off u + I.cc u := by
    have := hB.off.2 (u + 1) (by omega); simp at this; rw [this, hoffu1]
  have hslv : t0.wa "g_sl" u = I.sl u := by have := hB.sl.2 u (by omega); simpa using this
  have hdegv : t0.wa "g_deg" u = I.deg u := by have := hB.deg.2 u hun; simpa using this
  have hoffL : u + 1 < t0.wlen "g_off" := by have := hB.off.1; omega
  have hslL : u < t0.wlen "g_sl" := by have := hB.sl.1; omega
  have hdegL : u < t0.wlen "g_deg" := by have := hB.deg.1; omega
  refine runs_while (fun q t => VInv I u t0 q t) (I.cc u) _ ?_ ?_ t0
    ⟨by simp [hx], by funext y; simp, by funext y; simp,
     by funext y; simp, fun q' hq' => absurd hq' (Nat.not_lt_zero _),
     fun q' hq' => absurd hq' (Nat.not_lt_zero _), fun q' hq' => absurd hq' (Nat.not_lt_zero _),
     fun p _ => ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp, by simp⟩
  · intro q hq t hI
    have hU := hI.U
    have htcap : t.cap = t0.cap := hU.cap
    have hwr : ∀ x, x ∉ vertWR → t.w x = t0.w x := hU.wreg
    have hwa : ∀ a, a ∉ vertWA → t.wa a = t0.wa a ∧ t.wlen a = t0.wlen a := hU.warr
    have htu : t.w "g_u" = u := by rw [hwr _ (by simp [vertWR])]; exact hu
    have htD : t.w "gD" = I.δ := by rw [hwr _ (by simp [vertWR])]; exact hB.A.gD
    have htM : t.w "gM" = I.sl I.n := by rw [hwr _ (by simp [vertWR])]; exact hB.gM
    have htoff : t.wa "g_off" = t0.wa "g_off" := (hwa _ (by simp [vertWA])).1
    have htoffL : t.wlen "g_off" = t0.wlen "g_off" := (hwa _ (by simp [vertWA])).2
    have htsl : t.wa "g_sl" = t0.wa "g_sl" := (hwa _ (by simp [vertWA])).1
    have htslL : t.wlen "g_sl" = t0.wlen "g_sl" := (hwa _ (by simp [vertWA])).2
    have htdeg : t.wa "g_deg" = t0.wa "g_deg" := (hwa _ (by simp [vertWA])).1
    have htdegL : t.wlen "g_deg" = t0.wlen "g_deg" := (hwa _ (by simp [vertWA])).2
    obtain ⟨lOwn, lSt, lHd, lSrc, lNxt, lHead, lW⟩ := hI.lens
    set x := I.off u + q with hxdef
    set P := I.sl u + q * I.δ with hPdef
    set R := I.lenF u q with hRdef
    have hRle : q * I.δ + R ≤ I.ns u := L6In.range_le hk hδ hq
    have hRδ : R ≤ I.δ := L6In.lenF_le hk hδ hq
    have hxN : x < I.off I.n := by omega
    have hPR : P + R ≤ I.sl I.n := by omega
    have hqδ : q * I.δ ≤ 2 * I.m := by omega
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := x) (y := I.off u + I.cc u) (by rw [evalW_var, hI.gx])
        (by rw [evalW_load_of (j := u + 1) (evalW_add_of (by rw [evalW_var, htu])
          (evalW_lit_of (by omega)) (by omega)) (by rw [htoffL]; exact hoffL), htoff, hoffv1])
        (by omega)]
      simp [hxdef, hq]
    · apply wp_sound
      have hcapP : P + I.δ + 1 < t0.cap := by omega
      have hqδ' : q * I.δ < t0.cap := by omega
      have hqδ1 : q * (I.δ - 1) ≤ q * I.δ := Nat.mul_le_mul_left _ (by omega)
      by_cases hmid : q + 1 < I.cc u
      · have hRm : R = I.δ := L6In.lenF_mid hmid
        have hchainL : P + I.δ - 1 < t.wlen "gHead" := by rw [lHead]; omega
        simp [vertBody, wp, hI.gx, htu, htoff, htoffL, hoffv, hoffv1, htsl, htslL, hslv, htD,
          fit, htcap, lOwn, lSt, hxdef, hPdef, hmid, show u < t0.wlen "g_off" by omega, hslL,
          show q * I.δ < t0.cap by omega, show I.sl u + q * I.δ < t0.cap by omega,
          show I.off u + q < t0.wlen "gOwn" by omega, show I.off u + q < t0.wlen "gSt" by omega,
          show I.off u + q + 1 < t0.cap by omega, show 1 < t0.cap by omega,
          show u + 1 < t0.cap by omega, show 0 < t0.cap by omega,
          show I.sl u + q * I.δ + I.δ < t0.cap by omega,
          show I.sl u + q * I.δ + I.δ - 1 < t.wlen "gHead" by omega,
          show I.sl u + q * I.δ + I.δ - 1 < t.vlen "gW" by rw [lW]; omega, hoffL,
          show I.off u + q + 1 < I.off u + I.cc u by omega]
        show Runs realOps slotLoop _ _
        refine (slotLoop_runs _ P R x (by simp) (by simp [hPdef]) (by simp [hRm]) (by simp [hxdef, hI.gx])
          (by simp [lSrc]; omega) (by simp [lNxt]; omega) (by simp [htcap]; omega)).mono ?_
        rintro _ ⟨t', hS, rfl⟩
        have hSU := hS.U
        have ht'cap : t'.cap = t0.cap := by rw [hSU.cap]; simp [htcap]
        have ht'r : t'.w "g_r" = R := by rw [hSU.wreg _ (by simp [slotWR])]; simp [hRm]
        have ht'x : t'.w "g_x" = x := by rw [hSU.wreg _ (by simp [slotWR])]; simp [hI.gx, hxdef]
        have ht'p : t'.w "g_p" = P := by rw [hSU.wreg _ (by simp [slotWR])]; simp [hPdef]
        have ht'M : t'.w "gM" = I.sl I.n := by rw [hSU.wreg _ (by simp [slotWR])]; simp [htM]
        have ht'hdL : t'.wlen "gHd" = t0.wlen "gHd" := by
          rw [(hSU.warr _ (by simp [slotWA])).2]; simp [lHd]
        have ht'nL : t'.wlen "gNxt" = t0.wlen "gNxt" := by rw [hS.nL]; simp [lNxt]
        have hsrc' := hS.src
        have hnxt' := hS.nxt
        simp only [State.charge_wa, State.setW_wa, State.storeW_wa, State.storeV_wa] at hsrc' hnxt'
        have hown' : t'.wa "gOwn" = fun y => if y = x then u else t.wa "gOwn" y := by
          rw [(hSU.warr _ (by simp [slotWA])).1]; funext y; simp [hxdef]
        have hst' : t'.wa "gSt" = fun y => if y = x then P else t.wa "gSt" y := by
          rw [(hSU.warr _ (by simp [slotWA])).1]; funext y; simp [hxdef, hPdef]
        have hhd' : t'.wa "gHd" = t.wa "gHd" := by
          rw [(hSU.warr _ (by simp [slotWA])).1]; funext y; simp
        have hhead' : t'.wa "gHead" = fun p => if p = P + I.δ - 1 then x + 1 else t.wa "gHead" p := by
          rw [(hSU.warr _ (by simp [slotWA])).1]; funext p; simp [hxdef, hPdef]
        have hW' : t'.va "gW" = fun p => if p = P + I.δ - 1 then 0 else t.va "gW" p := by
          rw [(hSU.varr _ (by simp)).1]; funext p; simp [hPdef]
        have hR0 : R ≠ 0 := by omega
        simp [wp, ht'r, hR0, ht'x, ht'p, ht'M, ht'cap, ht'hdL, ht'nL, fit, inc,
          show 0 < t0.cap by omega, show 1 < t0.cap by omega, show P + R < t0.cap by omega,
          show x < t0.wlen "gHd" by omega, show P + R - 1 < t0.wlen "gNxt" by omega,
          show x + 1 < t0.cap by omega]
        have hU' : Unchanged t t' vertWA ["gW"] vertWR [] := Unchanged.trans (by simp [vertWR, vertWA])
          (hSU.mono (by simp [slotWA, vertWA]) (by simp) (by simp [slotWR, vertWR]) (List.Subset.refl _))
        have hlen : ∀ a, a ∉ slotWA → t'.wlen a = t.wlen a := by
          intro a ha; rw [(hSU.warr a ha).2]; simp
        have hc' := hS.c
        simp only [State.charge_cost, State.setW_cost, State.storeW_cost, State.storeV_cost] at hc'
        have hPq : ∀ q' < q, ∀ o < I.lenF u q', I.sl u + q' * I.δ + o < P := by
          intro q' hq' o ho
          have h1 := L6In.lenF_le hk hδ (show q' < I.cc u by omega)
          have h2 : (q' + 1) * I.δ ≤ q * I.δ := Nat.mul_le_mul_right _ (by omega)
          have h3 : (q' + 1) * I.δ = q' * I.δ + I.δ := by ring
          omega
        have hPc : ∀ q' < q, I.sl u + q' * I.δ + (I.δ - 1) < P := by
          intro q' hq'
          have h2 : (q' + 1) * I.δ ≤ q * I.δ := Nat.mul_le_mul_right _ (by omega)
          have h3 : (q' + 1) * I.δ = q' * I.δ + I.δ := by ring
          omega
        refine ⟨by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- own
          funext y; simp [hown', hI.own]
          by_cases hy : y = x
          · simp [hy, hxdef]
          · simp [hy]
            by_cases h1 : I.off u ≤ y ∧ y < I.off u + q
            · simp [h1, show I.off u ≤ y ∧ y < I.off u + (q + 1) by omega]
            · rw [if_neg h1, if_neg (by omega)]
        · -- st
          funext y; simp [hst', hI.st]
          by_cases hy : y = x
          · simp [hy, hxdef, hPdef]
          · simp [hy]
            by_cases h1 : I.off u ≤ y ∧ y < I.off u + q
            · simp [h1, show I.off u ≤ y ∧ y < I.off u + (q + 1) by omega]
            · rw [if_neg h1, if_neg (by omega)]
        · -- hd
          funext y; simp [hhd', hI.hd]
          by_cases hy : y = x
          · simp [hy, hxdef, L6In.hdF, ← hRdef, hR0, hPdef]
          · simp [hy]
            by_cases h1 : I.off u ≤ y ∧ y < I.off u + q
            · simp [h1, show I.off u ≤ y ∧ y < I.off u + (q + 1) by omega]
            · rw [if_neg h1, if_neg (by omega)]
        · -- src
          intro q' hq' o ho
          simp [hsrc']
          rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
          · have := hPq q' hq' o ho
            rw [if_neg (by omega)]; exact hI.src q' hq' o ho
          · rw [if_pos (by rw [← hRdef] at ho; omega)]
        · -- nxt
          intro q' hq' o ho
          simp [hnxt']
          rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
          · have := hPq q' hq' o ho
            rw [if_neg (by omega), if_neg (by omega)]; exact hI.nxt q' hq' o ho
          · rw [← hRdef] at ho ⊢
            by_cases hlast : o + 1 = R
            · rw [if_pos (by omega), if_pos hlast]
            · rw [if_neg (by omega), if_pos (by omega), if_neg hlast]
        · -- chain
          intro q' hq' hq'c
          rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
          · have hne : I.sl u + q' * I.δ + (I.δ - 1) ≠ P + I.δ - 1 := by have := hPc q' hq'; omega
            simp [hhead', hW', hne]; exact hI.chain q' hq' hq'c
          · have heq : I.sl u + q' * I.δ + (I.δ - 1) = P + I.δ - 1 := by omega
            simp [hhead', hW', heq]; omega
        · -- frS
          intro p hp
          obtain ⟨f1, f2, f3, f4⟩ := hI.frS p hp
          have hpP : p < P := by omega
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp [hsrc']; rw [if_neg (by omega)]; exact f1
          · simp [hnxt']; rw [if_neg (by omega), if_neg (by omega)]; exact f2
          · simp [hhead']; rw [if_neg (by omega)]; exact f3
          · simp [hW']; rw [if_neg (by omega)]; exact f4
        · -- lens
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp [hlen "gOwn" (by simp [slotWA]), lOwn]
          · simp [hlen "gSt" (by simp [slotWA]), lSt]
          · simp [hlen "gHd" (by simp [slotWA]), lHd]
          · simp [hS.sL, lSrc]
          · simp [hS.nL, lNxt]
          · simp [hlen "gHead" (by simp [slotWA]), lHead]
          · simp [(hSU.varr "gW" (by simp)).2, lW]
        · -- U
          exact hI.U.trans (hU'.trans (by simp [vertWR, vertWA]))
        · -- cost
          have hc := hI.c
          simp [sum_range_succ]
          rw [← hRdef]
          omega
      · -- last chunk: no chain edge
        have hRl : R = I.deg u - q * (I.δ - 1) := L6In.lenF_last hmid
        have hdegL' : u < t.wlen "g_deg" := by rw [htdegL]; exact hdegL
        simp [vertBody, wp, hI.gx, htu, htoff, htoffL, hoffv, hoffv1, htsl, htslL, hslv, htD,
          fit, htcap, lOwn, lSt, hxdef, hPdef, hmid, show u < t0.wlen "g_off" by omega, hslL,
          show q * I.δ < t0.cap by omega, show I.sl u + q * I.δ < t0.cap by omega,
          show I.off u + q < t0.wlen "gOwn" by omega, show I.off u + q < t0.wlen "gSt" by omega,
          show I.off u + q + 1 < t0.cap by omega, show 1 < t0.cap by omega,
          show u + 1 < t0.cap by omega, show 0 < t0.cap by omega, hoffL,
          show ¬ I.off u + q + 1 < I.off u + I.cc u by omega, htdeg, hdegv, hdegL',
          show q * (I.δ - 1) < t0.cap by omega]
        show Runs realOps slotLoop _ _
        refine (slotLoop_runs _ P R x (by simp) (by simp [hPdef]) (by simp [hRl])
          (by simp [hxdef, hI.gx]) (by simp [lSrc]; omega) (by simp [lNxt]; omega)
          (by simp [htcap]; omega)).mono ?_
        rintro _ ⟨t', hS, rfl⟩
        have hSU := hS.U
        have ht'cap : t'.cap = t0.cap := by rw [hSU.cap]; simp [htcap]
        have ht'r : t'.w "g_r" = R := by rw [hSU.wreg _ (by simp [slotWR])]; simp [hRl]
        have ht'x : t'.w "g_x" = x := by rw [hSU.wreg _ (by simp [slotWR])]; simp [hI.gx, hxdef]
        have ht'p : t'.w "g_p" = P := by rw [hSU.wreg _ (by simp [slotWR])]; simp [hPdef]
        have ht'M : t'.w "gM" = I.sl I.n := by rw [hSU.wreg _ (by simp [slotWR])]; simp [htM]
        have ht'hdL : t'.wlen "gHd" = t0.wlen "gHd" := by
          rw [(hSU.warr _ (by simp [slotWA])).2]; simp [lHd]
        have ht'nL : t'.wlen "gNxt" = t0.wlen "gNxt" := by rw [hS.nL]; simp [lNxt]
        have hsrc' := hS.src
        have hnxt' := hS.nxt
        simp only [State.charge_wa, State.setW_wa, State.storeW_wa, State.storeV_wa] at hsrc' hnxt'
        have hown' : t'.wa "gOwn" = fun y => if y = x then u else t.wa "gOwn" y := by
          rw [(hSU.warr _ (by simp [slotWA])).1]; funext y; simp [hxdef]
        have hst' : t'.wa "gSt" = fun y => if y = x then P else t.wa "gSt" y := by
          rw [(hSU.warr _ (by simp [slotWA])).1]; funext y; simp [hxdef, hPdef]
        have hhd' : t'.wa "gHd" = t.wa "gHd" := by
          rw [(hSU.warr _ (by simp [slotWA])).1]; funext y; simp
        have hhead' : t'.wa "gHead" = t.wa "gHead" := by
          rw [(hSU.warr _ (by simp [slotWA])).1]; funext p; simp
        have hW' : t'.va "gW" = t.va "gW" := by
          rw [(hSU.varr _ (by simp)).1]; funext p; simp
        have hU' : Unchanged t t' vertWA ["gW"] vertWR [] := Unchanged.trans (by simp [vertWR, vertWA])
          (hSU.mono (by simp [slotWA, vertWA]) (by simp) (by simp [slotWR, vertWR]) (List.Subset.refl _))
        have hlen : ∀ a, a ∉ slotWA → t'.wlen a = t.wlen a := by
          intro a ha; rw [(hSU.warr a ha).2]; simp
        have hc' := hS.c
        simp only [State.charge_cost, State.setW_cost, State.storeW_cost, State.storeV_cost] at hc'
        have hPq : ∀ q' < q, ∀ o < I.lenF u q', I.sl u + q' * I.δ + o < P := by
          intro q' hq' o ho
          have h1 := L6In.lenF_le hk hδ (show q' < I.cc u by omega)
          have h2 : (q' + 1) * I.δ ≤ q * I.δ := Nat.mul_le_mul_right _ (by omega)
          have h3 : (q' + 1) * I.δ = q' * I.δ + I.δ := by ring
          omega
        -- common facts for both head cases
        have hsrcF : ∀ q' < q + 1, ∀ o < I.lenF u q', t'.wa "gSrc" (I.sl u + q' * I.δ + o) = I.off u + q' := by
          intro q' hq' o ho
          simp [hsrc']
          rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
          · have := hPq q' hq' o ho
            rw [if_neg (by omega)]; exact hI.src q' hq' o ho
          · rw [if_pos (by rw [← hRdef] at ho; omega)]
        have hchainF : ∀ q' < q + 1, q' + 1 < I.cc u →
            t'.wa "gHead" (I.sl u + q' * I.δ + (I.δ - 1)) = I.off u + q' + 1 ∧
            t'.va "gW" (I.sl u + q' * I.δ + (I.δ - 1)) = 0 := by
          intro q' hq' hq'c
          rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
          · rw [hhead', hW']; exact hI.chain q' hq' hq'c
          · exact absurd hq'c hmid
        have hownF : (fun y => if y = x then u else t.wa "gOwn" y) =
            fun y => if I.off u ≤ y ∧ y < I.off u + (q + 1) then u else t0.wa "gOwn" y := by
          funext y; rw [hI.own]
          by_cases hy : y = x
          · simp [hy, hxdef]
          · simp only [hy, if_false]
            by_cases h1 : I.off u ≤ y ∧ y < I.off u + q
            · rw [if_pos h1, if_pos (by omega)]
            · rw [if_neg h1, if_neg (by omega)]
        have hstF : (fun y => if y = x then P else t.wa "gSt" y) =
            fun y => if I.off u ≤ y ∧ y < I.off u + (q + 1) then I.sl u + (y - I.off u) * I.δ
              else t0.wa "gSt" y := by
          funext y; rw [hI.st]
          by_cases hy : y = x
          · simp [hy, hxdef, hPdef]
          · simp only [hy, if_false]
            by_cases h1 : I.off u ≤ y ∧ y < I.off u + q
            · rw [if_pos h1, if_pos (by omega)]
            · rw [if_neg h1, if_neg (by omega)]
        have hlens : t'.wlen "gOwn" = t0.wlen "gOwn" ∧ t'.wlen "gSt" = t0.wlen "gSt" ∧
            t'.wlen "gHd" = t0.wlen "gHd" ∧ t'.wlen "gSrc" = t0.wlen "gSrc" ∧
            t'.wlen "gNxt" = t0.wlen "gNxt" ∧ t'.wlen "gHead" = t0.wlen "gHead" ∧
            t'.vlen "gW" = t0.vlen "gW" :=
          ⟨by simp [hlen "gOwn" (by simp [slotWA]), lOwn], by simp [hlen "gSt" (by simp [slotWA]), lSt],
           by simp [hlen "gHd" (by simp [slotWA]), lHd], by simp [hS.sL, lSrc], by simp [hS.nL, lNxt],
           by simp [hlen "gHead" (by simp [slotWA]), lHead], by simp [(hSU.varr "gW" (by simp)).2, lW]⟩
        by_cases hR0 : R = 0
        · simp [wp, ht'r, hR0, ht'x, ht'p, ht'M, ht'cap, ht'hdL, ht'nL, fit, inc,
            show 0 < t0.cap by omega, show 1 < t0.cap by omega,
            show x < t0.wlen "gHd" by omega, show x + 1 < t0.cap by omega]
          refine ⟨by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · funext y; simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and]
            rw [hown'] at *; exact congrFun hownF y
          · funext y; simp only [State.charge_wa, State.setW_wa, State.storeW_wa]; rw [hst']
            exact congrFun hstF y
          · funext y; simp [hhd', hI.hd]
            by_cases hy : y = x
            · simp [hy, hxdef, L6In.hdF, ← hRdef, hR0]
            · simp [hy]
              by_cases h1 : I.off u ≤ y ∧ y < I.off u + q
              · simp [h1, show I.off u ≤ y ∧ y < I.off u + (q + 1) by omega]
              · rw [if_neg h1, if_neg (by omega)]
          · intro q' hq' o ho; simp; exact hsrcF q' hq' o ho
          · intro q' hq' o ho
            simp [hnxt']
            rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
            · have := hPq q' hq' o ho
              rw [if_neg (by omega)]; exact hI.nxt q' hq' o ho
            · rw [← hRdef] at ho; omega
          · intro q' hq' hq'c; simpa using hchainF q' hq' hq'c
          · intro p hp
            obtain ⟨f1, f2, f3, f4⟩ := hI.frS p hp
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp [hsrc']; rw [if_neg (by omega)]; exact f1
            · simp [hnxt']; rw [if_neg (by omega)]; exact f2
            · simp [hhead']; exact f3
            · simp [hW']; exact f4
          · simpa using hlens
          · exact hI.U.trans (hU'.trans (by simp [vertWR, vertWA]))
          · have hc := hI.c
            simp [sum_range_succ]
            rw [← hRdef]
            omega
        · simp [wp, ht'r, hR0, ht'x, ht'p, ht'M, ht'cap, ht'hdL, ht'nL, fit, inc,
            show 0 < t0.cap by omega, show 1 < t0.cap by omega, show P + R < t0.cap by omega,
            show x < t0.wlen "gHd" by omega, show P + R - 1 < t0.wlen "gNxt" by omega,
            show x + 1 < t0.cap by omega]
          refine ⟨by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · funext y; simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
            rw [hown']; simp; exact congrFun hownF y
          · funext y; simp only [State.charge_wa, State.setW_wa, State.storeW_wa]; rw [hst']
            simp; exact congrFun hstF y
          · funext y; simp [hhd', hI.hd]
            by_cases hy : y = x
            · simp [hy, hxdef, L6In.hdF, ← hRdef, hR0, hPdef]
            · simp [hy]
              by_cases h1 : I.off u ≤ y ∧ y < I.off u + q
              · simp [h1, show I.off u ≤ y ∧ y < I.off u + (q + 1) by omega]
              · rw [if_neg h1, if_neg (by omega)]
          · intro q' hq' o ho; simp; exact hsrcF q' hq' o ho
          · intro q' hq' o ho
            simp [hnxt']
            rcases Nat.lt_succ_iff_lt_or_eq.mp hq' with hq' | rfl
            · have := hPq q' hq' o ho
              rw [if_neg (by omega), if_neg (by omega)]; exact hI.nxt q' hq' o ho
            · rw [← hRdef] at ho ⊢
              by_cases hlast : o + 1 = R
              · rw [if_pos (by omega), if_pos hlast]
              · rw [if_neg (by omega), if_pos (by omega), if_neg hlast]
          · intro q' hq' hq'c; simpa using hchainF q' hq' hq'c
          · intro p hp
            obtain ⟨f1, f2, f3, f4⟩ := hI.frS p hp
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp [hsrc']; rw [if_neg (by omega)]; exact f1
            · simp [hnxt']; rw [if_neg (by omega), if_neg (by omega)]; exact f2
            · simp [hhead']; exact f3
            · simp [hW']; exact f4
          · simpa using hlens
          · exact hI.U.trans (hU'.trans (by simp [vertWR, vertWA]))
          · have hc := hI.c
            simp [sum_range_succ]
            rw [← hRdef]
            omega
  · intro t hI
    have hU := hI.U
    have htcap : t.cap = t0.cap := hU.cap
    have htu : t.w "g_u" = u := by rw [hU.wreg _ (by simp [vertWR])]; exact hu
    have htoff : t.wa "g_off" = t0.wa "g_off" := (hU.warr _ (by simp [vertWA])).1
    have htoffL : t.wlen "g_off" = t0.wlen "g_off" := (hU.warr _ (by simp [vertWA])).2
    refine ⟨?_, t, hI, rfl⟩
    rw [evalW_lt_of (x := I.off u + I.cc u) (y := I.off u + I.cc u) (by rw [evalW_var, hI.gx])
      (by rw [evalW_load_of (j := u + 1) (evalW_add_of (by rw [evalW_var, htu])
        (evalW_lit_of (by omega)) (by omega)) (by rw [htoffL]; exact hoffL), htoff, hoffv1])
      (by omega)]
    simp

/-! ## The emission loop -/

theorem mul_pred_add (k d : ℕ) (hd : 1 ≤ d) : k * d = k * (d - 1) + k := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp [Nat.mul_succ]

/-- Slot of the `i`-th kept edge of `u`. -/
noncomputable def slotR (I : L6In) (u i : ℕ) : ℕ := I.sl u + (i / (I.δ - 1)) * I.δ + i % (I.δ - 1)

theorem slotR_inj {I : L6In} {u i i' : ℕ} (hδ : 3 ≤ I.δ) (h : slotR I u i = slotR I u i') : i = i' := by
  unfold slotR at h
  have hd : 0 < I.δ := by omega
  have ho : i % (I.δ - 1) < I.δ := lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  have ho' : i' % (I.δ - 1) < I.δ := lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  have h1 : (i / (I.δ - 1)) * I.δ + i % (I.δ - 1) = (i' / (I.δ - 1)) * I.δ + i' % (I.δ - 1) := by omega
  have hq : i / (I.δ - 1) = i' / (I.δ - 1) := by
    have e1 : ((i / (I.δ - 1)) * I.δ + i % (I.δ - 1)) / I.δ = i / (I.δ - 1) := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt ho, zero_add]
    have e2 : ((i' / (I.δ - 1)) * I.δ + i' % (I.δ - 1)) / I.δ = i' / (I.δ - 1) := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt ho', zero_add]
    rw [← e1, ← e2, h1]
  have hr : i % (I.δ - 1) = i' % (I.δ - 1) := by rw [hq] at h1; omega
  rw [← Nat.div_add_mod i (I.δ - 1), ← Nat.div_add_mod i' (I.δ - 1), hq, hr]

/-- A real slot is never a chain slot. -/
theorem slotR_ne_chain {I : L6In} {u i q : ℕ} (hδ : 3 ≤ I.δ) :
    slotR I u i ≠ I.sl u + q * I.δ + (I.δ - 1) := by
  unfold slotR
  intro h
  have hd : 0 < I.δ := by omega
  have ho : i % (I.δ - 1) < I.δ - 1 := Nat.mod_lt _ (by omega)
  have h1 : (i / (I.δ - 1)) * I.δ + i % (I.δ - 1) = q * I.δ + (I.δ - 1) := by omega
  have e1 : ((i / (I.δ - 1)) * I.δ + i % (I.δ - 1)) % I.δ = i % (I.δ - 1) := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have e2 : (q * I.δ + (I.δ - 1)) % I.δ = I.δ - 1 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, e2] at e1
  omega

theorem slotR_ge (I : L6In) (u i : ℕ) : I.sl u ≤ slotR I u i := by unfold slotR; omega

/-- The `i`-th kept edge lies in the block of `u`. -/
theorem slotR_lt {I : L6In} {u i : ℕ} (hk : I.keep u ≠ 0) (hδ : 3 ≤ I.δ) (hi : i < I.deg u) :
    slotR I u i < I.sl u + I.ns u := by
  unfold slotR
  have hns : I.ns u = I.deg u + I.cc u - 1 := by simp [L6In.ns, hk]
  have hp := L6In.cc_pred_le hk hδ
  have hle := L6In.deg_le_cc hk hδ
  have hq : i / (I.δ - 1) < I.cc u := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
  have hdm := Nat.div_add_mod i (I.δ - 1)
  have h2 := mul_pred_add (i / (I.δ - 1)) I.δ (by omega)
  have h3 : (I.δ - 1) * (i / (I.δ - 1)) = (i / (I.δ - 1)) * (I.δ - 1) := by ring
  have h4 : (i / (I.δ - 1)) * (I.δ - 1) ≤ (I.cc u - 1) * (I.δ - 1) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

def emitWR : List String := ["g_j", "g_e", "g_q", "g_p", "g_i"]

/-- Invariant of the emission loop of kept `u` after `j` group positions. -/
structure EInv (I : L6In) (u : ℕ) (t0 : State ℝ≥0) (j : ℕ) (t : State ℝ≥0) : Prop where
  gj : t.w "g_j" = pfx I.src I.m u + j
  gi : t.w "g_i" = ((I.grp u |>.take j).filter (fun e => decide (I.kept u e))).length
  real : ∀ i < ((I.grp u |>.take j).filter (fun e => decide (I.kept u e))).length,
    t.wa "gHead" (slotR I u i) = I.off (I.dst ((I.KL u).getD i 0)) ∧
    t.va "gW" (slotR I u i) = I.wt ((I.KL u).getD i 0)
  fr : ∀ p, (∀ i < ((I.grp u |>.take j).filter (fun e => decide (I.kept u e))).length,
    p ≠ slotR I u i) → t.wa "gHead" p = t0.wa "gHead" p ∧ t.va "gW" p = t0.va "gW" p
  hL : t.wlen "gHead" = t0.wlen "gHead"
  wL : t.vlen "gW" = t0.vlen "gW"
  U : Unchanged t0 t ["gHead"] ["gW"] emitWR []
  c : t.cost ≤ t0.cost + 10 * j

theorem prefix_getD {l₁ l₂ : List ℕ} (h : l₁ <+: l₂) {i : ℕ} (hi : i < l₁.length) :
    l₂.getD i 0 = l₁.getD i 0 := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ 0 i hi

theorem keptArr_grp {I : L6In} {u e : ℕ} (hun : u < I.n) (hk : I.keep u ≠ 0) (he : e ∈ I.grp u) :
    I.keptArr I.n e = if I.kept u e then 1 else 0 := by
  obtain ⟨hem, hs⟩ := I.mem_grp.mp he
  unfold L6In.keptArr L6In.keptE
  by_cases hkp : I.kept u e
  · rw [if_pos ⟨hem, by omega, by rw [hs]; exact hk, by rw [hs]; exact hkp⟩, if_pos hkp]
  · rw [if_neg (by rintro ⟨-, -, -, h⟩; rw [hs] at h; exact hkp h), if_neg hkp]

theorem emitLoop_runs (I : L6In) (t0 : State ℝ≥0) (u : ℕ) (hB : BEnv I t0) (hu : t0.w "g_u" = u)
    (hun : u < I.n) (hk : I.keep u ≠ 0) (hδ : 3 ≤ I.δ) (hi0 : t0.w "g_i" = 0)
    (hj0 : t0.w "g_j" = pfx I.src I.m u)
    (hlHead : I.sl I.n ≤ t0.wlen "gHead") (hlW : I.sl I.n ≤ t0.vlen "gW")
    (hoffn : I.off I.n ≤ I.n + I.m) (hsln : I.sl I.n ≤ 2 * I.m) (hδm : I.δ ≤ 2 * I.m + I.n + 3)
    (hcap : 8 * (I.n + I.m) + 16 < t0.cap) :
    Runs realOps emitLoop t0 (fun r => ∃ t, EInv I u t0 (I.grp u).length t ∧ r = t.charge 1) := by
  set L := I.grp u with hLdef
  have hE := hB.A
  have hslle : I.sl (u + 1) ≤ I.sl I.n := sl_mono I (by omega)
  have hslu1 : I.sl (u + 1) = I.sl u + I.ns u := I.sl_succ u
  have hcntL : u + 1 < t0.wlen "g_cnt" := by have := hE.cnt.1; omega
  have hcnt1 : t0.wa "g_cnt" (u + 1) = pfx I.src I.m u + L.length := by
    have := hE.cnt.2 (u + 1) (by omega); simp at this; rw [this, pfx_succ, hLdef, I.grp_length]
  have hpm : pfx I.src I.m u + L.length ≤ I.m := by
    have h1 : pfx I.src I.m (u + 1) ≤ pfx I.src I.m I.n := pfx_mono _ _ (by omega)
    rw [pfx_total _ _ _ hE.hsrc, pfx_succ, ← I.grp_length] at h1; exact h1
  have hslv : t0.wa "g_sl" u = I.sl u := by have := hB.sl.2 u (by omega); simpa using this
  have hslL : u < t0.wlen "g_sl" := by have := hB.sl.1; omega
  have hoffL : I.n < t0.wlen "g_off" := by have := hB.off.1; omega
  refine runs_while (fun j t => EInv I u t0 j t) L.length _ ?_ ?_ t0
    ⟨by simp [hj0], by simp [hi0], fun i hi => by simp at hi, fun p _ => ⟨rfl, rfl⟩, rfl, rfl,
     by simp, by simp⟩
  · intro j hjL t hI
    have hU := hI.U
    have hgi := hI.gi
    have hreal := hI.real
    have hfr := hI.fr
    rw [← hLdef] at hgi hreal hfr
    have htcap : t.cap = t0.cap := hU.cap
    have hwr : ∀ x, x ∉ emitWR → t.w x = t0.w x := hU.wreg
    have hwa : ∀ a, a ∉ ["gHead"] → t.wa a = t0.wa a ∧ t.wlen a = t0.wlen a := hU.warr
    have htu : t.w "g_u" = u := by rw [hwr _ (by simp [emitWR])]; exact hu
    have htD : t.w "gD" = I.δ := by rw [hwr _ (by simp [emitWR])]; exact hE.gD
    have htcnt : t.wa "g_cnt" (u + 1) = pfx I.src I.m u + L.length := by
      rw [(hwa _ (by simp)).1]; exact hcnt1
    have htcntL : u + 1 < t.wlen "g_cnt" := by rw [(hwa _ (by simp)).2]; exact hcntL
    have htord : t.wa "g_ord" (pfx I.src I.m u + j) = L.getD j 0 := by
      rw [(hwa _ (by simp)).1]; rw [I.grp_length] at hjL; exact hE.ord u hun j hjL
    have htordL : pfx I.src I.m u + j < t.wlen "g_ord" := by rw [(hwa _ (by simp)).2, hE.ordL]; omega
    set e := L.getD j 0 with hedef
    have heL : e ∈ L := getD_mem L hjL
    have hem : e < I.m := (I.mem_grp.mp heL).1
    have hen : I.dst e < I.n := hE.hdst e hem
    have htkept : t.wa "g_kept" e = if I.kept u e then 1 else 0 := by
      rw [(hwa _ (by simp)).1, hB.kept]; exact keptArr_grp hun hk heL
    have htkL : e < t.wlen "g_kept" := by rw [(hwa _ (by simp)).2, hB.kL]; exact hem
    have htoff : t.wa "g_off" (I.dst e) = I.off (I.dst e) := by
      rw [(hwa _ (by simp)).1]; have := hB.off.2 (I.dst e) (by omega); simpa using this
    have htoffL : I.dst e < t.wlen "g_off" := by rw [(hwa _ (by simp)).2]; omega
    have htdst : t.wa "dst" e = I.dst e := by rw [(hwa _ (by simp)).1]; exact hE.dst e hem
    have htdstL : e < t.wlen "dst" := by rw [(hwa _ (by simp)).2]; have := hE.dstL; omega
    have htw : t.va "w" e = I.wt e := by rw [(hU.varr _ (by simp)).1]; exact hE.w e hem
    have htwL : e < t.vlen "w" := by rw [(hU.varr _ (by simp)).2]; have := hE.wL; omega
    have htsl : t.wa "g_sl" u = I.sl u := by rw [(hwa _ (by simp)).1]; exact hslv
    have htslL : u < t.wlen "g_sl" := by rw [(hwa _ (by simp)).2]; exact hslL
    have htake : L.take (j + 1) = L.take j ++ [e] := take_succ_getD L hjL
    set F := (L.take j).filter (fun e => decide (I.kept u e)) with hFdef
    have hFpre : F <+: I.KL u := by
      rw [hFdef, L6In.KL, ← hLdef]; exact (List.take_prefix j L).filter _
    have hFle : F.length ≤ I.deg u := by
      rw [← I.KL_length hk]; exact hFpre.length_le
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [inGroup_eval htu hI.gj htcntL htcnt (by omega) (by omega)]
      simp [hjL]
    · apply wp_sound
      by_cases hkp : I.kept u e
      · -- emit
        have hFe : (L.take (j + 1)).filter (fun e => decide (I.kept u e)) = F ++ [e] := by
          rw [htake, List.filter_append]; simp [hkp, hFdef]
        have hFe_pre : F ++ [e] <+: I.KL u := by
          rw [← hFe, L6In.KL, ← hLdef]; exact (List.take_prefix (j + 1) L).filter _
        have hlt : F.length < I.deg u := by
          have := hFe_pre.length_le; rw [I.KL_length hk] at this; simp at this; omega
        have hKLe : (I.KL u).getD F.length 0 = e := by
          rw [prefix_getD hFe_pre (by simp)]; simp
        have hslot := slotR_lt hk hδ hlt
        have hdegm : I.deg u ≤ I.m := le_trans (I.deg_le u) (by rw [← hLdef]; omega)
        set i := F.length with hidef
        have hqd : i / (I.δ - 1) * (I.δ - 1) ≤ i := Nat.div_mul_le_self _ _
        have hmod : i - i / (I.δ - 1) * (I.δ - 1) = i % (I.δ - 1) := by
          rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm]
        have hp : I.sl u + i / (I.δ - 1) * I.δ + (i - i / (I.δ - 1) * (I.δ - 1)) = slotR I u i := by
          rw [hmod]; rfl
        have hqδ : i / (I.δ - 1) * I.δ ≤ 2 * I.m := by unfold slotR at hslot; omega
        have hδ1 : I.δ - 1 ≠ 0 := by omega
        simp [emitBody, inc, wp, hI.gj, htord, htordL, htkept, htkL, hkp, fit, htcap, hgi, htD,
          htu, htsl, htslL, htdst, htdstL, htoff, htoffL, htw, htwL, hδ1,
          show 0 < t0.cap by omega, show 1 < t0.cap by omega,
          show i / (I.δ - 1) * I.δ < t0.cap by omega,
          show I.sl u + i / (I.δ - 1) * I.δ < t0.cap by omega,
          show i / (I.δ - 1) * (I.δ - 1) < t0.cap by omega,
          show I.sl u + i / (I.δ - 1) * I.δ + (i - i / (I.δ - 1) * (I.δ - 1)) < t0.cap by omega,
          show I.sl u + i / (I.δ - 1) * I.δ + (i - i / (I.δ - 1) * (I.δ - 1)) < t.wlen "gHead" by
            rw [hI.hL]; rw [hp]; omega,
          show I.sl u + i / (I.δ - 1) * I.δ + (i - i / (I.δ - 1) * (I.δ - 1)) < t.vlen "gW" by
            rw [hI.wL]; rw [hp]; omega,
          show i + 1 < t0.cap by omega, show pfx I.src I.m u + j + 1 < t0.cap by omega]
        rw [hp]
        refine ⟨by simp; ring, ?_, ?_, ?_, by simp [hI.hL], by simp [hI.wL],
          by simpa [emitWR] using hU, by simp; have := hI.c; omega⟩
        · rw [← hLdef, hFe]; simp [hidef]
        · intro i' hi'
          rw [← hLdef, hFe] at hi'; simp at hi'
          have hKLe' : (I.KL u)[i]?.getD 0 = e := by simpa using hKLe
          by_cases hii : i' = i
          · rw [hii]; simp [hKLe']
          · have hne : slotR I u i' ≠ slotR I u i := fun h => hii (slotR_inj hδ h)
            simp [hne]
            exact hreal i' (by omega)
        · intro p hp'
          rw [← hLdef, hFe] at hp'
          have hpi : p ≠ slotR I u i := hp' i (by rw [List.length_append, List.length_singleton, hidef]; omega)
          simp [hpi]
          exact hfr p (fun i' hi' => hp' i' (by rw [List.length_append, List.length_singleton]; omega))
      · -- skip
        have hFe : (L.take (j + 1)).filter (fun e => decide (I.kept u e)) = F := by
          rw [htake, List.filter_append]; simp [hkp, hFdef]
        simp [emitBody, inc, wp, hI.gj, htord, htordL, htkept, htkL, hkp, fit, htcap,
          show 0 < t0.cap by omega, show 1 < t0.cap by omega,
          show pfx I.src I.m u + j + 1 < t0.cap by omega]
        refine ⟨by simp; ring, ?_, ?_, ?_, by simp [hI.hL], by simp [hI.wL],
          by simpa [emitWR] using hU, by simp; have := hI.c; omega⟩
        · rw [← hLdef, hFe]; simpa using hgi
        · intro i' hi'; rw [← hLdef, hFe] at hi'; simpa using hreal i' hi'
        · intro p hp'; rw [← hLdef, hFe] at hp'; simpa using hfr p hp'
  · intro t hI
    have hU := hI.U
    have htcap : t.cap = t0.cap := hU.cap
    have htu : t.w "g_u" = u := by rw [hU.wreg _ (by simp [emitWR])]; exact hu
    have htcnt : t.wa "g_cnt" (u + 1) = pfx I.src I.m u + L.length := by
      rw [(hU.warr _ (by simp)).1]; exact hcnt1
    have htcntL : u + 1 < t.wlen "g_cnt" := by rw [(hU.warr _ (by simp)).2]; exact hcntL
    refine ⟨?_, t, hI, rfl⟩
    rw [inGroup_eval htu hI.gj htcntL htcnt (by omega) (by omega)]
    simp

/-! ## One kept vertex of pass B -/

def bkWA : List String := ["gRep", "gOwn", "gSt", "gHd", "gSrc", "gNxt", "gHead"]
def bkWR : List String := ["g_x", "g_q", "g_p", "g_r", "g_k", "g_i", "g_j", "g_e"]

/-- Facts established for a processed kept vertex `v` (all read from state `r`). -/
structure VFacts (I : L6In) (v : ℕ) (r : State ℝ≥0) : Prop where
  rep : r.wa "gRep" v = I.off v
  own : ∀ q < I.cc v, r.wa "gOwn" (I.off v + q) = v
  st : ∀ q < I.cc v, r.wa "gSt" (I.off v + q) = I.sl v + q * I.δ
  hd : ∀ q < I.cc v, r.wa "gHd" (I.off v + q) = I.hdF v q
  src : ∀ q < I.cc v, ∀ o < I.lenF v q, r.wa "gSrc" (I.sl v + q * I.δ + o) = I.off v + q
  nxt : ∀ q < I.cc v, ∀ o < I.lenF v q, r.wa "gNxt" (I.sl v + q * I.δ + o) =
    if o + 1 = I.lenF v q then I.sl I.n else I.sl v + q * I.δ + o + 1
  chain : ∀ q, q + 1 < I.cc v →
    r.wa "gHead" (I.sl v + q * I.δ + (I.δ - 1)) = I.off v + q + 1 ∧
    r.va "gW" (I.sl v + q * I.δ + (I.δ - 1)) = 0
  real : ∀ i < I.deg v, r.wa "gHead" (slotR I v i) = I.off (I.dst ((I.KL v).getD i 0)) ∧
    r.va "gW" (slotR I v i) = I.wt ((I.KL v).getD i 0)

/-- Postcondition of `passBKept` for kept `u` from `t`. -/
structure BKPost (I : L6In) (u : ℕ) (t r : State ℝ≥0) : Prop where
  F : VFacts I u r
  repFr : ∀ v, v ≠ u → r.wa "gRep" v = t.wa "gRep" v
  vFr : ∀ y, (y < I.off u ∨ I.off u + I.cc u ≤ y) → r.wa "gOwn" y = t.wa "gOwn" y ∧
    r.wa "gSt" y = t.wa "gSt" y ∧ r.wa "gHd" y = t.wa "gHd" y
  sFr : ∀ p < I.sl u, r.wa "gSrc" p = t.wa "gSrc" p ∧ r.wa "gNxt" p = t.wa "gNxt" p ∧
    r.wa "gHead" p = t.wa "gHead" p ∧ r.va "gW" p = t.va "gW" p
  lens : ∀ a ∈ bkWA, r.wlen a = t.wlen a
  wL : r.vlen "gW" = t.vlen "gW"
  U : Unchanged t r bkWA ["gW"] bkWR []
  c : r.cost ≤ t.cost + 4 * I.ns u + 20 * I.cc u + 10 * (I.grp u).length + 6

theorem passBKept_runs (I : L6In) (t : State ℝ≥0) (u : ℕ) (hB : BEnv I t) (hu : t.w "g_u" = u)
    (hun : u < I.n) (hk : I.keep u ≠ 0) (hδ : 3 ≤ I.δ)
    (hlRep : I.n ≤ t.wlen "gRep")
    (hlOwn : I.off I.n ≤ t.wlen "gOwn") (hlSt : I.off I.n ≤ t.wlen "gSt")
    (hlHd : I.off I.n ≤ t.wlen "gHd") (hlSrc : I.sl I.n ≤ t.wlen "gSrc")
    (hlNxt : I.sl I.n ≤ t.wlen "gNxt") (hlHead : I.sl I.n ≤ t.wlen "gHead")
    (hlW : I.sl I.n ≤ t.vlen "gW")
    (hoffn : I.off I.n ≤ I.n + I.m) (hsln : I.sl I.n ≤ 2 * I.m) (hδm : I.δ ≤ 2 * I.m + I.n + 3)
    (hcap : 8 * (I.n + I.m) + 16 < t.cap) :
    Runs realOps passBKept t (BKPost I u t) := by
  have hE := hB.A
  have hoffv : t.wa "g_off" u = I.off u := by have := hB.off.2 u (by omega); simpa using this
  have hoffL : u < t.wlen "g_off" := by have := hB.off.1; omega
  have hcntv : t.wa "g_cnt" u = pfx I.src I.m u := by have := hE.cnt.2 u (by omega); simpa using this
  have hcntL : u < t.wlen "g_cnt" := by have := hE.cnt.1; omega
  have hoffle : I.off u ≤ I.off I.n := off_mono I (by omega)
  unfold passBKept
  -- gRep[u] := off u ; g_x := off u
  refine runs_seq (runs_wstore (j := u) (a := I.off u) (by simp [hu])
    (by rw [evalW_load_of (j := u) (by simp [hu]) hoffL, hoffv]) (by omega) ?_)
  refine runs_seq (runs_wset (a := I.off u) (by
    rw [evalW_load_of (j := u) (by simp [hu]) (by simpa using hoffL)]; simp [hoffv]) ?_)
  set t2 := (((t.storeW "gRep" u (I.off u)).charge 1).setW "g_x" (I.off u)).charge 1 with ht2
  have hB2 : BEnv I t2 := hB.of_frame (wa := ["gRep"]) (va := []) (wr := ["g_x"]) (vr := [])
    (by simp [ht2]) (by simp) (by simp) (by simp)
  refine runs_seq ((vertLoop_runs I t2 u hB2 (by simp [ht2, hu]) hun hk hδ (by simp [ht2])
    (by simpa [ht2] using hlOwn) (by simpa [ht2] using hlSt) (by simpa [ht2] using hlHd)
    (by simpa [ht2] using hlSrc) (by simpa [ht2] using hlNxt) (by simpa [ht2] using hlHead)
    (by simpa [ht2] using hlW) hoffn hsln hδm (by simpa [ht2] using hcap)).mono ?_)
  rintro _ ⟨tv, hV, rfl⟩
  have hVU := hV.U
  have hBv : BEnv I (tv.charge 1) := (hB2.of_frame hVU (by simp [vertWA]) (by simp)
    (by simp [vertWR])).of_frame (Unchanged.charge _ _ [] [] [] []) (by simp) (by simp) (by simp)
  have hvu : tv.w "g_u" = u := by rw [hVU.wreg _ (by simp [vertWR])]; simp [ht2, hu]
  have hvcap : tv.cap = t.cap := by rw [hVU.cap]; simp [ht2]
  -- g_i := 0 ; g_j := g_cnt[u]
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp [hvcap]; omega)) ?_)
  have hvcnt : tv.wa "g_cnt" u = pfx I.src I.m u := by
    rw [(hVU.warr _ (by simp [vertWA])).1]; simp [ht2, hcntv]
  have hvcntL : u < tv.wlen "g_cnt" := by rw [(hVU.warr _ (by simp [vertWA])).2]; simpa [ht2] using hcntL
  refine runs_seq (runs_wset (a := pfx I.src I.m u) (by
    rw [evalW_load_of (j := u) (by simp [hvu]) (by simpa using hvcntL)]; simp [hvcnt]) ?_)
  set t4 := (((((tv.charge 1).setW "g_i" 0).charge 1).setW "g_j" (pfx I.src I.m u)).charge 1)
    with ht4
  have hB4 : BEnv I t4 := hBv.of_frame (wa := []) (va := []) (wr := ["g_i", "g_j"]) (vr := [])
    (by simp [ht4]) (by simp) (by simp) (by simp)
  obtain ⟨lOwn, lSt, lHd, lSrc, lNxt, lHead, lW⟩ := hV.lens
  refine (emitLoop_runs I t4 u hB4 (by simp [ht4, hvu]) hun hk hδ (by simp [ht4]) (by simp [ht4])
    (by simp [ht4, lHead, ht2]; exact hlHead) (by simp [ht4, lW, ht2]; exact hlW) hoffn hsln hδm
    (by simp [ht4, hvcap]; omega)).mono ?_
  rintro _ ⟨te, hEm, rfl⟩
  have hEU := hEm.U
  -- relating te to tv
  have hteHead : ∀ p, (∀ i < I.deg u, p ≠ slotR I u i) →
      te.wa "gHead" p = tv.wa "gHead" p ∧ te.va "gW" p = tv.va "gW" p := by
    intro p hp
    have := hEm.fr p (by
      intro i hi
      have hlen : ((I.grp u).take (I.grp u).length).filter (fun e => decide (I.kept u e)) = I.KL u := by
        rw [List.take_length]; rfl
      rw [hlen, I.KL_length hk] at hi
      exact hp i hi)
    simpa [ht4] using this
  have hteA : ∀ a, a ≠ "gHead" → te.wa a = tv.wa a := by
    intro a ha; rw [(hEU.warr a (by simp [ha])).1]; simp [ht4]
  have hteAL : ∀ a, a ≠ "gHead" → te.wlen a = tv.wlen a := by
    intro a ha; rw [(hEU.warr a (by simp [ha])).2]; simp [ht4]
  have hReal : ∀ i < I.deg u, te.wa "gHead" (slotR I u i) = I.off (I.dst ((I.KL u).getD i 0)) ∧
      te.va "gW" (slotR I u i) = I.wt ((I.KL u).getD i 0) := by
    intro i hi
    have hlen : ((I.grp u).take (I.grp u).length).filter (fun e => decide (I.kept u e)) = I.KL u := by
      rw [List.take_length]; rfl
    have := hEm.real i (by rw [hlen, I.KL_length hk]; exact hi)
    exact this
  -- vertex array values of tv
  have hvOwn := hV.own
  have hvSt := hV.st
  have hvHd := hV.hd
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rep
    simp only [State.charge_wa]; rw [hteA _ (by decide), (hVU.warr _ (by simp [vertWA])).1]
    simp [ht2]
  · intro q hq; simp only [State.charge_wa]; rw [hteA _ (by decide), hvOwn]; simp; omega
  · intro q hq; simp only [State.charge_wa]; rw [hteA _ (by decide), hvSt]
    simp [show I.off u ≤ I.off u + q by omega, show I.off u + q < I.off u + I.cc u by omega]
  · intro q hq; simp only [State.charge_wa]; rw [hteA _ (by decide), hvHd]
    simp [show I.off u + q < I.off u + I.cc u by omega]
  · intro q hq o ho; simp only [State.charge_wa]; rw [hteA _ (by decide)]; exact hV.src q hq o ho
  · intro q hq o ho; simp only [State.charge_wa]; rw [hteA _ (by decide)]; exact hV.nxt q hq o ho
  · intro q hq
    have h := hteHead (I.sl u + q * I.δ + (I.δ - 1)) (fun i _ => (slotR_ne_chain hδ).symm)
    simp only [State.charge_wa, State.charge_va]
    rw [h.1, h.2]; exact hV.chain q (by omega) hq
  · intro i hi; simpa using hReal i hi
  · -- repFr
    intro v hv
    simp only [State.charge_wa]; rw [hteA _ (by decide), (hVU.warr _ (by simp [vertWA])).1]
    simp [ht2, hv]
  · -- vFr
    intro y hy
    simp only [State.charge_wa]
    rw [hteA _ (by decide), hteA _ (by decide), hteA _ (by decide), hvOwn, hvSt, hvHd]
    have hny : ¬ (I.off u ≤ y ∧ y < I.off u + I.cc u) := by omega
    simp only [hny, if_false, ht2, State.charge_wa, State.setW_wa, State.storeW_wa]
    simp
  · -- sFr
    intro p hp
    have h := hteHead p (fun i _ => by have := slotR_ge I u i; omega)
    obtain ⟨f1, f2, f3, f4⟩ := hV.frS p hp
    simp only [State.charge_wa, State.charge_va]
    rw [hteA _ (by decide), hteA _ (by decide), h.1, h.2, f1, f2, f3, f4]
    simp [ht2]
  · -- lens
    intro a ha
    simp only [State.charge_wlen]
    by_cases hah : a = "gHead"
    · subst hah; rw [hEm.hL]; simp [ht4, lHead, ht2]
    · rw [hteAL a hah]
      simp [bkWA] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [(hVU.warr _ (by simp [vertWA])).2]; simp [ht2]
      · simp [lOwn, ht2]
      · simp [lSt, ht2]
      · simp [lHd, ht2]
      · simp [lSrc, ht2]
      · simp [lNxt, ht2]
      · exact absurd rfl hah
  · simp only [State.charge_vlen]; rw [hEm.wL]; simp [ht4, lW, ht2]
  · -- U
    have h1 : Unchanged t t2 bkWA ["gW"] bkWR [] := by simp [ht2, bkWA, bkWR]
    have h2 : Unchanged t2 tv bkWA ["gW"] bkWR [] :=
      hVU.mono (by simp [vertWA, bkWA]) (List.Subset.refl _) (by simp [vertWR, bkWR]) (by simp)
    have h3 : Unchanged tv t4 bkWA ["gW"] bkWR [] := by simp [ht4, bkWR]
    have h4 : Unchanged t4 te bkWA ["gW"] bkWR [] :=
      hEU.mono (by simp [bkWA]) (List.Subset.refl _) (by simp [emitWR, bkWR]) (by simp)
    simpa using h1.trans (h2.trans (h3.trans h4))
  · -- cost
    have hc1 := hV.c
    have hc2 := hEm.c
    rw [L6In.lsum_eq hk hδ] at hc1
    simp [ht4, ht2] at hc1 hc2 ⊢
    omega

/-! ## Pass B outer loop -/

def bWR : List String := ["g_x", "g_q", "g_p", "g_r", "g_k", "g_i", "g_j", "g_e", "g_u"]

structure BInv (I : L6In) (st0 : State ℝ≥0) (u : ℕ) (t : State ℝ≥0) : Prop where
  E : BEnv I t
  gu : t.w "g_u" = u
  F : ∀ v < u, I.keep v ≠ 0 → VFacts I v t
  lens : ∀ a ∈ bkWA, t.wlen a = st0.wlen a
  wL : t.vlen "gW" = st0.vlen "gW"
  U : Unchanged st0 t bkWA ["gW"] bWR []
  c : t.cost ≤ st0.cost + 4 * I.sl u + 20 * I.off u + 10 * pfx I.src I.m u + 12 * u

theorem VFacts.of_frame {I : L6In} {v : ℕ} {r r' : State ℝ≥0} (h : VFacts I v r)
    (hrep : r'.wa "gRep" v = r.wa "gRep" v)
    (hv : ∀ y < I.off (v + 1), r'.wa "gOwn" y = r.wa "gOwn" y ∧ r'.wa "gSt" y = r.wa "gSt" y ∧
      r'.wa "gHd" y = r.wa "gHd" y)
    (hs : ∀ p < I.sl (v + 1), r'.wa "gSrc" p = r.wa "gSrc" p ∧ r'.wa "gNxt" p = r.wa "gNxt" p ∧
      r'.wa "gHead" p = r.wa "gHead" p ∧ r'.va "gW" p = r.va "gW" p)
    (hk : I.keep v ≠ 0) (hδ : 3 ≤ I.δ) : VFacts I v r' := by
  have hoff := I.off_succ v
  have hsl := I.sl_succ v
  refine ⟨by rw [hrep]; exact h.rep, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_,
    fun q hq o ho => ?_, fun q hq o ho => ?_, fun q hq => ?_, fun i hi => ?_⟩
  · rw [(hv _ (by omega)).1]; exact h.own q hq
  · rw [(hv _ (by omega)).2.1]; exact h.st q hq
  · rw [(hv _ (by omega)).2.2]; exact h.hd q hq
  · have := L6In.range_le hk hδ hq
    rw [(hs _ (by omega)).1]; exact h.src q hq o ho
  · have := L6In.range_le hk hδ hq
    rw [(hs _ (by omega)).2.1]; exact h.nxt q hq o ho
  · have h1 := L6In.range_le hk hδ (show q < I.cc v by omega)
    have h2 := L6In.lenF_mid hq
    have hp : I.sl v + q * I.δ + (I.δ - 1) < I.sl (v + 1) := by omega
    rw [(hs _ hp).2.2.1, (hs _ hp).2.2.2]; exact h.chain q hq
  · have h1 := slotR_lt hk hδ hi
    have hp : slotR I v i < I.sl (v + 1) := by omega
    rw [(hs _ hp).2.2.1, (hs _ hp).2.2.2]; exact h.real i hi

theorem passBLoop_runs (I : L6In) (st0 : State ℝ≥0) (hδ : 3 ≤ I.δ)
    (hoffn : I.off I.n ≤ I.n + I.m) (hsln : I.sl I.n ≤ 2 * I.m) (hδm : I.δ ≤ 2 * I.m + I.n + 3)
    (hcap : 8 * (I.n + I.m) + 16 < st0.cap)
    (hlRep : I.n ≤ st0.wlen "gRep")
    (hlOwn : I.off I.n ≤ st0.wlen "gOwn") (hlSt : I.off I.n ≤ st0.wlen "gSt")
    (hlHd : I.off I.n ≤ st0.wlen "gHd") (hlSrc : I.sl I.n ≤ st0.wlen "gSrc")
    (hlNxt : I.sl I.n ≤ st0.wlen "gNxt") (hlHead : I.sl I.n ≤ st0.wlen "gHead")
    (hlW : I.sl I.n ≤ st0.vlen "gW") (h0 : BInv I st0 0 st0) :
    Runs realOps passBLoop st0 (fun r => ∃ t, BInv I st0 I.n t ∧ r = t.charge 1) := by
  refine runs_while (fun u t => BInv I st0 u t) I.n _ ?_ ?_ st0 h0
  · intro u hun t hI
    have hB := hI.E
    have hE := hB.A
    have htcap : t.cap = st0.cap := hI.U.cap
    have hkeepL : u < t.wlen "gKeep" := by have := hE.keep.1; omega
    have hkeepv : t.wa "gKeep" u = I.keep u := by have := hE.keep.2 u hun; simpa using this
    have hlen : ∀ a ∈ bkWA, st0.wlen a ≤ t.wlen a := fun a ha => le_of_eq (hI.lens a ha).symm
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (x := u) (y := I.n) (by rw [evalW_var, hI.gu]) (by rw [evalW_var, hE.n])
        (by omega)]
      simp [hun]
    · unfold passBBody
      have hkev : evalW (t.charge 1) (eq (load "gKeep" (var "g_u")) (lit 0)) =
          some (if I.keep u = 0 then 1 else 0) := by
        rw [evalW_eq_of (x := I.keep u) (y := 0)
          (evalW_load_of (j := u) (by simp [hI.gu]) (by simpa using hkeepL) |>.trans
            (by simp [hkeepv]))
          (evalW_lit_of (by simp [htcap]; omega)) (by simp [htcap]; omega)]
      refine runs_seq ?_
      by_cases hk : I.keep u = 0
      · refine runs_ite_true (x := 1) (by rw [hkev, if_pos hk]) one_ne_zero (runs_skip ?_)
        refine runs_wset (a := u + 1) (evalW_add_of (by simp [hI.gu])
          (evalW_lit_of (by simp [htcap]; omega)) (by simp [htcap]; omega)) ?_
        refine ⟨hB.of_frame (wa := []) (va := []) (wr := ["g_u"]) (vr := [])
            (by simp) (by simp) (by simp) (by simp), by simp, fun v hv hkv => ?_,
          fun a ha => by simpa using hI.lens a ha, by simpa using hI.wL,
          by simpa [bWR] using hI.U, ?_⟩
        · have hvu : v ≠ u := by rintro rfl; exact hkv hk
          have := hI.F v (by omega) hkv
          exact this.of_frame (by simp) (fun y _ => by simp) (fun p _ => by simp) hkv hδ
        · have h1 := hI.c
          simp [I.sl_succ, I.off_succ, pfx_succ, I.ns_zero hk, I.cc_zero hk]
          omega
      · refine runs_ite_false (by rw [hkev, if_neg hk]) ?_
        refine (passBKept_runs I ((t.charge 1).charge 1) u
          ((hB.of_frame (Unchanged.charge _ _ [] [] [] []) (by simp) (by simp) (by simp)).of_frame
            (Unchanged.charge _ _ [] [] [] []) (by simp) (by simp) (by simp))
          (by simp [hI.gu]) hun hk hδ
          (by have := hlen "gRep" (by simp [bkWA]); simp; omega)
          (by have := hlen "gOwn" (by simp [bkWA]); simp; omega)
          (by have := hlen "gSt" (by simp [bkWA]); simp; omega)
          (by have := hlen "gHd" (by simp [bkWA]); simp; omega)
          (by have := hlen "gSrc" (by simp [bkWA]); simp; omega)
          (by have := hlen "gNxt" (by simp [bkWA]); simp; omega)
          (by have := hlen "gHead" (by simp [bkWA]); simp; omega)
          (by simp [hI.wL]; exact hlW) hoffn hsln hδm (by simp [htcap]; exact hcap)).mono ?_
        intro r hK
        have hrcap : r.cap = st0.cap := by rw [hK.U.cap]; simp [htcap]
        have hru : r.w "g_u" = u := by rw [hK.U.wreg _ (by simp [bkWR])]; simp [hI.gu]
        refine runs_wset (a := u + 1) (evalW_add_of (by rw [evalW_var, hru])
          (evalW_lit_of (by rw [hrcap]; omega)) (by rw [hrcap]; omega)) ?_
        refine ⟨?_, by simp, fun v hv hkv => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
        · exact (hB.of_frame (Unchanged.charge _ _ [] [] [] []) (by simp) (by simp) (by simp)).of_frame
            (Unchanged.charge _ _ [] [] [] []) (by simp) (by simp) (by simp) |>.of_frame hK.U
            (by simp [bkWA]) (by simp) (by simp [bkWR]) |>.of_frame
            (show Unchanged r ((r.setW "g_u" (u + 1)).charge 1) [] [] ["g_u"] [] by simp)
            (by simp) (by simp) (by simp)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
          · have hF := hI.F v hv hkv
            have hoff : I.off (v + 1) ≤ I.off u := off_mono I (by omega)
            have hsl : I.sl (v + 1) ≤ I.sl u := sl_mono I (by omega)
            refine hF.of_frame ?_ (fun y hy => ?_) (fun p hp => ?_) hkv hδ
            · simp; rw [hK.repFr v (by omega)]; simp
            · have := hK.vFr y (Or.inl (by omega)); simpa using this
            · have := hK.sFr p (by omega); simpa using this
          · have hF := hK.F
            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simpa using hF.rep
            · intro q hq; simpa using hF.own q hq
            · intro q hq; simpa using hF.st q hq
            · intro q hq; simpa using hF.hd q hq
            · intro q hq o ho; simpa using hF.src q hq o ho
            · intro q hq o ho; simpa using hF.nxt q hq o ho
            · intro q hq; simpa using hF.chain q hq
            · intro i hi; simpa using hF.real i hi
        · simp; rw [hK.lens a ha]; simp; exact hI.lens a ha
        · simp; rw [hK.wL]; simp; exact hI.wL
        · have h1 : Unchanged st0 ((t.charge 1).charge 1) bkWA ["gW"] bWR [] := by
            simpa using hI.U
          have h2 : Unchanged ((t.charge 1).charge 1) r bkWA ["gW"] bWR [] :=
            hK.U.mono (List.Subset.refl _) (List.Subset.refl _) (by simp [bkWR, bWR]) (by simp)
          have h3 := h1.trans h2
          simpa [bWR] using h3
        · have h1 := hI.c
          have h2 := hK.c
          have h3 : (I.grp u).length = cntk I.src I.m u := I.grp_length u
          simp at h2
          simp [I.sl_succ, I.off_succ, pfx_succ]
          omega
  · intro t hI
    have htcap : t.cap = st0.cap := hI.U.cap
    refine ⟨?_, t, hI, rfl⟩
    rw [evalW_lt_of (x := I.n) (y := I.n) (by rw [evalW_var, hI.gu]) (by rw [evalW_var, hI.E.A.n])
      (by omega)]
    simp

/-! ## The whole pass B -/

structure BPost (I : L6In) (st r : State ℝ≥0) : Prop where
  E : BEnv I r
  F : ∀ v < I.n, I.keep v ≠ 0 → VFacts I v r
  stN : r.wa "gSt" (I.off I.n) = I.sl I.n
  gS : r.w "gS" = I.off I.s
  lSt : r.wlen "gSt" = I.off I.n + 1
  lHd : r.wlen "gHd" = I.off I.n
  lNxt : r.wlen "gNxt" = I.sl I.n
  lSrc : r.wlen "gSrc" = I.sl I.n
  lHead : r.wlen "gHead" = I.sl I.n
  lW : r.vlen "gW" = I.sl I.n
  lRep : r.wlen "gRep" = I.n
  lOwn : r.wlen "gOwn" = I.off I.n
  U : Unchanged st r bkWA ["gW"] (bWR ++ ["gS"]) []
  c : r.cost ≤ st.cost + 8 * (I.off I.n + I.sl I.n) + 20 * I.off I.n + 10 * I.m + 13 * I.n + 30

theorem keep_s (I : L6In) : I.keep I.s ≠ 0 := by
  have : I.keep I.s = 1 := (keepF_eq_one I.src I.dst I.m I.s I.s).mpr (Or.inl rfl)
  omega

theorem passBProg_runs (I : L6In) (st : State ℝ≥0) (hB : BEnv I st) (hδ : 3 ≤ I.δ)
    (hsn : I.s < I.n) (hs : st.w "s" = I.s)
    (hcap : 8 * (I.n + I.m) + 16 < st.cap) :
    Runs realOps passBProg st (BPost I st) := by
  have hE := hB.A
  have hpm : pfx I.src I.m I.n = I.m := pfx_total _ _ _ hE.hsrc
  have hoffn : I.off I.n ≤ I.n + I.m := by have := I.off_le hδ I.n; omega
  have hsln : I.sl I.n ≤ 2 * I.m := by have := I.sl_le hδ I.n; omega
  have hδm : I.δ ≤ 2 * I.m + I.n + 3 := by
    simp only [L6In.δ, deltaF]
    apply max_le (by omega)
    exact le_trans (Nat.div_le_self _ _) (by omega)
  apply wp_sound
  simp only [passBProg, wp]
  simp [hB.gN, hB.gM, hE.n, fit, show I.off I.n + 1 < st.cap by omega, show 1 < st.cap by omega,
    show 0 < st.cap by omega]
  show Runs realOps passBLoop _ _
  refine (passBLoop_runs I _ hδ hoffn hsln hδm (by simp; omega) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    ⟨hB.of_frame (wa := bkWA) (va := ["gW"]) (wr := ["g_u"]) (vr := [])
      (by simp [bkWA]) (by simp [bkWA]) (by simp) (by simp), by simp,
     fun v hv => absurd hv (Nat.not_lt_zero _), fun a _ => rfl, rfl, by simp,
     by simp [L6In.sl, L6In.off, pfx]⟩).mono ?_
  rintro _ ⟨t, hI, rfl⟩
  have htcap : t.cap = st.cap := by rw [hI.U.cap]; simp
  have hlens := hI.lens
  have htN : t.w "gN" = I.off I.n := hI.E.gN
  have htM : t.w "gM" = I.sl I.n := hI.E.gM
  have hts : t.w "s" = I.s := by rw [hI.U.wreg _ (by simp [bWR])]; simp [hs]
  have hFs := hI.F I.s hsn (keep_s I)
  have hlSt : t.wlen "gSt" = I.off I.n + 1 := by rw [hlens _ (by simp [bkWA])]; simp
  have hlRep : t.wlen "gRep" = I.n := by rw [hlens _ (by simp [bkWA])]; simp
  simp [wp, htN, htM, hts, fit, htcap, hlSt, hlRep, hsn, hFs.rep,
    show I.off I.n < st.cap by omega, show I.sl I.n < st.cap by omega]
  refine ⟨?_, fun v hv hkv => ?_, by simp, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hI.E.of_frame (wa := ["gSt"]) (va := []) (wr := ["gS"]) (vr := [])
      (by simp) (by simp) (by simp) (by simp)
  · have hF := hI.F v hv hkv
    have hle : I.off (v + 1) ≤ I.off I.n := off_mono I (by omega)
    refine hF.of_frame (by simp) (fun y hy => ?_) (fun p hp => by simp) hkv hδ
    have hyN : y ≠ I.off I.n := by omega
    simp [hyN]
  · simpa using hlSt
  · have := hlens "gHd" (by simp [bkWA]); simp at this ⊢; exact this
  · have := hlens "gNxt" (by simp [bkWA]); simp at this ⊢; exact this
  · have := hlens "gSrc" (by simp [bkWA]); simp at this ⊢; exact this
  · have := hlens "gHead" (by simp [bkWA]); simp at this ⊢; exact this
  · have := hI.wL; simp at this ⊢; exact this
  · simpa using hlRep
  · have := hlens "gOwn" (by simp [bkWA]); simp at this ⊢; exact this
  · have h := hI.U
    have h2 := (Unchanged.trans (by simp [bkWA, bWR]) h : Unchanged st t bkWA ["gW"] bWR [])
    have h3 := h2.mono (List.Subset.refl _) (List.Subset.refl _)
      (show bWR ⊆ bWR ++ ["gS"] by simp) (List.Subset.refl _)
    simpa [bkWA, bWR] using h3
  · have h1 := hI.c
    rw [hpm] at h1
    simp at h1 ⊢; omega

end Frontier.CHD.L6
