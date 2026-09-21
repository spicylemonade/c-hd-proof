import Frontier.CHD.L6.SpineIface
import Mathlib.Analysis.MeanInequalities

/-!
# `CoreSpec` from the spine and master specifications (agent-10, COORD G2-8)

`coreSpec_of_spine : SpineSpec e ps spine P Ks → MasterSpec P Km →
  CoreSpec e ps (coreTop spine) (Ks * (Km + 1) + 250)` for every word exponent `e ≥ 32`.

* the prefix `corePre` (save `n, s, m`; `paramsProg`; `levelTab`; `initLab`) establishes `SpineIn`
  (`corePre_runs`), at cost `≤ 29 cn + 200`;
* exactness: the spine's top-level run is complete (`complete_of_topRun`), so the label table
  decodes to the distances (`coreOut_of_labAt`);
* cost: spine `≤ Ks (lg.cost + Tchd)`, master `lg.cost ≤ Km Tchd`, prefix/postfix `≤ 232 Tchd`.
NON-GATE (a composition theorem; `SpineSpec` and `MasterSpec` are the open obligations).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD.LabTab WExpr Stmt

/-! ## `CoreIn` is stable under fragments that do not touch its names -/

theorem CoreIn.of_unchanged {e : ℕ} {ps : List Stmt} {H : Graph} {src : Fin H.n} {cn cm : ℕ}
    {t r : State ℝ≥0} {wa va wr vr : List String} (h : CoreIn e ps H src cn cm t)
    (hu : Unchanged t r wa va wr vr)
    (hSt : "gSt" ∉ wa) (hHead : "gHead" ∉ wa) (hHd : "gHd" ∉ wa) (hNxt : "gNxt" ∉ wa)
    (hW : "gW" ∉ va) (hS : "gS" ∉ wr) (hN : "gN" ∉ wr) (hM : "gM" ∉ wr) (hcn : "cn" ∉ wr)
    (hcm : "cm" ∉ wr) (hD : "gD" ∉ wr) : CoreIn e ps H src cn cm r where
  procs := by rw [hu.procs]; exact h.procs
  csr := h.csr.of_unchanged hu hSt
  graph := graphAt_of_unchanged hu hHead hW h.graph
  gS := by rw [hu.wreg _ hS]; exact h.gS
  gN := by rw [hu.wreg _ hN]; exact h.gN
  gM := by rw [hu.wreg _ hM]; exact h.gM
  cnR := by rw [hu.wreg _ hcn]; exact h.cnR
  cmR := by rw [hu.wreg _ hcm]; exact h.cmR
  gD x := by rw [(hu.warr _ hSt).1, hu.wreg _ hD]; exact h.gD x
  dd := by rw [hu.wreg _ hD]; exact h.dd
  sizeN := h.sizeN
  sizeM := h.sizeM
  cn_le := h.cn_le
  cm_pos := h.cm_pos
  cn_pos := h.cn_pos
  sorted := h.sorted
  simple := h.simple
  hd x := by rw [(hu.warr _ hHd).1, (hu.warr _ hSt).1]; exact h.hd x
  nxt x p h1 h2 := by
    rw [(hu.warr _ hSt).1] at h1 h2
    rw [(hu.warr _ hNxt).1, (hu.warr _ hSt).1]; exact h.nxt x p h1 h2
  hdLen := by rw [(hu.warr _ hHd).2]; exact h.hdLen
  nxtLen := by rw [(hu.warr _ hNxt).2]; exact h.nxtLen
  cap := by rw [hu.cap]; exact h.cap
  dens := h.dens

/-! ## The master theorem's graph facts -/

theorem eout_card_le {H : Graph} {t : State ℝ≥0} (hc : RamBaseCase.CSRAt t H) (u : Fin H.n) :
    (BM.Eout H {u}).card ≤ t.wa "gSt" (u + 1) - t.wa "gSt" u := by
  classical
  have hsub : ∀ e ∈ BM.Eout H {u},
      (e : ℕ) ∈ Finset.Ico (t.wa "gSt" u) (t.wa "gSt" (u + 1)) := by
    intro e he
    simp only [BM.Eout, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at he
    rw [Finset.mem_Ico]
    exact (hc.src e u).mp he
  have h := Finset.card_le_card_of_injOn (fun e : Fin H.m => (e : ℕ)) (fun e he => hsub e he)
    (fun a _ b _ hab => Fin.ext hab)
  rw [Nat.card_Ico] at h
  exact h

theorem masterIn_of_coreIn {e : ℕ} {ps : List Stmt} {H : Graph} {src : Fin H.n} {cn cm : ℕ}
    {t : State ℝ≥0} (h : CoreIn e ps H src cn cm t) (hm : 0 < H.m) : MasterIn H src cn cm where
  sizeN := h.sizeN
  sizeM := h.sizeM
  cn_le := h.cn_le
  cm_pos := h.cm_pos
  cn_pos := h.cn_pos
  mpos := hm
  deg u := (eout_card_le h.csr u).trans ((h.gD u).trans h.dd)
  dens := h.dens
  sorted x := h.sorted src x
  simple := h.simple

/-! ## Word capacity for the per-level tables -/

theorem lgN_le_self {cn : ℕ} (hcn : 1 ≤ cn) : CostSkeleton.lgN cn ≤ cn :=
  max_le hcn (Nat.log_le_self 2 cn)

theorem two_pow_lgN_le {cn : ℕ} (hcn : 1 ≤ cn) : 2 ^ CostSkeleton.lgN cn ≤ 2 * cn := by
  unfold CostSkeleton.lgN
  rcases le_total 1 (Nat.log 2 cn) with h | h
  · rw [max_eq_right h]
    have := Nat.pow_log_le_self 2 (show cn ≠ 0 by omega)
    omega
  · rw [max_eq_left h]; omega

theorem levelTab_cap (cn cm e cap : ℕ) (hcn : 1 ≤ cn) (hcm : 1 ≤ cm) (he : 32 ≤ e)
    (hcap : (cn + cm + 2) ^ (e + 1) ≤ cap) :
    CostSkeleton.tF cn cm * CostSkeleton.tF cn cm * CostSkeleton.tF cn cm *
        2 ^ ((CostSkeleton.LF cn cm + 1) * CostSkeleton.tF cn cm) + 2 ^ (CostSkeleton.tF cn cm + 1) +
        CostSkeleton.LF cn cm + CostSkeleton.tF cn cm + 5 < cap := by
  have hT := CostSkeleton.tF_le cn cm
  have hT16 := CostSkeleton.sixteen_le_tF cn cm
  have hg := lgN_le_self hcn
  have h2g := two_pow_lgN_le hcn
  have hX : 18014398509481984 * cn ^ 6 ≤ cap := by
    have h1 : cn ^ 6 * 4 ^ 27 ≤ (cn + cm + 2) ^ 6 * (cn + cm + 2) ^ 27 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 6) (Nat.pow_le_pow_left (by omega) 27)
    have h2 : (cn + cm + 2) ^ 6 * (cn + cm + 2) ^ 27 = (cn + cm + 2) ^ 33 := by
      rw [← pow_add]
    have h3 : (cn + cm + 2) ^ 33 ≤ (cn + cm + 2) ^ (e + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h4 : cn ^ 6 * 4 ^ 27 = 18014398509481984 * cn ^ 6 := by norm_num; ring
    omega
  have hc6 : cn ≤ cn ^ 6 := le_self_pow hcn (by norm_num)
  rw [show CostSkeleton.LF cn cm = CostSkeleton.lgN cn / CostSkeleton.tF cn cm + 1 from rfl]
  generalize CostSkeleton.tF cn cm = T at hT hT16 ⊢
  generalize CostSkeleton.lgN cn = g at hT hg h2g ⊢
  have hq : g / T ≤ g := Nat.div_le_self g T
  have hLT : (g / T + 1 + 1) * T ≤ g + 2 * T := by
    have h1 : (g / T + 1 + 1) * T = g / T * T + 2 * T := by ring
    have h2 := Nat.div_mul_le_self g T
    omega
  have hpow : 2 ^ ((g / T + 1 + 1) * T) ≤ 2 ^ 32 * (2 * cn) ^ 3 := by
    calc 2 ^ ((g / T + 1 + 1) * T) ≤ 2 ^ (32 + 3 * g) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ 32 * (2 ^ g) ^ 3 := by rw [pow_add, ← pow_mul, mul_comm 3 g]
      _ ≤ 2 ^ 32 * (2 * cn) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2g 3)
  have hT3 : T * T * T ≤ (17 * cn) ^ 3 := by
    have h1 : T ≤ 17 * cn := by omega
    calc T * T * T = T ^ 3 := by ring
      _ ≤ (17 * cn) ^ 3 := Nat.pow_le_pow_left h1 3
  have hA : T * T * T * 2 ^ ((g / T + 1 + 1) * T) ≤ 168809394601984 * cn ^ 6 := by
    calc T * T * T * 2 ^ ((g / T + 1 + 1) * T) ≤ (17 * cn) ^ 3 * (2 ^ 32 * (2 * cn) ^ 3) :=
          Nat.mul_le_mul hT3 hpow
      _ = 168809394601984 * cn ^ 6 := by ring
  have hP : 2 ^ (T + 1) ≤ 262144 * cn := by
    calc 2 ^ (T + 1) ≤ 2 ^ (17 + g) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ 17 * 2 ^ g := pow_add _ _ _
      _ ≤ 2 ^ 17 * (2 * cn) := Nat.mul_le_mul_left _ h2g
      _ = 262144 * cn := by ring
  generalize T * T * T * 2 ^ ((g / T + 1 + 1) * T) = A at hA ⊢
  generalize 2 ^ (T + 1) = Q at hP ⊢
  generalize cn ^ 6 = c6 at hA hX hc6
  omega

/-! ## The prefix -/

/-- Arrays written by the prefix. -/
def preWA : List String := ["cp.tau", "cp.M", "dfin", "dhops", "de", "dver", "vcnt"]
/-- Value arrays written by the prefix. -/
def preVA : List String := ["dlen"]
/-- Registers written by the prefix. -/
def preWR : List String :=
  ["core.n", "core.s", "core.m", "cp.x", "cp.lg", "cp.dd", "cp.t", "cp.r", "cp.k", "cp.L",
   "cp.p", "cp.i", "cp.c", "cp.q", "cp.l"]

theorem corePre_runs {e : ℕ} (he : 32 ≤ e) {ps : List Stmt} {H : Graph} {src : Fin H.n}
    {cn cm : ℕ} {t : State ℝ≥0} (h : CoreIn e ps H src cn cm t) :
    Runs realOps corePre t (fun r => ∃ c0, PreIn e ps H src cn cm c0 r ∧
      Unchanged t r preWA preVA preWR [] ∧
      r.w "core.n" = t.w "n" ∧ r.w "core.s" = t.w "s" ∧ r.w "core.m" = t.w "m" ∧
      r.cost ≤ t.cost + 29 * cn + 200 ∧ r.cost ≤ c0 + 12 * cn + 8) := by
  have hcn1 := h.cn_pos
  unfold corePre
  refine runs_seq (runs_wset (a := t.w "n") (evalW_var' _ _) ?_)
  refine runs_seq (runs_wset (a := t.w "s") (by simp) ?_)
  refine runs_seq (runs_wset (a := t.w "m") (by simp) ?_)
  set t3 := ((((((t.setW "core.n" (t.w "n")).charge 1).setW "core.s" (t.w "s")).charge 1).setW
    "core.m" (t.w "m")).charge 1) with ht3
  have hU3 : Unchanged t t3 [] [] ["core.n", "core.s", "core.m"] [] := by
    rw [ht3]; simp
  have hI3 : CoreIn e ps H src cn cm t3 :=
    h.of_unchanged hU3 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp)
  have h3n : t3.w "core.n" = t.w "n" := by rw [ht3]; simp
  have h3s : t3.w "core.s" = t.w "s" := by rw [ht3]; simp
  have h3m : t3.w "core.m" = t.w "m" := by rw [ht3]; simp
  have h3c : t3.cost = t.cost + 3 := by rw [ht3]; simp
  have hcap6 : (cn + cm + 2) ^ 6 ≤ t3.cap :=
    (Nat.pow_le_pow_right (by omega) (by omega)).trans hI3.cap
  refine runs_seq ((paramsProg_runs t3 cn cm hI3.cnR hI3.cmR hcn1 hcap6).mono ?_)
  rintro t4 ⟨h4lg, h4dd, h4t, h4k, h4L, hU4, hc4⟩
  have hI4 : CoreIn e ps H src cn cm t4 :=
    hI3.of_unchanged hU4 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [cpWR])
      (by simp [cpWR]) (by simp [cpWR]) (by simp [cpWR]) (by simp [cpWR]) (by simp [cpWR])
  have hcapL := levelTab_cap cn cm e t4.cap hcn1 hI4.cm_pos he hI4.cap
  refine runs_seq ((levelTab_runs t4 (CostSkeleton.tF cn cm) (CostSkeleton.LF cn cm)
    (by have := CostSkeleton.sixteen_le_tF cn cm; omega) h4t h4L hcapL).mono ?_)
  rintro t5 ⟨h5tau, h5M, h5tl, h5Ml, hU5, hc5⟩
  have hI5 : CoreIn e ps H src cn cm t5 :=
    hI4.of_unchanged hU5 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp [ltWR])
      (by simp [ltWR]) (by simp [ltWR]) (by simp [ltWR]) (by simp [ltWR]) (by simp [ltWR])
  have hcap1 : 1 < t5.cap := by
    have h2 : 2 ≤ (cn + cm + 2) ^ (e + 1) := by
      calc 2 ≤ (cn + cm + 2) ^ 1 := by rw [pow_one]; omega
        _ ≤ (cn + cm + 2) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have := hI5.cap
    omega
  refine (wp_sound (ops := realOps) initLab _ t5 (initLab_wp (G := H) t5 src hI5.gN hI5.gS
    hcap1)).mono ?_
  rintro t6 ⟨hLab, hU6, hc6⟩
  have hI6 : CoreIn e ps H src cn cm t6 :=
    hI5.of_unchanged hU6 (by simp [labW]) (by simp [labW]) (by simp [labW]) (by simp [labW])
      (by simp [labV]) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  have r5 : ∀ x, x ∉ ltWR → t5.w x = t4.w x := fun x hx => hU5.wreg x hx
  have r6 : ∀ x, t6.w x = t5.w x := fun x => hU6.wreg x (by simp)
  have a6 : ∀ a, a ∉ labW → t6.wa a = t5.wa a ∧ t6.wlen a = t5.wlen a := fun a ha => hU6.warr a ha
  refine ⟨t5.cost, ⟨hI6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hLab⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r6, r5 _ (by simp [ltWR])]; exact h4lg
  · rw [r6, r5 _ (by simp [ltWR])]; exact h4dd
  · rw [r6, r5 _ (by simp [ltWR])]; exact h4t
  · rw [r6, r5 _ (by simp [ltWR])]; exact h4k
  · rw [r6, r5 _ (by simp [ltWR])]; exact h4L
  · intro l hl; rw [(a6 _ (by simp [labW])).1]; exact h5tau l hl
  · intro l hl; rw [(a6 _ (by simp [labW])).1]; exact h5M l hl
  · rw [(a6 _ (by simp [labW])).2]; exact h5tl
  · rw [(a6 _ (by simp [labW])).2]; exact h5Ml
  · -- the composed frame
    have hU3' : Unchanged t t3 preWA preVA preWR [] :=
      hU3.mono (by simp) (by simp) (by simp [preWR]) (by simp)
    have hU4' : Unchanged t3 t4 preWA preVA preWR [] :=
      hU4.mono (by simp) (by simp) (by simp [cpWR, preWR]) (by simp)
    have hU5' : Unchanged t4 t5 preWA preVA preWR [] :=
      hU5.mono (by simp [preWA]) (by simp) (by simp [ltWR, preWR]) (by simp)
    have hU6' : Unchanged t5 t6 preWA preVA preWR [] :=
      hU6.mono (by simp [labW, preWA]) (by simp [labV, preVA]) (by simp) (by simp)
    exact ((hU3'.trans hU4').trans hU5').trans hU6'
  · rw [r6, r5 _ (by simp [ltWR]), hU4.wreg _ (by simp [cpWR])]; exact h3n
  · rw [r6, r5 _ (by simp [ltWR]), hU4.wreg _ (by simp [cpWR])]; exact h3s
  · rw [r6, r5 _ (by simp [ltWR]), hU4.wreg _ (by simp [cpWR])]; exact h3m
  · -- cost
    have hTle : CostSkeleton.tF cn cm ≤ 16 + cn :=
      (CostSkeleton.tF_le cn cm).trans (by have := lgN_le_self hcn1; omega)
    have hLle : CostSkeleton.LF cn cm ≤ cn + 1 := by
      have h1 : CostSkeleton.LF cn cm = CostSkeleton.lgN cn / CostSkeleton.tF cn cm + 1 := rfl
      have h2 := Nat.div_le_self (CostSkeleton.lgN cn) (CostSkeleton.tF cn cm)
      have h3 := lgN_le_self hcn1
      omega
    have hsq := Nat.sqrt_le_self (CostSkeleton.tF cn cm)
    have hN := hI6.sizeN
    rw [hc6]
    omega
  · have hN := hI6.sizeN
    rw [hc6]
    omega

/-! ## The postfix -/

theorem corePost_runs (t : State ℝ≥0) :
    Runs realOps corePost t (fun r => r.w "n" = t.w "core.n" ∧ r.w "s" = t.w "core.s" ∧
      r.w "m" = t.w "core.m" ∧ Unchanged t r [] [] ["n", "s", "m"] [] ∧ r.cost = t.cost + 3) := by
  unfold corePost
  refine runs_seq (runs_wset (a := t.w "core.n") (evalW_var' _ _) ?_)
  refine runs_seq (runs_wset (a := t.w "core.s") (by simp) ?_)
  refine runs_wset (a := t.w "core.m") (by simp) ?_
  refine ⟨by simp, by simp, by simp, by simp, by simp⟩

/-! ## A polynomial bound on `Tchd` (for the budget) -/

theorem Tchd_le_sq (n m : ℕ) : GateCCalc.Tchd n m ≤ ((n : ℝ) + m + 2) ^ 2 := by
  unfold GateCCalc.Tchd
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) ≤ (m : ℝ) + 1 := by
    have hpos : 0 < (m : ℝ) / ((n : ℝ) + 1) + 2 := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have hdiv : (m : ℝ) / ((n : ℝ) + 1) ≤ m := div_le_self hm (by linarith)
    linarith
  have h2 : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n + 2 by linarith)
    linarith
  have hlog2 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have h3 : (m : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) ^ ((2 : ℝ) / 3) ≤
      (1 / 3) * m + (2 / 3) * ((n : ℝ) * Real.log ((n : ℝ) + 2)) :=
    Real.geom_mean_le_arith_mean2_weighted (by norm_num) (by norm_num) hm (by positivity)
      (by norm_num)
  have h4 : (m : ℝ) * Real.log ((m : ℝ) / ((n : ℝ) + 1) + 2) ≤ m * (m + 1) :=
    mul_le_mul_of_nonneg_left h1 hm
  have h5 : (n : ℝ) * Real.log ((n : ℝ) + 2) ≤ n * (n + 1) := mul_le_mul_of_nonneg_left h2 hn
  nlinarith

/-! ## The edgeless case and the entry charge -/

/-- Without edges only the source is reachable, so `initLab`'s labels are complete. -/
theorem complete_init_of_m0 {H : Graph} (src : Fin H.n) (hm : H.m = 0) (v : Fin H.n) :
    CHD.Complete (BM.initLabels src) v := by
  have hnil : ∀ p : List (Fin H.m), p = [] := by
    intro p
    cases p with
    | nil => rfl
    | cons e _ => exact absurd e.2 (by omega)
  unfold CHD.Complete
  by_cases hv : v = src
  · subst hv; exact BM.initLabels_source
  · have hr : ¬ H.Reachable src v := by
      rintro ⟨p, hp⟩
      rw [hnil p] at hp
      cases hp
      exact hv rfl
    rw [dis_of_not_reachable hr]
    show (if v = src then _ else ⊤) = ⊤
    rw [if_neg hv]

theorem PreIn.charge {e : ℕ} {ps : List Stmt} {H : Graph} {src : Fin H.n} {cn cm c0 : ℕ}
    {t : State ℝ≥0} (h : PreIn e ps H src cn cm c0 t) (k : ℕ) :
    PreIn e ps H src cn cm c0 (t.charge k) where
  core := h.core.of_unchanged (Unchanged.charge t k [] [] [] []) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  lg := by simpa using h.lg
  dd := by simpa using h.dd
  tt := by simpa using h.tt
  k := by simpa using h.k
  L := by simpa using h.L
  tau l hl := by simpa using h.tau l hl
  M l hl := by simpa using h.M l hl
  tauLen := by simpa using h.tauLen
  MLen := by simpa using h.MLen
  lab := h.lab.of_unchanged (Unchanged.charge t k [] [] [] []) (by simp) (by simp) (by simp)

/-! ## The composition -/

set_option maxHeartbeats 1000000 in
theorem coreSpec_of_spine (e : ℕ) (he : 32 ≤ e) (ps : List Stmt) (spine : Stmt)
    (P : ℕ → ℕ → CostPar) (Ks Kb Kpol Km : ℝ) (Dp : ℕ) (hDp : 2 ≤ Dp) (hKs : 0 ≤ Ks) (hKm : 0 ≤ Km)
    (hbig : 12 + Ks * (Km + 1) + |Kb| + |Kpol| ≤ (4 : ℝ) ^ (e + 1 - Dp))
    (hsp : SpineSpec e ps spine P Ks Kb Kpol Km Dp) (hma : MasterSpec P Km) :
    CoreSpec e ps (coreTop spine) (Ks * (Km + 1) + 250) := by
  intro H src cn cm t hIn
  unfold coreTop
  refine runs_seq ((corePre_runs he hIn).mono ?_)
  rintro t6 ⟨c0, hPre, hU6, h6n, h6s, h6m, hc6, hc60⟩
  have hTn : (cn : ℝ) ≤ GateCCalc.Tchd cn cm := CostSkeleton.n_le_Tchd cn cm
  have hT0 : (0 : ℝ) ≤ GateCCalc.Tchd cn cm := le_trans (Nat.cast_nonneg cn) hTn
  have hcn1 : (1 : ℝ) ≤ cn := by exact_mod_cast hIn.cn_pos
  have hKc0 : 0 ≤ Ks * (Km + 1) := mul_nonneg hKs (by linarith)
  have hcap1 : 1 < t6.cap := by
    have h2 : 2 ≤ (cn + cm + 2) ^ (e + 1) := by
      calc 2 ≤ (cn + cm + 2) ^ 1 := by rw [pow_one]; omega
        _ ≤ (cn + cm + 2) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have := hPre.core.cap
    omega
  have hev : evalW t6 (eq (var "gM") (lit 0)) = some (if H.m = 0 then 1 else 0) :=
    evalW_eq_of (by rw [evalW_var', hPre.core.gM]) (evalW_lit_of (by omega)) hcap1
  have k6 := hU6.warr "gKeep" (by simp [preWA])
  have p6 := hU6.warr "gRep" (by simp [preWA])
  have hc6' : (t6.cost : ℝ) ≤ t.cost + 29 * cn + 200 := by exact_mod_cast hc6
  by_cases hm0 : H.m = 0
  · -- no edge: `initLab`'s table is already exact
    refine runs_seq (runs_ite_true (x := 1) (by rw [hev, if_pos hm0]) one_ne_zero (runs_skip ?_))
    refine (corePost_runs _).mono ?_
    rintro r ⟨hrn, hrs, hrm, hU8, hc8⟩
    have hout6 : CoreOut H src t6 := coreOut_of_labAt hPre.lab (complete_init_of_m0 src hm0)
    have e8 : ∀ a, r.wa a = t6.wa a ∧ r.wlen a = t6.wlen a := fun a => by
      have h := hU8.warr a (by simp); simpa using h
    have e8v : ∀ a, r.va a = t6.va a ∧ r.vlen a = t6.vlen a := fun a => by
      have h := hU8.varr a (by simp); simpa using h
    refine ⟨hout6.of_eq (e8 _).1 (e8 _).2 (e8v _).1 (e8v _).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(e8 _).1, (e8 _).2, k6.1, k6.2]; exact ⟨rfl, rfl⟩
    · rw [(e8 _).1, (e8 _).2, p6.1, p6.2]; exact ⟨rfl, rfl⟩
    · rw [hrn]; simpa using h6n
    · rw [hrs]; simpa using h6s
    · rw [hrm]; simpa using h6m
    · rw [hU8.cap]; simpa using hU6.cap
    · have hc8' : (r.cost : ℝ) = t6.cost + 5 := by
        have h := hc8; simp at h; rw [h]; push_cast; ring
      nlinarith
  · -- edges: run the spine
    refine runs_seq (runs_ite_false (by rw [hev, if_neg hm0]) ?_)
    have hmpos : 0 < H.m := Nat.pos_of_ne_zero hm0
    have hSp : SpineIn e ps H src cn cm c0 (t6.charge 1) := ⟨hPre.charge 1, hmpos⟩
    -- the budget, from the master theorem and the word capacity
    have hbud : ∀ (T : ℕ → ℕ) (Blow : WLab H src), Blow ≤ BM.initLabels src src →
        ∀ (res : BM.ResultD H src) (φ' : Finset (Fin H.m)) (gE : BM.DGl H src)
          (lg : BM.Log H src (FPData H src)), TopRun H src cn cm (P cn cm) T Blow res φ' gE lg →
          ((t6.charge 1).cost : ℝ) + Ks * ((lg.cost : ℝ) + GateCCalc.Tchd cn cm) + Kb +
            Kpol * ((cn : ℝ) + cm + 2) ^ Dp ≤ c0 + (t6.charge 1).cap := by
      intro T Blow hlow res φ' gE lg hrun
      have hmas := hma H src cn cm (masterIn_of_coreIn hIn hmpos) T Blow hlow res φ' gE lg hrun
      set X : ℝ := (cn : ℝ) + cm + 2 with hX
      have hX4 : (4 : ℝ) ≤ X := by
        have h2 : (1 : ℝ) ≤ cm := by exact_mod_cast hIn.cm_pos
        rw [hX]; linarith
      have hcapN : (cn + cm + 2) ^ (e + 1) ≤ t6.cap := hPre.core.cap
      have hcapR : X ^ (e + 1) ≤ ((t6.charge 1).cap : ℝ) := by
        have h := (Nat.cast_le (α := ℝ)).mpr hcapN
        push_cast at h
        simp only [State.charge_cap]
        rw [hX]; exact h
      have hDe : Dp ≤ e + 1 := by
        by_contra hne
        have h0 : e + 1 - Dp = 0 := by omega
        rw [h0, pow_zero] at hbig
        have h1 := abs_nonneg Kb
        have h2 := abs_nonneg Kpol
        have h3 : 0 ≤ Ks * (Km + 1) := mul_nonneg hKs (by linarith)
        linarith
      have hpow : (4 : ℝ) ^ (e + 1 - Dp) * X ^ Dp ≤ X ^ (e + 1) := by
        have h1 : (4 : ℝ) ^ (e + 1 - Dp) ≤ X ^ (e + 1 - Dp) := pow_le_pow_left₀ (by norm_num) hX4 _
        have h2 : X ^ (e + 1 - Dp) * X ^ Dp = X ^ (e + 1) := by
          rw [← pow_add]; congr 1; omega
        calc (4 : ℝ) ^ (e + 1 - Dp) * X ^ Dp ≤ X ^ (e + 1 - Dp) * X ^ Dp :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = X ^ (e + 1) := h2
      have hX1 : (1 : ℝ) ≤ X := by linarith
      have hX2D : X ^ 2 ≤ X ^ Dp := pow_le_pow_right₀ hX1 hDp
      have hX1D : X ≤ X ^ Dp := by
        calc X = X ^ 1 := (pow_one X).symm
          _ ≤ X ^ Dp := pow_le_pow_right₀ hX1 (by omega)
      have hTX : GateCCalc.Tchd cn cm ≤ X ^ Dp := by
        have := Tchd_le_sq cn cm; rw [← hX] at this; linarith
      have hKpX : Kpol * X ^ Dp ≤ |Kpol| * X ^ Dp :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      have hc60' : ((t6.charge 1).cost : ℝ) ≤ c0 + 12 * cn + 9 := by
        have h := hc60; simp only [State.charge_cost]; push_cast; exact_mod_cast (by omega : t6.cost + 1 ≤ c0 + 12 * cn + 9)
      have hcnX : 12 * (cn : ℝ) + 9 ≤ 12 * X ^ Dp := by
        have h1 : (cn : ℝ) + 1 ≤ X := by
          have h2 : (1 : ℝ) ≤ cm := by exact_mod_cast hIn.cm_pos
          rw [hX]; linarith
        linarith
      have hKbX : Kb ≤ |Kb| * X ^ Dp := by
        have h1 : (1 : ℝ) ≤ X ^ Dp := one_le_pow₀ hX1
        calc Kb ≤ |Kb| := le_abs_self Kb
          _ ≤ |Kb| * X ^ Dp := le_mul_of_one_le_right (abs_nonneg Kb) h1
      have hKsX : Ks * ((lg.cost : ℝ) + GateCCalc.Tchd cn cm) ≤ Ks * (Km + 1) * X ^ Dp := by
        have h1 : (lg.cost : ℝ) + GateCCalc.Tchd cn cm ≤ (Km + 1) * X ^ Dp := by
          calc (lg.cost : ℝ) + GateCCalc.Tchd cn cm ≤ Km * GateCCalc.Tchd cn cm + GateCCalc.Tchd cn cm := by
                linarith [hmas]
            _ = (Km + 1) * GateCCalc.Tchd cn cm := by ring
            _ ≤ (Km + 1) * X ^ Dp := mul_le_mul_of_nonneg_left hTX (by linarith)
        calc Ks * ((lg.cost : ℝ) + GateCCalc.Tchd cn cm) ≤ Ks * ((Km + 1) * X ^ Dp) :=
              mul_le_mul_of_nonneg_left h1 hKs
          _ = Ks * (Km + 1) * X ^ Dp := by ring
      have hsum : 12 * X ^ Dp + Ks * (Km + 1) * X ^ Dp + |Kb| * X ^ Dp + |Kpol| * X ^ Dp ≤
          (4 : ℝ) ^ (e + 1 - Dp) * X ^ Dp := by
        have h1 : 0 ≤ X ^ Dp := by positivity
        have e1 : 12 * X ^ Dp + Ks * (Km + 1) * X ^ Dp + |Kb| * X ^ Dp + |Kpol| * X ^ Dp =
            (12 + Ks * (Km + 1) + |Kb| + |Kpol|) * X ^ Dp := by ring
        rw [e1]
        exact mul_le_mul_of_nonneg_right hbig h1
      linarith
    refine (hsp H src cn cm c0 (t6.charge 1) hSp hbud
      (fun T Blow hlow res φ' gE lg hrun =>
        hma H src cn cm (masterIn_of_coreIn hIn hmpos) T Blow hlow res φ' gE lg hrun)).mono ?_
    rintro t7 ⟨T, Blow, res, φ', gE, lg, Hh, c1, hlow, hrun, hLab7, hF, hc7⟩
    refine (corePost_runs t7).mono ?_
    rintro r ⟨hrn, hrs, hrm, hU8, hc8⟩
    -- exactness
    have hcomp := complete_of_topRun (fun x => hIn.sorted src x) hIn.simple hIn.sizeN hlow hrun
    have hout7 : CoreOut H src t7 := coreOut_of_labAt hLab7 hcomp
    -- master cost
    have hmas := hma H src cn cm (masterIn_of_coreIn hIn hmpos) T Blow hlow res φ' gE lg hrun
    have e8 : ∀ a, r.wa a = t7.wa a ∧ r.wlen a = t7.wlen a := fun a => hU8.warr a (by simp)
    have e8v : ∀ a, r.va a = t7.va a ∧ r.vlen a = t7.vlen a := fun a => hU8.varr a (by simp)
    have ek : (t6.charge 1).wa "gKeep" = t.wa "gKeep" ∧ (t6.charge 1).wlen "gKeep" = t.wlen "gKeep" := by
      simpa using k6
    have ep : (t6.charge 1).wa "gRep" = t.wa "gRep" ∧ (t6.charge 1).wlen "gRep" = t.wlen "gRep" := by
      simpa using p6
    refine ⟨hout7.of_eq (e8 _).1 (e8 _).2 (e8v _).1 (e8v _).2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(e8 _).1, (e8 _).2, hF.keep.1, hF.keep.2, ek.1, ek.2]; exact ⟨rfl, rfl⟩
    · rw [(e8 _).1, (e8 _).2, hF.rep.1, hF.rep.2, ep.1, ep.2]; exact ⟨rfl, rfl⟩
    · rw [hrn, hF.n]; simpa using h6n
    · rw [hrs, hF.s]; simpa using h6s
    · rw [hrm, hF.m]; simpa using h6m
    · rw [hU8.cap, hF.cap]; simpa using hU6.cap
    · -- cost
      have hc8' : (r.cost : ℝ) = t7.cost + 3 := by exact_mod_cast hc8
      have hc7' : (t7.cost : ℝ) ≤ t6.cost + 1 + Ks * ((lg.cost : ℝ) + GateCCalc.Tchd cn cm) := by
        have h := hc7; simp only [State.charge_cost] at h; push_cast at h; linarith
      have hsp' : Ks * ((lg.cost : ℝ) + GateCCalc.Tchd cn cm) ≤
          Ks * ((Km + 1) * GateCCalc.Tchd cn cm) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hKs
      nlinarith

/-- **The C-HD target from the two remaining specifications**: the RAM spine (`SpineSpec`) and
the Layer-A master cost theorem (`MasterSpec`), for a word exponent `e ≥ 32` large enough for the
constants (`hbig`). -/
theorem chdTarget_of_spine (e : ℕ) (he : 32 ≤ e) (ps : List Stmt) (spine : Stmt)
    (P : ℕ → ℕ → CostPar) (Ks Kb Kpol Km : ℝ) (Dp : ℕ) (hDp : 2 ≤ Dp) (hKs : 0 ≤ Ks) (hKm : 0 ≤ Km)
    (hbig : 12 + Ks * (Km + 1) + |Kb| + |Kpol| ≤ (4 : ℝ) ^ (e + 1 - Dp))
    (hsp : SpineSpec e ps spine P Ks Kb Kpol Km Dp) (hma : MasterSpec P Km) :
    GateCTarget.CHDTarget GateCCalc.F :=
  chdTarget_of_core e (by omega) ps (coreTop spine) (Ks * (Km + 1) + 250)
    (by have : 0 ≤ Ks * (Km + 1) := mul_nonneg hKs (by linarith); linarith)
    (coreSpec_of_spine e he ps spine P Ks Kb Kpol Km Dp hDp hKs hKm hbig hsp hma)

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.coreSpec_of_spine
#print axioms Frontier.CHD.L6.chdTarget_of_spine
