import Frontier.CHD.L6.Run
import Frontier.CHD.L6.Out
import Frontier.CHD.L6.TchdCn

/-!
# The C-HD RAM body over an abstract core (agent-10)

`chdBody core` = `if m = 0 then trivialOut else (L6 ; core ; outProg)`.  The only assumption on
`core` is `CoreSpec`: from any state holding a reduced graph `H` in L6's format (the facts L6
proves), it leaves the exact distances from `gS` in the label table (`CoreOut`), keeps the arrays
`gKeep`, `gRep` and the register `n`, and costs at most `Kc · Tchd cn cm`.  Under `CoreSpec`,
`chdBody core` satisfies `Dispatch.BodySpec`, hence `CHDTarget F` (`Dispatch.chdTarget_of_body`).

**This file does NOT construct the core.**  `CoreSpec` for a concrete C-HD core RAM program is the
remaining gap (Layer B spine, FindPivots-HD, DS', labels, base case — other packages).
-/

open scoped NNReal ENNReal

namespace Frontier.CHD.L6

open Frontier Frontier.RAM WExpr Stmt Finset

/-! ## Live lists (for B-L2) -/

section Live

variable {I : L6In} {st t0 t : State ℝ≥0} (hB : BPost I st t0) (hS : SPInv I t0 (I.off I.n) t)
  (hδ : 3 ≤ I.δ)

include hB hS hδ in
theorem live_hd {x : ℕ} (hx : x < I.off I.n) :
    t.wa "gHd" x = if t.wa "gSt" x = t.wa "gSt" (x + 1) then I.sl I.n else t.wa "gSt" x := by
  obtain ⟨v, hv, hk, q, hq, hxq, ha, hb⟩ := st_range_any hB.F hB.stN hδ hx
  rw [sort_frame_wa hS (by simp), st_post hB hS hδ, st_post hB hS hδ, ha, hb, hxq,
    (hB.F v hv hk).hd q hq]
  unfold L6In.hdF
  by_cases h0 : I.lenF v q = 0
  · simp [h0]
  · simp [h0]

include hB hS hδ in
theorem live_nxt {x p : ℕ} (hx : x < I.off I.n) (hp1 : t.wa "gSt" x ≤ p)
    (hp2 : p < t.wa "gSt" (x + 1)) :
    t.wa "gNxt" p = if p + 1 = t.wa "gSt" (x + 1) then I.sl I.n else p + 1 := by
  rw [st_post hB hS hδ] at hp1 hp2 ⊢
  obtain ⟨v, hv, hk, q, hq, hxq, ha, hb⟩ := st_range_any hB.F hB.stN hδ hx
  rw [sort_frame_wa hS (by simp)]
  have := (hB.F v hv hk).nxt q hq (p - t0.wa "gSt" x) (by omega)
  rw [show I.sl v + q * I.δ + (p - t0.wa "gSt" x) = p by omega] at this
  rw [this, hb]
  by_cases h1 : p - t0.wa "gSt" x + 1 = I.lenF v q
  · rw [if_pos h1, if_pos (by omega)]
  · rw [if_neg h1, if_neg (by omega)]

end Live

/-! ## The core's contract -/

/-- What L6 hands to the core: a reduced graph `H` from source `src` in L6's RAM format. -/
structure CoreIn (e : ℕ) (ps : List Stmt) (H : Graph) (src : Fin H.n) (cn cm : ℕ) (t : State ℝ≥0) :
    Prop where
  /-- the procedure table of the program (the spine recurses via `Stmt.call`) -/
  procs : t.procs = ps
  csr : RamBaseCase.CSRAt t H
  graph : RAM.LabRAM.GraphAt t H
  gS : t.w "gS" = src
  gN : t.w "gN" = H.n
  gM : t.w "gM" = H.m
  cnR : t.w "cn" = cn
  cmR : t.w "cm" = cm
  gD : ∀ x : Fin H.n, t.wa "gSt" (x + 1) - t.wa "gSt" x ≤ t.w "gD"
  dd : t.w "gD" ≤ 5 * CostSkeleton.dd cn cm
  sizeN : H.n ≤ 2 * cn
  sizeM : H.m ≤ 2 * cm
  cn_le : cn ≤ cm + 1
  cm_pos : 1 ≤ cm
  cn_pos : 1 ≤ cn
  sorted : ∀ (s' x : Fin H.n), (outL H x).Pairwise (SortedRel H s')
  simple : ∀ x : Fin H.n, ((outL H x).map H.dst).Nodup
  hd : ∀ x : Fin H.n, t.wa "gHd" x = if t.wa "gSt" x = t.wa "gSt" (x + 1) then H.m else t.wa "gSt" x
  nxt : ∀ (x : Fin H.n) (p : ℕ), t.wa "gSt" x ≤ p → p < t.wa "gSt" (x + 1) →
    t.wa "gNxt" p = if p + 1 = t.wa "gSt" (x + 1) then H.m else p + 1
  /-- the live-list arrays are long enough (agent-09's `outRep_init`) -/
  hdLen : H.n ≤ t.wlen "gHd"
  nxtLen : H.m ≤ t.wlen "gNxt"
  cap : (cn + cm + 2) ^ (e + 1) ≤ t.cap
  /-- density on the dispatch branch (`m ≤ n F(n)`): needed by the insert charge `lg δ = O(t)` -/
  dens : CostSkeleton.dd cn cm ≤ GateCCalc.F cn + 1

/-- **The remaining gap**: a C-HD core RAM program `core` with constant `Kc`. -/
def CoreSpec (e : ℕ) (ps : List Stmt) (core : Stmt) (Kc : ℝ) : Prop :=
  ∀ (H : Graph) (src : Fin H.n) (cn cm : ℕ) (t : State ℝ≥0), CoreIn e ps H src cn cm t →
    Runs realOps core t (fun r => CoreOut H src r ∧
      (r.wa "gKeep" = t.wa "gKeep" ∧ r.wlen "gKeep" = t.wlen "gKeep") ∧
      (r.wa "gRep" = t.wa "gRep" ∧ r.wlen "gRep" = t.wlen "gRep") ∧
      r.w "n" = t.w "n" ∧ r.w "s" = t.w "s" ∧ r.w "m" = t.w "m" ∧ r.cap = t.cap ∧
      (r.cost : ℝ) ≤ t.cost + Kc * GateCCalc.Tchd cn cm)

/-! ## The `m = 0` output and the output wrapper -/

def trivialOut : Stmt :=
  seq (walloc "reach" (var "n")) (seq (valloc "dist" (var "n")) (wstore "reach" (var "s") (lit 1)))

theorem trivialOut_runs (G : Graph) (s : Fin G.n) (st : State ℝ≥0) (hm0 : G.m = 0)
    (hn : st.w "n" = G.n) (hs : st.w "s" = s) (hcap : G.n + 2 < st.cap) :
    Runs realOps trivialOut st (fun r => r.Solves G s ∧ r.cost = st.cost + 2 * G.n + 3) := by
  apply wp_sound
  have hsn : (s : ℕ) < G.n := s.2
  simp [trivialOut, wp, hn, hs, fit, show 1 < st.cap by omega, hsn]
  refine ⟨⟨by simp, by simp, fun v => ?_⟩, by ring⟩
  show (if _ = 0 then ⊤ else _) = G.dist s v
  by_cases hv : v = s
  · subst hv; simp
  · have hne : (v : ℕ) ≠ s := fun h => hv (Fin.ext h)
    simp only [State.storeW_wa, State.charge_wa, State.allocV_wa, State.allocW_wa, true_and, hne,
      if_false, if_true]
    symm
    rw [Graph.dist_eq_top_iff]
    rintro ⟨p, hp⟩
    cases hp with
    | nil => exact hv rfl
    | cons _ => rename_i e _ _; have := e.2; omega

/-! ## The body and its specification -/

def chdBody (core : Stmt) : Stmt :=
  ite (eq (var "m") (lit 0)) trivialOut
    (seq (l6Prog (MergeSort.sortRange "gW" "gHead")) (seq core outProg))

theorem deltaF_le_real (n m : ℕ) (hn : 1 ≤ n) :
    ((deltaF n m : ℕ) : ℝ) ≤ 4 * ((m : ℝ) / ((n : ℝ) + 1) + 2) := by
  unfold deltaF
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (((m + m + (n - 1)) / n : ℕ) : ℝ) ≤ 2 * (m : ℝ) / n + 1 := by
    have h2 : ((m + m + (n - 1)) / n : ℕ) * n ≤ m + m + (n - 1) := Nat.div_mul_le_self _ _
    have h3 : (((m + m + (n - 1)) / n : ℕ) : ℝ) * n ≤ 2 * (m : ℝ) + n := by
      have : ((((m + m + (n - 1)) / n) * n : ℕ) : ℝ) ≤ ((m + m + (n - 1) : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      have h4 : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
      linarith
    rw [div_add_one (by positivity), le_div_iff₀ (by positivity)]
    linarith
  have h5 : 2 * (m : ℝ) / n ≤ 4 * ((m : ℝ) / ((n : ℝ) + 1)) := by
    rw [div_le_iff₀ (by positivity)]
    have : 4 * ((m : ℝ) / ((n : ℝ) + 1)) * n = 4 * m * (n / (n + 1)) := by ring
    rw [this]
    have h6 : (1 : ℝ) / 2 ≤ (n : ℝ) / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hm0 : 0 ≤ (m : ℝ) / ((n : ℝ) + 1) := by positivity
  rcases le_total 3 ((m + m + (n - 1)) / n) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; push_cast; linarith

theorem CoreOut.of_eq {H : Graph} {src : Fin H.n} {t t' : State ℝ≥0} (h : CoreOut H src t)
    (h1 : t'.wa "dfin" = t.wa "dfin") (h2 : t'.wlen "dfin" = t.wlen "dfin")
    (h3 : t'.va "dlen" = t.va "dlen") (h4 : t'.vlen "dlen" = t.vlen "dlen") : CoreOut H src t' :=
  ⟨by rw [h2]; exact h.finL, by rw [h4]; exact h.lenL, fun x => by rw [h1, h3]; exact h.exact x⟩

/-- Constant of the body bound. -/
def bodyC (Kc : ℝ) : ℝ := 2 * Kc + 1500

/-- The dispatch-branch density transfers to the core parameters `(min(n, m+1), m)`. -/
theorem dens_cn (n m : ℕ) (hpre : m ≤ n * GateCCalc.F n) (hn : 1 ≤ n) :
    CostSkeleton.dd (min n (m + 1)) m ≤ GateCCalc.F (min n (m + 1)) + 1 := by
  unfold CostSkeleton.dd
  by_cases h : n ≤ m + 1
  · rw [min_eq_left h]
    have : m / n ≤ GateCCalc.F n := Nat.div_le_of_le_mul hpre
    omega
  · rw [min_eq_right (by omega)]
    have : m / (m + 1) = 0 := Nat.div_eq_of_lt (by omega)
    omega

theorem body_spec (e : ℕ) (he : 3 ≤ e) (ps : List Stmt) (core : Stmt) (Kc : ℝ) (hKc : 0 ≤ Kc)
    (hcore : CoreSpec e ps core Kc) :
    Dispatch.BodySpec e ps (chdBody core)
      (fun G => G.m ≤ G.n * GateCCalc.F G.n ∧ 16 ≤ Nat.log 2 G.n)
      (fun n m => bodyC Kc * GateCCalc.Tchd n m) := by
  intro G s st hInit hpre
  have hI := initFacts_of_initLike he hInit
  have hcapE : st.cap = (G.n + G.m + 2) ^ (e + 1) := by
    have := hInit.2.2.2.2.2.2.1
    rw [this]; rfl
  have hn1 : 1 ≤ G.n := by have := s.2; omega
  have hTge := Dispatch.Tchd_ge G.n G.m
  have hTn : (1 : ℝ) ≤ GateCCalc.Tchd G.n G.m := by
    have : (1 : ℝ) ≤ G.n := by exact_mod_cast hn1
    have : (0 : ℝ) ≤ G.m := Nat.cast_nonneg _
    linarith
  have hcap4 := hI.cap
  have hk3 : 27 ≤ (G.n + G.m + 2) ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ (G.n + G.m + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hk4 : (G.n + G.m + 2) ^ 4 = (G.n + G.m + 2) * (G.n + G.m + 2) ^ 3 := by ring
  have hcapB : 8 * (G.n + G.m) + 16 < st.cap := by nlinarith
  unfold chdBody
  have hmev : evalW st (eq (var "m") (lit 0)) = some (if G.m = 0 then 1 else 0) :=
    evalW_eq_of (by rw [evalW_var, hI.m]) (evalW_lit_of (by omega)) (by omega)
  by_cases hm0 : G.m = 0
  · refine runs_ite_true (x := 1) (by rw [hmev, if_pos hm0]) one_ne_zero
      ((trivialOut_runs G s (st.charge 1) hm0 (by simpa using hI.n) (by simpa using hI.sreg)
        (by simp; omega)).mono ?_)
    rintro r ⟨hsol, hc⟩
    refine ⟨hsol, ?_⟩
    rw [hc]
    simp only [State.charge_cost]
    push_cast
    have : (G.n : ℝ) ≤ GateCCalc.Tchd G.n G.m := by
      have : (0 : ℝ) ≤ G.m := Nat.cast_nonneg _; linarith
    unfold bodyC
    nlinarith
  · refine runs_ite_false (by rw [hmev, if_neg hm0]) ?_
    have hIc : InitFacts G s (st.charge 1) :=
      ⟨by simpa using hI.n, by simpa using hI.m, by simpa using hI.sreg,
       fun e he => by simpa using hI.src e he, by simpa using hI.srcL,
       fun e he => by simpa using hI.dst e he, by simpa using hI.dstL,
       fun e he => by simpa using hI.w e he, by simpa using hI.wL, by simpa using hI.cap⟩
    refine runs_seq ((l6_runs G s (st.charge 1) hIc).mono ?_)
    rintro r1 ⟨t0, t, hB, hS, rfl, hU, hcn, hcm, hc1⟩
    set I := L6In.ofGraph G s with hIdef
    have hδ : 3 ≤ I.δ := delta_ge I
    have hsn : I.s < I.n := s.2
    set H := Hgr hB hS hδ with hHdef
    set R := kred hB hS hδ (rfl : I.n = G.n) (rfl : I.m = G.m) (rfl : I.s = s)
      (L6In.ofGraph_src G s) (L6In.ofGraph_dst G s) (L6In.ofGraph_wt G s) hsn with hRdef
    have hoffs : I.off I.s < I.off I.n := L6In.off_lt_of_keep hsn (keep_s I)
    have hsort_w : ∀ x ∉ sortWR, t.w x = t0.w x := hS.U.wreg
    have hNt : t.w "gN" = I.off I.n := by
      rw [hsort_w _ (by simp [sortWR, MergeSort.msRegs])]; exact hB.E.gN
    have hMt : t.w "gM" = I.sl I.n := by
      rw [hsort_w _ (by simp [sortWR, MergeSort.msRegs])]; exact hB.E.gM
    have hDt : t.w "gD" = I.δ := by
      rw [hsort_w _ (by simp [sortWR, MergeSort.msRegs])]; exact hB.E.A.gD
    have hSt : t.w "gS" = I.off I.s := by
      rw [hsort_w _ (by simp [sortWR, MergeSort.msRegs])]; exact hB.gS
    have hcapt : (t.charge 1).cap = (G.n + G.m + 2) ^ (e + 1) := by rw [hU.cap]; simp [hcapE]
    have hprocs : (t.charge 1).procs = ps := by
      rw [hU.procs]; simp only [State.charge_procs]
      rw [hInit.2.2.2.2.2.2.2.2]; rfl
    have hIn : CoreIn e ps H (R.rep s) (min G.n (G.m + 1)) G.m (t.charge 1) := {
      procs := hprocs
      csr := (csrAt hB hS hδ).of_unchanged (Unchanged.charge t 1 [] [] [] []) (by simp)
      graph := ⟨(graphAt hB hS hδ).head, (graphAt hB hS hδ).w⟩
      gS := by
        show t.w "gS" = (if I.off I.s < I.off I.n then I.off I.s else 0)
        rw [if_pos hoffs, hSt]
      gN := hNt
      gM := hMt
      cnR := hcn
      cmR := hcm
      gD := by
        intro x
        show t.wa "gSt" (x + 1) - t.wa "gSt" x ≤ t.w "gD"
        rw [hDt, st_post hB hS hδ, st_post hB hS hδ]
        obtain ⟨v, -, hk, q, hq, -, ha, hb⟩ := st_range_any hB.F hB.stN hδ x.2
        have := L6In.lenF_le hk hδ hq
        omega
      dd := by show t.w "gD" ≤ _; rw [hDt]; exact I.delta_le_dd hn1
      sizeN := I.off_n_le_cn hδ hsn
      sizeM := I.sl_n_le hδ
      cn_le := min_le_right _ _
      cm_pos := by omega
      cn_pos := le_min hn1 (by omega)
      sorted := outL_sorted hB hS hδ
      simple := outL_simple hB hS hδ
      hd := fun x => live_hd hB hS hδ x.2
      nxt := fun x p h1 h2 => live_nxt hB hS hδ x.2 h1 h2
      hdLen := by
        show I.off I.n ≤ (t.charge 1).wlen "gHd"
        rw [State.charge_wlen, (hS.U.warr "gHd" (by simp [sortWR, MergeSort.msRegs])).2, hB.lHd]
      nxtLen := by
        show I.sl I.n ≤ (t.charge 1).wlen "gNxt"
        rw [State.charge_wlen, (hS.U.warr "gNxt" (by simp [sortWR, MergeSort.msRegs])).2, hB.lNxt]
      cap := by
        rw [hcapt]
        exact Nat.pow_le_pow_left (by have := min_le_left G.n (G.m + 1); omega) _
      dens := dens_cn G.n G.m hpre.1 hn1 }
    refine runs_seq ((hcore H (R.rep s) _ _ (t.charge 1) hIn).mono ?_)
    rintro r2 ⟨hout, ⟨hk2a, hk2l⟩, ⟨hr2a, hr2l⟩, hn2, -, -, hcap2, hc2⟩
    have hnt : (t.charge 1).w "n" = G.n := by
      rw [hU.wreg _ (by simp [L6WR, keepWR, paramWR, csortWR, passAWR, bWR, sortWR,
        MergeSort.msRegs])]; simpa using hI.n
    have hr2n : r2.w "n" = G.n := by rw [hn2, hnt]
    have hr2cap : r2.cap = (G.n + G.m + 2) ^ (e + 1) := by rw [hcap2, hcapt]
    have hcap3 : G.n + 2 < r2.cap := by rw [hr2cap]; omega
    unfold outProg
    refine runs_seq (runs_walloc (k := G.n) (by rw [evalW_var, hr2n]) ?_)
    refine runs_seq (runs_valloc (k := G.n) (by simp [hr2n]) ?_)
    refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by simp; omega)) ?_)
    classical
    -- facts about the state t3 before the output loop
    have hkeepT : t.wa "gKeep" = t0.wa "gKeep" := sort_frame_wa hS (by simp)
    have hkeepTL : t.wlen "gKeep" = t0.wlen "gKeep" := (hS.U.warr _ (by simp)).2
    have hrepT : t.wa "gRep" = t0.wa "gRep" := sort_frame_wa hS (by simp)
    have hrepTL : t.wlen "gRep" = t0.wlen "gRep" := (hS.U.warr _ (by simp)).2
    refine (outLoop_runs R _ (by simp [hr2n]) (by simp) ?_ ?_ ?_ ?_ ?_ (by simp) (by simp)
      (fun u => by simp) (fun u => by simp) (by simp; omega)).mono ?_
    · -- gKeep length
      simp [hk2l, hkeepTL]
      have := hB.E.A.keep.1; simp at this; exact this
    · -- gKeep values
      intro v
      simp [hk2a, hkeepT]
      have := hB.E.A.keep.2 v v.2; simp at this
      rw [this]; rfl
    · -- gRep length
      simp [hr2l, hrepTL, hB.lRep]
      exact le_rfl
    · -- gRep values
      intro v hv
      simp [hr2a, hrepT]
      have hvn : (v : ℕ) < I.n := v.2
      have hv' : I.keep v ≠ 0 := hv
      rw [(hB.F v hvn hv').rep]
      show I.off v = (if I.off v < I.off I.n then I.off v else 0)
      rw [if_pos (L6In.off_lt_of_keep hvn hv')]
    · -- the label table survives the allocations
      exact hout.of_eq (by funext j; simp) (by simp) (by funext j; simp) (by simp)
    · rintro _ ⟨t', hO, rfl⟩
      have hcore3 : CoreOut H (R.rep s)
          ((((((r2.allocW "reach" G.n).charge (G.n + 1)).allocV "dist" G.n realOps.zero).charge
            (G.n + 1)).setW "g_v" 0).charge 1) :=
        hout.of_eq (by funext j; simp) (by simp) (by funext j; simp) (by simp)
      refine ⟨solves_of_oinv R hcore3 hO, ?_⟩
      -- cost
      have hoc := hO.c
      simp only [State.charge_cost, State.setW_cost, State.allocV_cost, State.allocW_cost] at hoc ⊢
      have hT1 := GateCCalc.Tchd_cn_le G.n G.m
      have hsize : I.off I.n + I.sl I.n ≤ 2 * (G.n + G.m) := by
        have h1 := I.off_n_le_cn hδ hsn
        have h2 := I.sl_n_le hδ
        have h3 := min_le_left G.n (G.m + 1)
        show I.off I.n + I.sl I.n ≤ 2 * (I.n + I.m)
        omega
      have hlog := GateCCalc.nm_log_le G.n G.m I.δ hn1 (by omega) (deltaF_le_real G.n G.m hn1)
      have hc1R : ((t.charge 1).cost : ℝ) ≤ (st.cost : ℝ) + 1 + 60 * ((G.n : ℝ) + G.m) +
          80 * ((I.off I.n + I.sl I.n : ℕ) : ℝ) * ((Nat.log 2 I.δ : ℝ) + 1) + 100 := by
        have h0 := hc1
        change (t.charge 1).cost ≤ (st.charge 1).cost + 60 * (G.n + G.m) +
          80 * (I.off I.n + I.sl I.n) * (Nat.log 2 I.δ + 1) + 100 at h0
        simp only [State.charge_cost] at h0 ⊢
        have h := (Nat.cast_le (α := ℝ)).mpr h0
        push_cast at h ⊢; linarith
      have hsizeR : ((I.off I.n + I.sl I.n : ℕ) : ℝ) * ((Nat.log 2 I.δ : ℝ) + 1) ≤
          2 * (((G.n + G.m : ℕ) : ℝ) * ((Nat.log 2 I.δ : ℝ) + 1)) := by
        have h1 : ((I.off I.n + I.sl I.n : ℕ) : ℝ) ≤ 2 * ((G.n + G.m : ℕ) : ℝ) := by exact_mod_cast hsize
        have h2 : (0 : ℝ) ≤ (Nat.log 2 I.δ : ℝ) + 1 := by positivity
        nlinarith
      have hocR : (t'.cost : ℝ) ≤ (r2.cost : ℝ) + (G.n + 1) + (G.n + 1) + 1 + 9 * G.n := by
        have h := (Nat.cast_le (α := ℝ)).mpr hoc; push_cast at h; linarith
      have hnT : (G.n : ℝ) ≤ GateCCalc.Tchd G.n G.m := by
        have : (0 : ℝ) ≤ G.m := Nat.cast_nonneg _; linarith
      have hKT : Kc * GateCCalc.Tchd (min G.n (G.m + 1)) G.m ≤ Kc * (2 * GateCCalc.Tchd G.n G.m) :=
        mul_le_mul_of_nonneg_left hT1 hKc
      have hc2' : (r2.cost : ℝ) ≤ ((t.charge 1).cost : ℝ) + Kc * GateCCalc.Tchd (min G.n (G.m + 1)) G.m :=
        hc2
      push_cast at hlog hsizeR hc1R ⊢
      unfold bodyC
      linarith


/-! ## The reduction of `CHDTarget F` to `CoreSpec` -/

/-- **Gate-C reduction (NON-GATE until `CoreSpec` is proved for a concrete core):** a C-HD core RAM
program satisfying `CoreSpec` yields `CHDTarget F`. -/
theorem chdTarget_of_core (e : ℕ) (he : 3 ≤ e) (ps : List Stmt) (core : Stmt) (Kc : ℝ) (hKc : 0 ≤ Kc)
    (hcore : CoreSpec e ps core Kc) : GateCTarget.CHDTarget GateCCalc.F :=
  Dispatch.chdTarget_of_body e he ps (chdBody core) (bodyC Kc) (by unfold bodyC; linarith)
    (body_spec e he ps core Kc hKc hcore)

end Frontier.CHD.L6

#print axioms Frontier.CHD.L6.body_spec
#print axioms Frontier.CHD.L6.chdTarget_of_core
