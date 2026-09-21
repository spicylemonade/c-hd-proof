import Frontier.CHD.WinScanB

/-!
# WinScanC — the RAM scan over a row of vertices (BM.19–21 and BM.27–28; agent-02, NON-GATE)

`scanLoop lenE elemE startE` runs, for every vertex `u` of a row (length `lenE`, `i`-th element
`elemE`), the inner window loop `winInner` from the start slot `startE` of `u` (the pointer
`sp.ptr[u]` for BM.19–21, the range head `gSt[u]` for BM.27–28) and stores the stop slot back into
`sp.ptr[u]`.  Its spec (`scanLoop_spec`): the machine ends in a state representing
`(xs.flatMap (fun u => slots (P0 u) (Q u))).foldl (relaxInsCc dlOps T B (some Bi)) fs0`, where
`Q u` is the first slot `≥ P0 u` of `u` whose candidate is not below `B` (or the range end), and
`sp.ptr[u] = Q u`.  The RAM cost is `≤ 124 ×` the Layer-A cost plus `38` per vertex.

`winScan` is agent-08's `windowScan (candB Kb kbf "sp.lt") (relaxInsRAM Kb kbf Klo klof)` text.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DIns Frontier.CHD.RelaxIns Frontier.CHD.RamBaseCase WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- `(lvl - 1) * n + e` (child row; agent-08's `RamSpine.chr`). -/
def chr (e : WExpr) : WExpr := add (mul (sub (var "lvl") (lit 1)) (var "n")) e

/-- The scan over a row of vertices. -/
def scanLoop (lenE elemE startE : WExpr) (Kb : LReg) (kbf : String) (Klo : LReg)
    (klof : String) : Stmt :=
  seq (wset "sp.i" (lit 0))
  (.while (lt (var "sp.i") lenE)
     (seq (wset "ru" elemE)
     (seq (wset "sp.p" startE)
     (seq (wset "sp.pe" (load "gSt" (add (var "ru") (lit 1))))
     (seq (wset "sp.go" (lit 1))
     (seq (winInner Kb kbf Klo klof)
     (seq (wstore "sp.ptr" (var "ru") (var "sp.p"))
          (wset "sp.i" (add (var "sp.i") (lit 1))))))))))

/-- **BM.19–21**: the window scan of the child's `U` row from the pointers `sp.ptr`. -/
def winScan (Kb : LReg) (kbf : String) (Klo : LReg) (klof : String) : Stmt :=
  scanLoop (load "U.len" (sub (var "lvl") (lit 1))) (load "U" (chr (var "sp.i")))
    (load "sp.ptr" (var "ru")) Kb kbf Klo klof

/-- Registers written by the scan. -/
def scanW : List String := innerW ++ ["ru", "sp.pe", "sp.i"]

/-- The frame of the scan. -/
def FrameW (st r : State ℝ≥0) : Prop :=
  Unchanged st r (labW ++ insWA ++ ["sp.ptr"]) (labV ++ [entA.l]) scanW riV

/-- `q` is where the scan of `u` from `p0` stops at the bound `B` (label `du` of `u`). -/
def ScanStop (st : State ℝ≥0) (du : WLab G s) (u : Fin G.n) (p0 q : ℕ) (B : WLab G s) : Prop :=
  p0 ≤ q ∧ q ≤ st.wa "gSt" ((u : ℕ) + 1) ∧
  (∀ j (hj : j < G.m), p0 ≤ j → j < q → ext du ⟨j, hj⟩ < B) ∧
  (∀ hq : q < G.m, q < st.wa "gSt" ((u : ℕ) + 1) → ¬ ext du ⟨q, hq⟩ < B)

section Gen
variable {V : Type} {ops : VOps V}

/-- `arr[i] := e` with the successor state kept abstract. -/
theorem runs_wstore_val {arr : String} {i e : WExpr} {s : State V} {Q : State V → Prop}
    {j a : ℕ} (hi : evalW s i = some j) (he : evalW s e = some a) (hj : j < s.wlen arr)
    (hQ : ∀ r, (∀ k, r.wa arr k = if k = j then a else s.wa arr k) →
      Unchanged s r [arr] [] [] [] → r.wlen arr = s.wlen arr → r.cost = s.cost + 1 → Q r) :
    Runs ops (.wstore arr i e) s Q :=
  runs_wstore hi he hj (hQ _ (fun k => by simp [State.charge, State.storeW])
    ((unch_charge 1).mpr ((unch_storeW (List.mem_singleton_self _) j a).mpr
      (Unchanged.refl _ _ _ _ _))) rfl rfl)

theorem evalW_sub_of' {s : State V} {a b : WExpr} {x y : ℕ} (ha : evalW s a = some x)
    (hb : evalW s b = some y) : evalW s (.sub a b) = some (x - y) := by
  simp [evalW, ha, hb]

theorem evalW_mul_of' {s : State V} {a b : WExpr} {x y : ℕ} (ha : evalW s a = some x)
    (hb : evalW s b = some y) (hc : x * y < s.cap) : evalW s (.mul a b) = some (x * y) := by
  simp [evalW, ha, hb, fit, hc]

end Gen

theorem slots_length {a : ℕ} : ∀ {b : ℕ}, b ≤ G.m → (slots G a b).length = b - a
  | 0, _ => by simp [slots]
  | b + 1, hb => by
    by_cases hab : a ≤ b
    · rw [slots_succ hab (by omega), List.length_append, slots_length (by omega)]
      simp only [List.length_singleton]; omega
    · have : b + 1 - a = 0 := by omega
      simp [slots, this]

theorem flatSlots_mem {st : State ℝ≥0} (hcsr : CSRAt st G) {xs : List (Fin G.n)}
    {P0 Q : Fin G.n → ℕ} (h : ∀ u ∈ xs, st.wa "gSt" u ≤ P0 u ∧ Q u ≤ st.wa "gSt" ((u : ℕ) + 1))
    (e : Fin G.m) :
    e ∈ xs.flatMap (fun u => slots G (P0 u) (Q u)) ↔
      G.src e ∈ xs ∧ P0 (G.src e) ≤ e ∧ (e : ℕ) < Q (G.src e) := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨u, hu, he⟩
    rw [mem_slots] at he
    have hs : G.src e = u :=
      (hcsr.src e u).mpr ⟨le_trans (h u hu).1 he.1, lt_of_lt_of_le he.2 (h u hu).2⟩
    subst hs
    exact ⟨hu, he⟩
  · rintro ⟨hu, h1, h2⟩
    exact ⟨G.src e, hu, mem_slots.mpr ⟨h1, h2⟩⟩

theorem flatSlots_nodup {st : State ℝ≥0} (hcsr : CSRAt st G) {xs : List (Fin G.n)}
    (hxs : xs.Nodup) {P0 Q : Fin G.n → ℕ}
    (h : ∀ u ∈ xs, st.wa "gSt" u ≤ P0 u ∧ Q u ≤ st.wa "gSt" ((u : ℕ) + 1)) :
    (xs.flatMap (fun u => slots G (P0 u) (Q u))).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun u _ => slots_nodup _ _, ?_⟩
  refine List.Pairwise.imp_of_mem (fun {u w} hu hw huw => ?_) hxs
  intro e he he'
  rw [mem_slots] at he he'
  have h1 : G.src e = u :=
    (hcsr.src e u).mpr ⟨le_trans (h u hu).1 he.1, lt_of_lt_of_le he.2 (h u hu).2⟩
  have h2 : G.src e = w :=
    (hcsr.src e w).mpr ⟨le_trans (h w hw).1 he'.1, lt_of_lt_of_le he'.2 (h w hw).2⟩
  exact huw (h1.symm.trans h2)

/-- Steps that write registers and arrays outside the label table, `D`, and the graph keep the
representation. -/
theorem Reps.of_arrs {c0 bcap ecap lv bse : ℕ} {B Bi : WLab G s} {Kb : LReg} {kbf : String}
    {Klo : LReg} {klof : String} {r r' : State ℝ≥0} {fs : BM.RSt G s}
    {H' : Fin G.n → ℕ → List (Fin G.m)} {wa va wr vr : List String}
    (h : Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r fs H') (hu : Unchanged r r' wa va wr vr)
    (hc : r.cost ≤ r'.cost) (hK : ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof] ++
      ["lab.uselo", "ds.lv", "ds.b", "ds.fresh"], a ∉ wr) (hKl : Kb.l ∉ vr ∧ Klo.l ∉ vr)
    (hwl : ∀ a ∈ labW, a ∉ wa) (hvl : "dlen" ∉ va) (hwd : ∀ a ∈ wa, a ∉ dW)
    (hvd : ∀ a ∈ va, a ∉ dV) (hg1 : "gHead" ∉ wa) (hg2 : "gW" ∉ va) (hg3 : "gSt" ∉ wa) :
    Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r' fs H' := by
  have hvc : vc (G := G) r' = vc r := vc_of_unchanged hu (hwl _ (by decide))
  have hm : ∀ a, a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof] ++
      ["lab.uselo", "ds.lv", "ds.b", "ds.fresh"] → a ∉ wr := hK
  refine ⟨h.lab.of_unchanged hu hwl hvl hc, ?_, h.ba.of_unchanged hu hwd hvd, ?_,
    PoolRep.of_unchanged h.pool hu hwd hvd (hm _ (by simp)), h.inv, h.bd, h.wk,
    graphAt_of_unchanged hu hg1 hg2 h.gr, CSRAt.of_unchanged h.csr hu hg3, ?_, ?_,
    by rw [hu.wreg _ (hm _ (by simp))]; exact h.uselo,
    by rw [hu.wreg _ (hm _ (by simp))]; exact h.dslv,
    by rw [hu.wreg _ (hm _ (by simp))]; exact h.dsb⟩
  · rw [hvc]; exact h.dr.of_unchanged hu hwd hvd
  · rw [hvc]; exact h.live.of_unchanged hu hwd hvd
  · rw [hvc]
    exact h.kb.of_unchanged hu (fun a ha => hm a (by simp [ha])) hKl.1 (hm _ (by simp))
  · rw [hvc]
    exact h.klo.of_unchanged hu (fun a ha => hm a (by simp [ha])) hKl.2 (hm _ (by simp))

open Classical in
/-- **The scan over a row of vertices.** -/
theorem scanLoop_spec (T : ℕ) {c0 bcap ecap lv bse : ℕ} {B Bi : WLab G s} {Kb : LReg}
    {kbf : String} {Klo : LReg} {klof : String} (hy : BlkHyg Kb kbf Klo klof)
    (hl : LoopHyg Kb kbf Klo klof) (hli : ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof], a ≠ "sp.i")
    (lenE elemE startE : WExpr) (st : State ℝ≥0) (fs0 : BM.RSt G s)
    (H0 : Fin G.n → ℕ → List (Fin G.m))
    (h0 : Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof st fs0 H0)
    (xs : List (Fin G.n)) (hxs : xs.Nodup) (P0 : Fin G.n → ℕ)
    (hlenE : ∀ r, FrameW st r → evalW r lenE = some xs.length)
    (helemE : ∀ r (i : ℕ) (hi : i < xs.length), FrameW st r → r.w "sp.i" = i →
      evalW r elemE = some (xs[i] : ℕ))
    (hstartE : ∀ r (u : Fin G.n), FrameW st r → r.wlen "sp.ptr" = st.wlen "sp.ptr" →
      r.w "ru" = u → r.wa "sp.ptr" u = st.wa "sp.ptr" u → evalW r startE = some (P0 u))
    (hP0 : ∀ u ∈ xs, st.wa "gSt" u ≤ P0 u ∧ P0 u ≤ st.wa "gSt" ((u : ℕ) + 1))
    (hcomp : ∀ u ∈ xs, fs0.d u = dis (s := s) u ∧ fs0.d u ≠ ⊤)
    (hptrl : G.n ≤ st.wlen "sp.ptr") (hncap : G.n + 2 ≤ st.cap)
    (hfr : fs0.g.fresh + G.m + 1 < ecap)
    (hcapD : 2 * fs0.Dc.blocks.length + ecap + bse + 4 < st.cap)
    (hB : st.cost + (xs.length + 1) * ((G.m + 1) * CE fs0.Dc.blocks.length + 101) ≤
      c0 + st.cap)
    (hm : G.m + 2 ≤ st.cap) :
    Runs realOps (scanLoop lenE elemE startE Kb kbf Klo klof) st (fun r => ∃ (H' : Fin G.n → ℕ → List (Fin G.m)) (Q : Fin G.n → ℕ),
      (∀ u ∈ xs, ScanStop st (fs0.d u) u (P0 u) (Q u) B ∧ r.wa "sp.ptr" u = Q u) ∧
      (∀ u : Fin G.n, u ∉ xs → r.wa "sp.ptr" u = st.wa "sp.ptr" u) ∧
      r.wlen "sp.ptr" = st.wlen "sp.ptr" ∧
      HExt H0 (vc st) H' (vc r) ∧
      Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r
        ((xs.flatMap (fun u => slots G (P0 u) (Q u))).foldl
          (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0) H' ∧
      FrameW st r ∧ st.cost ≤ r.cost ∧
      r.cost + 124 * fs0.c ≤ st.cost + 124 * ((xs.flatMap (fun u => slots G (P0 u) (Q u))).foldl
          (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0).c + 38 * xs.length + 2) := by
  set nb := fs0.Dc.blocks.length with hnb
  set Y := (G.m + 1) * CE nb with hY
  have hCE : 214 ≤ CE nb := by unfold CE; omega
  have h1c : 1 < st.cap := by omega
  have hxl : xs.length ≤ G.n := by
    have := hxs.length_le_card; rwa [Fintype.card_fin] at this
  have hfix : ∀ a ∈ ["lab.uselo", "ds.lv", "ds.b", "ds.fresh"],
      a ∉ winW ++ ["ru", "sp.pe", "sp.i"] := by decide
  have hK : ∀ {wr : List String}, (∀ a ∈ wr, a ∈ winW ++ ["ru", "sp.pe", "sp.i"]) →
      ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof] ++ ["lab.uselo", "ds.lv", "ds.b", "ds.fresh"],
        a ∉ wr := by
    intro wr hwr a ha haw
    have hw := hwr a haw
    rw [List.mem_append] at ha
    rcases ha with ha | ha
    · have h2 := hl.w a ha
      have h3 := hli a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw h2
      tauto
    · exact hfix a ha hw
  have hKn : Kb.l ∉ ([] : List String) ∧ Klo.l ∉ ([] : List String) := ⟨by simp, by simp⟩
  have toF : ∀ {a b : State ℝ≥0} {wa va wr vr : List String}, Unchanged a b wa va wr vr →
      (∀ x ∈ wa, x ∈ labW ++ insWA ++ ["sp.ptr"]) → (∀ x ∈ va, x ∈ labV ++ [entA.l]) →
      (∀ x ∈ wr, x ∈ scanW) → (∀ x ∈ vr, x ∈ riV) →
      Unchanged a b (labW ++ insWA ++ ["sp.ptr"]) (labV ++ [entA.l]) scanW riV :=
    fun h h1 h2 h3 h4 => h.mono (by intro x hx; exact h1 x hx) (by intro x hx; exact h2 x hx)
      (by intro x hx; exact h3 x hx) (by intro x hx; exact h4 x hx)
  -- the loop invariant after `k` vertices
  let I : ℕ → State ℝ≥0 → Prop := fun k r => ∃ (H' : Fin G.n → ℕ → List (Fin G.m))
    (Q : Fin G.n → ℕ),
    r.w "sp.i" = k ∧ FrameW st r ∧ r.wlen "sp.ptr" = st.wlen "sp.ptr" ∧
    (∀ u ∈ xs.take k, ScanStop st (fs0.d u) u (P0 u) (Q u) B ∧ r.wa "sp.ptr" u = Q u) ∧
    (∀ u : Fin G.n, u ∉ xs.take k → r.wa "sp.ptr" u = st.wa "sp.ptr" u) ∧
    HExt H0 (vc st) H' (vc r) ∧
    Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r
      (((xs.take k).flatMap (fun u => slots G (P0 u) (Q u))).foldl
        (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0) H' ∧
    st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 1 + k * (Y + 38) ∧
    r.cost + 124 * fs0.c ≤ st.cost + 124 * (((xs.take k).flatMap
      (fun u => slots G (P0 u) (Q u))).foldl (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0).c
      + 38 * k + 1
  apply runs_seq
  refine runs_wset_val (evalW_lit_of (by omega)) (fun r0 hi0 hU0 hc0 => ?_)
  refine runs_while I xs.length _ (fun k hk r hI => ?_) (fun r hI => ?_) r0 ?_
  · -- one vertex
    obtain ⟨H', Q, hik, hFW, hwl, hdone, hrest, hE, hR, hclo, hchi, hrel⟩ := hI
    have hux : xs[k] ∈ xs := List.getElem_mem hk
    set u : Fin G.n := xs[k] with hu
    have hunt : u ∉ xs.take k := by
      intro hm'
      rw [List.mem_take_iff_getElem] at hm'
      obtain ⟨j, hj, hjk⟩ := hm'
      have := (List.Nodup.getElem_inj_iff hxs).mp hjk
      omega
    have hcapr : r.cap = st.cap := Unchanged.cap hFW
    set Lk := (xs.take k).flatMap (fun w => slots G (P0 w) (Q w)) with hLk
    set fsk := Lk.foldl (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0 with hfsk
    obtain ⟨-, -, -, hnbk, hstab⟩ :=
      foldl_invs (T := T) (B := B) (lo := some Bi) Lk fs0 h0.wk h0.inv h0.bd
    have hdu : fsk.d u = fs0.d u := hstab u (hcomp u hux).1
    have hbnd : ∀ w ∈ xs.take k, st.wa "gSt" w ≤ P0 w ∧ Q w ≤ st.wa "gSt" ((w : ℕ) + 1) :=
      fun w hw => ⟨(hP0 w (List.mem_of_mem_take hw)).1, (hdone w hw).1.2.1⟩
    have hLnd : Lk.Nodup := flatSlots_nodup h0.csr (hxs.sublist (List.take_sublist k xs)) hbnd
    have hLsrc : ∀ e ∈ Lk, G.src e ∈ xs.take k :=
      fun e he => ((flatSlots_mem h0.csr hbnd e).mp he).1
    have hpeM : st.wa "gSt" ((u : ℕ) + 1) ≤ G.m := h0.csr.le_m u
    have hLlen : Lk.length + (st.wa "gSt" ((u : ℕ) + 1) - P0 u) ≤ G.m := by
      have hnd : (Lk ++ slots G (P0 u) (st.wa "gSt" ((u : ℕ) + 1))).Nodup := by
        rw [List.nodup_append]
        refine ⟨hLnd, slots_nodup _ _, fun a ha b hb hab => ?_⟩
        subst hab
        have h1 := hLsrc a ha
        rw [mem_slots] at hb
        have h2 : G.src a = u := (h0.csr.src a u).mpr ⟨le_trans (hP0 u hux).1 hb.1, hb.2⟩
        rw [h2] at h1
        exact hunt h1
      have := hnd.length_le_card
      rw [List.length_append, slots_length hpeM, Fintype.card_fin] at this
      exact this
    have hfrk : fsk.g.fresh ≤ fs0.g.fresh + Lk.length :=
      foldl_fresh_le (T := T) (B := B) (lo := some Bi) Lk fs0
    have hcc : (r.charge 1).cost = r.cost + 1 := rfl
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of (s := r) (x := k) (y := xs.length)
        (by rw [evalW_var]; exact congrArg some hik) (hlenE r hFW) (by omega), if_pos hk]
    have hFW0 : FrameW st (r.charge 1) := (unch_charge 1).mpr hFW
    have hR0 : Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof (r.charge 1) fsk H' :=
      hR.of_regs (Unchanged.charge r 1 [] [] [] []) (by omega) (hK (by simp)) hKn
    -- `ru := U[i]`
    apply runs_seq
    refine runs_wset_val (helemE (r.charge 1) k hk hFW0 hik) (fun r1 hru1 hU1 hc1 => ?_)
    have hFW1 : FrameW st r1 :=
      Unchanged.trans hFW0 (toF hU1 (by simp) (by simp) (by decide) (by simp))
    have hp1 := hU1.warr "sp.ptr" (by simp)
    have hR1 := hR0.of_regs hU1 (by omega) (hK (by decide)) hKn
    -- `sp.p := start`
    apply runs_seq
    refine runs_wset_val (hstartE r1 u hFW1 (by rw [hp1.2]; exact hwl) hru1
      (by rw [hp1.1]; exact hrest u hunt)) (fun r2 hp2 hU2 hc2 => ?_)
    have hFW2 : FrameW st r2 :=
      Unchanged.trans hFW1 (toF hU2 (by simp) (by simp) (by decide) (by simp))
    have hR2 := hR1.of_regs hU2 (by omega) (hK (by decide)) hKn
    have hg2 := Unchanged.warr hFW2 "gSt" (by decide)
    have hru2 : r2.w "ru" = u := by rw [hU2.wreg "ru" (by decide)]; exact hru1
    have hcap2 : r2.cap = st.cap := Unchanged.cap hFW2
    have hulen : (u : ℕ) + 1 < r2.wlen "gSt" := by
      rw [hg2.2]; have := h0.csr.len; have := u.isLt; omega
    -- `sp.pe := gSt[ru + 1]`
    apply runs_seq
    refine runs_wset_val (a := st.wa "gSt" ((u : ℕ) + 1)) ?_ (fun r3 hpe3 hU3 hc3 => ?_)
    · have := u.isLt
      rw [evalW_load_of (evalW_add_of (x := (u : ℕ)) (y := 1)
        (by rw [evalW_var]; exact congrArg some hru2) (evalW_lit_of (by omega)) (by omega)) hulen,
        hg2.1]
    have hFW3 : FrameW st r3 :=
      Unchanged.trans hFW2 (toF hU3 (by simp) (by simp) (by decide) (by simp))
    have hR3 := hR2.of_regs hU3 (by omega) (hK (by decide)) hKn
    have hcap3 : r3.cap = st.cap := Unchanged.cap hFW3
    -- `sp.go := 1`
    apply runs_seq
    refine runs_wset_val (evalW_lit_of (by omega)) (fun r4 hgo4 hU4 hc4 => ?_)
    have hFW4 : FrameW st r4 :=
      Unchanged.trans hFW3 (toF hU4 (by simp) (by simp) (by decide) (by simp))
    have hR4 := hR3.of_regs hU4 (by omega) (hK (by decide)) hKn
    have hcap4 : r4.cap = st.cap := Unchanged.cap hFW4
    have hg4 := Unchanged.warr hFW4 "gSt" (by decide)
    have hp4 : r4.w "sp.p" = P0 u := by
      rw [hU4.wreg "sp.p" (by decide), hU3.wreg "sp.p" (by decide)]; exact hp2
    have hpe4 : r4.w "sp.pe" = st.wa "gSt" ((u : ℕ) + 1) := by
      rw [hU4.wreg "sp.pe" (by decide)]; exact hpe3
    have hru4 : r4.w "ru" = u := by
      rw [hU4.wreg "ru" (by decide), hU3.wreg "ru" (by decide)]; exact hru2
    have hwa4 : r4.wa "sp.ptr" = r.wa "sp.ptr" := by
      rw [(hU4.warr "sp.ptr" (by simp)).1, (hU3.warr "sp.ptr" (by simp)).1,
        (hU2.warr "sp.ptr" (by simp)).1, hp1.1]; rfl
    have hwl4 : r4.wlen "sp.ptr" = st.wlen "sp.ptr" := by
      rw [(hU4.warr "sp.ptr" (by simp)).2, (hU3.warr "sp.ptr" (by simp)).2,
        (hU2.warr "sp.ptr" (by simp)).2, hp1.2]; exact hwl
    have hvc4 : vc (G := G) r4 = vc r :=
      (vc_of_unchanged hU4 (by simp)).trans ((vc_of_unchanged hU3 (by simp)).trans
        ((vc_of_unchanged hU2 (by simp)).trans ((vc_of_unchanged hU1 (by simp)).trans rfl)))
    have hc4' : r4.cost = r.cost + 5 := by omega
    -- the inner window loop of `u`
    have f1 : (k + 2) * (Y + 101) ≤ (xs.length + 1) * (Y + 101) :=
      Nat.mul_le_mul_right _ (by omega)
    have f2 : (k + 2) * (Y + 101) = k * (Y + 38) + 63 * k + 2 * Y + 202 := by ring
    have f3 : (st.wa "gSt" ((u : ℕ) + 1) - P0 u + 1) * CE nb ≤ Y :=
      Nat.mul_le_mul_right _ (by omega)
    apply runs_seq
    refine (winInner_spec T hy hl r4 fsk H' hR4 u (hdu.trans (hcomp u hux).1)
      (by rw [hdu]; exact (hcomp u hux).2) (P0 u) (st.wa "gSt" ((u : ℕ) + 1)) hp4 hpe4 hgo4
      hru4 ⟨by rw [hg4.1]; exact (hP0 u hux).1, (hP0 u hux).2, by rw [hg4.1]⟩ (by omega)
      (by rw [hnbk, hcap4]; exact hcapD) (by rw [hnbk, hcap4, ← hnb]; omega)
      (by rw [hcap4]; exact hm)).mono ?_
    rintro r5 ⟨q, H'', hq0, hqe, hp5, hwin5, hstop5, hE5, hR5, hru5, hpe5, hU5, hc5lo, hc5hi,
      hc5rel⟩
    rw [hnbk, ← hnb] at hc5hi
    have hptr5 := hU5.warr "sp.ptr" (by decide)
    have hcap5 : r5.cap = st.cap := hU5.cap.trans hcap4
    -- `sp.ptr[ru] := sp.p`
    apply runs_seq
    refine runs_wstore_val (j := (u : ℕ)) (a := q) (by rw [evalW_var]; exact congrArg some hru5)
      (by rw [evalW_var]; exact congrArg some hp5)
      (by rw [hptr5.2, hwl4]; have := u.isLt; omega) (fun r6 hst6 hU6 hwl6 hc6 => ?_)
    have hi6 : r6.w "sp.i" = k := by
      rw [hU6.wreg "sp.i" (by simp), hU5.wreg "sp.i" (by decide), hU4.wreg "sp.i" (by decide),
        hU3.wreg "sp.i" (by decide), hU2.wreg "sp.i" (by decide), hU1.wreg "sp.i" (by decide)]
      exact hik
    have hcap6 : r6.cap = st.cap := hU6.cap.trans hcap5
    -- `sp.i := sp.i + 1`
    refine runs_wset_val (evalW_add_of (x := k) (y := 1)
      (by rw [evalW_var]; exact congrArg some hi6) (evalW_lit_of (by omega)) (by omega))
      (fun r7 hi7 hU7 hc7 => ?_)
    have hwa7 : ∀ w : ℕ, r7.wa "sp.ptr" w = if w = u then q else r.wa "sp.ptr" w := by
      intro w
      rw [(hU7.warr "sp.ptr" (by simp)).1, hst6, hptr5.1, hwa4]
    have hvc7 : vc (G := G) r7 = vc r5 :=
      (vc_of_unchanged hU7 (by simp)).trans (vc_of_unchanged hU6 (by decide))
    have hL' : (xs.take (k + 1)).flatMap (fun w => slots G (P0 w) (Function.update Q u q w)) =
        Lk ++ slots G (P0 u) q := by
      rw [← List.take_append_getElem hk, List.flatMap_append, List.flatMap_singleton,
        Function.update_self]
      congr 1
      exact List.flatMap_congr (fun w hw => by
        have hwu : w ≠ u := fun h => hunt (h ▸ hw)
        rw [Function.update_of_ne hwu])
    have f4 : (q - P0 u) * CE nb ≤ Y := Nat.mul_le_mul_right _ (by omega)
    have f5 : (k + 1) * (Y + 38) = k * (Y + 38) + Y + 38 := by ring
    refine ⟨H'', Function.update Q u q, hi7, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, ?_⟩
    · exact Unchanged.trans hFW4 (Unchanged.trans
        (toF hU5 (fun x hx => List.mem_append_left _ hx) (fun x hx => hx)
          (fun x hx => List.mem_append_left _ hx) (fun x hx => hx))
        (Unchanged.trans (toF hU6 (by simp) (by simp) (by simp) (by simp))
          (toF hU7 (by simp) (by simp) (by decide) (by simp))))
    · rw [(hU7.warr "sp.ptr" (by simp)).2, hwl6, hptr5.2, hwl4]
    · intro w hw
      rw [← List.take_append_getElem hk, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw
      · have hwu : w ≠ u := fun h => hunt (h ▸ hw)
        have hwu' : (w : ℕ) ≠ u := fun h => hwu (Fin.ext h)
        rw [Function.update_of_ne hwu, hwa7, if_neg hwu']
        exact hdone w hw
      · subst hw
        rw [Function.update_self, hwa7, if_pos rfl]
        refine ⟨⟨hq0, hqe, fun j hj h1 h2 => ?_, fun hq hqlt => ?_⟩, rfl⟩
        · have := hwin5 j hj h1 h2; rwa [hdu] at this
        · obtain ⟨hq', h⟩ := hstop5 hqlt
          rw [hdu] at h; exact h
    · intro w hw
      rw [← List.take_append_getElem hk, List.mem_append, List.mem_singleton, not_or] at hw
      have hwu' : (w : ℕ) ≠ u := fun h => hw.2 (Fin.ext h)
      rw [hwa7, if_neg hwu']
      exact hrest w hw.1
    · rw [hvc7]
      exact hE.trans (by rw [← hvc4]; exact hE5)
    · rw [hL', List.foldl_append]
      exact hR5.of_arrs (hU6.comp hU7) (by omega) (hK (by decide)) ⟨by simp, by simp⟩
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [hL', List.foldl_append, ← hfsk]
      omega
  · -- exit
    obtain ⟨H', Q, hik, hFW, hwl, hdone, hrest, hE, hR, hclo, hchi, hrel⟩ := hI
    rw [List.take_length] at hdone hrest hR hrel
    have hcapr : r.cap = st.cap := Unchanged.cap hFW
    refine ⟨by rw [evalW_lt_of (s := r) (x := xs.length) (y := xs.length)
        (by rw [evalW_var]; exact congrArg some hik) (hlenE r hFW) (by omega),
        if_neg (lt_irrefl _)], H', Q, hdone, hrest, hwl, hE,
      hR.of_regs (Unchanged.charge r 1 [] [] [] []) (by simp) (hK (by simp)) hKn,
      (unch_charge 1).mpr hFW, by simp; omega, by simp; omega⟩
  · -- the start
    have hp0 := hU0.warr "sp.ptr" (by simp)
    refine ⟨H0, fun _ => 0, hi0, toF hU0 (by simp) (by simp) (by decide) (by simp), hp0.2,
      fun u hu => by simp at hu, fun u _ => by rw [hp0.1], ?_, ?_, by omega,
      by rw [zero_mul]; omega, ?_⟩
    · rw [vc_of_unchanged hU0 (by simp)]; exact HExt.refl _ _
    · simp only [List.take_zero, List.flatMap_nil, List.foldl_nil]
      exact h0.of_regs hU0 (by omega) (hK (by decide)) hKn
    · simp only [List.take_zero, List.flatMap_nil, List.foldl_nil]; omega

/-- CSR ranges are sorted by candidate (`CoreIn.sorted`, positional form). -/
def CSRSorted (G : Graph) (s : Fin G.n) : Prop :=
  ∀ j j' : Fin G.m, G.src j = G.src j' → (j : ℕ) ≤ j' → ∀ lab : WLab G s, ext lab j ≤ ext lab j'

/-- **The window pointer invariant** of `u` at the bound `b` (agent-08): `sp.ptr[u]` is the
first slot of `u`'s CSR range whose candidate `du ⊕ e` is not below `b` (or the range end). -/
def PtrAt (st : State ℝ≥0) (du : WLab G s) (u : Fin G.n) (b : WLab G s) : Prop :=
  ScanStop st du u (st.wa "gSt" u) (st.wa "sp.ptr" u) b

/-- With sorted ranges, the slots scanned from the `Bi`-pointer up to the `B`-stop are exactly
the window edges `Bi ≤ cand < B` of `u`. -/
theorem window_char (hsort : CSRSorted G s) {st : State ℝ≥0} (hcsr : CSRAt st G)
    {du : WLab G s} {u : Fin G.n} {p0 q : ℕ} {Bi B : WLab G s}
    (h1 : ScanStop st du u (st.wa "gSt" u) p0 Bi) (h2 : ScanStop st du u p0 q B) (e : Fin G.m)
    (he : G.src e = u) : (p0 ≤ e ∧ (e : ℕ) < q) ↔ (Bi ≤ ext du e ∧ ext du e < B) := by
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  have hr := (hcsr.src e u).mp he
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, b3 e e.isLt h1 h2⟩
    have hp0m : p0 < G.m := lt_of_le_of_lt h1 e.isLt
    have hp0e : p0 < st.wa "gSt" ((u : ℕ) + 1) := by omega
    have hnot := a4 hp0m hp0e
    have hsrc0 : G.src ⟨p0, hp0m⟩ = u := (hcsr.src _ u).mpr ⟨a1, hp0e⟩
    exact le_trans (not_lt.mp hnot) (hsort ⟨p0, hp0m⟩ e (hsrc0.trans he.symm) h1 du)
  · rintro ⟨h1, h2⟩
    constructor
    · by_contra hlt
      push_neg at hlt
      exact absurd h1 (not_le.mpr (a3 e e.isLt hr.1 hlt))
    · by_contra hge
      push_neg at hge
      have hqm : q < G.m := lt_of_le_of_lt hge e.isLt
      have hqe : q < st.wa "gSt" ((u : ℕ) + 1) := lt_of_le_of_lt hge hr.2
      have hsrcq : G.src ⟨q, hqm⟩ = u :=
        (hcsr.src _ u).mpr ⟨by show st.wa "gSt" (u : ℕ) ≤ q; omega, hqe⟩
      exact b4 hqm hqe (lt_of_le_of_lt (hsort ⟨q, hqm⟩ e (hsrcq.trans he.symm) hge du) h2)

/-- The pointer advances from `Bi` to `B`. -/
theorem ptr_advance {st r : State ℝ≥0} (hg : r.wa "gSt" = st.wa "gSt") {du : WLab G s}
    {u : Fin G.n} {p0 q : ℕ} {Bi B : WLab G s} (hBiB : Bi ≤ B)
    (h1 : ScanStop st du u (st.wa "gSt" u) p0 Bi) (h2 : ScanStop st du u p0 q B)
    (hq : r.wa "sp.ptr" u = q) : PtrAt r du u B := by
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  unfold PtrAt ScanStop
  rw [hg, hq]
  refine ⟨le_trans a1 b1, b2, fun j hj h1 h2 => ?_, b4⟩
  by_cases hjp : j < p0
  · exact lt_of_lt_of_le (a3 j hj h1 hjp) hBiB
  · exact b3 j hj (not_lt.mp hjp) h2

open Classical in
/-- **BM.19–21, the window scan** (agent-08's `windowScan` with B-LAB's `candB` and
`relaxInsRAM`).  From the pointer invariant at the pull bound `Bi` for the child's `U` row `xs`,
the scan relaxes (with insertion into the level's `D` when `Bi ≤ cand`) exactly the window edges
`L'` of LoopD's step — `L'.Nodup` and `e ∈ L' ↔ src e ∈ U_i ∧ Bi ≤ cand ∧ cand < B` — ends
representing `L'.foldl (relaxInsCc dlOps T B (some Bi)) fs0`, and re-establishes the pointer
invariant at `B`.  RAM cost `≤ 124 ×` Layer-A cost `+ 38 |U_i| + 2`. -/
theorem winScan_spec (T : ℕ) {c0 bcap ecap lv bse : ℕ} {B Bi : WLab G s} {Kb : LReg}
    {kbf : String} {Klo : LReg} {klof : String} (hy : BlkHyg Kb kbf Klo klof)
    (hl : LoopHyg Kb kbf Klo klof) (hli : ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof], a ≠ "sp.i")
    (hsort : CSRSorted G s) (hBiB : Bi ≤ B)
    (st : State ℝ≥0) (fs0 : BM.RSt G s) (H0 : Fin G.n → ℕ → List (Fin G.m))
    (h0 : Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof st fs0 H0)
    (l nw : ℕ) (hl1 : 1 ≤ l) (hlv : st.w "lvl" = l) (hnw : st.w "n" = nw)
    (hrow : l * nw < st.cap) (xs : List (Fin G.n)) (hxs : xs.Nodup)
    (hU : RamLevel.RowRep st "U" "U.len" nw (l - 1) (xs.map Fin.val))
    (hcomp : ∀ u ∈ xs, fs0.d u = dis (s := s) u ∧ fs0.d u ≠ ⊤)
    (hptr : ∀ u ∈ xs, PtrAt st (fs0.d u) u Bi)
    (hptrl : G.n ≤ st.wlen "sp.ptr") (hncap : G.n + 2 ≤ st.cap)
    (hfr : fs0.g.fresh + G.m + 1 < ecap)
    (hcapD : 2 * fs0.Dc.blocks.length + ecap + bse + 4 < st.cap)
    (hB : st.cost + (xs.length + 1) * ((G.m + 1) * CE fs0.Dc.blocks.length + 101) ≤
      c0 + st.cap)
    (hm : G.m + 2 ≤ st.cap) :
    Runs realOps (winScan Kb kbf Klo klof) st (fun r => ∃ (L' : List (Fin G.m))
      (H' : Fin G.n → ℕ → List (Fin G.m)),
      L'.Nodup ∧
      (∀ e, e ∈ L' ↔ G.src e ∈ xs ∧ Bi ≤ ext (fs0.d (G.src e)) e ∧
        ext (fs0.d (G.src e)) e < B) ∧
      HExt H0 (vc st) H' (vc r) ∧
      Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r
        (L'.foldl (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0) H' ∧
      (∀ u ∈ xs, PtrAt r (fs0.d u) u B) ∧
      (∀ u : Fin G.n, u ∉ xs → r.wa "sp.ptr" u = st.wa "sp.ptr" u) ∧
      r.wlen "sp.ptr" = st.wlen "sp.ptr" ∧ FrameW st r ∧ st.cost ≤ r.cost ∧
      r.cost + 124 * fs0.c ≤ st.cost +
        124 * (L'.foldl (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0).c +
        38 * xs.length + 2) := by
  have hbnd0 : ∀ u : Fin G.n, u ∈ xs → st.wa "gSt" u ≤ st.wa "sp.ptr" u ∧
      st.wa "sp.ptr" u ≤ st.wa "gSt" ((u : ℕ) + 1) := fun u hu => ⟨(hptr u hu).1, (hptr u hu).2.1⟩
  refine (scanLoop_spec T hy hl hli _ _ _ st fs0 H0 h0 xs hxs (fun u => st.wa "sp.ptr" u) ?_ ?_ ?_
    hbnd0 hcomp hptrl hncap hfr hcapD hB hm).mono ?_
  · -- the row length
    intro r hr
    have hlv' : r.w "lvl" = l := by rw [Unchanged.wreg hr "lvl" (by decide)]; exact hlv
    have hUl := Unchanged.warr hr "U.len" (by decide)
    have hcap : r.cap = st.cap := Unchanged.cap hr
    have e1 : evalW r (sub (var "lvl") (lit 1)) = some (l - 1) :=
      evalW_sub_of' (by rw [evalW_var, hlv']) (evalW_lit_of (by omega))
    rw [evalW_load_of e1 (by rw [hUl.2]; exact hU.2.2.1), hUl.1, hU.2.2.2.1, List.length_map]
  · -- the `i`-th vertex of the row
    intro r i hi hr hri
    have hlv' : r.w "lvl" = l := by rw [Unchanged.wreg hr "lvl" (by decide)]; exact hlv
    have hnw' : r.w "n" = nw := by rw [Unchanged.wreg hr "n" (by decide)]; exact hnw
    have hUa := Unchanged.warr hr "U" (by decide)
    have hcap : r.cap = st.cap := Unchanged.cap hr
    have hlen : xs.length ≤ nw := by have := hU.1; simpa using this
    have hsplit : l * nw = (l - 1) * nw + nw := by
      conv_lhs => rw [show l = (l - 1) + 1 by omega]
      rw [Nat.succ_mul]
    have hwU : (l - 1 + 1) * nw ≤ st.wlen "U" := hU.2.1
    rw [show l - 1 + 1 = l by omega] at hwU
    have e1 : evalW r (sub (var "lvl") (lit 1)) = some (l - 1) :=
      evalW_sub_of' (by rw [evalW_var, hlv']) (evalW_lit_of (by omega))
    have e2 : evalW r (mul (sub (var "lvl") (lit 1)) (var "n")) = some ((l - 1) * nw) :=
      evalW_mul_of' e1 (by rw [evalW_var, hnw']) (by omega)
    have e3 : evalW r (chr (var "sp.i")) = some ((l - 1) * nw + i) :=
      evalW_add_of e2 (by rw [evalW_var, hri]) (by omega)
    rw [evalW_load_of e3 (by rw [hUa.2]; omega), hUa.1,
      hU.2.2.2.2 i (by simpa using hi), List.getElem_map]
  · -- the start slot = the pointer
    intro r u hr hwl hru hpu
    rw [evalW_load_of (j := (u : ℕ)) (by rw [evalW_var]; exact congrArg some hru)
      (by rw [hwl]; have := u.isLt; omega), hpu]
  · rintro r ⟨H', Q, hQ, hrest, hwl, hE, hR, hFW, hclo, hrel⟩
    have hbnd : ∀ u : Fin G.n, u ∈ xs → st.wa "gSt" u ≤ st.wa "sp.ptr" u ∧
        Q u ≤ st.wa "gSt" ((u : ℕ) + 1) := fun u hu => ⟨(hptr u hu).1, (hQ u hu).1.2.1⟩
    refine ⟨xs.flatMap (fun u : Fin G.n => slots G (st.wa "sp.ptr" u) (Q u)), H',
      flatSlots_nodup h0.csr hxs hbnd, fun e => ?_, hE, hR, fun u hu => ?_, hrest, hwl, hFW,
      hclo, hrel⟩
    · rw [flatSlots_mem h0.csr hbnd e]
      constructor
      · rintro ⟨hu, h1, h2⟩
        exact ⟨hu, (window_char hsort h0.csr (hptr _ hu) (hQ _ hu).1 e rfl).mp ⟨h1, h2⟩⟩
      · rintro ⟨hu, h1⟩
        exact ⟨hu, (window_char hsort h0.csr (hptr _ hu) (hQ _ hu).1 e rfl).mpr h1⟩
    · exact ptr_advance (Unchanged.warr hFW "gSt" (by decide)).1 hBiB (hptr u hu) (hQ u hu).1
        (hQ u hu).2

end Frontier.CHD.WinScan
