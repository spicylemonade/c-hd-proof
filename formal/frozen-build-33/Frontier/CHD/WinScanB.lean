import Frontier.CHD.WinScanA
import Frontier.CHD.RelaxIns
import Frontier.CHD.RamBaseCase

/-!
# WinScanB — the RAM window scan of one vertex (BM.19–21 inner loop; agent-02, NON-GATE)

`winInner Kb kbf Klo klof` scans the sorted CSR range of `u = ru` from slot `sp.p` while the
candidate `d[u] ⊕ e` is below `B` (block `Kb`), relaxing each scanned edge with insertion into the
level's D when valid and `B_i ≤ cand` (`relaxInsRAM`, `lo` block `Klo`).  Its spec: the scanned
slots are `[p0, q)` for the first slot `q ≥ p0` whose candidate is `≥ B` (or the range end), and
the machine ends in a state representing `(slots p0 q).foldl (relaxInsCc (dlOps) T B (some Bi))`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DIns Frontier.CHD.RelaxIns Frontier.CHD.RamBaseCase WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- The machine state `r` represents the relaxation-scan state `fs` (ghost history `H'`). -/
structure Reps (c0 bcap ecap lv bse : ℕ) (B Bi : WLab G s) (Kb : LReg) (kbf : String)
    (Klo : LReg) (klof : String) (r : State ℝ≥0) (fs : BM.RSt G s)
    (H' : Fin G.n → ℕ → List (Fin G.m)) : Prop where
  lab : LabAt r fs.d H' c0
  dr : DRep r H' (vc r) bcap lv bse fs.Dc
  ba : BlkArrs r bcap
  live : LiveRep r H' (vc r) fs.g.L
  pool : PoolRep r fs.g.fresh ecap
  inv : DInv fs.g fs.Dc
  bd : fs.Dc.Bd = B
  wk : WalkInv fs.d
  gr : GraphAt r G
  csr : CSRAt r G
  kb : WHolds r Kb kbf H' (vc r) B
  klo : WHolds r Klo klof H' (vc r) Bi
  uselo : r.w "lab.uselo" ≠ 0
  dslv : r.w "ds.lv" = lv
  dsb : r.w "ds.b" = bse

/-- Register-only steps (and charges) keep the representation. -/
theorem Reps.of_regs {c0 bcap ecap lv bse : ℕ} {B Bi : WLab G s} {Kb : LReg} {kbf : String}
    {Klo : LReg} {klof : String} {r r' : State ℝ≥0} {fs : BM.RSt G s}
    {H' : Fin G.n → ℕ → List (Fin G.m)} {wr vr : List String}
    (h : Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r fs H') (hu : Unchanged r r' [] [] wr vr)
    (hc : r.cost ≤ r'.cost) (hK : ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof] ++
      ["lab.uselo", "ds.lv", "ds.b", "ds.fresh"], a ∉ wr) (hKl : Kb.l ∉ vr ∧ Klo.l ∉ vr) :
    Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r' fs H' := by
  have hw0 : ∀ a ∈ ([] : List String), a ∉ dW := by simp
  have hv0 : ∀ a ∈ ([] : List String), a ∉ dV := by simp
  have hvc : vc (G := G) r' = vc r := vc_of_unchanged hu (by simp)
  have hm : ∀ a, a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof] ++ ["lab.uselo", "ds.lv", "ds.b", "ds.fresh"] →
      a ∉ wr := hK
  refine ⟨h.lab.of_unchanged hu (by simp) (by simp) hc, ?_, h.ba.of_unchanged hu hw0 hv0, ?_,
    PoolRep.of_unchanged h.pool hu hw0 hv0 (hm _ (by simp)), h.inv, h.bd, h.wk,
    graphAt_of_unchanged hu (by simp) (by simp) h.gr, CSRAt.of_unchanged h.csr hu (by simp), ?_, ?_,
    by rw [hu.wreg _ (hm _ (by simp))]; exact h.uselo, by rw [hu.wreg _ (hm _ (by simp))]; exact h.dslv,
    by rw [hu.wreg _ (hm _ (by simp))]; exact h.dsb⟩
  · rw [hvc]; exact h.dr.of_unchanged hu hw0 hv0
  · rw [hvc]; exact h.live.of_unchanged hu hw0 hv0
  · rw [hvc]
    exact h.kb.of_unchanged hu (fun a ha => hm a (by simp [ha])) hKl.1 (hm _ (by simp))
  · rw [hvc]
    exact h.klo.of_unchanged hu (fun a ha => hm a (by simp [ha])) hKl.2 (hm _ (by simp))

/-- Register hygiene of the bound blocks w.r.t. everything `relaxInsRAM` writes. -/
structure BlkHyg (Kb : LReg) (kbf : String) (Klo : LReg) (klof : String) : Prop where
  kb : BoundRegs Kb kbf
  klo : BoundRegs Klo klof
  kbw : ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof], a ∉ riW
  kbl : Kb.l ∉ riV ∧ Klo.l ∉ riV
  lod : ∀ a ∈ Klo.ws, a ∉ ["lab.lolt", "lab.ge"]
  lofd : klof ∉ ["lab.lolt", "lab.ge"]

open Classical in
/-- **One scanned edge**: `relaxInsRAM` maps a representation of `fs` to one of
`relaxInsCc (dlOps) T B (some Bi) fs e`. -/
theorem Reps.step (T : ℕ) {c0 bcap ecap lv bse : ℕ} {B Bi : WLab G s} {Kb : LReg} {kbf : String}
    {Klo : LReg} {klof : String} (hy : BlkHyg Kb kbf Klo klof) {r : State ℝ≥0} {fs : BM.RSt G s}
    {H' : Fin G.n → ℕ → List (Fin G.m)} (h : Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r fs H')
    (e : Fin G.m) (hru : r.w "ru" = G.src e) (hre : r.w "re" = e) (hu : fs.d (G.src e) ≠ ⊤)
    (hfr1 : fs.g.fresh + 1 < ecap) (hcapD : 2 * fs.Dc.blocks.length + ecap + bse + 4 < r.cap)
    (hB : r.cost + 64 ≤ c0 + r.cap) (hm : G.m + 2 ≤ r.cap) :
    Runs realOps (relaxInsRAM Kb kbf Klo klof) r (fun r' => ∃ H'',
      HExt H' (vc r) H'' (vc r') ∧
      Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r' (BM.relaxInsCc (BM.dlOps G s) T B (some Bi) fs e) H'' ∧
      Unchanged r r' (labW ++ insWA) (labV ++ [entA.l]) riW riV ∧ r.cost ≤ r'.cost ∧
      r'.cost ≤ r.cost + 190 + 35 * (Nat.log 2 (fs.Dc.blocks.length - 1) + 1) ∧
      r'.cost + 100 * fs.c ≤
        r.cost + 100 * (BM.relaxInsCc (BM.dlOps G s) T B (some Bi) fs e).c) := by
  have hri := relaxInsRAM_spec T r fs.d H' c0 h.lab h.gr e hru hre hu Kb kbf hy.kb B h.kb Klo klof
    hy.klo (some Bi) (Or.inr ⟨Bi, rfl, h.uselo, h.klo⟩) hy.lod hy.lofd (by decide) fs.g fs.Dc bcap
    ecap lv bse h.dr h.ba h.live h.pool h.inv.wf h.inv.fr h.inv.ids h.inv.lf h.dslv h.dsb hfr1
    hcapD hB hm fs.c
  refine hri.mono ?_
  rintro r' ⟨H'', hE, hL', hD', hBA', hLv', hP', hg', hU, hc1, hc2, hc3⟩
  obtain ⟨hI', hBd', -⟩ := h.inv.relaxInsCc (T := T) (lo := some Bi) h.bd e
  obtain ⟨hw', -⟩ := relaxInsCc_d_complete (T := T) (B := B) (lo := some Bi) fs h.wk e
  have hK := fun a (ha : a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof]) => hy.kbw a ha
  refine ⟨H'', hE, ⟨?_, hD', hBA', hLv', hP', hI', hBd', hw', hg',
    CSRAt.of_unchanged h.csr hU (by decide), ?_, ?_, ?_, ?_, ?_⟩, hU, hc1, hc2, hc3⟩
  · have : (⟨fs.d, fs.g, fs.Dc, fs.c⟩ : BM.RSt G s) = fs := rfl
    rw [this] at hL'; exact hL'
  · exact (h.kb.ext hE).of_unchanged hU (fun a ha => hK a (by simp [ha])) hy.kbl.1
      (hK _ (by simp))
  · exact (h.klo.ext hE).of_unchanged hU (fun a ha => hK a (by simp [ha])) hy.kbl.2
      (hK _ (by simp))
  · rw [hU.wreg _ (by decide)]; exact h.uselo
  · rw [hU.wreg _ (by decide)]; exact h.dslv
  · rw [hU.wreg _ (by decide)]; exact h.dsb

open Classical in
theorem relaxInsCc_fresh_le {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} (st : BM.RSt G s)
    (e : Fin G.m) :
    (BM.relaxInsCc (BM.dlOps G s) T B lo st e).g.fresh ≤ st.g.fresh + 1 := by
  have hins : ∀ v lam, (BM.insC (BM.dlOps G s) T st.g st.Dc v lam).1.fresh ≤ st.g.fresh + 1 := by
    intro v lam
    rw [(insC_dl (G := G) (s := s) T st.g st.Dc v lam).2.1]
    unfold insertNS; split_ifs <;> simp
  unfold BM.relaxInsCc
  by_cases hv : BM.ValidRelax G s st.d B e
  · rw [if_pos hv]
    cases lo with
    | none => exact hins _ _
    | some b =>
      by_cases hb : b ≤ ext (st.d (G.src e)) e
      · simp only [if_pos hb]; exact hins _ _
      · simp only [if_neg hb]; exact Nat.le_succ _
  · rw [if_neg hv]; exact Nat.le_succ _

open Classical in
/-- Every scanned edge costs at least `1` in Layer A. -/
theorem relaxInsCc_c_ge {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} (st : BM.RSt G s)
    (e : Fin G.m) : st.c + 1 ≤ (BM.relaxInsCc (BM.dlOps G s) T B lo st e).c := by
  unfold BM.relaxInsCc
  by_cases hv : BM.ValidRelax G s st.d B e
  · rw [if_pos hv]
    cases lo with
    | none => exact Nat.le_add_right _ _
    | some b =>
      by_cases hb : b ≤ ext (st.d (G.src e)) e
      · simp only [if_pos hb]; exact Nat.le_add_right _ _
      · simp only [if_neg hb]; exact le_rfl
  · simp only [if_neg hv]; exact le_rfl

theorem foldl_fresh_le {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} :
    ∀ (L : List (Fin G.m)) (st : BM.RSt G s),
      (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).g.fresh ≤ st.g.fresh + L.length
  | [], st => by simp
  | e :: L, st => by
    have h1 := relaxInsCc_fresh_le (T := T) (B := B) (lo := lo) st e
    have h2 := foldl_fresh_le (T := T) (B := B) (lo := lo) L (BM.relaxInsCc (BM.dlOps G s) T B lo st e)
    simp only [List.foldl_cons, List.length_cons]; omega

theorem slots_length_le (a b : ℕ) : (slots G a b).length ≤ b - a := by
  unfold slots
  exact (List.length_filterMap_le _ _).trans (by simp)

section Gen
variable {V : Type} {ops : VOps V}

theorem unch_charge_left {s r : State V} {wa va wr vr : List String} (k : ℕ) :
    Unchanged (s.charge k) r wa va wr vr ↔ Unchanged s r wa va wr vr := by
  constructor <;> intro h <;> exact ⟨h.warr, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩

/-- `x := e` with the successor state kept abstract. -/
theorem runs_wset_val {x : String} {e : WExpr} {a : ℕ} {s : State V} {Q : State V → Prop}
    (he : evalW s e = some a)
    (hQ : ∀ r, r.w x = a → Unchanged s r [] [] [x] [] → r.cost = s.cost + 1 → Q r) :
    Runs ops (.wset x e) s Q :=
  runs_wset he (hQ _ (by simp [State.charge, State.setW])
    ((unch_charge 1).mpr ((unch_setW (List.mem_singleton_self _) a).mpr (Unchanged.refl _ _ _ _ _)))
    rfl)

end Gen

/-- The inner loop of the window scan: scan `u = ru`'s CSR slots from `sp.p` below `sp.pe`. -/
def winInner (Kb : LReg) (kbf : String) (Klo : LReg) (klof : String) : Stmt :=
  .while (var "sp.go")
    (seq (ite (lt (var "sp.p") (var "sp.pe"))
            (seq (wset "re" (var "sp.p")) (LabRAM.candB Kb kbf "sp.lt"))
            (wset "sp.lt" (lit 0)))
    (ite (var "sp.lt")
       (seq (relaxInsRAM Kb kbf Klo klof) (wset "sp.p" (add (var "sp.p") (lit 1))))
       (wset "sp.go" (lit 0))))

/-- Registers of the inner loop. -/
def winW : List String := ["re", "sp.lt", "sp.p", "sp.go"]

/-- The loop registers are none of the bound registers. -/
structure LoopHyg (Kb : LReg) (kbf : String) (Klo : LReg) (klof : String) : Prop where
  w : ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof], a ∉ winW ++ ["ru", "sp.pe"] ++ X0.ws ++
    ["lab.c1", "lab.c2"]

/-- Per-edge cost bound of the scan. -/
def CE (nb : ℕ) : ℕ := 214 + 35 * (Nat.log 2 (nb - 1) + 1)

/-- Registers the inner loop may write. -/
def innerW : List String := riW ++ winW ++ X0.ws ++ ["lab.c1", "lab.c2"]

open Classical in
/-- **The inner loop of the window scan** (one vertex `u`). -/
theorem winInner_spec (T : ℕ) {c0 bcap ecap lv bse : ℕ} {B Bi : WLab G s} {Kb : LReg}
    {kbf : String} {Klo : LReg} {klof : String} (hy : BlkHyg Kb kbf Klo klof)
    (hl : LoopHyg Kb kbf Klo klof) (st : State ℝ≥0) (fs0 : BM.RSt G s)
    (H0 : Fin G.n → ℕ → List (Fin G.m))
    (h0 : Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof st fs0 H0)
    (u : Fin G.n) (hcomp : fs0.d u = dis (s := s) u) (hfin : fs0.d u ≠ ⊤)
    (p0 pe : ℕ) (hp0 : st.w "sp.p" = p0) (hpe : st.w "sp.pe" = pe) (hgo : st.w "sp.go" = 1)
    (hru : st.w "ru" = u)
    (hrange : st.wa "gSt" u ≤ p0 ∧ p0 ≤ pe ∧ pe = st.wa "gSt" ((u : ℕ) + 1))
    (hfr1 : fs0.g.fresh + (pe - p0) + 1 < ecap)
    (hcapD : 2 * fs0.Dc.blocks.length + ecap + bse + 4 < st.cap)
    (hB : st.cost + (pe - p0 + 1) * CE fs0.Dc.blocks.length + 64 ≤ c0 + st.cap)
    (hm : G.m + 2 ≤ st.cap) :
    Runs realOps (winInner Kb kbf Klo klof) st (fun r => ∃ q H',
      p0 ≤ q ∧ q ≤ pe ∧ r.w "sp.p" = q ∧
      (∀ j (hj : j < G.m), p0 ≤ j → j < q → ext (fs0.d u) ⟨j, hj⟩ < B) ∧
      (q < pe → ∃ hq : q < G.m, ¬ ext (fs0.d u) ⟨q, hq⟩ < B) ∧
      HExt H0 (vc st) H' (vc r) ∧
      Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r
        ((slots G p0 q).foldl (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0) H' ∧
      r.w "ru" = u ∧ r.w "sp.pe" = pe ∧
      Unchanged st r (labW ++ insWA) (labV ++ [entA.l]) innerW riV ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + (q - p0) * CE fs0.Dc.blocks.length + 30 ∧
      r.cost + 124 * fs0.c ≤ st.cost +
        124 * ((slots G p0 q).foldl (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0).c + 30) := by
  set nb := fs0.Dc.blocks.length with hnb
  have hpeM : pe ≤ G.m := by rw [hrange.2.2]; exact h0.csr.le_m u
  -- the loop invariant
  let I : State ℝ≥0 → Prop := fun r => ∃ p H', r.w "sp.p" = p ∧ p0 ≤ p ∧ p ≤ pe ∧
    r.w "sp.pe" = pe ∧ r.w "ru" = u ∧ (r.w "sp.go" = 0 ∨ r.w "sp.go" = 1) ∧
    (∀ j (hj : j < G.m), p0 ≤ j → j < p → ext (fs0.d u) ⟨j, hj⟩ < B) ∧
    (r.w "sp.go" = 0 → (p = pe ∨ ∃ hp : p < G.m, ¬ ext (fs0.d u) ⟨p, hp⟩ < B)) ∧
    HExt H0 (vc st) H' (vc r) ∧
    Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r
      ((slots G p0 p).foldl (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0) H' ∧
    Unchanged st r (labW ++ insWA) (labV ++ [entA.l]) innerW riV ∧ r.cap = st.cap ∧
    st.cost ≤ r.cost ∧
    r.cost ≤ st.cost + (p - p0) * CE nb + (if r.w "sp.go" = 0 then 26 else 0) ∧
    r.cost + 124 * fs0.c ≤ st.cost +
      124 * ((slots G p0 p).foldl (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0).c +
      (if r.w "sp.go" = 0 then 26 else 0)
  let μ : State ℝ≥0 → ℕ := fun r => 2 * (pe - r.w "sp.p") + r.w "sp.go"
  refine runs_while_var I μ _ (fun r hI => ?_) st ⟨p0, H0, hp0, le_rfl, hrange.2.1, hpe, hru,
    Or.inr hgo, fun j _ h1 h2 => absurd h2 (by omega), fun h => by rw [hgo] at h; exact absurd h one_ne_zero,
    HExt.refl _ _, by rw [slots_self]; exact h0, Unchanged.refl _ _ _ _ _, rfl, le_rfl,
    by rw [hgo]; simp, by rw [hgo, slots_self]; simp⟩
  obtain ⟨p, H', hp, hp0p, hppe, hpe', hru', hgo', hwin, hstop, hE, hR, hU, hcap', hclo, hchi,
    hrel⟩ := hI
  set fsp := (slots G p0 p).foldl (BM.relaxInsCc (BM.dlOps G s) T B (some Bi)) fs0 with hfsp
  obtain ⟨-, -, -, hnbp, hstab⟩ := foldl_invs (T := T) (B := B) (lo := some Bi) (slots G p0 p) fs0
    h0.wk h0.inv h0.bd
  have hdu : fsp.d u = fs0.d u := hstab u hcomp
  have hfrp : fsp.g.fresh ≤ fs0.g.fresh + (p - p0) :=
    (foldl_fresh_le (T := T) (B := B) (lo := some Bi) (slots G p0 p) fs0).trans
      (Nat.add_le_add_left (slots_length_le p0 p) _)
  refine ⟨r.w "sp.go", by simp, fun hne => ?_, fun hz => ?_⟩
  · -- one more iteration
    have hg1 : r.w "sp.go" = 1 := by rcases hgo' with h | h; exact absurd h hne; exact h
    rw [hg1] at hchi hrel
    simp only [if_neg one_ne_zero, add_zero] at hchi hrel
    have hmr : G.m + 2 ≤ r.cap := by rw [hcap']; exact hm
    have h1c : 1 < r.cap := by omega
    have hfix : ∀ a ∈ ["lab.uselo", "ds.lv", "ds.b", "ds.fresh"],
        a ∉ winW ++ X0.ws ++ ["lab.c1", "lab.c2"] := by decide
    have hK : ∀ {wr : List String}, (∀ a ∈ wr, a ∈ winW ++ X0.ws ++ ["lab.c1", "lab.c2"]) →
        ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof] ++ ["lab.uselo", "ds.lv", "ds.b", "ds.fresh"],
          a ∉ wr := by
      intro wr hwr a ha haw
      have hw := hwr a haw
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · apply hl.w a ha
        simp only [List.mem_append] at hw ⊢
        tauto
      · exact hfix a ha hw
    have hKl : Kb.l ∉ [X0.l] ∧ Klo.l ∉ [X0.l] :=
      ⟨fun h => hy.kb.l (by simp only [X0, List.mem_singleton] at h; rw [h]; decide),
       fun h => hy.klo.l (by simp only [X0, List.mem_singleton] at h; rw [h]; decide)⟩
    have hKn : Kb.l ∉ ([] : List String) ∧ Klo.l ∉ ([] : List String) := ⟨by simp, by simp⟩
    have toI : ∀ {a b : State ℝ≥0} {wa va wr vr : List String}, Unchanged a b wa va wr vr →
        (∀ x ∈ wa, x ∈ labW ++ insWA) → (∀ x ∈ va, x ∈ labV ++ [entA.l]) →
        (∀ x ∈ wr, x ∈ innerW) → (∀ x ∈ vr, x ∈ riV) →
        Unchanged a b (labW ++ insWA) (labV ++ [entA.l]) innerW riV :=
      fun h h1 h2 h3 h4 => h.mono (by intro x hx; exact h1 x hx) (by intro x hx; exact h2 x hx)
        (by intro x hx; exact h3 x hx) (by intro x hx; exact h4 x hx)
    apply runs_seq
    by_cases hpl : p < pe
    · -- a slot is left: test its candidate
      have hpm : p < G.m := lt_of_lt_of_le hpl hpeM
      set e : Fin G.m := ⟨p, hpm⟩ with he
      have hsrc : G.src e = u := (h0.csr.src e u).mpr
        ⟨le_trans hrange.1 hp0p, lt_of_lt_of_eq hpl hrange.2.2⟩
      have hdu' : fsp.d (G.src e) = fs0.d u := by rw [hsrc]; exact hdu
      have hfinp : fsp.d (G.src e) ≠ ⊤ := by rw [hdu']; exact hfin
      have hmulS : (p - p0 + 1) * CE nb = (p - p0) * CE nb + CE nb := by ring
      have hmulB : (p - p0 + 1) * CE nb ≤ (pe - p0 + 1) * CE nb :=
        Nat.mul_le_mul_right _ (by omega)
      have hCE : 214 ≤ CE nb := by unfold CE; omega
      have hlt1 : evalW (r.charge 1) (lt (var "sp.p") (var "sp.pe")) = some 1 := by
        rw [evalW_lt_of (s := r.charge 1) (x := p) (y := pe)
          (by rw [evalW_var]; exact congrArg some hp)
          (by rw [evalW_var]; exact congrArg some hpe') h1c, if_pos hpl]
      apply runs_ite_true hlt1 one_ne_zero
      apply runs_seq
      refine runs_wset_val (a := p) (by rw [evalW_var]; exact congrArg some hp)
        (fun r3 hre3 hU3 hc3 => ?_)
      have hU13 : Unchanged r r3 [] [] ["re"] [] :=
        (unch_charge_left 1).mp ((unch_charge_left 1).mp hU3)
      have hc3' : r3.cost = r.cost + 3 := by rw [hc3]; rfl
      have hR3 : Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r3 fsp H' :=
        hR.of_regs hU13 (by omega) (hK (by decide)) hKn
      have hru3 : r3.w "ru" = G.src e := by rw [hU13.wreg "ru" (by decide), hru', hsrc]
      have hcap3 : r3.cap = st.cap := hU13.cap.trans hcap'
      refine (candB_spec r3 fsp.d H' c0 hR3.lab hR3.gr e hru3 hre3 hfinp Kb kbf "sp.lt" hy.kb
        (by decide) B hR3.kb (by rw [hcap3]; omega) (by rw [hcap3]; exact hm)).mono ?_
      rintro r4 ⟨-, hvc4, -, -, hlt4, hU4, hc4a, hc4b⟩
      have hR4 : Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r4 fsp H' :=
        hR3.of_regs hU4 (by omega) (hK (by decide)) hKl
      rw [hdu'] at hlt4
      have hcap4 : r4.cap = st.cap := hU4.cap.trans hcap3
      have hvc4' : vc (G := G) r4 = vc r := hvc4.trans (vc_of_unchanged hU13 (by simp))
      by_cases hc : ext (fs0.d u) e < B
      · -- the candidate is below `B`: relax (with insertion) and advance
        rw [if_pos hc] at hlt4
        apply runs_ite_true (x := 1) (by rw [evalW_var, hlt4]) one_ne_zero
        apply runs_seq
        have hR5 : Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof (r4.charge 1) fsp H' :=
          hR4.of_regs (Unchanged.charge r4 1 [] [] [] []) (by show r4.cost ≤ r4.cost + 1; omega)
            (hK (by decide)) hKn
        refine (Reps.step T hy hR5 e ?_ ?_ hfinp ?_ ?_ ?_ ?_).mono ?_
        · show r4.w "ru" = G.src e
          rw [hU4.wreg "ru" (by decide)]; exact hru3
        · show r4.w "re" = (e : ℕ)
          rw [hU4.wreg "re" (by decide)]; exact hre3
        · omega
        · show _ < r4.cap
          rw [hcap4, hnbp]; exact hcapD
        · show r4.cost + 1 + 64 ≤ c0 + r4.cap
          rw [hcap4]; omega
        · show G.m + 2 ≤ r4.cap
          rw [hcap4]; exact hm
        rintro r6 ⟨H'', hE6, hR6, hU6, hc6a, hc6b, hc6c⟩
        have hΔ := relaxInsCc_c_ge (T := T) (B := B) (lo := some Bi) fsp e
        have hp6 : r6.w "sp.p" = p := by
          rw [hU6.wreg "sp.p" (by decide)]
          show r4.w "sp.p" = p
          rw [hU4.wreg "sp.p" (by decide), hU13.wreg "sp.p" (by decide)]; exact hp
        have hcap6 : r6.cap = st.cap := hU6.cap.trans hcap4
        have hCEe : 214 + 35 * (Nat.log 2 (fsp.Dc.blocks.length - 1) + 1) = CE nb := by
          rw [hnbp]; rfl
        have hc5 : (r4.charge 1).cost = r4.cost + 1 := rfl
        refine runs_wset_val (evalW_add_of (x := p) (y := 1)
          (by rw [evalW_var]; exact congrArg some hp6)
          (evalW_lit_of (by omega)) (by omega)) (fun r7 hp7 hU67 hc7 => ?_)
        have hvc5 : vc (G := G) (r4.charge 1) = vc r := hvc4'
        have hvc7 : vc (G := G) r7 = vc r6 := vc_of_unchanged hU67 (by simp)
        have hgo7 : r7.w "sp.go" = 1 := by
          rw [hU67.wreg "sp.go" (by decide), hU6.wreg "sp.go" (by decide)]
          show r4.w "sp.go" = 1
          rw [hU4.wreg "sp.go" (by decide), hU13.wreg "sp.go" (by decide)]; exact hg1
        refine ⟨⟨p + 1, H'', hp7, by omega, by omega, ?_, ?_, Or.inr hgo7, ?_,
          fun h => absurd (h.symm.trans hgo7) zero_ne_one, ?_, ?_, ?_, hU67.cap.trans hcap6,
          by omega, ?_, ?_⟩, ?_⟩
        · rw [hU67.wreg "sp.pe" (by decide), hU6.wreg "sp.pe" (by decide)]
          show r4.w "sp.pe" = pe
          rw [hU4.wreg "sp.pe" (by decide), hU13.wreg "sp.pe" (by decide)]; exact hpe'
        · rw [hU67.wreg "ru" (by decide), hU6.wreg "ru" (by decide)]
          show r4.w "ru" = u
          rw [hU4.wreg "ru" (by decide), hU13.wreg "ru" (by decide)]; exact hru'
        · intro j hj h1 h2
          rcases Nat.lt_or_ge j p with h3 | h3
          · exact hwin j hj h1 h3
          · have hjp : (⟨j, hj⟩ : Fin G.m) = e := Fin.ext (by show j = p; omega)
            rw [hjp]; exact hc
        · rw [hvc7]
          exact hE.trans (by rw [← hvc5]; exact hE6)
        · rw [slots_succ hp0p hpm, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          exact hR6.of_regs hU67 (by omega) (hK (by decide)) hKn
        · refine hU.trans ((toI hU13 (by simp) (by simp) (by decide) (by simp)).trans
            ((toI hU4 (by simp) (by simp) (by decide) (by decide)).trans
            ((toI (Unchanged.charge r4 1 [] [] [] []) (by simp) (by simp) (by simp) (by simp)).trans
            ((toI hU6 (fun x hx => hx) (fun x hx => hx) ?_ (fun x hx => hx)).trans
            (toI hU67 (by simp) (by simp) (by decide) (by simp))))))
          intro x hx
          simp only [innerW, List.mem_append]
          exact Or.inl (Or.inl (Or.inl hx))
        · rw [hgo7, if_neg one_ne_zero, add_zero]
          have : (p + 1 - p0) * CE nb = (p - p0) * CE nb + CE nb := by
            rw [show p + 1 - p0 = p - p0 + 1 by omega]; exact hmulS
          omega
        · rw [hgo7, if_neg one_ne_zero, add_zero, slots_succ hp0p hpm, List.foldl_append]
          simp only [List.foldl_cons, List.foldl_nil]
          show r7.cost + 124 * fs0.c ≤
            st.cost + 124 * (BM.relaxInsCc (BM.dlOps G s) T B (some Bi) fsp e).c
          omega
        · show 2 * (pe - r7.w "sp.p") + r7.w "sp.go" < 2 * (pe - r.w "sp.p") + r.w "sp.go"
          rw [hp7, hgo7, hp, hg1]; omega
      · -- the candidate is not below `B`: stop
        rw [if_neg hc] at hlt4
        apply runs_ite_false (by rw [evalW_var, hlt4])
        refine runs_wset_val (evalW_lit_of (by show 0 < r4.cap; omega))
          (fun r7 hgo7 hU47 hc7 => ?_)
        have hU47' : Unchanged r4 r7 [] [] ["sp.go"] [] := (unch_charge_left 1).mp hU47
        have hc7' : r7.cost = r4.cost + 2 := by rw [hc7]; rfl
        have hvc7 : vc (G := G) r7 = vc r := (vc_of_unchanged hU47' (by simp)).trans hvc4'
        have hp7 : r7.w "sp.p" = p := by
          rw [hU47'.wreg "sp.p" (by decide), hU4.wreg "sp.p" (by decide),
            hU13.wreg "sp.p" (by decide)]; exact hp
        refine ⟨⟨p, H', hp7, hp0p, hppe, ?_, ?_, Or.inl hgo7, hwin, fun _ => Or.inr ⟨hpm, hc⟩,
          by rw [hvc7]; exact hE, hR4.of_regs hU47' (by omega) (hK (by decide)) hKn, ?_,
          hU47'.cap.trans hcap4, by omega, ?_, ?_⟩, ?_⟩
        · rw [hU47'.wreg "sp.pe" (by decide), hU4.wreg "sp.pe" (by decide),
            hU13.wreg "sp.pe" (by decide)]; exact hpe'
        · rw [hU47'.wreg "ru" (by decide), hU4.wreg "ru" (by decide),
            hU13.wreg "ru" (by decide)]; exact hru'
        · exact hU.trans ((toI hU13 (by simp) (by simp) (by decide) (by simp)).trans
            ((toI hU4 (by simp) (by simp) (by decide) (by decide)).trans
            (toI hU47' (by simp) (by simp) (by decide) (by simp))))
        · rw [hgo7, if_pos rfl]
          have : r7.cost = r4.cost + 2 := by rw [hc7]; rfl
          omega
        · rw [hgo7, if_pos rfl, ← hfsp]
          omega
        · show 2 * (pe - r7.w "sp.p") + r7.w "sp.go" < 2 * (pe - r.w "sp.p") + r.w "sp.go"
          rw [hp7, hgo7, hp, hg1]; omega
    · -- the range is exhausted: stop
      have hpe_eq : p = pe := by omega
      have hlt0 : evalW (r.charge 1) (lt (var "sp.p") (var "sp.pe")) = some 0 := by
        rw [evalW_lt_of (s := r.charge 1) (x := p) (y := pe)
          (by rw [evalW_var]; exact congrArg some hp)
          (by rw [evalW_var]; exact congrArg some hpe') h1c, if_neg hpl]
      apply runs_ite_false hlt0
      refine runs_wset_val (evalW_lit_of (by show 0 < r.cap; omega)) (fun r3 hlt3 hU3 hc3 => ?_)
      have hU13 : Unchanged r r3 [] [] ["sp.lt"] [] :=
        (unch_charge_left 1).mp ((unch_charge_left 1).mp hU3)
      apply runs_ite_false (by rw [evalW_var, hlt3])
      refine runs_wset_val (evalW_lit_of (by show 0 < r3.cap; rw [hU13.cap]; omega))
        (fun r4 hgo4 hU4 hc4 => ?_)
      have hU34 : Unchanged r3 r4 [] [] ["sp.go"] [] := (unch_charge_left 1).mp hU4
      have hvc4 : vc (G := G) r4 = vc r :=
        (vc_of_unchanged hU34 (by simp)).trans (vc_of_unchanged hU13 (by simp))
      have hp4 : r4.w "sp.p" = p := by
        rw [hU34.wreg "sp.p" (by decide), hU13.wreg "sp.p" (by decide)]; exact hp
      have hc4' : r4.cost = r.cost + 5 := by rw [hc4]; show r3.cost + 1 + 1 = _; rw [hc3]; rfl
      refine ⟨⟨p, H', hp4, hp0p, hppe, ?_, ?_, Or.inl hgo4, hwin, fun _ => Or.inl hpe_eq,
        by rw [hvc4]; exact hE, hR.of_regs (hU13.comp hU34) (by omega) (hK (by decide)) hKn, ?_,
        hU34.cap.trans (hU13.cap.trans hcap'), by omega, ?_, ?_⟩, ?_⟩
      · rw [hU34.wreg "sp.pe" (by decide), hU13.wreg "sp.pe" (by decide)]; exact hpe'
      · rw [hU34.wreg "ru" (by decide), hU13.wreg "ru" (by decide)]; exact hru'
      · exact hU.trans ((toI hU13 (by simp) (by simp) (by decide) (by simp)).trans
          (toI hU34 (by simp) (by simp) (by decide) (by simp)))
      · rw [hgo4, if_pos rfl]; omega
      · rw [hgo4, if_pos rfl, ← hfsp]; omega
      · show 2 * (pe - r4.w "sp.p") + r4.w "sp.go" < 2 * (pe - r.w "sp.p") + r.w "sp.go"
        rw [hp4, hgo4, hp, hg1]; omega
  · -- exit
    have hcost : r.cost ≤ st.cost + (p - p0) * CE nb + 26 := by
      rw [hz, if_pos rfl] at hchi; exact hchi
    have hrel' : r.cost + 124 * fs0.c ≤ st.cost + 124 * fsp.c + 26 := by
      rw [hz, if_pos rfl] at hrel; exact hrel
    refine ⟨p, H', hp0p, hppe, hp, hwin, fun hq => ?_, hE,
      hR.of_regs (Unchanged.charge r 1 [] [] [] []) (by show r.cost ≤ r.cost + 1; omega)
        (by simp) (by simp), hru', hpe', (unch_charge 1).mpr hU, by show st.cost ≤ r.cost + 1; omega,
      by show r.cost + 1 ≤ _; omega,
      by show r.cost + 1 + 124 * fs0.c ≤ st.cost + 124 * fsp.c + 30; omega⟩
    rcases hstop hz with h | h
    · omega
    · exact h

end Frontier.CHD.WinScan
