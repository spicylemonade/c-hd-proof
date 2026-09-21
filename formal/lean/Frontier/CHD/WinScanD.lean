import Frontier.CHD.WinScanC

/-!
# WinScanD — the `W'` relaxations BM.27–28 (agent-02, NON-GATE)

`wScan lenE elemE` is the row scan `scanLoop` started at the range HEADS `gSt[ru]` (with
`lo = B'_f` in the `Klo` block).  For every `x` of the `W'` row it relaxes (with insertion into
`D` when `B'_f ≤ cand`) the prefix of `x`'s sorted CSR range whose candidates are below `B`, and
sets `sp.ptr[x]` to the first slot with candidate `≥ B`.

Layer A (`CallD`/`finD`) folds `relaxInsCc dlOps T B (some B'_f)` over a list `L` ENUMERATING all
out-edges of `W'`.  We take `L := xs.flatMap (full range of x)`: the edges the RAM skips (the
tail of each range) all have candidate `≥ B`, hence are not `ValidRelax` and only bump the Layer-A
cost counter (`fold_full`).  So the RAM state represents `L.foldl ...` (`Reps` ignores the
counter), and the RAM cost is bounded by the (larger) Layer-A cost.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.DIns Frontier.CHD.RelaxIns Frontier.CHD.RamBaseCase WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- BM.27–28: the scan of the `W'` row from the range heads. -/
def wScan (lenE elemE : WExpr) (Kb : LReg) (kbf : String) (Klo : LReg) (klof : String) : Stmt :=
  scanLoop lenE elemE (load "gSt" (var "ru")) Kb kbf Klo klof

/-! ### Layer A: invalid tails only bump the cost counter -/

open Classical in
theorem relaxInsCc_shift {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} (st : BM.RSt G s)
    (k : ℕ) (e : Fin G.m) :
    BM.relaxInsCc (BM.dlOps G s) T B lo ⟨st.d, st.g, st.Dc, st.c + k⟩ e =
      ⟨(BM.relaxInsCc (BM.dlOps G s) T B lo st e).d, (BM.relaxInsCc (BM.dlOps G s) T B lo st e).g,
        (BM.relaxInsCc (BM.dlOps G s) T B lo st e).Dc,
        (BM.relaxInsCc (BM.dlOps G s) T B lo st e).c + k⟩ := by
  unfold BM.relaxInsCc
  dsimp only
  by_cases hv : BM.ValidRelax G s st.d B e
  · rw [if_pos hv, if_pos hv]
    cases lo with
    | none => simp only [BM.RSt.mk.injEq, true_and] <;> omega
    | some b =>
      by_cases hb : b ≤ ext (st.d (G.src e)) e
      · simp only [if_pos hb, BM.RSt.mk.injEq, true_and] <;> omega
      · simp only [if_neg hb, BM.RSt.mk.injEq, true_and] <;> omega
  · rw [if_neg hv, if_neg hv]
    simp only [BM.RSt.mk.injEq, true_and] <;> omega

theorem foldl_shift {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} :
    ∀ (L : List (Fin G.m)) (st : BM.RSt G s) (k : ℕ),
      L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) ⟨st.d, st.g, st.Dc, st.c + k⟩ =
        ⟨(L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).d,
          (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).g,
          (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).Dc,
          (L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st).c + k⟩
  | [], st, k => rfl
  | e :: L, st, k => by
    simp only [List.foldl_cons]
    rw [relaxInsCc_shift st k e]
    exact foldl_shift L _ k

open Classical in
theorem foldl_invalid {T : ℕ} {B : WLab G s} {lo : Option (WLab G s)} :
    ∀ (L : List (Fin G.m)) (st : BM.RSt G s), (∀ e ∈ L, ¬ ext (st.d (G.src e)) e < B) →
      L.foldl (BM.relaxInsCc (BM.dlOps G s) T B lo) st = ⟨st.d, st.g, st.Dc, st.c + L.length⟩
  | [], st, _ => rfl
  | e :: L, st, h => by
    simp only [List.foldl_cons]
    have hv : ¬ BM.ValidRelax G s st.d B e := fun hv => h e (by simp) hv.2
    have h1 : BM.relaxInsCc (BM.dlOps G s) T B lo st e = ⟨st.d, st.g, st.Dc, st.c + 1⟩ := by
      unfold BM.relaxInsCc; rw [if_neg hv]
    rw [h1, foldl_invalid L ⟨st.d, st.g, st.Dc, st.c + 1⟩ (fun e' he' => h e' (by simp [he']))]
    simp only [BM.RSt.mk.injEq, List.length_cons, true_and] <;> omega

theorem slots_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    slots G a c = slots G a b ++ slots G b c := by
  unfold slots
  rw [← List.filterMap_append, show c - a = (b - a) + (c - b) by omega, ← List.range'_append,
    show a + 1 * (b - a) = b by omega]

/-- **The full ranges fold like the scanned prefixes**, up to the cost counter. -/
theorem fold_full {st : State ℝ≥0} (hsort : CSRSorted G s) (hcsr : CSRAt st G) {T : ℕ}
    {B lo' : WLab G s} (Q : Fin G.n → ℕ) :
    ∀ (ys : List (Fin G.n)) (st0 : BM.RSt G s), WalkInv st0.d → DInv st0.g st0.Dc →
      st0.Dc.Bd = B →
      (∀ u ∈ ys, st0.d u = dis (s := s) u ∧
        ScanStop st (dis (s := s) u) u (st.wa "gSt" u) (Q u) B) →
      ∃ k, (ys.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (st.wa "gSt" ((u : ℕ) + 1)))).foldl
          (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0 =
        ⟨((ys.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
            (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0).d,
          ((ys.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
            (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0).g,
          ((ys.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
            (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0).Dc,
          ((ys.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (Q u))).foldl
            (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0).c + k⟩
  | [], st0, _, _, _, _ => ⟨0, rfl⟩
  | u :: ys, st0, hw, hI, hB, h => by
    obtain ⟨hdu, q1, q2, q3, q4⟩ := h u (by simp)
    set st1 := (slots G (st.wa "gSt" u) (Q u)).foldl
      (BM.relaxInsCc (BM.dlOps G s) T B (some lo')) st0 with hst1
    obtain ⟨hw1, hI1, hB1, -, hstab1⟩ :=
      foldl_invs (T := T) (B := B) (lo := some lo') (slots G (st.wa "gSt" u) (Q u)) st0 hw hI hB
    have hd1u : st1.d u = dis (s := s) u := (hstab1 u hdu).trans hdu
    -- the tail of `u`'s range is invalid at `st1`
    have htail : ∀ e ∈ slots G (Q u) (st.wa "gSt" ((u : ℕ) + 1)), ¬ ext (st1.d (G.src e)) e < B := by
      intro e he
      rw [mem_slots] at he
      have hsrc : G.src e = u := (hcsr.src e u).mpr ⟨le_trans q1 he.1, he.2⟩
      rw [hsrc, hd1u]
      have hqm : Q u < G.m := lt_of_le_of_lt he.1 e.isLt
      have hqe : Q u < st.wa "gSt" ((u : ℕ) + 1) := lt_of_le_of_lt he.1 he.2
      have hsq : G.src ⟨Q u, hqm⟩ = u := (hcsr.src _ u).mpr ⟨q1, hqe⟩
      intro hlt
      exact q4 hqm hqe (lt_of_le_of_lt (hsort ⟨Q u, hqm⟩ e (hsq.trans hsrc.symm) he.1 _) hlt)
    have hsplit := slots_split (G := G) q1 q2
    have hrest : ∀ v ∈ ys, st1.d v = dis (s := s) v ∧
        ScanStop st (dis (s := s) v) v (st.wa "gSt" v) (Q v) B := fun v hv => by
      obtain ⟨h1, h2⟩ := h v (by simp [hv])
      exact ⟨(hstab1 v h1).trans h1, h2⟩
    obtain ⟨k, hk⟩ := fold_full hsort hcsr Q ys st1 hw1 hI1 hB1 hrest
    refine ⟨k + (slots G (Q u) (st.wa "gSt" ((u : ℕ) + 1))).length, ?_⟩
    simp only [List.flatMap_cons, List.foldl_append]
    rw [hsplit, List.foldl_append, ← hst1, foldl_invalid _ st1 htail, foldl_shift, hk]
    simp only [BM.RSt.mk.injEq, true_and] <;> omega

/-- The full ranges of a vertex row enumerate the out-edges of the row's vertices. -/
theorem fullSlots_enum {st : State ℝ≥0} (hcsr : CSRAt st G) {xs : List (Fin G.n)}
    (hxs : xs.Nodup) :
    BM.Enumerates G (xs.flatMap (fun u : Fin G.n =>
      slots G (st.wa "gSt" u) (st.wa "gSt" ((u : ℕ) + 1)))) xs.toFinset := by
  have hb : ∀ u : Fin G.n, u ∈ xs → st.wa "gSt" u ≤ st.wa "gSt" u ∧
      st.wa "gSt" ((u : ℕ) + 1) ≤ st.wa "gSt" ((u : ℕ) + 1) := fun _ _ => ⟨le_rfl, le_rfl⟩
  refine ⟨flatSlots_nodup hcsr hxs hb, fun e => ?_⟩
  rw [flatSlots_mem hcsr hb e, List.mem_toFinset]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, ((hcsr.src e (G.src e)).mp rfl).1, ((hcsr.src e (G.src e)).mp rfl).2⟩

theorem Reps.shift {c0 bcap ecap lv bse : ℕ} {B Bi : WLab G s} {Kb : LReg} {kbf : String}
    {Klo : LReg} {klof : String} {r : State ℝ≥0} {fs : BM.RSt G s}
    {H' : Fin G.n → ℕ → List (Fin G.m)}
    (h : Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r fs H') (k : ℕ) :
    Reps c0 bcap ecap lv bse B Bi Kb kbf Klo klof r ⟨fs.d, fs.g, fs.Dc, fs.c + k⟩ H' :=
  ⟨h.lab, h.dr, h.ba, h.live, h.pool, h.inv, h.bd, h.wk, h.gr, h.csr, h.kb, h.klo, h.uselo,
    h.dslv, h.dsb⟩

open Classical in
/-- **BM.27–28, the `W'` relaxations.**  For the `W'` row `xs` (complete vertices), the scan
from the range heads ends representing `L.foldl (relaxInsCc dlOps T B (some B'f)) fs0` for the
enumeration `L` of all out-edges of `W'` (`fullSlots_enum`), sets the pointer invariant at `B`
for `W'`, and costs `≤ 124 ×` the Layer-A cost `+ 38 |W'| + 2`. -/
theorem wScan_spec (T : ℕ) {c0 bcap ecap lv bse : ℕ} {B Bf : WLab G s} {Kb : LReg}
    {kbf : String} {Klo : LReg} {klof : String} (hy : BlkHyg Kb kbf Klo klof)
    (hl : LoopHyg Kb kbf Klo klof) (hli : ∀ a ∈ Kb.ws ++ [kbf] ++ Klo.ws ++ [klof], a ≠ "sp.i")
    (hsort : CSRSorted G s) (lenE elemE : WExpr) (st : State ℝ≥0) (fs0 : BM.RSt G s)
    (H0 : Fin G.n → ℕ → List (Fin G.m))
    (h0 : Reps c0 bcap ecap lv bse B Bf Kb kbf Klo klof st fs0 H0)
    (xs : List (Fin G.n)) (hxs : xs.Nodup)
    (hlenE : ∀ r, FrameW st r → evalW r lenE = some xs.length)
    (helemE : ∀ r (i : ℕ) (hi : i < xs.length), FrameW st r → r.w "sp.i" = i →
      evalW r elemE = some (xs[i] : ℕ))
    (hcomp : ∀ u ∈ xs, fs0.d u = dis (s := s) u ∧ fs0.d u ≠ ⊤)
    (hptrl : G.n ≤ st.wlen "sp.ptr") (hncap : G.n + 2 ≤ st.cap)
    (hfr : fs0.g.fresh + G.m + 1 < ecap)
    (hcapD : 2 * fs0.Dc.blocks.length + ecap + bse + 4 < st.cap)
    (hB : st.cost + (xs.length + 1) * ((G.m + 1) * CE fs0.Dc.blocks.length + 101) ≤
      c0 + st.cap)
    (hm : G.m + 2 ≤ st.cap) :
    Runs realOps (wScan lenE elemE Kb kbf Klo klof) st (fun r =>
      ∃ H' : Fin G.n → ℕ → List (Fin G.m),
      HExt H0 (vc st) H' (vc r) ∧
      Reps c0 bcap ecap lv bse B Bf Kb kbf Klo klof r
        ((xs.flatMap (fun u : Fin G.n => slots G (st.wa "gSt" u) (st.wa "gSt" ((u : ℕ) + 1)))).foldl
          (BM.relaxInsCc (BM.dlOps G s) T B (some Bf)) fs0) H' ∧
      (∀ u ∈ xs, PtrAt r (fs0.d u) u B) ∧
      (∀ u : Fin G.n, u ∉ xs → r.wa "sp.ptr" u = st.wa "sp.ptr" u) ∧
      r.wlen "sp.ptr" = st.wlen "sp.ptr" ∧ FrameW st r ∧ st.cost ≤ r.cost ∧
      r.cost + 124 * fs0.c ≤ st.cost + 124 * ((xs.flatMap (fun u : Fin G.n =>
        slots G (st.wa "gSt" u) (st.wa "gSt" ((u : ℕ) + 1)))).foldl
          (BM.relaxInsCc (BM.dlOps G s) T B (some Bf)) fs0).c + 38 * xs.length + 2) := by
  have hP0 : ∀ u : Fin G.n, u ∈ xs → st.wa "gSt" u ≤ st.wa "gSt" u ∧
      st.wa "gSt" u ≤ st.wa "gSt" ((u : ℕ) + 1) := fun u _ => ⟨le_rfl, h0.csr.le u⟩
  refine (scanLoop_spec T hy hl hli lenE elemE _ st fs0 H0 h0 xs hxs
    (fun u => st.wa "gSt" u) hlenE helemE ?_ hP0 hcomp hptrl hncap hfr hcapD hB hm).mono ?_
  · intro r u hr _ hru _
    have hg := Unchanged.warr hr "gSt" (by decide)
    have hlen := h0.csr.len
    have hu := u.isLt
    rw [evalW_load_of (j := (u : ℕ)) (by rw [evalW_var]; exact congrArg some hru)
      (by rw [hg.2]; omega), hg.1]
  · rintro r ⟨H', Q, hQ, hrest, hwl, hE, hR, hFW, hclo, hrel⟩
    have hQ' : ∀ u ∈ xs, fs0.d u = dis (s := s) u ∧
        ScanStop st (dis (s := s) u) u (st.wa "gSt" u) (Q u) B := fun u hu => by
      have h1 := (hcomp u hu).1
      exact ⟨h1, h1 ▸ (hQ u hu).1⟩
    obtain ⟨k, hk⟩ := fold_full (lo' := Bf) hsort h0.csr Q xs fs0 h0.wk h0.inv h0.bd hQ'
    refine ⟨H', hE, ?_, fun u hu => ?_, hrest, hwl, hFW, hclo, ?_⟩
    · rw [hk]; exact hR.shift k
    · have hg := (Unchanged.warr hFW "gSt" (by decide)).1
      unfold PtrAt
      rw [(hQ u hu).2]
      unfold ScanStop
      rw [hg]
      exact (hQ u hu).1
    · rw [hk]
      show r.cost + 124 * fs0.c ≤ st.cost + 124 * (((xs.flatMap (fun u : Fin G.n =>
        slots G (st.wa "gSt" u) (Q u))).foldl (BM.relaxInsCc (BM.dlOps G s) T B (some Bf)) fs0).c
        + k) + 38 * xs.length + 2
      omega

end Frontier.CHD.WinScan
