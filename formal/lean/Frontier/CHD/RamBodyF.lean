import Frontier.CHD.RamBodyI
import Frontier.CHD.DGlobal

/-!
# Frontier.CHD.RamBodyF — frame lemmas for the level body (owner: agent-01)

**NON-GATE** (B-L4).  Reusable frame facts of the spine predicates:
* `NoAlloc` / `Runs.lens`: statements without allocations or calls keep all array lengths;
* `static_frame` / `static_of_unch`: `Static` from the lengths of the spine arrays and the static
  tables;
* `SetRow.toList`, `setRow_of_eq`, `ptrOK_congr`, `clear_frame`.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.RamBody

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamLevel
  Frontier.CHD.BM Frontier.CHD.RamBaseCase Frontier.CHD.LabTab Frontier.CHD.RamSpine
  Frontier.CHD.RamInit WExpr Stmt

/-! ## Statements without allocation keep all lengths (agent-04's `DGlob.NoAlloc`) -/

section noalloc

variable {V : Type} {ops : VOps V}

/-- Boolean check of `DGlob.NoAlloc` (for `decide` on concrete statements). -/
def naB : Stmt → Bool
  | .walloc _ _ => false
  | .valloc _ _ => false
  | .call _ => false
  | .seq a b => naB a && naB b
  | .ite _ a b => naB a && naB b
  | .while _ b => naB b
  | _ => true

theorem noAlloc_of_naB : ∀ c : Stmt, naB c = true → DGlob.NoAlloc c
  | .skip, _ => trivial
  | .wset _ _, _ => trivial
  | .vset _ _, _ => trivial
  | .vle _ _ _, _ => trivial
  | .wstore _ _ _, _ => trivial
  | .vstore _ _ _, _ => trivial
  | .walloc _ _, h => by simp [naB] at h
  | .valloc _ _, h => by simp [naB] at h
  | .call _, h => by simp [naB] at h
  | .seq a b, h => by
    simp only [naB, Bool.and_eq_true] at h
    exact ⟨noAlloc_of_naB a h.1, noAlloc_of_naB b h.2⟩
  | .ite _ a b, h => by
    simp only [naB, Bool.and_eq_true] at h
    exact ⟨noAlloc_of_naB a h.1, noAlloc_of_naB b h.2⟩
  | .while _ b, h => noAlloc_of_naB b h

/-- Add the lengths to any postcondition of an allocation-free statement. -/
theorem Runs.lens {c : Stmt} {s : State ℝ≥0} {Q : State ℝ≥0 → Prop} (hc : naB c = true)
    (h : Runs realOps c s Q) : Runs realOps c s (fun r => Q r ∧ r.wlen = s.wlen ∧ r.vlen = s.vlen) :=
  (DGlob.Runs.keep_len h (noAlloc_of_naB c hc)).mono fun _ ⟨h1, h2, h3⟩ => ⟨h1, funext h2, funext h3⟩

end noalloc

/-! ## `Static` frames -/

section static

variable {G : Graph} {s : Fin G.n}

/-- **`Static` from the lengths of the spine arrays and the static tables.** -/
theorem static_frame {st r : State ℝ≥0} {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    (h : Static st G LF body τf Mf) (hwl : ∀ a ∈ spArrs, r.wlen a = st.wlen a)
    (hvl : r.vlen "sl.l" = st.vlen "sl.l")
    (hwa : ∀ a ∈ ["gSt", "gHead", "cp.tau", "cp.M", "hp_P"], r.wa a = st.wa a)
    (hgW : r.va "gW" = st.va "gW") (hgWl : r.vlen "gW" = st.vlen "gW")
    (hn : r.w "n" = st.w "n") (hgN : r.w "gN" = st.w "gN") (hhp : r.w "hp_n" = st.w "hp_n")
    (hpr : r.procs = st.procs) (hcap : r.cap = st.cap) : Static r G LF body τf Mf := by
  have wl : ∀ a ∈ spArrs, r.wlen a = st.wlen a := hwl
  have mem : ∀ a ∈ rowArrs ++ lenArrs ++ slotW ++ ["sp.xm", "sp.ptr", "cp.tau", "cp.M", "gSt",
      "gHead", "gKeep", "gRep", "hp_A", "hp_P"] ++ labW, a ∈ spArrs := fun a ha => ha
  refine ⟨by rw [hn]; exact h.n, by rw [hgN]; exact h.gN, ?_, ?_, by rw [hpr]; exact h.proc,
    fun a ha => by rw [wl a (mem a (by simp [ha]))]; exact h.rows a ha,
    fun a ha => by rw [wl a (mem a (by simp [ha]))]; exact h.lens a ha,
    fun i hi => ?_, by rw [wl _ (mem _ (by simp))]; exact h.xm,
    by rw [wl _ (mem _ (by simp))]; exact h.ptr, by rw [wl _ (mem _ (by simp))]; exact h.tau,
    by rw [wl _ (mem _ (by simp))]; exact h.Ml,
    fun l hl => by rw [hwa _ (by simp)]; exact h.tauv l hl,
    fun l hl => by rw [hwa _ (by simp)]; exact h.Mv l hl, ?_, by rw [hcap]; exact h.cap,
    fun l hl => by rw [hcap]; exact h.tauCap l hl, fun l hl => by rw [hcap]; exact h.MCap l hl⟩
  · obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h.graph
    refine ⟨⟨by rw [wl _ (mem _ (by simp))]; exact h1, fun i hi => ?_⟩, ⟨by rw [hgWl]; exact h3,
      fun i hi => ?_⟩⟩
    · rw [hwa _ (by simp)]; exact h2 i hi
    · rw [hgW]; exact h4 i hi
  · obtain ⟨c1, c2, c3, c4⟩ := h.csr
    refine ⟨by rw [wl _ (mem _ (by simp))]; exact c1, fun u => ?_, fun u => ?_, fun e u => ?_⟩
    · rw [hwa _ (by simp)]; exact c2 u
    · rw [hwa _ (by simp)]; exact c3 u
    · rw [hwa _ (by simp)]; exact c4 e u
  · have := h.slots i hi
    exact ⟨by rw [hvl]; exact this.l, by rw [wl _ (mem _ (by simp [slotW]))]; exact this.h,
      by rw [wl _ (mem _ (by simp [slotW]))]; exact this.v,
      by rw [wl _ (mem _ (by simp [slotW]))]; exact this.e,
      by rw [wl _ (mem _ (by simp [slotW]))]; exact this.r,
      by rw [wl _ (mem _ (by simp [slotW]))]; exact this.f⟩
  · obtain ⟨e1, e2, e3, e4⟩ := h.heap
    exact ⟨by rw [hhp]; exact e1, by rw [wl _ (mem _ (by simp))]; exact e2,
      by rw [wl _ (mem _ (by simp))]; exact e3, fun v hv => by rw [hwa _ (by simp)]; exact e4 v hv⟩

/-- `Static` survives every fragment writing no spine array, no `sl.l`/`gW` and not `n`, `gN`,
`hp_n`. -/
theorem static_of_unch {st r : State ℝ≥0} {LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ}
    {wa va wr vr : List String} (h : Static st G LF body τf Mf) (hU : Unchanged st r wa va wr vr)
    (hwa : ∀ a ∈ spArrs, a ∉ wa) (hsl : "sl.l" ∉ va) (hgw : "gW" ∉ va) (hn : "n" ∉ wr)
    (hgN : "gN" ∉ wr) (hhp : "hp_n" ∉ wr) : Static r G LF body τf Mf :=
  static_frame h (fun a ha => (hU.warr a (hwa a ha)).2) (hU.varr _ hsl).2
    (fun a ha => (hU.warr a (hwa a (by simp at ha; rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      simp [spArrs]))).1) (hU.varr _ hgw).1 (hU.varr _ hgw).2 (hU.wreg _ hn) (hU.wreg _ hgN)
    (hU.wreg _ hhp) hU.procs hU.cap

end static

/-! ## Rows, pointers, clears -/

section rows

variable {G : Graph} {s : Fin G.n}

/-- A set row as a duplicate-free list of vertices. -/
theorem SetRow.toList {st : State ℝ≥0} {arr len : String} {l : ℕ} {X : Finset (Fin G.n)}
    (h : SetRow st arr len l X) :
    ∃ lX : List (Fin G.n), RowRep st arr len G.n l (lX.map Fin.val) ∧ lX.Nodup ∧ lX.toFinset = X := by
  classical
  obtain ⟨xs, hR, hnd, hmem⟩ := h
  have hlt : ∀ x ∈ xs, x < G.n := by
    intro x hx; obtain ⟨u, -, rfl⟩ := (hmem x).mp hx; exact u.2
  refine ⟨xs.pmap (fun x hx => (⟨x, hx⟩ : Fin G.n)) hlt, ?_, ?_, ?_⟩
  · have : (xs.pmap (fun x hx => (⟨x, hx⟩ : Fin G.n)) hlt).map Fin.val = xs := by
      rw [List.map_pmap]; simp
    rw [this]; exact hR
  · exact List.Nodup.pmap (fun _ _ _ _ h => by simpa using h) hnd
  · ext u
    simp only [List.mem_toFinset, List.mem_pmap]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨v, hv, hvx⟩ := (hmem x).mp hx
      rw [show (⟨x, _⟩ : Fin G.n) = v from Fin.ext hvx.symm]; exact hv
    · intro hu
      exact ⟨u, (hmem u).mpr ⟨u, hu, rfl⟩, rfl⟩

/-- A set row from a duplicate-free list of vertices. -/
theorem SetRow.ofList {st : State ℝ≥0} {arr len : String} {l : ℕ} {lX : List (Fin G.n)}
    (hR : RowRep st arr len G.n l (lX.map Fin.val)) (hnd : lX.Nodup) :
    SetRow st arr len l lX.toFinset :=
  ⟨lX.map Fin.val, hR, hnd.map Fin.val_injective, fun x => by
    simp only [List.mem_map, List.mem_toFinset]⟩

theorem setRow_of_eq {st st' : State ℝ≥0} {arr len : String} {l : ℕ} {X : Finset (Fin G.n)}
    (h : SetRow st arr len l X) (hwl : st'.wlen arr = st.wlen arr)
    (hwl' : st'.wlen len = st.wlen len) (hlen : st'.wa len l = st.wa len l)
    (harr : ∀ i < G.n, st'.wa arr (l * G.n + i) = st.wa arr (l * G.n + i)) :
    SetRow st' arr len l X := by
  obtain ⟨xs, hR, hnd, hmem⟩ := h
  exact ⟨xs, hR.of_eq hwl hwl' hlen harr, hnd, hmem⟩

theorem setRow_of_unch {st st' : State ℝ≥0} {arr len : String} {l : ℕ} {X : Finset (Fin G.n)}
    {wa va wr vr : List String} (h : SetRow st arr len l X) (hU : Unchanged st st' wa va wr vr)
    (ha : arr ∉ wa) (hl : len ∉ wa) : SetRow st' arr len l X :=
  setRow_of_eq h (hU.warr _ ha).2 (hU.warr _ hl).2 (by rw [(hU.warr _ hl).1])
    (fun i _ => by rw [(hU.warr _ ha).1])

/-- The pointer invariant only reads `gSt`, `sp.ptr` and the label of `u`. -/
theorem ptrOK_congr {st r : State ℝ≥0} {d d' : Labels G s} {B : WLab G s} {u : Fin G.n}
    (h : PtrOK st d B u) (hgs : r.wa "gSt" = st.wa "gSt") (hp : r.wa "sp.ptr" u = st.wa "sp.ptr" u)
    (hd : d' u = d u) : PtrOK r d' B u := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by rw [hgs, hp]; exact h1, by rw [hgs, hp]; exact h2, fun j hj h5 h6 => ?_,
    fun hq h7 => ?_⟩
  · rw [hd]; exact h3 j hj (by rw [← hgs]; exact h5) (by rw [← hp]; exact h6)
  · rw [hd]
    have := h4 (by rw [← hp]; exact hq) (by rw [← hp, ← hgs]; exact h7)
    simpa [hp] using this

/-- `Clear` at `l` from the three arrays below level `l + 1`. -/
theorem clear_frame {st r : State ℝ≥0} {n l : ℕ} (h : Clear st n l)
    (hg : ∀ i < (l + 1) * n, r.wa "sp.g" i = st.wa "sp.g" i)
    (hu : ∀ i < (l + 1) * n, r.wa "sp.inU" i = st.wa "sp.inU" i)
    (hx : ∀ x < n, r.wa "sp.xm" x = st.wa "sp.xm" x) : Clear r n l := by
  have key : ∀ l' ≤ l, ∀ x < n, l' * n + x < (l + 1) * n := fun l' hl' x hx => by
    have : (l' + 1) * n ≤ (l + 1) * n := Nat.mul_le_mul_right _ (by omega)
    have : l' * n + x < (l' + 1) * n := by rw [Nat.succ_mul]; omega
    omega
  exact ⟨fun l' hl' x hx => by rw [hg _ (key l' hl' x hx)]; exact h.g l' hl' x hx,
    fun l' hl' x hx => by rw [hu _ (key l' hl' x hx)]; exact h.inU l' hl' x hx,
    fun x hx' => by rw [hx x hx']; exact h.xm x hx'⟩

theorem clear_of_unch {st r : State ℝ≥0} {n l : ℕ} {wa va wr vr : List String} (h : Clear st n l)
    (hU : Unchanged st r wa va wr vr) (hg : "sp.g" ∉ wa) (hu : "sp.inU" ∉ wa)
    (hx : "sp.xm" ∉ wa) : Clear r n l :=
  clear_frame h (fun i _ => by rw [(hU.warr _ hg).1]) (fun i _ => by rw [(hU.warr _ hu).1])
    (fun x _ => by rw [(hU.warr _ hx).1])

theorem clear_mono {st : State ℝ≥0} {n l l' : ℕ} (h : Clear st n l) (hl : l' ≤ l) : Clear st n l' :=
  ⟨fun l'' h'' x hx => h.g l'' (le_trans h'' hl) x hx,
    fun l'' h'' x hx => h.inU l'' (le_trans h'' hl) x hx, h.xm⟩

end rows

end Frontier.CHD.RamBody
