import Frontier.CHD.TreeRAM9

/-!
# Frontier.CHD.TreeRAM10 — one-time allocation of the tree-layer and tail arrays (owner agent-03)

**NON-GATE** (Layer B).  `allocFP` allocates (zero-initialised, `walloc`) the arrays of the B-L2 tree layer (`TA0`) and of the
FindPivots tail (`PTA`), of size `gN` (`pt.GV`: `2 gN`), once, in the spine prologue.  `allocFP_spec`: `TA0 N ∧ PTA N`
afterwards, nothing else changes except the allocated arrays, cost `25 N + 25`.  `allocAll` / `allocAll_spec` is the generic
allocation of a list of arrays.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V}

/-- Allocate every array of `names` with size `e`. -/
def allocAll (names : List String) (e : WExpr) : Stmt := names.foldr (fun a acc => .seq (.walloc a e) acc) .skip

theorem allocAll_spec {e : WExpr} {k : ℕ} {w0 : String → ℕ} {cap0 : ℕ}
    (he : ∀ s : State V, s.w = w0 → s.cap = cap0 → evalW s e = some k) :
    ∀ (names : List String) (s : State V), s.w = w0 → s.cap = cap0 →
      Runs ops (allocAll names e) s (fun s' => (∀ a ∈ names, s'.wlen a = k ∧ ∀ j, s'.wa a j = 0) ∧
        (∀ a, a ∉ names → s'.wlen a = s.wlen a ∧ s'.wa a = s.wa a) ∧ s'.w = s.w ∧ s'.v = s.v ∧ s'.va = s.va ∧
        s'.vlen = s.vlen ∧ s'.cap = s.cap ∧ s'.procs = s.procs ∧ s'.cost = s.cost + names.length * (k + 1) + 1)
  | [], s, _, _ => runs_skip ⟨fun a ha => absurd ha List.not_mem_nil, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl,
      rfl, by simp⟩
  | a :: names, s, hw, hc => by
    apply runs_seq
    refine runs_walloc (k := k) (he s hw hc) ?_
    refine Runs.mono (allocAll_spec he names ((s.allocW a k).charge (k + 1)) (by simp [hw]) (by simp [hc])) ?_
    rintro s' ⟨hin, hout, h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨fun b hb => ?_, fun b hb => ?_, by rw [h1]; rfl, by rw [h2]; rfl, by rw [h3]; rfl, by rw [h4]; rfl,
      by rw [h5]; rfl, by rw [h6]; rfl, by rw [h7]; simp [List.length_cons]; ring⟩
    · by_cases hbn : b ∈ names
      · exact hin b hbn
      · have hba : b = a := by
          rcases List.mem_cons.mp hb with h | h
          · exact h
          · exact absurd h hbn
        subst hba
        obtain ⟨l1, l2⟩ := hout b hbn
        refine ⟨by rw [l1]; simp, fun j => by rw [l2]; simp⟩
    · have hba : b ≠ a := fun h => hb (h ▸ List.mem_cons_self)
      have hbn : b ∉ names := fun h => hb (List.mem_cons_of_mem _ h)
      obtain ⟨l1, l2⟩ := hout b hbn
      refine ⟨by rw [l1]; simp [hba], by rw [l2]; funext j; simp [hba]⟩

/-- The arrays of size `gN`. -/
def fpArrsN : List String :=
  ["tr.tid", "tr.nx", "fp.par", "tr.inP", "tr.hd", "tr.tl", "tr.ln",
   "pt.an", "pt.af", "pt.al", "pt.nx", "fp.inS", "fp.inQ", "pt.as", "pt.PT", "pt.PF", "pt.PL", "pt.PN",
   "pt.GO", "pt.GL", "fp.TV", "fp.toff", "fp.tlen"]

/-- (Spine prologue) Allocate the tree-layer and tail arrays. -/
def allocFP : Stmt := .seq (allocAll fpArrsN (.var "gN")) (.walloc "pt.GV" (.add (.var "gN") (.var "gN")))

/-- **The allocation** establishes agent-09's `TA` (`TA0`) and the tail's `PTA`, touching only the allocated arrays. -/
theorem allocFP_spec {st : State V} {N : ℕ} (hN : st.w "gN" = N) (hcap : 2 * N < st.cap) :
    Runs ops allocFP st (fun st' => TA0 N st' ∧ PTA N st' ∧
      (∀ a, a ∉ "pt.GV" :: fpArrsN → st'.wlen a = st.wlen a ∧ st'.wa a = st.wa a) ∧ st'.w = st.w ∧
      st'.v = st.v ∧ st'.va = st.va ∧ st'.vlen = st.vlen ∧ st'.cap = st.cap ∧ st'.procs = st.procs ∧
      st'.cost = st.cost + 25 * N + 25) := by
  apply runs_seq
  refine Runs.mono (allocAll_spec (ops := ops) (e := .var "gN") (k := N) (w0 := st.w) (cap0 := st.cap)
    (fun s hw _ => by simp [hw, hN]) fpArrsN st rfl rfl) ?_
  rintro s1 ⟨hin, hout, h1, h2, h3, h4, h5, h6, h7⟩
  have hN1 : s1.w "gN" = N := by rw [h1]; exact hN
  refine runs_walloc (k := N + N) (by simp [hN1, fit_of_lt (show N + N < s1.cap by rw [h5]; omega)]) ?_
  have hA : ∀ a, a ∈ fpArrsN → ((s1.allocW "pt.GV" (N + N)).charge (N + N + 1)).wlen a = N ∧
      ∀ j, ((s1.allocW "pt.GV" (N + N)).charge (N + N + 1)).wa a j = 0 := by
    intro a ha
    have hne : a ≠ "pt.GV" := by rintro rfl; simp [fpArrsN] at ha
    obtain ⟨l1, l2⟩ := hin a ha
    exact ⟨by simp [hne, l1], fun j => by simp [hne, l2]⟩
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun v => (hA "tr.inP" (by decide)).2 v⟩,
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      fun x _ => by rw [(hA "fp.inS" (by decide)).2 x]; simp,
      fun x _ => by rw [(hA "fp.inQ" (by decide)).2 x]; simp,
      fun x _ => by rw [(hA "pt.as" (by decide)).2 x]; simp⟩,
    fun a ha => ?_, by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5], by simp [h6], ?_⟩
  all_goals first
    | exact (hA _ (by decide)).1.ge
    | skip
  · simp <;> omega
  · have hne : a ≠ "pt.GV" := fun h => ha (h ▸ List.mem_cons_self)
    have hnin : a ∉ fpArrsN := fun h => ha (List.mem_cons_of_mem _ h)
    obtain ⟨l1, l2⟩ := hout a hnin
    exact ⟨by simp [hne, l1], by funext j; simp [hne, l2]⟩
  · simp [h7, fpArrsN]; ring

end Frontier.CHD.PartitionRAM
