import Frontier.RAMRep
import Frontier.RAMWP
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Sort
import Mathlib.Order.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Frontier.CHD.MergeSort — a verified RAM bottom-up merge sort (agent-06; Layer B, NON-GATE)

Layer A: `mergePass le w L` merges consecutive chunks `[2jw, 2jw+w)`, `[2jw+w, 2(j+1)w)` of `L` with core
`List.merge`; `msortIter le w p L` iterates `p` passes with widths `w, 2w, 4w, …`.  Every pass is a permutation,
turns `w`-chunk-sorted lists into `2w`-chunk-sorted lists, and `p` passes from width `1` with `|L| ≤ 2^p` give a
sorted permutation (for a transitive, total Boolean relation).

Layer B: `sortRange W H` sorts the slots `[a, b)` of the value array `W` together with the parallel word array
`H` by the key `(W[p], H[p])` (lexicographic; values compared by `ops.le`, words by `lt`), for `a = ms_a`,
`b = ms_b`.  It allocates its own scratch arrays `ms_W` (values) and `ms_H` (words) of length `b - a` and writes
only the registers `msRegs`.  Each pass merges the blocks of width `w` from the source range into the scratch
arrays (merge loop = `List.merge` step by step), then copies back; widths `1, 2, 4, …` until `w ≥ b - a`.

Main theorem: `sortRange_spec` (generic value semantics with a total preorder `ops.le`) and
`sortRange_spec_real` (`realOps`): the range ends sorted by `keyLe` and a permutation of the input pairs, all
other cells of `W`, `H` and everything outside the write sets `[H, ms_H] [W, ms_W] msRegs []` are unchanged
(`RAMRep.Unchanged`), and the cost is at most `40 (b - a + 1) (log₂ (b - a) + 1)`.
-/

namespace Frontier.CHD.MergeSort


open List

variable {α : Type*} (le : α → α → Bool)

/-- Merge `k` consecutive pairs of `w`-chunks. -/
def mergeBlocks (w : ℕ) : ℕ → List α → List α
  | 0, L => L
  | k + 1, L => merge (L.take w) ((L.drop w).take w) le ++ mergeBlocks w k (L.drop (2 * w))

/-- One pass of width `w` (fuel `|L|` is enough since each block consumes `≥ 2` elements for `w ≥ 1`). -/
def mergePass (w : ℕ) (L : List α) : List α := mergeBlocks le w L.length L

/-- The `w`-chunks of `L` are sorted. -/
def ChunkSorted (w : ℕ) (L : List α) : Prop :=
  ∀ j : ℕ, ((L.drop (j * w)).take w).Pairwise (fun a b => le a b = true)

variable {le}

theorem mergeBlocks_nil (w : ℕ) : ∀ k, mergeBlocks le w k ([] : List α) = []
  | 0 => rfl
  | k + 1 => by simp [mergeBlocks, mergeBlocks_nil w k]

theorem mergeBlocks_perm (w : ℕ) : ∀ (k : ℕ) (L : List α), (mergeBlocks le w k L).Perm L
  | 0, L => Perm.refl L
  | k + 1, L => by
    simp only [mergeBlocks]
    have h1 := merge_perm_append le (xs := L.take w) (ys := (L.drop w).take w)
    have h2 := mergeBlocks_perm w k (L.drop (2 * w))
    have e : L = L.take w ++ (L.drop w).take w ++ L.drop (2 * w) := by
      have hd : L.drop (2 * w) = (L.drop w).drop w := by rw [List.drop_drop]; congr 1; omega
      rw [hd, List.append_assoc, List.take_append_drop, List.take_append_drop]
    calc merge (L.take w) ((L.drop w).take w) le ++ mergeBlocks le w k (L.drop (2 * w))
        ~ (L.take w ++ (L.drop w).take w) ++ L.drop (2 * w) := Perm.append h1 h2
      _ = L := e.symm

theorem mergePass_perm (w : ℕ) (L : List α) : (mergePass le w L).Perm L :=
  mergeBlocks_perm w _ L


theorem length_mergeBlocks (w : ℕ) : ∀ (k : ℕ) (L : List α), (mergeBlocks le w k L).length = L.length :=
  fun k L => (mergeBlocks_perm w k L).length_eq

theorem length_mergePass (w : ℕ) (L : List α) : (mergePass le w L).length = L.length :=
  (mergePass_perm w L).length_eq

/-- `mergeBlocks` with fuel at least `|L|` (and `w ≥ 1`) is idempotent in the fuel. -/
theorem mergeBlocks_fuel (w : ℕ) (hw : 1 ≤ w) :
    ∀ (k k' : ℕ) (L : List α), L.length ≤ k → L.length ≤ k' → mergeBlocks le w k L = mergeBlocks le w k' L
  | 0, k', L, hk, _ => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [mergeBlocks_nil, mergeBlocks_nil]
  | k + 1, 0, L, _, hk' => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [mergeBlocks_nil, mergeBlocks_nil]
  | k + 1, k' + 1, L, hk, hk' => by
    simp only [mergeBlocks]
    by_cases h : L = []
    · subst h; simp [mergeBlocks_nil]
    · have hlen : (L.drop (2 * w)).length < L.length := by
        simp only [List.length_drop]
        have : 0 < L.length := List.length_pos_of_ne_nil h
        omega
      rw [mergeBlocks_fuel w hw k k' (L.drop (2 * w)) (by omega) (by omega)]

variable (trans : ∀ a b c : α, le a b = true → le b c = true → le a c = true)
  (total : ∀ a b : α, (le a b || le b a) = true)

include trans total in
/-- Chunk sortedness doubles after one pass. -/
theorem mergeBlocks_chunkSorted (w : ℕ) (hw : 1 ≤ w) :
    ∀ (k : ℕ) (L : List α), L.length ≤ 2 * w * k → ChunkSorted le w L →
      ChunkSorted le (2 * w) (mergeBlocks le w k L)
  | 0, L, hk, _ => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hk)
    subst this; intro j; simp [mergeBlocks]
  | k + 1, L, hk, hL => by
    simp only [mergeBlocks]
    set M := merge (L.take w) ((L.drop w).take w) le with hM
    set R := mergeBlocks le w k (L.drop (2 * w)) with hR
    have hMs : M.Pairwise (fun a b => le a b = true) := by
      have h0 := hL 0
      have h1 := hL 1
      simp only [zero_mul, List.drop_zero, one_mul] at h0 h1
      exact pairwise_merge trans total _ _ h0 h1
    have hRs : ChunkSorted le (2 * w) R := by
      apply mergeBlocks_chunkSorted w hw k
      · simp only [List.length_drop]; rw [Nat.mul_succ] at hk; omega
      · intro j
        have := hL (j + 2)
        rw [List.drop_drop]
        convert this using 3
        ring
    have hMlen : M.length = min w L.length + min w (L.length - w) := by
      simp [hM, List.length_merge, List.length_take, List.length_drop]
    intro j
    rcases Nat.lt_or_ge L.length (2 * w) with hsmall | hbig
    · -- everything fits in the first block; `R = []`
      have hRnil : R = [] := by
        rw [hR]
        have : L.drop (2 * w) = [] := List.drop_eq_nil_of_le (by omega)
        rw [this, mergeBlocks_nil]
      rw [hRnil, List.append_nil]
      rcases j with _ | j
      · simp only [zero_mul, List.drop_zero]
        exact hMs.sublist (List.take_sublist _ _)
      · have h2 : 2 * w ≤ (j + 1) * (2 * w) := Nat.le_mul_of_pos_left _ (by omega)
        have : M.drop ((j + 1) * (2 * w)) = [] := List.drop_eq_nil_of_le (by rw [hMlen]; omega)
        rw [this]; simp
    · have hMlen2 : M.length = 2 * w := by rw [hMlen]; omega
      rcases j with _ | j
      · simp only [zero_mul, List.drop_zero]
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        exact hMs
      · have e : (j + 1) * (2 * w) = M.length + j * (2 * w) := by rw [hMlen2]; ring
        rw [e, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
          show M.length + j * (2 * w) - M.length = j * (2 * w) by omega]
        exact hRs j

include trans total in
theorem mergePass_chunkSorted (w : ℕ) (hw : 1 ≤ w) (L : List α) (hL : ChunkSorted le w L) :
    ChunkSorted le (2 * w) (mergePass le w L) := by
  apply mergeBlocks_chunkSorted trans total w hw
  · nlinarith
  · exact hL

/-- Iterate passes: widths `w, 2w, 4w, …` (`p` passes). -/
def msortIter (le : α → α → Bool) : ℕ → ℕ → List α → List α
  | _, 0, L => L
  | w, p + 1, L => msortIter le (2 * w) p (mergePass le w L)

theorem msortIter_perm : ∀ (w p : ℕ) (L : List α), (msortIter le w p L).Perm L
  | _, 0, L => Perm.refl L
  | w, p + 1, L => (msortIter_perm (2 * w) p _).trans (mergePass_perm w L)

include trans total in
theorem msortIter_chunkSorted : ∀ (w p : ℕ), 1 ≤ w → ∀ (L : List α), ChunkSorted le w L →
    ChunkSorted le (2 ^ p * w) (msortIter le w p L)
  | w, 0, _, L, hL => by simp only [msortIter, pow_zero, one_mul]; exact hL
  | w, p + 1, hw, L, hL => by
    have h := msortIter_chunkSorted (2 * w) p (by omega) _ (mergePass_chunkSorted trans total w hw L hL)
    show ChunkSorted le (2 ^ (p + 1) * w) (msortIter le (2 * w) p (mergePass le w L))
    have e : 2 ^ (p + 1) * w = 2 ^ p * (2 * w) := by ring
    rw [e]; exact h

theorem chunkSorted_one (L : List α) : ChunkSorted le 1 L := by
  intro j
  have hlen : ((L.drop (j * 1)).take 1).length ≤ 1 := by simp
  generalize (L.drop (j * 1)).take 1 = M at hlen ⊢
  match M, hlen with
  | [], _ => exact List.Pairwise.nil
  | [a], _ => exact List.pairwise_singleton _ a
  | _ :: _ :: _, hl => simp at hl

include trans total in
/-- **Sorting theorem.**  `p` passes from width `1` with `|L| ≤ 2^p` give a sorted permutation. -/
theorem msortIter_sorted (p : ℕ) (L : List α) (hp : L.length ≤ 2 ^ p) :
    (msortIter le 1 p L).Pairwise (fun a b => le a b = true) ∧ (msortIter le 1 p L).Perm L := by
  refine ⟨?_, msortIter_perm 1 p L⟩
  have h := msortIter_chunkSorted trans total 1 p le_rfl L (chunkSorted_one L) 0
  simp only [zero_mul, List.drop_zero, mul_one] at h
  have hlen : (msortIter le 1 p L).length ≤ 2 ^ p := by
    rw [(msortIter_perm 1 p L).length_eq]; exact hp
  rwa [List.take_of_length_le hlen] at h


/-! ### Facts used by the RAM refinement -/

/-- Fuel `k` with `|L| ≤ 2wk` is enough: any two such fuels agree. -/
theorem mergeBlocks_fuel2 (w : ℕ) (hw : 1 ≤ w) :
    ∀ (k k' : ℕ) (L : List α), L.length ≤ 2 * w * k → L.length ≤ 2 * w * k' →
      mergeBlocks le w k L = mergeBlocks le w k' L
  | 0, k', L, hk, _ => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hk)
    subst this; rw [mergeBlocks_nil, mergeBlocks_nil]
  | k + 1, 0, L, _, hk' => by
    have : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hk')
    subst this; rw [mergeBlocks_nil, mergeBlocks_nil]
  | k + 1, k' + 1, L, hk, hk' => by
    simp only [mergeBlocks]
    rw [mergeBlocks_fuel2 w hw k k' (L.drop (2 * w))
      (by simp only [List.length_drop]; rw [Nat.mul_succ] at hk; omega)
      (by simp only [List.length_drop]; rw [Nat.mul_succ] at hk'; omega)]

theorem mergePass_eq (w : ℕ) (hw : 1 ≤ w) (L : List α) (k : ℕ) (hk : L.length ≤ 2 * w * k) :
    mergePass le w L = mergeBlocks le w k L :=
  mergeBlocks_fuel2 w hw _ _ L (by nlinarith) hk

/-- Dropping `j` full blocks of output. -/
theorem mergeBlocks_drop (w : ℕ) :
    ∀ (j k : ℕ) (L : List α), j ≤ k → 2 * w * j ≤ L.length →
      (mergeBlocks le w k L).drop (2 * w * j) = mergeBlocks le w (k - j) (L.drop (2 * w * j))
  | 0, k, L, _, _ => by simp
  | j + 1, 0, L, hj, _ => by omega
  | j + 1, k + 1, L, hj, hL => by
    simp only [mergeBlocks]
    have hM : (merge (L.take w) ((L.drop w).take w) le).length = 2 * w := by
      simp only [List.length_merge, List.length_take, List.length_drop]
      rw [Nat.mul_succ] at hL; omega
    have e : 2 * w * (j + 1) = (merge (L.take w) ((L.drop w).take w) le).length + 2 * w * j := by
      rw [hM]; ring
    rw [e, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show (merge (L.take w) ((L.drop w).take w) le).length + 2 * w * j -
        (merge (L.take w) ((L.drop w).take w) le).length = 2 * w * j by omega]
    rw [mergeBlocks_drop w j k (L.drop (2 * w)) (by omega)
      (by simp only [List.length_drop]; rw [Nat.mul_succ] at hL; omega)]
    rw [List.drop_drop, show k + 1 - (j + 1) = k - j by omega]
    congr 2; rw [hM]

/-- The `j`-th block of the output. -/
theorem mergeBlocks_block (w : ℕ) (j k : ℕ) (L : List α) (hj : j < k) (hL : 2 * w * j ≤ L.length) :
    (mergeBlocks le w k L).drop (2 * w * j) =
      merge ((L.drop (2 * w * j)).take w) ((L.drop (2 * w * j + w)).take w) le ++
        mergeBlocks le w (k - j - 1) (L.drop (2 * w * j + 2 * w)) := by
  rw [mergeBlocks_drop w j k L hj.le hL]
  obtain ⟨r, hr⟩ : ∃ r, k - j = r + 1 := ⟨k - j - 1, by omega⟩
  rw [show k - j - 1 = r by omega, hr]
  simp only [mergeBlocks, List.drop_drop]

theorem msortIter_succ' (w : ℕ) : ∀ (p : ℕ) (L : List α),
    msortIter le w (p + 1) L = mergePass le (2 ^ p * w) (msortIter le w p L)
  | 0, L => by simp [msortIter]
  | p + 1, L => by
    show msortIter le (2 * w) (p + 1) (mergePass le w L) = _
    rw [msortIter_succ' (2 * w) p (mergePass le w L)]
    show mergePass le (2 ^ p * (2 * w)) (msortIter le (2 * w) p (mergePass le w L)) =
      mergePass le (2 ^ (p + 1) * w) (msortIter le (2 * w) p (mergePass le w L))
    congr 1; ring

theorem length_msortIter (w p : ℕ) (L : List α) : (msortIter le w p L).length = L.length :=
  (msortIter_perm w p L).length_eq

/-- One merge step taking the left head. -/
theorem merge_drop_left (A B : List α) (i j : ℕ) (hi : i < A.length)
    (hle : ∀ hj : j < B.length, le A[i] B[j] = true) :
    merge (A.drop i) (B.drop j) le = A[i] :: merge (A.drop (i + 1)) (B.drop j) le := by
  rw [List.drop_eq_getElem_cons hi]
  by_cases hj : j < B.length
  · rw [List.drop_eq_getElem_cons hj, cons_merge_cons, if_pos (hle hj)]
  · have hB : B.drop j = [] := List.drop_eq_nil_of_le (by omega)
    rw [hB, merge_right, merge_right]

/-- One merge step taking the right head. -/
theorem merge_drop_right (A B : List α) (i j : ℕ) (hj : j < B.length)
    (hlt : ∀ hi : i < A.length, le A[i] B[j] = false) :
    merge (A.drop i) (B.drop j) le = B[j] :: merge (A.drop i) (B.drop (j + 1)) le := by
  rw [List.drop_eq_getElem_cons hj]
  by_cases hi : i < A.length
  · rw [List.drop_eq_getElem_cons hi, cons_merge_cons, if_neg (by simp [hlt hi])]
  · have hA : A.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [hA, nil_merge, nil_merge]

/-! ### The lexicographic key -/

/-- Lexicographic order on `(value, head)` pairs from a Boolean total preorder on values. -/
def keyLe {V : Type*} (vle : V → V → Bool) (x y : V × ℕ) : Bool :=
  vle x.1 y.1 && (!vle y.1 x.1 || decide (x.2 ≤ y.2))

theorem keyLe_trans {V : Type*} {vle : V → V → Bool}
    (htr : ∀ a b c, vle a b = true → vle b c = true → vle a c = true) :
    ∀ x y z : V × ℕ, keyLe vle x y = true → keyLe vle y z = true → keyLe vle x z = true := by
  intro x y z hxy hyz
  simp only [keyLe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at *
  refine ⟨htr _ _ _ hxy.1 hyz.1, ?_⟩
  by_cases hzx : vle z.1 x.1 = true
  · right
    have hzy : vle z.1 y.1 = true := htr _ _ _ hzx hxy.1
    have hyx : vle y.1 x.1 = true := htr _ _ _ hyz.1 hzx
    have h1 : x.2 ≤ y.2 := by
      rcases hxy.2 with h | h
      · rw [hyx] at h; exact absurd h (by simp)
      · exact h
    have h2 : y.2 ≤ z.2 := by
      rcases hyz.2 with h | h
      · rw [hzy] at h; exact absurd h (by simp)
      · exact h
    omega
  · left; simpa using hzx

theorem keyLe_total {V : Type*} {vle : V → V → Bool}
    (hto : ∀ a b, vle a b = true ∨ vle b a = true) :
    ∀ x y : V × ℕ, (keyLe vle x y || keyLe vle y x) = true := by
  intro x y
  simp only [keyLe, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  by_cases h1 : vle x.1 y.1 = true <;> by_cases h2 : vle y.1 x.1 = true
  · rcases Nat.le_total x.2 y.2 with h | h
    · exact Or.inl ⟨h1, Or.inr h⟩
    · exact Or.inr ⟨h2, Or.inr h⟩
  · exact Or.inl ⟨h1, Or.inl (by simpa using h2)⟩
  · exact Or.inr ⟨h2, Or.inl (by simpa using h1)⟩
  · rcases hto x.1 y.1 with h | h
    · exact absurd h h1
    · exact absurd h h2


/-! ## Layer B: the RAM program -/

section Program

open Frontier.RAM

/-- `x := x + 1` -/
def incr (x : String) : Stmt := .wset x (.add (.var x) (.lit 1))

/-- source address `a + x` -/
def srcAt (x : String) : WExpr := .add (.var "ms_a") (.var x)

/-- copy the source pair at `a + x` into the scratch slot `k`, then `x := x + 1` -/
def takeFrom (W H x : String) : Stmt :=
  .seq (.vstore "ms_W" (.var "ms_k") (.load W (srcAt x)))
    (.seq (.wstore "ms_H" (.var "ms_k") (.load H (srcAt x))) (incr x))

/-- `ms_c := [take the left head]`: left run non-empty and (right run empty or `key(i) ≤ key(j)`),
the key being lexicographic `(W[p], H[p])`. -/
def decideStmt (W H : String) : Stmt :=
  .ite (.lt (.var "ms_i") (.var "ms_mid"))
    (.ite (.lt (.var "ms_j") (.var "ms_hi"))
      (.seq (.vle "ms_c" (.load W (srcAt "ms_i")) (.load W (srcAt "ms_j")))
        (.seq (.vle "ms_d" (.load W (srcAt "ms_j")) (.load W (srcAt "ms_i")))
          (.ite (.var "ms_c")
            (.ite (.var "ms_d")
              (.ite (.lt (.load H (srcAt "ms_j")) (.load H (srcAt "ms_i")))
                (.wset "ms_c" (.lit 0)) .skip)
              .skip)
            .skip)))
      (.wset "ms_c" (.lit 1)))
    (.wset "ms_c" (.lit 0))

/-- one output element of the current block -/
def mergeBody (W H : String) : Stmt :=
  .seq (decideStmt W H)
    (.seq (.ite (.var "ms_c") (takeFrom W H "ms_i") (takeFrom W H "ms_j")) (incr "ms_k"))

def mergeLoop (W H : String) : Stmt := .while (.lt (.var "ms_k") (.var "ms_hi")) (mergeBody W H)

/-- `r := min(e, s)` -/
def setMin (r : String) (e : WExpr) : Stmt :=
  .ite (.lt e (.var "ms_s")) (.wset r e) (.wset r (.var "ms_s"))

/-- set up the block starting at `lo`: `mid = min(lo + w, s)`, `hi = min(lo + 2w, s)`, `i = lo`, `j = mid`,
`k = lo` -/
def blockSetup : Stmt :=
  .seq (setMin "ms_mid" (.add (.var "ms_lo") (.var "ms_w")))
    (.seq (setMin "ms_hi" (.add (.var "ms_lo") (.add (.var "ms_w") (.var "ms_w"))))
      (.seq (.wset "ms_i" (.var "ms_lo"))
        (.seq (.wset "ms_j" (.var "ms_mid")) (.wset "ms_k" (.var "ms_lo")))))

/-- merge the block starting at `lo` -/
def blockBody (W H : String) : Stmt :=
  .seq blockSetup (.seq (mergeLoop W H) (.wset "ms_lo" (.var "ms_hi")))

def blockLoop (W H : String) : Stmt := .while (.lt (.var "ms_lo") (.var "ms_s")) (blockBody W H)

/-- copy scratch slot `k` back to the source slot `a + k` -/
def copyBody (W H : String) : Stmt :=
  .seq (.vstore W (srcAt "ms_k") (.load "ms_W" (.var "ms_k")))
    (.seq (.wstore H (srcAt "ms_k") (.load "ms_H" (.var "ms_k"))) (incr "ms_k"))

def copyLoop (W H : String) : Stmt := .while (.lt (.var "ms_k") (.var "ms_s")) (copyBody W H)

/-- one pass of width `w`, then `w := 2w` -/
def passBody (W H : String) : Stmt :=
  .seq (.wset "ms_lo" (.lit 0))
    (.seq (blockLoop W H)
      (.seq (.wset "ms_k" (.lit 0))
        (.seq (copyLoop W H) (.wset "ms_w" (.add (.var "ms_w") (.var "ms_w"))))))

def passLoop (W H : String) : Stmt := .while (.lt (.var "ms_w") (.var "ms_s")) (passBody W H)

/-- **sortRange**: sort slots `[ms_a, ms_b)` of `W` (values) with the parallel word array `H` by
`(W[p], H[p])`. -/
def sortRange (W H : String) : Stmt :=
  .seq (.wset "ms_s" (.sub (.var "ms_b") (.var "ms_a")))
    (.seq (.valloc "ms_W" (.var "ms_s"))
      (.seq (.walloc "ms_H" (.var "ms_s"))
        (.seq (.wset "ms_w" (.lit 1)) (passLoop W H))))

/-- registers written by `sortRange` -/
def msRegs : List String :=
  ["ms_s", "ms_w", "ms_lo", "ms_mid", "ms_hi", "ms_i", "ms_j", "ms_k", "ms_c", "ms_d"]

end Program

/-! ### Representation -/

section Rep

open Frontier.RAM

variable {V : Type} (W H : String)

/-- the source pair at relative position `p` -/
def srcFn (a : ℕ) (st : State V) (p : ℕ) : V × ℕ := (st.va W (a + p), st.wa H (a + p))

/-- the scratch pair at position `q` -/
def bufFn (st : State V) (q : ℕ) : V × ℕ := (st.va "ms_W" q, st.wa "ms_H" q)

/-- the list `f 0, …, f (s - 1)` -/
def segL {β : Type*} (f : ℕ → β) (s : ℕ) : List β := (List.range s).map f

@[simp] theorem length_segL {β : Type*} (f : ℕ → β) (s : ℕ) : (segL f s).length = s := by
  simp [segL]

theorem getElem?_segL {β : Type*} (f : ℕ → β) (s q : ℕ) (hq : q < s) : (segL f s)[q]? = some (f q) := by
  simp [segL, List.getElem?_range hq]

/-- Everything `sortRange` may not touch is as in `st0`; scratch arrays have length `s`. -/
structure Frame (st0 st : State V) (a s : ℕ) : Prop where
  unch : Unchanged st0 st [H, "ms_H"] [W, "ms_W"] msRegs []
  outW : ∀ p, (p < a ∨ a + s ≤ p) → st.va W p = st0.va W p
  outH : ∀ p, (p < a ∨ a + s ≤ p) → st.wa H p = st0.wa H p
  lenW : st.vlen W = st0.vlen W
  lenH : st.wlen H = st0.wlen H
  lenMW : st.vlen "ms_W" = s
  lenMH : st.wlen "ms_H" = s

variable {W H}
variable {st0 st : State V} {a s : ℕ}

theorem Frame.charge (h : Frame W H st0 st a s) (k : ℕ) : Frame W H st0 (st.charge k) a s :=
  ⟨⟨h.unch.warr, h.unch.varr, h.unch.wreg, h.unch.vreg, h.unch.cap, h.unch.procs⟩,
    h.outW, h.outH, h.lenW, h.lenH, h.lenMW, h.lenMH⟩

theorem Frame.setW (h : Frame W H st0 st a s) {x : String} (hx : x ∈ msRegs) (v : ℕ) :
    Frame W H st0 (st.setW x v) a s := by
  refine ⟨⟨h.unch.warr, h.unch.varr, fun y hy => ?_, h.unch.vreg, h.unch.cap, h.unch.procs⟩,
    h.outW, h.outH, h.lenW, h.lenH, h.lenMW, h.lenMH⟩
  have hne : y ≠ x := fun e => hy (e ▸ hx)
  simp only [State.setW, if_neg hne]
  exact h.unch.wreg y hy

theorem Frame.storeV_ms (h : Frame W H st0 st a s) (hW : W ≠ "ms_W") (j : ℕ) (v : V) :
    Frame W H st0 (st.storeV "ms_W" j v) a s := by
  refine ⟨⟨h.unch.warr, fun b hb => ?_, h.unch.wreg, h.unch.vreg, h.unch.cap, h.unch.procs⟩,
    fun p hp => ?_, h.outH, h.lenW, h.lenH, h.lenMW, h.lenMH⟩
  · have hne : b ≠ "ms_W" := fun e => hb (by simp [e])
    have e1 : (st.storeV "ms_W" j v).va b = st.va b := by
      funext q; simp only [State.storeV]; rw [if_neg (by rintro ⟨h1, -⟩; exact hne h1)]
    rw [e1]; exact h.unch.varr b hb
  · simp only [State.storeV]; rw [if_neg (by rintro ⟨h1, -⟩; exact hW h1)]; exact h.outW p hp

theorem Frame.storeW_ms (h : Frame W H st0 st a s) (hH : H ≠ "ms_H") (j : ℕ) (v : ℕ) :
    Frame W H st0 (st.storeW "ms_H" j v) a s := by
  refine ⟨⟨fun b hb => ?_, h.unch.varr, h.unch.wreg, h.unch.vreg, h.unch.cap, h.unch.procs⟩,
    h.outW, fun p hp => ?_, h.lenW, h.lenH, h.lenMW, h.lenMH⟩
  · have hne : b ≠ "ms_H" := fun e => hb (by simp [e])
    have e1 : (st.storeW "ms_H" j v).wa b = st.wa b := by
      funext q; simp only [State.storeW]; rw [if_neg (by rintro ⟨h1, -⟩; exact hne h1)]
    rw [e1]; exact h.unch.warr b hb
  · simp only [State.storeW]; rw [if_neg (by rintro ⟨h1, -⟩; exact hH h1)]; exact h.outH p hp

theorem Frame.storeV_src (h : Frame W H st0 st a s) {j : ℕ} (hj1 : a ≤ j)
    (hj2 : j < a + s) (v : V) : Frame W H st0 (st.storeV W j v) a s := by
  refine ⟨⟨h.unch.warr, fun b hb => ?_, h.unch.wreg, h.unch.vreg, h.unch.cap, h.unch.procs⟩,
    fun p hp => ?_, h.outH, h.lenW, h.lenH, h.lenMW, h.lenMH⟩
  · have hne : b ≠ W := fun e => hb (by simp [e])
    have e1 : (st.storeV W j v).va b = st.va b := by
      funext q; simp only [State.storeV]; rw [if_neg (by rintro ⟨h1, -⟩; exact hne h1)]
    rw [e1]; exact h.unch.varr b hb
  · simp only [State.storeV]; rw [if_neg (by rintro ⟨-, h2⟩; omega)]; exact h.outW p hp

theorem Frame.storeW_src (h : Frame W H st0 st a s) {j : ℕ} (hj1 : a ≤ j)
    (hj2 : j < a + s) (v : ℕ) : Frame W H st0 (st.storeW H j v) a s := by
  refine ⟨⟨fun b hb => ?_, h.unch.varr, h.unch.wreg, h.unch.vreg, h.unch.cap, h.unch.procs⟩,
    h.outW, fun p hp => ?_, h.lenW, h.lenH, h.lenMW, h.lenMH⟩
  · have hne : b ≠ H := fun e => hb (by simp [e])
    have e1 : (st.storeW H j v).wa b = st.wa b := by
      funext q; simp only [State.storeW]; rw [if_neg (by rintro ⟨h1, -⟩; exact hne h1)]
    rw [e1]; exact h.unch.warr b hb
  · simp only [State.storeW]; rw [if_neg (by rintro ⟨-, h2⟩; omega)]; exact h.outH p hp

end Rep




/-! ### The merge step -/

section Merge

open Frontier.RAM

variable {V : Type} {ops : VOps V} {W H : String}

/-- the decision taken by `decideStmt` -/
def TakeLeft (ops : VOps V) (W H : String) (st : State V) : Prop :=
  st.w "ms_i" < st.w "ms_mid" ∧ (st.w "ms_j" < st.w "ms_hi" →
    keyLe ops.le (srcFn W H (st.w "ms_a") st (st.w "ms_i"))
      (srcFn W H (st.w "ms_a") st (st.w "ms_j")) = true)

/-- `decideStmt` only writes `ms_c`, `ms_d` and costs at most `8`. -/
def DecPost (st r : State V) : Prop :=
  r.wa = st.wa ∧ r.va = st.va ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ r.cap = st.cap ∧
    r.procs = st.procs ∧ r.v = st.v ∧ (∀ y, y ≠ "ms_c" → y ≠ "ms_d" → r.w y = st.w y) ∧
    r.cost ≤ st.cost + 8

theorem runs_decide {st : State V} (h1 : 1 < st.cap)
    (hi : st.w "ms_i" < st.w "ms_mid" → st.w "ms_a" + st.w "ms_i" < st.cap ∧
      st.w "ms_a" + st.w "ms_i" < st.vlen W ∧ st.w "ms_a" + st.w "ms_i" < st.wlen H)
    (hj : st.w "ms_j" < st.w "ms_hi" → st.w "ms_a" + st.w "ms_j" < st.cap ∧
      st.w "ms_a" + st.w "ms_j" < st.vlen W ∧ st.w "ms_a" + st.w "ms_j" < st.wlen H) :
    Runs ops (decideStmt W H) st (fun r => DecPost st r ∧ (r.w "ms_c" ≠ 0 ↔ TakeLeft ops W H st)) := by
  apply wp_sound
  have h0 : 0 < st.cap := by omega
  by_cases hI : st.w "ms_i" < st.w "ms_mid"
  · by_cases hJ : st.w "ms_j" < st.w "ms_hi"
    · obtain ⟨ci, wi, hi'⟩ := hi hI
      obtain ⟨cj, wj, hj'⟩ := hj hJ
      by_cases hc : ops.le (st.va W (st.w "ms_a" + st.w "ms_i")) (st.va W (st.w "ms_a" + st.w "ms_j")) = true
      · by_cases hd : ops.le (st.va W (st.w "ms_a" + st.w "ms_j")) (st.va W (st.w "ms_a" + st.w "ms_i")) = true
        · by_cases hh : st.wa H (st.w "ms_a" + st.w "ms_j") < st.wa H (st.w "ms_a" + st.w "ms_i")
          · simp +contextual [decideStmt, wp, srcAt, evalW_lt', evalW_lit', evalW_add', evalW_load',
              evalV_load', fit_of_lt h1, fit_of_lt h0, fit_of_lt ci, fit_of_lt cj, hI, hJ, hc, hd, hh, wi, hi', wj, hj',
              DecPost, TakeLeft, keyLe, srcFn, h1, not_le.mpr hh]
          · simp +contextual [decideStmt, wp, srcAt, evalW_lt', evalW_lit', evalW_add', evalW_load',
              evalV_load', fit_of_lt h1, fit_of_lt h0, fit_of_lt ci, fit_of_lt cj, hI, hJ, hc, hd, hh, wi, hi', wj, hj',
              DecPost, TakeLeft, keyLe, srcFn, h1, not_lt.mp hh]
        · simp +contextual [decideStmt, wp, srcAt, evalW_lt', evalW_lit', evalW_add', evalW_load',
            evalV_load', fit_of_lt h1, fit_of_lt h0, fit_of_lt ci, fit_of_lt cj, hI, hJ, hc, hd, wi, hi', wj, hj',
            DecPost, TakeLeft, keyLe, srcFn, h1]
      · simp +contextual [decideStmt, wp, srcAt, evalW_lt', evalW_lit', evalW_add', evalW_load',
          evalV_load', fit_of_lt h1, fit_of_lt h0, fit_of_lt ci, fit_of_lt cj, hI, hJ, hc, wi, hi', wj, hj',
          DecPost, TakeLeft, keyLe, srcFn, h1]
    · simp +contextual [decideStmt, wp, evalW_lt', evalW_lit', fit_of_lt h1, fit_of_lt h0, hI, hJ, DecPost,
        TakeLeft]
  · simp +contextual [decideStmt, wp, evalW_lt', evalW_lit', fit_of_lt h1, fit_of_lt h0, hI, DecPost,
      TakeLeft]

/-- the state after `takeFrom W H x` -/
def takeState (W H x : String) (st : State V) : State V :=
  ((((((st.storeV "ms_W" (st.w "ms_k") (st.va W (st.w "ms_a" + st.w x))).charge 1).storeW "ms_H"
    (st.w "ms_k") (st.wa H (st.w "ms_a" + st.w x))).charge 1).setW x (st.w x + 1)).charge 1)

/-- the state after `incr x` -/
def incrState (x : String) (st : State V) : State V := (st.setW x (st.w x + 1)).charge 1

theorem runs_takeFrom {x : String} {st : State V} {Q : State V → Prop}
    (hcap : st.w "ms_a" + st.w x < st.cap) (h1 : 1 < st.cap) (hx1 : st.w x + 1 < st.cap)
    (hW : st.w "ms_a" + st.w x < st.vlen W) (hH : st.w "ms_a" + st.w x < st.wlen H)
    (hk1 : st.w "ms_k" < st.vlen "ms_W") (hk2 : st.w "ms_k" < st.wlen "ms_H")
    (hQ : Q (takeState W H x st)) : Runs ops (takeFrom W H x) st Q := by
  unfold takeFrom incr srcAt
  apply runs_seq
  refine runs_vstore (j := st.w "ms_k") (a := st.va W (st.w "ms_a" + st.w x)) rfl
    (evalV_load_of (evalW_add_of rfl rfl hcap) hW) hk1 ?_
  apply runs_seq
  refine runs_wstore (j := st.w "ms_k") (a := st.wa H (st.w "ms_a" + st.w x)) rfl
    (evalW_load_of (evalW_add_of rfl rfl hcap) hH) hk2 ?_
  exact runs_wset (a := st.w x + 1) (evalW_add_of rfl (evalW_lit_of h1) hx1) hQ

theorem runs_incr {x : String} {st : State V} {Q : State V → Prop} (h1 : 1 < st.cap)
    (hx1 : st.w x + 1 < st.cap) (hQ : Q (incrState x st)) : Runs ops (incr x) st Q :=
  runs_wset (evalW_add_of rfl (evalW_lit_of h1) hx1) hQ

section StateLemmas

variable {x : String} {st : State V}

@[simp] theorem takeState_w (y : String) :
    (takeState W H x st).w y = if y = x then st.w x + 1 else st.w y := rfl
@[simp] theorem takeState_v : (takeState W H x st).v = st.v := rfl
@[simp] theorem takeState_va (b : String) (q : ℕ) :
    (takeState W H x st).va b q =
      if b = "ms_W" ∧ q = st.w "ms_k" then st.va W (st.w "ms_a" + st.w x) else st.va b q := rfl
@[simp] theorem takeState_wa (b : String) (q : ℕ) :
    (takeState W H x st).wa b q =
      if b = "ms_H" ∧ q = st.w "ms_k" then st.wa H (st.w "ms_a" + st.w x) else st.wa b q := rfl
@[simp] theorem takeState_vlen : (takeState W H x st).vlen = st.vlen := rfl
@[simp] theorem takeState_wlen : (takeState W H x st).wlen = st.wlen := rfl
@[simp] theorem takeState_cap : (takeState W H x st).cap = st.cap := rfl
@[simp] theorem takeState_procs : (takeState W H x st).procs = st.procs := rfl
@[simp] theorem takeState_cost : (takeState W H x st).cost = st.cost + 3 := rfl

@[simp] theorem incrState_w (y : String) :
    (incrState x st).w y = if y = x then st.w x + 1 else st.w y := rfl
@[simp] theorem incrState_v : (incrState x st).v = st.v := rfl
@[simp] theorem incrState_va : (incrState x st).va = st.va := rfl
@[simp] theorem incrState_wa : (incrState x st).wa = st.wa := rfl
@[simp] theorem incrState_vlen : (incrState x st).vlen = st.vlen := rfl
@[simp] theorem incrState_wlen : (incrState x st).wlen = st.wlen := rfl
@[simp] theorem incrState_cap : (incrState x st).cap = st.cap := rfl
@[simp] theorem incrState_procs : (incrState x st).procs = st.procs := rfl
@[simp] theorem incrState_cost : (incrState x st).cost = st.cost + 1 := rfl

end StateLemmas

variable {st0 st r : State V} {a s : ℕ}

theorem Frame.takeState (h : Frame W H st0 st a s) (hW : W ≠ "ms_W") (hH : H ≠ "ms_H") {x : String}
    (hx : x ∈ msRegs) : Frame W H st0 (takeState W H x st) a s :=
  ((((h.storeV_ms hW _ _).charge 1).storeW_ms hH _ _).charge 1).setW hx _ |>.charge 1

theorem Frame.incrState (h : Frame W H st0 st a s) {x : String} (hx : x ∈ msRegs) :
    Frame W H st0 (incrState x st) a s :=
  (h.setW hx _).charge 1

theorem Frame.of_decPost (h : Frame W H st0 st a s) (hr : DecPost st r) : Frame W H st0 r a s := by
  obtain ⟨hwa, hva, hwlen, hvlen, hcap, hprocs, hv, hw, -⟩ := hr
  refine ⟨⟨fun b hb => ?_, fun b hb => ?_, fun y hy => ?_, fun y hy => ?_, ?_, ?_⟩,
    fun p hp => ?_, fun p hp => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwa, hwlen]; exact h.unch.warr b hb
  · rw [hva, hvlen]; exact h.unch.varr b hb
  · rw [hw y (fun e => hy (by simp [e, msRegs])) (fun e => hy (by simp [e, msRegs]))]
    exact h.unch.wreg y hy
  · rw [hv]; exact h.unch.vreg y hy
  · rw [hcap]; exact h.unch.cap
  · rw [hprocs]; exact h.unch.procs
  · rw [hva]; exact h.outW p hp
  · rw [hwa]; exact h.outH p hp
  · rw [hvlen]; exact h.lenW
  · rw [hwlen]; exact h.lenH
  · rw [hvlen]; exact h.lenMW
  · rw [hwlen]; exact h.lenMH

theorem Frame.cap_eq (h : Frame W H st0 st a s) : st.cap = st0.cap := h.unch.cap

end Merge


/-! ### The merge loop -/

section MergeLoop

open Frontier.RAM

variable {V : Type} {ops : VOps V} {W H : String}

/-- Invariant of the merge loop of the block `[lo, hi)` (runs `A = L[lo, mid)`, `B = L[mid, hi)`) after `k`
output elements: `Out[0, lo + k)` is in the scratch arrays, the unconsumed parts of the runs merge to the rest
of `merge A B`, the source segment still holds `Lcur`. -/
structure MInv (ops : VOps V) (W H : String) (st0 : State V) (a s w lo mid hi : ℕ)
    (A B Out Lcur : List (V × ℕ)) (c0 k : ℕ) (st : State V) : Prop where
  frame : Frame W H st0 st a s
  ra : st.w "ms_a" = a
  rs : st.w "ms_s" = s
  rw : st.w "ms_w" = w
  rlo : st.w "ms_lo" = lo
  rmid : st.w "ms_mid" = mid
  rhi : st.w "ms_hi" = hi
  rk : st.w "ms_k" = lo + k
  ij : ∃ i j, i + j = k ∧ i ≤ A.length ∧ j ≤ B.length ∧ st.w "ms_i" = lo + i ∧
    st.w "ms_j" = mid + j ∧
    (merge A B (keyLe ops.le)).drop k = merge (A.drop i) (B.drop j) (keyLe ops.le)
  buf : ∀ q < lo + k, Out[q]? = some (bufFn st q)
  src : ∀ p < s, Lcur[p]? = some (srcFn W H a st p)
  cost : st.cost ≤ c0 + 16 * k

/-- Static facts about one block. -/
structure BlockOK (ops : VOps V) (W H : String) (st0 : State V) (a s lo mid hi : ℕ)
    (A B Out Lcur : List (V × ℕ)) : Prop where
  hW : W ≠ "ms_W"
  hH : H ≠ "ms_H"
  lm : lo ≤ mid
  mh : mid ≤ hi
  hs : hi ≤ s
  lenA : A.length = mid - lo
  lenB : B.length = hi - mid
  eltA : ∀ i < A.length, A[i]? = Lcur[lo + i]?
  eltB : ∀ j < B.length, B[j]? = Lcur[mid + j]?
  out : ∀ q < hi - lo, Out[lo + q]? = (merge A B (keyLe ops.le))[q]?
  cap : 3 * (a + s) + 2 < st0.cap
  lenW : a + s ≤ st0.vlen W
  lenH : a + s ≤ st0.wlen H

variable {st0 st r : State V} {a s w lo mid hi c0 k : ℕ} {A B Out Lcur : List (V × ℕ)}

theorem MInv.charge (hM : MInv ops W H st0 a s w lo mid hi A B Out Lcur c0 k st) (j : ℕ) :
    MInv ops W H st0 a s w lo mid hi A B Out Lcur (c0 + j) k (st.charge j) :=
  ⟨hM.frame.charge j, hM.ra, hM.rs, hM.rw, hM.rlo, hM.rmid, hM.rhi, hM.rk, hM.ij, hM.buf, hM.src,
    by simp only [State.charge_cost]; have := hM.cost; omega⟩

theorem elt_of_src (hM : MInv ops W H st0 a s w lo mid hi A B Out Lcur c0 k st)
    {C : List (V × ℕ)} {base i : ℕ} (hC : ∀ i < C.length, C[i]? = Lcur[base + i]?) (hi : i < C.length)
    (hs : base + i < s) : C[i] = srcFn W H a st (base + i) := by
  have h1 := hC i hi
  rw [List.getElem?_eq_getElem hi, hM.src (base + i) hs] at h1
  exact Option.some.inj h1

theorem MInv.jlt (hb : BlockOK ops W H st0 a s lo mid hi A B Out Lcur)
    (hM : MInv ops W H st0 a s w lo mid hi A B Out Lcur c0 k st) (hk : k < hi - lo)
    (hn : ¬ TakeLeft ops W H (st.charge 1)) : st.w "ms_j" < hi := by
  obtain ⟨i, j, hij, hiA, hjB, hri, hrj, -⟩ := hM.ij
  simp only [TakeLeft, State.charge_w, hri, hrj, hM.rmid, hM.rhi, not_and, not_imp] at hn
  by_cases hI : lo + i < mid
  · rw [hrj]; exact (hn hI).1
  · have := hb.lenA; have := hb.lenB; have := hb.lm; have := hb.mh
    rw [hrj]; omega

theorem MInv.left (hb : BlockOK ops W H st0 a s lo mid hi A B Out Lcur)
    (hM : MInv ops W H st0 a s w lo mid hi A B Out Lcur c0 k st) (hk : k < hi - lo)
    (hr : DecPost (st.charge 1) r) (hT : TakeLeft ops W H (st.charge 1)) :
    MInv ops W H st0 a s w lo mid hi A B Out Lcur c0 (k + 1)
      (incrState "ms_k" (takeState W H "ms_i" (r.charge 1))) := by
  have hfr : Frame W H st0 r a s := (hM.frame.charge 1).of_decPost hr
  obtain ⟨hwa, hva, hwlen, hvlen, hcap, hprocs, hv, hw, hcost⟩ := hr
  simp only [State.charge_wa, State.charge_va, State.charge_wlen, State.charge_vlen, State.charge_cap, State.charge_v, State.charge_cost] at hwa hva hwlen hvlen hcap hv hcost
  have rw' : ∀ y, y ≠ "ms_c" → y ≠ "ms_d" → r.w y = st.w y := fun y h1 h2 => hw y h1 h2
  obtain ⟨i, j, hij, hiA, hjB, hri, hrj, hmerge⟩ := hM.ij
  simp only [TakeLeft, State.charge_w, hri, hrj, hM.rmid, hM.rhi, hM.ra] at hT
  have hlA := hb.lenA; have hlB := hb.lenB; have := hb.lm; have := hb.mh; have := hb.hs
  have hiA' : i < A.length := by omega
  have hAi : A[i] = srcFn W H a st (lo + i) := elt_of_src hM hb.eltA hiA' (by omega)
  have hkey : ∀ hj : j < B.length, keyLe ops.le A[i] B[j] = true := by
    intro hj
    rw [hAi, elt_of_src hM hb.eltB hj (by omega)]
    have := hT.2 (by omega)
    simpa [srcFn] using this
  have hstep := merge_drop_left A B i j hiA' hkey
  have ra' := rw' "ms_a" (by decide) (by decide)
  have ri' := rw' "ms_i" (by decide) (by decide)
  have rk' := rw' "ms_k" (by decide) (by decide)
  refine ⟨(hfr.charge 1 |>.takeState hb.hW hb.hH (by simp [msRegs])).incrState (by simp [msRegs]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨i + 1, j, by omega, hiA', hjB, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [ra', hM.ra]
  · simp [rw' "ms_s" (by decide) (by decide), hM.rs]
  · simp [rw' "ms_w" (by decide) (by decide), hM.rw]
  · simp [rw' "ms_lo" (by decide) (by decide), hM.rlo]
  · simp [rw' "ms_mid" (by decide) (by decide), hM.rmid]
  · simp [rw' "ms_hi" (by decide) (by decide), hM.rhi]
  · simp [rk', hM.rk]; omega
  · simp [ri', hri]; omega
  · simp [rw' "ms_j" (by decide) (by decide), hrj]
  · rw [List.drop_add_one_eq_tail_drop, hmerge, hstep]; rfl
  · intro q hq
    simp only [bufFn, incrState_va, incrState_wa, takeState_va, takeState_wa, State.charge_va, State.charge_wa, State.charge_w,
      true_and, rk', hM.rk, ra', ri', hri, hva, hwa]
    by_cases hq' : q = lo + k
    · subst hq'
      simp only [if_true]
      have e1 := hb.out k hk
      rw [e1, show k = k + 0 by rfl, ← List.getElem?_drop, hmerge, hstep]
      simp only [List.getElem?_cons_zero, Option.some.injEq]
      rw [hAi, hM.ra]
      rfl
    · simp only [hq', if_false]
      exact hM.buf q (by omega)
  · intro p hp
    have e := hM.src p hp
    rw [e]
    simp only [srcFn, incrState_va, incrState_wa, takeState_va, takeState_wa, State.charge_va, State.charge_wa, hva, hwa,
      hb.hW, hb.hH, false_and, if_false]
  · simp only [incrState_cost, takeState_cost, State.charge_cost]
    have := hM.cost
    omega

theorem MInv.right (hb : BlockOK ops W H st0 a s lo mid hi A B Out Lcur)
    (hM : MInv ops W H st0 a s w lo mid hi A B Out Lcur c0 k st) (hk : k < hi - lo)
    (hr : DecPost (st.charge 1) r) (hT : ¬ TakeLeft ops W H (st.charge 1)) :
    MInv ops W H st0 a s w lo mid hi A B Out Lcur c0 (k + 1)
      (incrState "ms_k" (takeState W H "ms_j" (r.charge 1))) := by
  have hjlt := hM.jlt hb hk hT
  have hfr : Frame W H st0 r a s := (hM.frame.charge 1).of_decPost hr
  obtain ⟨hwa, hva, hwlen, hvlen, hcap, hprocs, hv, hw, hcost⟩ := hr
  simp only [State.charge_wa, State.charge_va, State.charge_wlen, State.charge_vlen, State.charge_cap, State.charge_v, State.charge_cost] at hwa hva hwlen hvlen hcap hv hcost
  have rw' : ∀ y, y ≠ "ms_c" → y ≠ "ms_d" → r.w y = st.w y := fun y h1 h2 => hw y h1 h2
  obtain ⟨i, j, hij, hiA, hjB, hri, hrj, hmerge⟩ := hM.ij
  simp only [TakeLeft, State.charge_w, hri, hrj, hM.rmid, hM.rhi, hM.ra, not_and, not_imp] at hT
  have hlA := hb.lenA; have hlB := hb.lenB; have := hb.lm; have := hb.mh; have := hb.hs
  have hjB' : j < B.length := by rw [hrj] at hjlt; omega
  have hBj : B[j] = srcFn W H a st (mid + j) := elt_of_src hM hb.eltB hjB' (by omega)
  have hkey : ∀ hi' : i < A.length, keyLe ops.le A[i] B[j] = false := by
    intro hi'
    rw [elt_of_src hM hb.eltA hi' (by omega), hBj]
    have := (hT (by omega)).2
    simpa [srcFn] using this
  have hstep := merge_drop_right A B i j hjB' hkey
  have ra' := rw' "ms_a" (by decide) (by decide)
  have rj' := rw' "ms_j" (by decide) (by decide)
  have rk' := rw' "ms_k" (by decide) (by decide)
  refine ⟨(hfr.charge 1 |>.takeState hb.hW hb.hH (by simp [msRegs])).incrState (by simp [msRegs]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨i, j + 1, by omega, hiA, hjB', ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [ra', hM.ra]
  · simp [rw' "ms_s" (by decide) (by decide), hM.rs]
  · simp [rw' "ms_w" (by decide) (by decide), hM.rw]
  · simp [rw' "ms_lo" (by decide) (by decide), hM.rlo]
  · simp [rw' "ms_mid" (by decide) (by decide), hM.rmid]
  · simp [rw' "ms_hi" (by decide) (by decide), hM.rhi]
  · simp [rk', hM.rk]; omega
  · simp [rw' "ms_i" (by decide) (by decide), hri]
  · simp [rj', hrj]; omega
  · rw [List.drop_add_one_eq_tail_drop, hmerge, hstep]; rfl
  · intro q hq
    simp only [bufFn, incrState_va, incrState_wa, takeState_va, takeState_wa, State.charge_va, State.charge_wa, State.charge_w,
      true_and, rk', hM.rk, ra', rj', hrj, hva, hwa]
    by_cases hq' : q = lo + k
    · subst hq'
      simp only [if_true]
      have e1 := hb.out k hk
      rw [e1, show k = k + 0 by rfl, ← List.getElem?_drop, hmerge, hstep]
      simp only [List.getElem?_cons_zero, Option.some.injEq]
      rw [hBj, hM.ra]
      rfl
    · simp only [hq', if_false]
      exact hM.buf q (by omega)
  · intro p hp
    have e := hM.src p hp
    rw [e]
    simp only [srcFn, incrState_va, incrState_wa, takeState_va, takeState_wa, State.charge_va, State.charge_wa, hva, hwa,
      hb.hW, hb.hH, false_and, if_false]
  · simp only [incrState_cost, takeState_cost, State.charge_cost]
    have := hM.cost
    omega

theorem runs_mergeLoop (hb : BlockOK ops W H st0 a s lo mid hi A B Out Lcur) (st : State V)
    (h0 : MInv ops W H st0 a s w lo mid hi A B Out Lcur c0 0 st) :
    Runs ops (mergeLoop W H) st (MInv ops W H st0 a s w lo mid hi A B Out Lcur (c0 + 1) (hi - lo)) := by
  have hcapb := hb.cap
  have hlW := hb.lenW; have hlH := hb.lenH; have := hb.lm; have := hb.mh; have := hb.hs
  have hlA := hb.lenA; have hlB := hb.lenB
  refine runs_while (fun k st => MInv ops W H st0 a s w lo mid hi A B Out Lcur c0 k st) (hi - lo) _
    ?_ ?_ st h0
  · intro k hk st hM
    have hcs : st.cap = st0.cap := hM.frame.cap_eq
    have hc1 : 1 < st.cap := by omega
    have hvW : st.vlen W = st0.vlen W := hM.frame.lenW
    have hwH : st.wlen H = st0.wlen H := hM.frame.lenH
    have hvM : st.vlen "ms_W" = s := hM.frame.lenMW
    have hwM : st.wlen "ms_H" = s := hM.frame.lenMH
    obtain ⟨i, j, hij, hiA, hjB, hri, hrj, -⟩ := hM.ij
    have hra := hM.ra; have hrk := hM.rk; have hrmid := hM.rmid; have hrhi := hM.rhi
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of rfl rfl hc1, if_pos (by rw [hrk, hrhi]; omega)]
    · unfold mergeBody
      apply runs_seq
      refine (runs_decide (W := W) (H := H) (st := st.charge 1) hc1 ?_ ?_).mono ?_
      · intro hI
        simp only [State.charge_w, State.charge_cap, State.charge_vlen, State.charge_wlen, hri, hrmid, hra] at hI ⊢
        refine ⟨by omega, by omega, by omega⟩
      · intro hJ
        simp only [State.charge_w, State.charge_cap, State.charge_vlen, State.charge_wlen, hrj, hrhi, hra] at hJ ⊢
        refine ⟨by omega, by omega, by omega⟩
      · rintro r ⟨hr, hflag⟩
        have hr' := hr
        obtain ⟨hwa, hva, hwlen, hvlen, hcap, hprocs, hv, hw, hcost⟩ := hr'
        simp only [State.charge_wa, State.charge_va, State.charge_wlen, State.charge_vlen, State.charge_cap, State.charge_v, State.charge_cost] at hwa hva hwlen hvlen hcap hv hcost
        have rw' : ∀ y, y ≠ "ms_c" → y ≠ "ms_d" → r.w y = st.w y := fun y h1 h2 => hw y h1 h2
        have ra' := rw' "ms_a" (by decide) (by decide)
        have ri' := rw' "ms_i" (by decide) (by decide)
        have rj' := rw' "ms_j" (by decide) (by decide)
        have rk' := rw' "ms_k" (by decide) (by decide)
        apply runs_seq
        by_cases hc : r.w "ms_c" = 0
        · have hnT : ¬ TakeLeft ops W H (st.charge 1) := fun h => (hflag.mpr h) hc
          have hjl := hM.jlt hb hk hnT
          refine runs_ite_false (show evalW r (.var "ms_c") = some 0 by rw [evalW_var, hc]) ?_
          refine runs_takeFrom (W := W) (H := H) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
            try simp only [State.charge_w, State.charge_cap, State.charge_vlen, State.charge_wlen, ra', rj', rk', hcap, hvlen, hwlen, hcs, hvW,
              hwH, hvM, hwM, hra, hrk] at hjl ⊢
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · refine runs_incr ?_ ?_ (hM.right hb hk hr hnT)
            · simp only [takeState_cap, State.charge_cap, hcap]; omega
            · simp only [takeState_cap, takeState_w, State.charge_cap, State.charge_w, hcap, rk', hrk]
              simp only [show ("ms_k" = "ms_j") = False by decide, if_false]
              omega
        · have hT : TakeLeft ops W H (st.charge 1) := hflag.mp hc
          have hil : st.w "ms_i" < mid := by
            have := hT.1; simpa [hrmid] using this
          refine runs_ite_true (show evalW r (.var "ms_c") = some (r.w "ms_c") from rfl) hc ?_
          refine runs_takeFrom (W := W) (H := H) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
            try simp only [State.charge_w, State.charge_cap, State.charge_vlen, State.charge_wlen, ra', ri', rk', hcap, hvlen, hwlen, hcs, hvW,
              hwH, hvM, hwM, hra, hrk] at hil ⊢
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · omega
          · refine runs_incr ?_ ?_ (hM.left hb hk hr hT)
            · simp only [takeState_cap, State.charge_cap, hcap]; omega
            · simp only [takeState_cap, takeState_w, State.charge_cap, State.charge_w, hcap, rk', hrk]
              simp only [show ("ms_k" = "ms_i") = False by decide, if_false]
              omega
  · intro st hM
    have hc1 : 1 < st.cap := by rw [hM.frame.cap_eq]; omega
    refine ⟨?_, hM.charge 1⟩
    rw [evalW_lt_of rfl rfl hc1, if_neg (by rw [hM.rk, hM.rhi]; omega)]

end MergeLoop


/-! ### The block loop (one pass) -/

section BlockLoop

open Frontier.RAM

variable {V : Type} {ops : VOps V} {W H : String}

theorem runs_setMin {r : String} {e : WExpr} {st : State V} {Q : State V → Prop} {x : ℕ}
    (he : evalW st e = some x) (h1 : 1 < st.cap)
    (hQ : Q (((st.charge 1).setW r (min x (st.w "ms_s"))).charge 1)) : Runs ops (setMin r e) st Q := by
  unfold setMin
  by_cases h : x < st.w "ms_s"
  · refine runs_ite_true (evalW_lt_of he rfl h1) (by simp [h]) ?_
    refine runs_wset (by rw [evalW_charge]; exact he) ?_
    rwa [min_eq_left h.le] at hQ
  · refine runs_ite_false (by rw [evalW_lt_of he rfl h1, if_neg h]) ?_
    refine runs_wset rfl ?_
    rwa [min_eq_right (by omega)] at hQ

/-- Static facts about one pass of width `w` over the current list `Lcur`. -/
structure PassOK (ops : VOps V) (W H : String) (st0 : State V) (a s w : ℕ)
    (Out Lcur : List (V × ℕ)) : Prop where
  hW : W ≠ "ms_W"
  hH : H ≠ "ms_H"
  w1 : 1 ≤ w
  ws : w < s
  lenL : Lcur.length = s
  out : Out = mergePass (keyLe ops.le) w Lcur
  cap : 3 * (a + s) + 2 < st0.cap
  lenW : a + s ≤ st0.vlen W
  lenH : a + s ≤ st0.wlen H

/-- Invariant of the block loop after `jb` blocks. -/
structure BInv (ops : VOps V) (W H : String) (st0 : State V) (a s w : ℕ) (Out Lcur : List (V × ℕ))
    (c0 jb : ℕ) (st : State V) : Prop where
  frame : Frame W H st0 st a s
  ra : st.w "ms_a" = a
  rs : st.w "ms_s" = s
  rw : st.w "ms_w" = w
  rlo : st.w "ms_lo" = min (2 * w * jb) s
  buf : ∀ q < min (2 * w * jb) s, Out[q]? = some (bufFn st q)
  src : ∀ p < s, Lcur[p]? = some (srcFn W H a st p)
  cost : st.cost ≤ c0 + 10 * jb + 16 * min (2 * w * jb) s

variable {st0 st : State V} {a s w c0 : ℕ} {Out Lcur : List (V × ℕ)}

theorem BInv.charge (h : BInv ops W H st0 a s w Out Lcur c0 jb st) (j : ℕ) :
    BInv ops W H st0 a s w Out Lcur (c0 + j) jb (st.charge j) :=
  ⟨h.frame.charge j, h.ra, h.rs, h.rw, h.rlo, h.buf, h.src, by simp only [State.charge_cost]; have := h.cost; omega⟩

/-- The block `jb` satisfies `BlockOK`. -/
theorem blockOK_of (hp : PassOK ops W H st0 a s w Out Lcur) {jb : ℕ} (hjb : 2 * w * jb < s) :
    BlockOK ops W H st0 a s (2 * w * jb) (min (2 * w * jb + w) s) (min (2 * w * jb + (w + w)) s)
      ((Lcur.drop (2 * w * jb)).take w) ((Lcur.drop (2 * w * jb + w)).take w) Out Lcur := by
  have hL := hp.lenL
  have hw := hp.w1
  refine ⟨hp.hW, hp.hH, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, hp.cap, hp.lenW, hp.lenH⟩
  · simp only [List.length_take, List.length_drop, hL]; omega
  · simp only [List.length_take, List.length_drop, hL]; omega
  · intro i hi
    simp only [List.length_take, List.length_drop] at hi
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
  · intro j hj
    simp only [List.length_take, List.length_drop, hL] at hj
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
    congr 1; omega
  · intro q hq
    have hjk : jb < s := by
      have : jb ≤ 2 * w * jb := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hblk := mergeBlocks_block (le := keyLe ops.le) w jb s Lcur hjk (by omega)
    rw [hp.out, mergePass, hL, ← List.getElem?_drop, hblk, List.getElem?_append_left]
    simp only [List.length_merge, List.length_take, List.length_drop, hL]
    omega

/-- Register-only update: arrays, lengths, value registers, cap and procedures are unchanged, and word
registers outside `ws` too. -/
def RegOnly (st r : State V) (ws : List String) : Prop :=
  r.wa = st.wa ∧ r.va = st.va ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ r.cap = st.cap ∧
    r.procs = st.procs ∧ r.v = st.v ∧ ∀ y, y ∉ ws → r.w y = st.w y

theorem Frame.of_regOnly {st r : State V} {ws : List String} (h : Frame W H st0 st a s)
    (hr : RegOnly st r ws) (hws : ∀ y ∈ ws, y ∈ msRegs) : Frame W H st0 r a s := by
  obtain ⟨hwa, hva, hwlen, hvlen, hcap, hprocs, hv, hw⟩ := hr
  refine ⟨⟨fun b hb => ?_, fun b hb => ?_, fun y hy => ?_, fun y hy => ?_, ?_, ?_⟩,
    fun p hp => ?_, fun p hp => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hwa, hwlen]; exact h.unch.warr b hb
  · rw [hva, hvlen]; exact h.unch.varr b hb
  · rw [hw y (fun e => hy (hws y e))]; exact h.unch.wreg y hy
  · rw [hv]; exact h.unch.vreg y hy
  · rw [hcap]; exact h.unch.cap
  · rw [hprocs]; exact h.unch.procs
  · rw [hva]; exact h.outW p hp
  · rw [hwa]; exact h.outH p hp
  · rw [hvlen]; exact h.lenW
  · rw [hwlen]; exact h.lenH
  · rw [hvlen]; exact h.lenMW
  · rw [hwlen]; exact h.lenMH

theorem runs_blockSetup {st : State V} {lo w s : ℕ} (hlo : st.w "ms_lo" = lo) (hw : st.w "ms_w" = w)
    (hs : st.w "ms_s" = s) (hcap : lo + (w + w) + 2 < st.cap) :
    Runs ops blockSetup st (fun r => RegOnly st r ["ms_mid", "ms_hi", "ms_i", "ms_j", "ms_k"] ∧
      r.w "ms_mid" = min (lo + w) s ∧ r.w "ms_hi" = min (lo + (w + w)) s ∧ r.w "ms_i" = lo ∧
      r.w "ms_j" = min (lo + w) s ∧ r.w "ms_k" = lo ∧ r.cost = st.cost + 7) := by
  apply wp_sound
  have h1 : 1 < st.cap := by omega
  have h0 : 0 < st.cap := by omega
  have e1 : lo + w < st.cap := by omega
  have e2 : w + w < st.cap := by omega
  have e3 : lo + (w + w) < st.cap := by omega
  by_cases c1 : lo + w < s <;> by_cases c2 : lo + (w + w) < s <;>
    simp +contextual [blockSetup, setMin, wp, evalW_lt', evalW_add', fit_of_lt h1, fit_of_lt h0, fit_of_lt e1,
      fit_of_lt e2, fit_of_lt e3, hlo, hw, hs, c1, c2, RegOnly] <;> omega

/-- The block loop leaves `Out` in the scratch arrays. -/
def BDone (_ops : VOps V) (W H : String) (st0 : State V) (a s w : ℕ) (Out Lcur : List (V × ℕ))
    (c0 : ℕ) (r : State V) : Prop :=
  Frame W H st0 r a s ∧ r.w "ms_a" = a ∧ r.w "ms_s" = s ∧ r.w "ms_w" = w ∧
    (∀ q < s, Out[q]? = some (bufFn r q)) ∧ (∀ p < s, Lcur[p]? = some (srcFn W H a r p)) ∧
    r.cost ≤ c0 + 1 + 26 * s

theorem runs_blockLoop (hp : PassOK ops W H st0 a s w Out Lcur) (st : State V)
    (h0 : BInv ops W H st0 a s w Out Lcur c0 0 st) :
    Runs ops (blockLoop W H) st (BDone ops W H st0 a s w Out Lcur c0) := by
  classical
  have hw1 := hp.w1
  have hws := hp.ws
  have hcapb := hp.cap
  have hex : ∃ K, s ≤ 2 * w * K := ⟨s, by nlinarith⟩
  have hK : s ≤ 2 * w * Nat.find hex := Nat.find_spec hex
  have hKmin : ∀ j < Nat.find hex, 2 * w * j < s := fun j hj => by
    have := Nat.find_min hex hj; omega
  have hKs : Nat.find hex ≤ s := Nat.find_min' hex (by nlinarith)
  refine (runs_while (fun jb st => BInv ops W H st0 a s w Out Lcur c0 jb st) (Nat.find hex)
    (fun r => BInv ops W H st0 a s w Out Lcur (c0 + 1) (Nat.find hex) r) ?_ ?_ st h0).mono ?_
  · intro jb hjb st hB
    have hlo := hKmin jb hjb
    have hmin : min (2 * w * jb) s = 2 * w * jb := min_eq_left hlo.le
    have hcs : st.cap = st0.cap := hB.frame.cap_eq
    have hc1 : 1 < st.cap := by omega
    have hbk := blockOK_of hp hlo
    have hra := hB.ra; have hrs := hB.rs; have hrw := hB.rw; have hrlo := hB.rlo
    rw [hmin] at hrlo
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of rfl rfl hc1, hrlo, hrs, if_pos hlo]
    · unfold blockBody
      apply runs_seq
      refine (runs_blockSetup (st := st.charge 1) (lo := 2 * w * jb) (w := w) (s := s) hrlo hrw hrs
        (by simp only [State.charge_cap]; omega)).mono ?_
      rintro u ⟨hu, humid, huhi, hui, huj, huk, hucost⟩
      have hfu : Frame W H st0 u a s :=
        (hB.frame.charge 1).of_regOnly hu (by
          intro y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp [msRegs])
      obtain ⟨hwa, hva, hwlen, hvlen, hcap, hprocs, hv, hw⟩ := hu
      simp only [State.charge_wa, State.charge_va, State.charge_cap, State.charge_w, State.charge_cost] at hwa hva hcap hw hucost
      apply runs_seq
      refine (runs_mergeLoop (w := w) (c0 := u.cost) hbk u ⟨hfu, ?_, ?_, ?_, ?_, humid, huhi,
        by rw [huk]; rfl,
        ⟨0, 0, rfl, Nat.zero_le _, Nat.zero_le _, by rw [hui]; rfl, by rw [huj]; rfl, by simp⟩,
        ?_, ?_, Nat.le_add_right _ _⟩).mono ?_
      · rw [hw _ (by simp), hra]
      · rw [hw _ (by simp), hrs]
      · rw [hw _ (by simp), hrw]
      · rw [hw _ (by simp), hrlo]
      · intro q hq
        have := hB.buf q (by rw [hmin]; omega)
        simpa [bufFn, hva, hwa] using this
      · intro p hp'
        have := hB.src p hp'
        simpa [srcFn, hva, hwa] using this
      · intro r hMr
        refine runs_wset rfl ?_
        have e : min (2 * w * (jb + 1)) s = min (2 * w * jb + (w + w)) s := by congr 1; ring
        refine ⟨(hMr.frame.setW (by simp [msRegs]) _).charge 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hMr.ra]
        · simp [hMr.rs]
        · simp [hMr.rw]
        · simp only [State.charge_w, State.setW_w, if_true, hMr.rhi]
          exact e.symm
        · intro q hq
          rw [e] at hq
          have := hMr.buf q (by have := hbk.lm; have := hbk.mh; omega)
          simpa [bufFn] using this
        · intro p hp'
          have := hMr.src p hp'
          simpa [srcFn] using this
        · have hc := hMr.cost
          have hcB := hB.cost
          rw [hmin] at hcB
          simp only [State.charge_cost, State.setW_cost] at hc ⊢
          rw [e]
          have := hbk.lm; have := hbk.mh
          omega
  · intro st hB
    have hcs : st.cap = st0.cap := hB.frame.cap_eq
    have hc1 : 1 < st.cap := by omega
    have hmin : min (2 * w * Nat.find hex) s = s := min_eq_right hK
    refine ⟨?_, hB.charge 1⟩
    rw [evalW_lt_of rfl rfl hc1, hB.rlo, hB.rs, hmin, if_neg (lt_irrefl _)]
  · intro r hB
    have hmin : min (2 * w * Nat.find hex) s = s := min_eq_right hK
    refine ⟨hB.frame, hB.ra, hB.rs, hB.rw, fun q hq => hB.buf q (by rw [hmin]; exact hq), hB.src, ?_⟩
    have := hB.cost
    rw [hmin] at this
    omega

end BlockLoop


/-! ### The copy-back loop -/

section CopyLoop

open Frontier.RAM

variable {V : Type} {ops : VOps V} {W H : String}

/-- the state after `copyBody` -/
def copyState (W H : String) (st : State V) : State V :=
  incrState "ms_k" ((((st.storeV W (st.w "ms_a" + st.w "ms_k") (st.va "ms_W" (st.w "ms_k"))).charge 1).storeW
    H (st.w "ms_a" + st.w "ms_k") (st.wa "ms_H" (st.w "ms_k"))).charge 1)

theorem runs_copyBody {st : State V} {Q : State V → Prop}
    (hcap : st.w "ms_a" + st.w "ms_k" < st.cap) (h1 : 1 < st.cap) (hk1 : st.w "ms_k" + 1 < st.cap)
    (hW : st.w "ms_a" + st.w "ms_k" < st.vlen W) (hH : st.w "ms_a" + st.w "ms_k" < st.wlen H)
    (hkW : st.w "ms_k" < st.vlen "ms_W") (hkH : st.w "ms_k" < st.wlen "ms_H")
    (hQ : Q (copyState W H st)) : Runs ops (copyBody W H) st Q := by
  unfold copyBody srcAt
  apply runs_seq
  refine runs_vstore (j := st.w "ms_a" + st.w "ms_k") (a := st.va "ms_W" (st.w "ms_k"))
    (evalW_add_of rfl rfl hcap) (evalV_load_of rfl hkW) hW ?_
  apply runs_seq
  refine runs_wstore (j := st.w "ms_a" + st.w "ms_k") (a := st.wa "ms_H" (st.w "ms_k"))
    (evalW_add_of rfl rfl hcap) (evalW_load_of rfl hkH) hH ?_
  exact runs_incr h1 hk1 hQ

/-- Invariant of the copy-back loop after `k` slots. -/
structure CInv (ops : VOps V) (W H : String) (st0 : State V) (a s w : ℕ) (Out : List (V × ℕ))
    (c0 k : ℕ) (st : State V) : Prop where
  frame : Frame W H st0 st a s
  ra : st.w "ms_a" = a
  rs : st.w "ms_s" = s
  rw : st.w "ms_w" = w
  rk : st.w "ms_k" = k
  buf : ∀ q < s, Out[q]? = some (bufFn st q)
  done : ∀ q < k, Out[q]? = some (srcFn W H a st q)
  cost : st.cost ≤ c0 + 4 * k

variable {st0 : State V} {a s w c0 : ℕ} {Out : List (V × ℕ)}

theorem runs_copyLoop (hW : W ≠ "ms_W") (hH : H ≠ "ms_H") (hcapb : 3 * (a + s) + 2 < st0.cap)
    (hlW : a + s ≤ st0.vlen W) (hlH : a + s ≤ st0.wlen H) (st : State V)
    (h0 : CInv ops W H st0 a s w Out c0 0 st) :
    Runs ops (copyLoop W H) st (CInv ops W H st0 a s w Out (c0 + 1) s) := by
  refine runs_while (fun k st => CInv ops W H st0 a s w Out c0 k st) s _ ?_ ?_ st h0
  · intro k hk st hC
    have hcs : st.cap = st0.cap := hC.frame.cap_eq
    have hc1 : 1 < st.cap := by omega
    have hvW := hC.frame.lenW; have hwH := hC.frame.lenH
    have hvM := hC.frame.lenMW; have hwM := hC.frame.lenMH
    have hra := hC.ra; have hrk := hC.rk
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of rfl rfl hc1, hrk, hC.rs, if_pos hk]
    · refine runs_copyBody ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        try simp only [State.charge_w, State.charge_cap, State.charge_vlen, State.charge_wlen, hra, hrk, hcs, hvW, hwH, hvM, hwM]
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · unfold copyState
          exact (((((hC.frame.charge 1).storeV_src (by simp only [State.charge_w, hra, hrk]; omega)
            (by simp only [State.charge_w, hra, hrk]; omega) _).charge 1).storeW_src
            (by simp only [State.charge_w, hra, hrk]; omega)
            (by simp only [State.charge_w, hra, hrk]; omega) _).charge 1).incrState (by simp [msRegs])
        · simp [copyState, hra]
        · simp [copyState, hC.rs]
        · simp [copyState, hC.rw]
        · simp [copyState, hrk]
        · intro q hq
          have := hC.buf q hq
          simpa [copyState, bufFn, Ne.symm hW, Ne.symm hH] using this
        · intro q hq
          simp only [copyState, srcFn, incrState_va, incrState_wa, State.charge_va, State.charge_wa, State.storeW_va, State.storeW_wa,
            State.storeV_va, State.storeV_wa, State.charge_w, true_and, hra, hrk, Nat.add_left_cancel_iff]
          by_cases hq' : q = k
          · subst hq'
            simp only [if_true]
            have := hC.buf q hk
            simpa [bufFn] using this
          · simp only [hq', if_false]
            exact hC.done q (by omega)
        · simp only [copyState, incrState_cost, State.charge_cost, State.storeW_cost, State.storeV_cost]
          have := hC.cost
          omega
  · intro st hC
    have hc1 : 1 < st.cap := by rw [hC.frame.cap_eq]; omega
    refine ⟨?_, ⟨hC.frame.charge 1, hC.ra, hC.rs, hC.rw, hC.rk, hC.buf, hC.done, ?_⟩⟩
    · rw [evalW_lt_of rfl rfl hc1, hC.rk, hC.rs, if_neg (lt_irrefl _)]
    · simp only [State.charge_cost]; have := hC.cost; omega

end CopyLoop


/-! ### The pass loop and the main theorem -/

section PassLoop

open Frontier.RAM

variable {V : Type} {ops : VOps V} {W H : String}

/-- Invariant of the pass loop after `p` passes: the source segment holds `msortIter _ 1 p L0`. -/
structure PInv (ops : VOps V) (W H : String) (st0 : State V) (a s : ℕ) (L0 : List (V × ℕ))
    (c0 p : ℕ) (st : State V) : Prop where
  frame : Frame W H st0 st a s
  ra : st.w "ms_a" = a
  rs : st.w "ms_s" = s
  rw : st.w "ms_w" = 2 ^ p
  src : ∀ q < s, (msortIter (keyLe ops.le) 1 p L0)[q]? = some (srcFn W H a st q)
  cost : st.cost ≤ c0 + p * (30 * s + 6)

variable {st0 : State V} {a s c0 : ℕ} {L0 : List (V × ℕ)}

theorem runs_passLoop (hW : W ≠ "ms_W") (hH : H ≠ "ms_H") (hL0 : L0.length = s)
    (hcapb : 3 * (a + s) + 2 < st0.cap) (hlW : a + s ≤ st0.vlen W) (hlH : a + s ≤ st0.wlen H)
    (st : State V) (h0 : PInv ops W H st0 a s L0 c0 0 st) :
    ∃ P, s ≤ 2 ^ P ∧ (∀ p < P, 2 ^ p < s) ∧
      Runs ops (passLoop W H) st (PInv ops W H st0 a s L0 (c0 + 1) P) := by
  classical
  have hex : ∃ P, s ≤ 2 ^ P := ⟨s, (Nat.lt_two_pow_self).le⟩
  have hK : s ≤ 2 ^ Nat.find hex := Nat.find_spec hex
  have hKmin : ∀ p < Nat.find hex, 2 ^ p < s := fun p hp => by
    have := Nat.find_min hex hp; omega
  refine ⟨Nat.find hex, hK, hKmin, ?_⟩
  refine runs_while (fun p st => PInv ops W H st0 a s L0 c0 p st) (Nat.find hex) _ ?_ ?_ st h0
  · intro p hp st hP
    have hws := hKmin p hp
    have hcs : st.cap = st0.cap := hP.frame.cap_eq
    have hc1 : 1 < st.cap := by omega
    have hc0 : 0 < st.cap := by omega
    have hra := hP.ra; have hrs := hP.rs; have hrw := hP.rw
    have hpass : PassOK ops W H st0 a s (2 ^ p)
        (mergePass (keyLe ops.le) (2 ^ p) (msortIter (keyLe ops.le) 1 p L0))
        (msortIter (keyLe ops.le) 1 p L0) :=
      ⟨hW, hH, Nat.one_le_two_pow, hws, by rw [length_msortIter, hL0], rfl, hcapb, hlW, hlH⟩
    refine ⟨1, ?_, one_ne_zero, ?_⟩
    · rw [evalW_lt_of rfl rfl hc1, hrw, hrs, if_pos hws]
    · unfold passBody
      apply runs_seq
      refine runs_wset (evalW_lit_of (by simp only [State.charge_cap]; omega)) ?_
      apply runs_seq
      refine (runs_blockLoop hpass _ ⟨((hP.frame.charge 1).setW (by simp [msRegs]) _).charge 1,
        by simp [hra], by simp [hrs], by simp [hrw], by simp, by simp, ?_, Nat.le_add_right _ _⟩).mono ?_
      · intro q hq
        have := hP.src q hq
        simpa [srcFn] using this
      · rintro r ⟨hfr, hra', hrs', hrw', hbuf, hsrc, hcost⟩
        apply runs_seq
        refine runs_wset (evalW_lit_of (by rw [hfr.cap_eq]; omega)) ?_
        apply runs_seq
        refine (runs_copyLoop (Out := mergePass (keyLe ops.le) (2 ^ p) (msortIter (keyLe ops.le) 1 p L0))
          (w := 2 ^ p) hW hH hcapb hlW hlH _ ⟨(hfr.setW (by simp [msRegs]) _).charge 1, by simp [hra'], by simp [hrs'],
          by simp [hrw'], by simp, ?_, fun q hq => absurd hq (Nat.not_lt_zero _),
          Nat.le_add_right _ _⟩).mono ?_
        · intro q hq
          have := hbuf q hq
          simpa [bufFn] using this
        · intro r' hC
          have hcs' : r'.cap = st0.cap := hC.frame.cap_eq
          refine runs_wset (evalW_add_of rfl rfl (by rw [hC.rw, hcs']; omega)) ?_
          refine ⟨(hC.frame.setW (by simp [msRegs]) _).charge 1, by simp [hC.ra], by simp [hC.rs], ?_, ?_, ?_⟩
          · simp only [State.charge_w, State.setW_w, if_true, hC.rw]
            rw [pow_succ]; ring
          · intro q hq
            rw [msortIter_succ', mul_one]
            have := hC.done q hq
            simpa [srcFn] using this
          · have h1 := hC.cost
            simp only [State.charge_cost, State.setW_cost] at h1 hcost ⊢
            have := hP.cost
            nlinarith
  · intro st hP
    have hc1 : 1 < st.cap := by rw [hP.frame.cap_eq]; omega
    refine ⟨?_, ⟨hP.frame.charge 1, hP.ra, hP.rs, hP.rw, hP.src, ?_⟩⟩
    · rw [evalW_lt_of rfl rfl hc1, hP.rw, hP.rs, if_neg (by omega)]
    · simp only [State.charge_cost]; have := hP.cost; omega

theorem runs_passLoop' (hW : W ≠ "ms_W") (hH : H ≠ "ms_H") (hL0 : L0.length = s)
    (hcapb : 3 * (a + s) + 2 < st0.cap) (hlW : a + s ≤ st0.vlen W) (hlH : a + s ≤ st0.wlen H)
    (st : State V) (h0 : PInv ops W H st0 a s L0 c0 0 st) :
    Runs ops (passLoop W H) st (fun r => ∃ P, s ≤ 2 ^ P ∧ (∀ p < P, 2 ^ p < s) ∧
      PInv ops W H st0 a s L0 (c0 + 1) P r) := by
  obtain ⟨P, h1, h2, h3⟩ := runs_passLoop hW hH hL0 hcapb hlW hlH st h0
  exact h3.mono (fun r hr => ⟨P, h1, h2, hr⟩)

end PassLoop


section Main

open Frontier.RAM

variable {V : Type}

/-- **Verified RAM merge sort.**  For a total preorder `ops.le` on values, `sortRange W H` run from a state
with `ms_a = a ≤ b = ms_b` (both arrays covering `[a, b)`, words below the cap) terminates in a state where
* the slots `[a, b)` hold a permutation of the original `(W[p], H[p])` pairs, sorted by `keyLe` (lexicographic:
  values by `ops.le`, then heads by `≤`);
* all other cells of `W` and `H`, their lengths, and everything outside the scratch arrays `ms_W`, `ms_H`
  and the registers `msRegs` are unchanged;
* the cost is at most `40 (b - a + 1) (log₂ (b - a) + 1)`. -/
theorem sortRange_spec (ops : VOps V)
    (htr : ∀ x y z, ops.le x y = true → ops.le y z = true → ops.le x z = true)
    (hto : ∀ x y, ops.le x y = true ∨ ops.le y x = true)
    (W H : String) (hW : W ≠ "ms_W") (hH : H ≠ "ms_H") (st : State V) (a b : ℕ)
    (ha : st.w "ms_a" = a) (hb : st.w "ms_b" = b) (hab : a ≤ b) (hlW : b ≤ st.vlen W)
    (hlH : b ≤ st.wlen H) (hcap : 3 * b + 2 < st.cap) :
    Runs ops (sortRange W H) st (fun r =>
      (segL (srcFn W H a r) (b - a)).Pairwise (fun x y => keyLe ops.le x y = true) ∧
      (segL (srcFn W H a r) (b - a)).Perm (segL (srcFn W H a st) (b - a)) ∧
      (∀ p, p < a ∨ b ≤ p → r.va W p = st.va W p ∧ r.wa H p = st.wa H p) ∧
      r.vlen W = st.vlen W ∧ r.wlen H = st.wlen H ∧
      Unchanged st r [H, "ms_H"] [W, "ms_W"] msRegs [] ∧
      r.cost ≤ st.cost + 40 * (b - a + 1) * (Nat.log 2 (b - a) + 1)) := by
  set s := b - a with hs
  set L0 := segL (srcFn W H a st) s with hL0def
  have hL0 : L0.length = s := length_segL _ _
  have hab' : a + s = b := by omega
  have h1 : 1 < st.cap := by omega
  unfold sortRange
  apply runs_seq
  refine runs_wset (a := s) (by simp [evalW_sub', ha, hb, hs]) ?_
  apply runs_seq
  refine runs_valloc rfl ?_
  apply runs_seq
  refine runs_walloc rfl ?_
  apply runs_seq
  refine runs_wset (evalW_lit_of (by simp only [State.charge_cap, State.allocW_cap, State.allocV_cap, State.setW_cap]; exact h1)) ?_
  refine Runs.mono (Q := fun r => ∃ P, s ≤ 2 ^ P ∧ (∀ p < P, 2 ^ p < s) ∧
    PInv ops W H st a s L0 (st.cost + 2 * s + 4 + 1) P r) ?_ ?_
  swap
  · rintro r ⟨P, hP1, hP2, hPr⟩
    have hseg : segL (srcFn W H a r) s = msortIter (keyLe ops.le) 1 P L0 := by
      apply List.ext_getElem?
      intro q
      by_cases hq : q < s
      · rw [getElem?_segL _ _ _ hq, hPr.src q hq]
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by
          rw [length_msortIter, hL0]; omega)]
    have hsorted := msortIter_sorted (keyLe_trans htr) (keyLe_total hto) P L0 (by rw [hL0]; exact hP1)
    rw [← hseg] at hsorted
    refine ⟨hsorted.1, hsorted.2, fun p hp => ⟨hPr.frame.outW p (by omega), hPr.frame.outH p (by omega)⟩,
      hPr.frame.lenW, hPr.frame.lenH, hPr.frame.unch, ?_⟩
    -- cost
    have hc := hPr.cost
    have hPlog : P ≤ Nat.log 2 s + 1 := by
      by_contra hcon
      have := hP2 (Nat.log 2 s + 1) (by omega)
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) s
      omega
    have hL1 : 1 ≤ Nat.log 2 s + 1 := by omega
    have e1 : P * (30 * s + 6) ≤ (Nat.log 2 s + 1) * (30 * s + 6) := Nat.mul_le_mul_right _ hPlog
    have e2 : 2 * s + 5 ≤ 5 * (s + 1) * (Nat.log 2 s + 1) := by nlinarith
    nlinarith
  apply runs_passLoop' (st0 := st) (a := a) (s := s) (L0 := L0) (c0 := st.cost + 2 * s + 4) hW hH hL0
    (by omega) (by omega) (by omega)
  refine ⟨⟨⟨fun b' hb' => ?_, fun b' hb' => ?_, fun y hy => ?_, fun y hy => ?_, rfl, rfl⟩, fun p _ => ?_,
      fun p _ => ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb'
    refine ⟨funext fun j => ?_, ?_⟩ <;> simp [hb'.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb'
    refine ⟨funext fun j => ?_, ?_⟩ <;> simp [hb'.2]
  · simp only [msRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hy.1, hy.2.1]
  · rfl
  · simp [hW]
  · simp [hH]
  · simp [hW]
  · simp [hH]
  · simp
  · simp
  · simp [ha]
  · simp
  · simp
  · intro q hq
    rw [show msortIter (keyLe ops.le) 1 0 L0 = L0 from rfl, hL0def, getElem?_segL _ _ _ hq]
    simp [srcFn, hW, hH]
  · simp only [State.charge_cost, State.setW_cost, State.allocW_cost, State.allocV_cost, State.charge_w, State.allocV_w, State.setW_w, if_true, zero_mul, add_zero]
    omega

/-- `realOps.le` is a total preorder. -/
theorem realOps_le_trans :
    ∀ x y z : NNReal, realOps.le x y = true → realOps.le y z = true → realOps.le x z = true := by
  intro x y z h1 h2
  simp only [realOps, decide_eq_true_eq] at *
  exact le_trans h1 h2

theorem realOps_le_total : ∀ x y : NNReal, realOps.le x y = true ∨ realOps.le y x = true := by
  intro x y
  simp only [realOps, decide_eq_true_eq]
  exact le_total x y

/-- `sortRange_spec` for the exact real semantics. -/
theorem sortRange_spec_real (W H : String) (hW : W ≠ "ms_W") (hH : H ≠ "ms_H") (st : State NNReal)
    (a b : ℕ) (ha : st.w "ms_a" = a) (hb : st.w "ms_b" = b) (hab : a ≤ b) (hlW : b ≤ st.vlen W)
    (hlH : b ≤ st.wlen H) (hcap : 3 * b + 2 < st.cap) :
    Runs realOps (sortRange W H) st (fun r =>
      (segL (srcFn W H a r) (b - a)).Pairwise (fun x y => keyLe realOps.le x y = true) ∧
      (segL (srcFn W H a r) (b - a)).Perm (segL (srcFn W H a st) (b - a)) ∧
      (∀ p, p < a ∨ b ≤ p → r.va W p = st.va W p ∧ r.wa H p = st.wa H p) ∧
      r.vlen W = st.vlen W ∧ r.wlen H = st.wlen H ∧
      Unchanged st r [H, "ms_H"] [W, "ms_W"] msRegs [] ∧
      r.cost ≤ st.cost + 40 * (b - a + 1) * (Nat.log 2 (b - a) + 1)) :=
  sortRange_spec realOps realOps_le_trans realOps_le_total W H hW hH st a b ha hb hab hlW hlH hcap

end Main

end Frontier.CHD.MergeSort
