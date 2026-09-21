import Frontier.RAMRep
import Frontier.RAMWP
import Mathlib.Order.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Frontier.CHD.IHeap — a verified RAM indexed binary min-heap (agent-06; Layer B, NON-GATE)

For the C-HD base case (bounded Dijkstra): `O(log size)` per operation, so a base call costs
`O(lg(|S| + δ τ₀))` per settled vertex / scanned edge, as `CostFinal.total_le_Tchd`'s `hbase` requires.

**Layer A.** Arrays are functions `ℕ → ℕ`: `A` maps slots `[0, n)` to vertices, `P` maps a vertex to its slot
`+ 1` (`0` = absent).  `HeapOK key A n` (every slot `≥` its parent in `key`), `PosOK N A P n` (`P` inverts `A`),
`T A n` the represented set.  Sift-up / sift-down step lemmas with the one-hole invariants `HeapUp` / `HeapDown`.

**Layer B.** Word arrays `hp_A`, `hp_P`; registers `hp_n` (size), `hp_v` (argument / result), `hp_c`, and the sift
registers `siftRegs`.  The key comparison is a PARAMETER `lessS : Stmt` with a Hoare spec `LessOK` (decides
`key hp_x < key hp_y` into `hp_lt`, writes only its own registers, cost `≤ Cl`, key representation `KeyRep`
stable under the heap's writes) — e.g. agent-02's label compare on the current labels.  Operations and specs:
* `initS x`     — `runs_init`: empty heap for vertices `< N` (`N` in register `x`), cost `2N + 3`;
* `pushS`       — `runs_push`: insert an absent `hp_v`, cost `≤ (Cl+12)(log₂(n+1)+1) + 6`;
* `decS`        — `runs_dec`: the key of the present `hp_v` went down (`key0 → key`);
* `pushOrDecS`  — `runs_pushOrDec`: the relaxation step (insert or decrease), cost `≤ (Cl+12)(log₂(n+1)+1) + 8`;
* `popS`        — `runs_pop`: `hp_v := ` the vertex of minimum key, removed; cost `≤ (2Cl+20)(log₂ n+1) + 12`;
* `clearS`      — `runs_clear`: empty the heap (resets `P`), cost `≤ 3n + 1`;
* `topS`        — `runs_top`: `hp_v := ` the minimum (heap unchanged), cost `1`;
* `pushOrDecX`  — `runs_pushOrDecX`: `pushOrDecS` with the vertex in `hp_x` (agent-08's base-loop interface).
Every spec states the new `HeapRep`, the new represented set, and the write set via `RAMRep.Unchanged`.
-/

namespace Frontier.CHD.IHeap

section LayerA

variable {K : Type*} [LinearOrder K] (key : ℕ → K)

/-- parent slot -/
def par (i : ℕ) : ℕ := (i - 1) / 2

theorem par_lt {i : ℕ} (hi : 0 < i) : par i < i := by unfold par; omega

theorem par_eq_iff {i j : ℕ} (hi : 0 < i) : par i = j ↔ i = 2 * j + 1 ∨ i = 2 * j + 2 := by
  unfold par; omega

/-- heap order on the slots `[0, n)` -/
def HeapOK (A : ℕ → ℕ) (n : ℕ) : Prop := ∀ i, 0 < i → i < n → key (A (par i)) ≤ key (A i)

/-- sift-up invariant at slot `j`: all edges except `(par j, j)` are ordered, and `par j` is below the
children of `j`. -/
def HeapUp (A : ℕ → ℕ) (n j : ℕ) : Prop :=
  (∀ i, 0 < i → i < n → i ≠ j → key (A (par i)) ≤ key (A i)) ∧
    (0 < j → ∀ i, 0 < i → i < n → par i = j → key (A (par j)) ≤ key (A i))

/-- sift-down invariant at slot `j`: all edges except those `(j, child)` are ordered, and `par j` is
below the children of `j`. -/
def HeapDown (A : ℕ → ℕ) (n j : ℕ) : Prop :=
  (∀ i, 0 < i → i < n → par i ≠ j → key (A (par i)) ≤ key (A i)) ∧
    (0 < j → ∀ i, 0 < i → i < n → par i = j → key (A (par j)) ≤ key (A i))

/-- swap slots `i` and `j` -/
def swapA (A : ℕ → ℕ) (i j : ℕ) : ℕ → ℕ := fun x => if x = i then A j else if x = j then A i else A x

variable {key}

/-- The root is minimal. -/
theorem HeapOK.root_le {A : ℕ → ℕ} {n : ℕ} (h : HeapOK key A n) : ∀ i < n, key (A 0) ≤ key (A i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact le_rfl
    · exact le_trans (ih (par i) (par_lt hpos) (by have := par_lt hpos; omega)) (h i hpos hi)

theorem HeapUp.done {A : ℕ → ℕ} {n : ℕ} (h : HeapUp key A n 0) : HeapOK key A n :=
  fun i hi hin => h.1 i hi hin (by omega)

theorem HeapUp.stop {A : ℕ → ℕ} {n j : ℕ} (h : HeapUp key A n j) (hle : key (A (par j)) ≤ key (A j)) :
    HeapOK key A n := by
  intro i hi hin
  by_cases hij : i = j
  · subst hij; exact hle
  · exact h.1 i hi hin hij

theorem HeapUp.swap {A : ℕ → ℕ} {n j : ℕ} (h : HeapUp key A n j) (hj : 0 < j) (hjn : j < n)
    (hlt : key (A j) < key (A (par j))) : HeapUp key (swapA A j (par j)) n (par j) := by
  have hpj : par j < j := par_lt hj
  constructor
  · intro i hi hin hip
    simp only [swapA]
    by_cases hij : i = j
    · -- the swapped edge
      subst hij
      rw [if_neg (by omega), if_pos rfl, if_pos rfl]
      exact hlt.le
    · rw [if_neg hij, if_neg hip]
      by_cases hpi : par i = j
      · -- a child of `j`
        rw [if_pos hpi]
        exact h.2 hj i hi hin hpi
      · rw [if_neg hpi]
        by_cases hpp : par i = par j
        · -- a sibling of `j`
          rw [if_pos hpp]
          exact le_trans hlt.le (hpp ▸ h.1 i hi hin hij)
        · rw [if_neg hpp]
          exact h.1 i hi hin hij
  · intro hp i hi hin hpi
    simp only [swapA]
    have hpp : par (par j) ≠ j := by have := par_lt hp; omega
    have hpp' : par (par j) ≠ par j := by have := par_lt hp; omega
    rw [if_neg hpp, if_neg hpp']
    have hjp : key (A (par (par j))) ≤ key (A (par j)) := h.1 (par j) hp (by omega) (by omega)
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl]; exact hjp
    · rw [if_neg hij, if_neg (by intro e; subst e; omega)]
      exact le_trans hjp (hpi ▸ h.1 i hi hin hij)

theorem HeapDown.leaf {A : ℕ → ℕ} {n j : ℕ} (h : HeapDown key A n j) (hl : n ≤ 2 * j + 1) :
    HeapOK key A n := by
  intro i hi hin
  refine h.1 i hi hin ?_
  intro e
  rw [par_eq_iff hi] at e
  omega

theorem HeapDown.stop {A : ℕ → ℕ} {n j : ℕ} (h : HeapDown key A n j)
    (hc : ∀ i, 0 < i → i < n → par i = j → key (A j) ≤ key (A i)) : HeapOK key A n := by
  intro i hi hin
  by_cases hpi : par i = j
  · rw [hpi]; exact hc i hi hin hpi
  · exact h.1 i hi hin hpi

theorem HeapDown.swap {A : ℕ → ℕ} {n j c : ℕ} (h : HeapDown key A n j) (hcj : par c = j) (hc0 : 0 < c)
    (hcn : c < n) (hmin : ∀ i, 0 < i → i < n → par i = j → key (A c) ≤ key (A i))
    (hlt : key (A c) < key (A j)) : HeapDown key (swapA A j c) n c := by
  have hjc : j < c := hcj ▸ par_lt hc0
  constructor
  · intro i hi hin hpi
    simp only [swapA]
    by_cases hij : i = j
    · -- the edge above `j`
      subst hij
      have hj0 : 0 < i := hi
      rw [if_pos rfl, if_neg (by have := par_lt hj0; omega), if_neg (by have := par_lt hj0; omega)]
      exact h.2 hj0 c hc0 hcn hcj
    · rw [if_neg hij]
      by_cases hic : i = c
      · subst hic
        rw [if_pos rfl, hcj, if_pos rfl]
        exact hlt.le
      · rw [if_neg hic]
        by_cases hpij : par i = j
        · -- the other child of `j`
          rw [hpij, if_pos rfl]
          exact hmin i hi hin hpij
        · rw [if_neg hpij, if_neg hpi]
          exact h.1 i hi hin hpij
  · intro _ i hi hin hpi
    simp only [swapA]
    rw [hcj, if_pos rfl]
    have hij : i ≠ j := by have := par_lt hi; omega
    have hic : i ≠ c := by have := par_lt hi; omega
    rw [if_neg hij, if_neg hic]
    have : par i ≠ j := by omega
    exact le_trans (le_of_eq rfl) (hpi ▸ h.1 i hi hin (by rw [hpi]; omega))

/-- Push: write `v` at slot `n`. -/
theorem HeapOK.push {A : ℕ → ℕ} {n : ℕ} (h : HeapOK key A n) (v : ℕ) :
    HeapUp key (Function.update A n v) (n + 1) n := by
  constructor
  · intro i hi hin hin'
    have hi' : i < n := by omega
    rw [Function.update_of_ne hin', Function.update_of_ne (by have := par_lt hi; omega)]
    exact h i hi hi'
  · intro hn i hi hin hpi
    rw [par_eq_iff hi] at hpi
    omega

/-- Pop: move the last slot to the root. -/
theorem HeapOK.pop {A : ℕ → ℕ} {n : ℕ} (h : HeapOK key A (n + 1)) :
    HeapDown key (Function.update A 0 (A n)) n 0 := by
  constructor
  · intro i hi hin hpi
    rw [Function.update_of_ne hpi, Function.update_of_ne (show i ≠ 0 by omega)]
    exact h i hi (by omega)
  · intro h0; omega

/-- Decrease-key: the key of the vertex at slot `j` went down. -/
theorem HeapOK.decrease {key0 : ℕ → K} {A : ℕ → ℕ} {n j : ℕ} (h : HeapOK key0 A n) (hj : j < n)
    (hinj : ∀ i < n, A i = A j → i = j) (hk : ∀ u, u ≠ A j → key u = key0 u) (hv : key (A j) ≤ key0 (A j)) :
    HeapUp key A n j := by
  constructor
  · intro i hi hin hij
    have hAi : A i ≠ A j := fun e => hij (hinj i hin e)
    rw [hk (A i) hAi]
    by_cases hpi : par i = j
    · rw [hpi]; exact le_trans hv (hpi ▸ h i hi hin)
    · have hAp : A (par i) ≠ A j := fun e => hpi (hinj (par i) (by have := par_lt hi; omega) e)
      rw [hk _ hAp]
      exact h i hi hin
  · intro hj0 i hi hin hpi
    have hAi : A i ≠ A j := fun e => by
      have := hinj i hin e; subst this; have := par_lt hi; omega
    have hAp : A (par j) ≠ A j := fun e => by
      have := hinj (par j) (by have := par_lt hj0; omega) e; have := par_lt hj0; omega
    rw [hk _ hAi, hk _ hAp]
    exact le_trans (h j hj0 hj) (hpi ▸ h i hi hin)


/-! ### The position table -/

/-- `P` inverts `A` on the slots `[0, n)`; vertices are `< N`. -/
structure PosOK (N : ℕ) (A P : ℕ → ℕ) (n : ℕ) : Prop where
  slots : ∀ i < n, A i < N ∧ P (A i) = i + 1
  back : ∀ v < N, P v ≠ 0 → P v ≤ n ∧ A (P v - 1) = v

/-- the represented set of vertices -/
def T (A : ℕ → ℕ) (n : ℕ) : Finset ℕ := (Finset.range n).image A

theorem PosOK.inj {N : ℕ} {A P : ℕ → ℕ} {n : ℕ} (h : PosOK N A P n) {i j : ℕ} (hi : i < n) (hj : j < n)
    (e : A i = A j) : i = j := by
  have h1 := (h.slots i hi).2
  have h2 := (h.slots j hj).2
  rw [e] at h1
  omega

theorem PosOK.mem_T {N : ℕ} {A P : ℕ → ℕ} {n : ℕ} (h : PosOK N A P n) {v : ℕ} (hv : v < N) :
    v ∈ T A n ↔ P v ≠ 0 := by
  simp only [T, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [(h.slots i hi).2]; omega
  · intro hP
    obtain ⟨h1, h2⟩ := h.back v hv hP
    exact ⟨P v - 1, by omega, h2⟩

theorem PosOK.lt_N {N : ℕ} {A P : ℕ → ℕ} {n : ℕ} (h : PosOK N A P n) {v : ℕ} (hv : v ∈ T A n) : v < N := by
  simp only [T, Finset.mem_image, Finset.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  exact (h.slots i hi).1

/-- the RAM swap of slots `j` and `p` (stores `A[j] := A p; A[p] := A j; P[A p] := j+1; P[A j] := p+1`) -/
def swapP (A P : ℕ → ℕ) (j p : ℕ) : ℕ → ℕ :=
  fun v => if v = A j then p + 1 else if v = A p then j + 1 else P v

theorem PosOK.swap {N : ℕ} {A P : ℕ → ℕ} {n j p : ℕ} (h : PosOK N A P n) (hj : j < n) (hp : p < n)
    (hjp : j ≠ p) : PosOK N (swapA A j p) (swapP A P j p) n := by
  have hne : A j ≠ A p := fun e => hjp (h.inj hj hp e)
  constructor
  · intro i hi
    simp only [swapA, swapP]
    by_cases hij : i = j
    · subst hij
      simp only [if_true, hne.symm, if_false]
      exact ⟨(h.slots p hp).1, trivial⟩
    · by_cases hip : i = p
      · subst hip
        simp only [hij, if_false, if_true]
        exact ⟨(h.slots j hj).1, trivial⟩
      · simp only [hij, hip, if_false]
        have hAi : A i ≠ A j := fun e => hij (h.inj hi hj e)
        have hAi' : A i ≠ A p := fun e => hip (h.inj hi hp e)
        simp only [hAi, hAi', if_false]
        exact h.slots i hi
  · intro v hv hP
    simp only [swapP] at hP ⊢
    simp only [swapA]
    by_cases hvj : v = A j
    · subst hvj
      simp only [if_true, Nat.add_sub_cancel, hjp.symm, if_false]
      exact ⟨by omega, trivial⟩
    · by_cases hvp : v = A p
      · subst hvp
        simp only [hvj, if_false, if_true, Nat.add_sub_cancel]
        exact ⟨by omega, trivial⟩
      · simp only [hvj, hvp, if_false] at hP ⊢
        obtain ⟨h1, h2⟩ := h.back v hv hP
        have hPj : P v - 1 ≠ j := fun e => hvj (by rw [← e, h2])
        have hPp : P v - 1 ≠ p := fun e => hvp (by rw [← e, h2])
        simp only [hPj, hPp, if_false]
        exact ⟨h1, h2⟩

theorem T_swap {A : ℕ → ℕ} {n j p : ℕ} (hj : j < n) (hp : p < n) : T (swapA A j p) n = T A n := by
  ext v
  simp only [T, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    unfold swapA
    by_cases hij : i = j
    · exact ⟨p, hp, by rw [if_pos hij]⟩
    · by_cases hip : i = p
      · exact ⟨j, hj, by rw [if_neg hij, if_pos hip]⟩
      · exact ⟨i, hi, by rw [if_neg hij, if_neg hip]⟩
  · rintro ⟨i, hi, rfl⟩
    unfold swapA
    by_cases hij : i = j
    · refine ⟨p, hp, ?_⟩
      by_cases hpj : p = j
      · rw [if_pos hpj, hpj, hij]
      · rw [if_neg hpj, if_pos rfl, hij]
    · by_cases hip : i = p
      · exact ⟨j, hj, by rw [if_pos rfl, hip]⟩
      · exact ⟨i, hi, by rw [if_neg hij, if_neg hip]⟩

theorem PosOK.push {N : ℕ} {A P : ℕ → ℕ} {n v : ℕ} (h : PosOK N A P n) (hv : v < N) (hP : P v = 0) :
    PosOK N (Function.update A n v) (Function.update P v (n + 1)) (n + 1) := by
  constructor
  · intro i hi
    by_cases hin : i = n
    · subst hin; simp [hv]
    · have hi' : i < n := by omega
      rw [Function.update_of_ne hin]
      have hAi : A i ≠ v := fun e => by have := (h.slots i hi').2; rw [e, hP] at this; omega
      rw [Function.update_of_ne hAi]
      exact h.slots i hi'
  · intro u hu hPu
    by_cases huv : u = v
    · subst huv; simp
    · rw [Function.update_of_ne huv] at hPu ⊢
      obtain ⟨h1, h2⟩ := h.back u hu hPu
      rw [Function.update_of_ne (by omega)]
      exact ⟨by omega, h2⟩

theorem T_push {A : ℕ → ℕ} {n v : ℕ} (hA : ∀ i < n, A i ≠ v ∨ True) :
    T (Function.update A n v) (n + 1) = insert v (T A n) := by
  ext u
  simp only [T, Finset.mem_image, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hin : i = n
    · subst hin; left; simp
    · right; exact ⟨i, by omega, by rw [Function.update_of_ne hin]⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨n, by omega, by simp⟩
    · exact ⟨i, by omega, by rw [Function.update_of_ne (by omega)]⟩

/-- Pop, `n + 1 ≥ 2` slots: the root vertex leaves, the last vertex moves to slot `0`. -/
theorem PosOK.pop {N : ℕ} {A P : ℕ → ℕ} {n : ℕ} (h : PosOK N A P (n + 1)) (hn : 0 < n) :
    PosOK N (Function.update A 0 (A n)) (Function.update (Function.update P (A 0) 0) (A n) 1) n := by
  have hne : A n ≠ A 0 := fun e => by have := h.inj (by omega) (by omega) e; omega
  constructor
  · intro i hi
    by_cases hi0 : i = 0
    · subst hi0; simp [(h.slots n (by omega)).1]
    · rw [Function.update_of_ne hi0]
      have hAi : A i ≠ A n := fun e => by have := h.inj (by omega) (by omega) e; omega
      have hAi0 : A i ≠ A 0 := fun e => by have := h.inj (by omega) (by omega) e; omega
      rw [Function.update_of_ne hAi, Function.update_of_ne hAi0]
      exact ⟨(h.slots i (by omega)).1, (h.slots i (by omega)).2⟩
  · intro v hv hPv
    by_cases hvn : v = A n
    · subst hvn; simp; omega
    · rw [Function.update_of_ne hvn] at hPv ⊢
      by_cases hv0 : v = A 0
      · subst hv0; simp at hPv
      · rw [Function.update_of_ne hv0] at hPv ⊢
        obtain ⟨h1, h2⟩ := h.back v hv hPv
        have hPn : P v - 1 ≠ n := fun e => hvn (by rw [← e, h2])
        have hP0 : P v - 1 ≠ 0 := fun e => hv0 (by rw [← e, h2])
        rw [Function.update_of_ne hP0]
        exact ⟨by omega, h2⟩

theorem T_pop {N : ℕ} {A P : ℕ → ℕ} {n : ℕ} (h : PosOK N A P (n + 1)) :
    T (Function.update A 0 (A n)) n = (T A (n + 1)).erase (A 0) := by
  ext u
  simp only [T, Finset.mem_image, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases hi0 : i = 0
    · subst hi0
      simp only [Function.update_self]
      exact ⟨fun e => by have := h.inj (by omega) (by omega) e; omega, n, by omega, rfl⟩
    · rw [Function.update_of_ne hi0]
      exact ⟨fun e => hi0 (h.inj (by omega) (by omega) e), i, by omega, rfl⟩
  · rintro ⟨hu, i, hi, rfl⟩
    by_cases hin : i = n
    · subst hin; exact ⟨0, by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · subst h0; exact absurd rfl hu
        · exact h0, by simp⟩
    · have hi0 : i ≠ 0 := fun e => hu (by rw [e])
      exact ⟨i, by omega, by rw [Function.update_of_ne hi0]⟩

theorem PosOK.pop_last {N : ℕ} {A P : ℕ → ℕ} (h : PosOK N A P 1) :
    PosOK N A (Function.update P (A 0) 0) 0 := by
  constructor
  · intro i hi; omega
  · intro v hv hPv
    by_cases hv0 : v = A 0
    · subst hv0; simp at hPv
    · rw [Function.update_of_ne hv0] at hPv
      obtain ⟨h1, h2⟩ := h.back v hv hPv
      have : P v - 1 = 0 := by omega
      exact absurd (by rw [← this, h2]) hv0

theorem PosOK.card_T {N : ℕ} {A P : ℕ → ℕ} {n : ℕ} (h : PosOK N A P n) : (T A n).card = n := by
  unfold T
  rw [Finset.card_image_of_injOn (fun i hi j hj e => h.inj (by simpa using hi) (by simpa using hj) e)]
  simp

theorem PosOK.lt_of_not_mem {N : ℕ} {A P : ℕ → ℕ} {n v : ℕ} (h : PosOK N A P n) (hv : v < N)
    (hvT : v ∉ T A n) : n < N := by
  have hsub : T A n ⊆ (Finset.range N).erase v := by
    intro u hu
    simp only [Finset.mem_erase, Finset.mem_range]
    exact ⟨fun e => hvT (e ▸ hu), h.lt_N hu⟩
  have := Finset.card_le_card hsub
  rw [h.card_T, Finset.card_erase_of_mem (by simpa using hv), Finset.card_range] at this
  omega

theorem PosOK.shrink {N : ℕ} {A P : ℕ → ℕ} {m : ℕ} (h : PosOK N A P (m + 1)) :
    PosOK N A (Function.update P (A m) 0) m := by
  constructor
  · intro i hi
    have hne : A i ≠ A m := fun e => by have := h.inj (by omega) (by omega) e; omega
    rw [Function.update_of_ne hne]
    exact h.slots i (by omega)
  · intro v hv hPv
    by_cases hvm : v = A m
    · subst hvm; simp at hPv
    · rw [Function.update_of_ne hvm] at hPv ⊢
      obtain ⟨h1, h2⟩ := h.back v hv hPv
      have : P v - 1 ≠ m := fun e => hvm (by rw [← e, h2])
      exact ⟨by omega, h2⟩

theorem HeapOK.congr {key key0 : ℕ → K} {A : ℕ → ℕ} {n : ℕ} (h : HeapOK key0 A n)
    (hk : ∀ i < n, key (A i) = key0 (A i)) : HeapOK key A n := by
  intro i hi hin
  rw [hk i hin, hk (par i) (by have := par_lt hi; omega)]
  exact h i hi hin

end LayerA


/-! ## Layer B: the RAM program

Word arrays `hp_A` (slot → vertex), `hp_P` (vertex → slot + 1, `0` = absent); registers `hp_n` (size),
`hp_v` (argument / result vertex), `hp_c` (temporary); sift registers `hp_j` (current slot), `hp_p`
(parent / chosen child), `hp_x`, `hp_y` (the two vertices handed to the comparison), `hp_go` (loop flag),
`hp_lt` (comparison result).  The key comparison is a parameter `lessS : Stmt`. -/

section Program

open Frontier.RAM

/-- `A[j] := b; A[p] := a; P[b] := j + 1; P[a] := p + 1` where `a = A[j]`, `b = A[p]` (swap slots `j`, `p`) -/
def swapS (a b : String) : Stmt :=
  .seq (.wstore "hp_A" (.var "hp_j") (.var b))
    (.seq (.wstore "hp_A" (.var "hp_p") (.var a))
      (.seq (.wstore "hp_P" (.var b) (.add (.var "hp_j") (.lit 1)))
        (.wstore "hp_P" (.var a) (.add (.var "hp_p") (.lit 1)))))

/-- `p := (j - 1) / 2; x := A[j]; y := A[p]` -/
def upPre : Stmt :=
  .seq (.wset "hp_p" (.div (.sub (.var "hp_j") (.lit 1)) (.lit 2)))
    (.seq (.wset "hp_x" (.load "hp_A" (.var "hp_j"))) (.wset "hp_y" (.load "hp_A" (.var "hp_p"))))

/-- after the comparison `lt = [key A[j] < key A[p]]`: swap and move up, or stop -/
def upPost : Stmt :=
  .ite (.var "hp_lt") (.seq (swapS "hp_x" "hp_y") (.wset "hp_j" (.var "hp_p"))) (.wset "hp_go" (.lit 0))

def upBody (lessS : Stmt) : Stmt :=
  .ite (.lt (.lit 0) (.var "hp_j")) (.seq upPre (.seq lessS upPost)) (.wset "hp_go" (.lit 0))

/-- sift the vertex at slot `hp_j` up -/
def siftUp (lessS : Stmt) : Stmt :=
  .seq (.wset "hp_go" (.lit 1)) (.while (.var "hp_go") (upBody lessS))

/-- `x := A[p + 1]; y := A[p]` (compare the right child with the left child) -/
def downPre1 : Stmt :=
  .seq (.wset "hp_x" (.load "hp_A" (.add (.var "hp_p") (.lit 1)))) (.wset "hp_y" (.load "hp_A" (.var "hp_p")))

/-- `x := A[p]; y := A[j]` (compare the chosen child with the current slot) -/
def downPre2 : Stmt :=
  .seq (.wset "hp_x" (.load "hp_A" (.var "hp_p"))) (.wset "hp_y" (.load "hp_A" (.var "hp_j")))

/-- choose the smaller child in `hp_p` (ties: left) -/
def downChoose (lessS : Stmt) : Stmt :=
  .ite (.lt (.add (.var "hp_p") (.lit 1)) (.var "hp_n"))
    (.seq downPre1 (.seq lessS (.ite (.var "hp_lt") (.wset "hp_p" (.add (.var "hp_p") (.lit 1))) .skip)))
    .skip

/-- after the comparison `lt = [key A[p] < key A[j]]`: swap and move down, or stop -/
def downPost : Stmt :=
  .ite (.var "hp_lt") (.seq (swapS "hp_y" "hp_x") (.wset "hp_j" (.var "hp_p"))) (.wset "hp_go" (.lit 0))

def downBody (lessS : Stmt) : Stmt :=
  .seq (.wset "hp_p" (.add (.add (.var "hp_j") (.var "hp_j")) (.lit 1)))
    (.ite (.lt (.var "hp_p") (.var "hp_n"))
      (.seq (downChoose lessS) (.seq downPre2 (.seq lessS downPost)))
      (.wset "hp_go" (.lit 0)))

/-- sift the vertex at slot `hp_j` down -/
def siftDown (lessS : Stmt) : Stmt :=
  .seq (.wset "hp_go" (.lit 1)) (.while (.var "hp_go") (downBody lessS))

/-- registers written by the sift loops -/
def siftRegs : List String := ["hp_j", "hp_p", "hp_x", "hp_y", "hp_go", "hp_lt"]

/-- all heap registers -/
def hpRegs : List String := ["hp_n", "hp_v", "hp_c", "hp_j", "hp_p", "hp_x", "hp_y", "hp_go", "hp_lt"]

end Program

/-! ### The comparison interface -/

section Interface

open Frontier.RAM

variable {V : Type} {K : Type*} [LinearOrder K]

/-- `lessS` decides `key hp_x < key hp_y` into `hp_lt`, writing only the registers `lwr` / `lvr` (never the
other heap registers), at cost `≤ Cl`, in any state satisfying the key representation `KeyRep`, which is
insensitive to the heap's own writes. -/
structure LessOK (ops : VOps V) (lessS : Stmt) (KeyRep : State V → Prop) (key : ℕ → K) (N Cl : ℕ)
    (lwr lvr : List String) : Prop where
  run : ∀ st, KeyRep st → st.w "hp_x" < N → st.w "hp_y" < N →
    Runs ops lessS st (fun r => r.w "hp_lt" = (if key (st.w "hp_x") < key (st.w "hp_y") then 1 else 0) ∧
      Unchanged st r [] [] lwr lvr ∧ r.cost ≤ st.cost + Cl ∧ KeyRep r)
  frame : ∀ st r, KeyRep st → Unchanged st r ["hp_A", "hp_P"] [] hpRegs [] → st.cost ≤ r.cost → KeyRep r
  regs : ∀ x ∈ lwr, x ∈ hpRegs → x = "hp_lt"
  lt_mem : "hp_lt" ∈ lwr

end Interface

/-! ### Strict cost growth (every statement is charged) -/

section CostLt

open Frontier.RAM

variable {V : Type} (ops : VOps V)

/-- Every successful run of a statement charges at least `1`. -/
theorem exec_cost_lt : ∀ (f : ℕ) (c : Stmt) (s r : State V), exec ops f c s = some r → s.cost < r.cost
  | 0, _, _, _, h => by simp [exec] at h
  | f + 1, c, s, r, h => by
    cases c with
    | skip => simp [exec] at h; subst h; simp [State.charge]
    | wset x e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.setW]
    | vset x e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.setV]
    | vle x a b =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨p, _, q, _, bit, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.setW]
    | wstore arr i e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨j, _, a, _, h⟩ := h
      split_ifs at h; simp at h; subst h; simp [State.charge, State.storeW]
    | vstore arr i e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨j, _, a, _, h⟩ := h
      split_ifs at h; simp at h; subst h; simp [State.charge, State.storeV]
    | walloc arr e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨k, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.allocW]
    | valloc arr e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨k, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.allocV]
    | seq a b =>
      rw [exec_seq, Option.bind_eq_some_iff] at h
      obtain ⟨s', h1, h2⟩ := h
      exact (exec_cost_lt f a s s' h1).trans (exec_cost_lt f b s' r h2)
    | ite c a b =>
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · have := exec_cost_lt f a _ r h2; simp [State.charge] at this; omega
      · have := exec_cost_lt f b _ r h2; simp [State.charge] at this; omega
    | «while» c b =>
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · rw [Option.bind_eq_some_iff] at h2
        obtain ⟨s', h3, h4⟩ := h2
        have i1 := exec_cost_lt f b _ s' h3
        have i2 := exec_cost_lt f (.while c b) s' r h4
        simp [State.charge] at i1; omega
      · simp at h2; subst h2; simp [State.charge]
    | call p =>
      rw [exec_call] at h
      cases hp : s.procs[p]? with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some body =>
        rw [hp] at h
        have := exec_cost_lt f body _ r h; simp [State.enter] at this; omega

variable {ops}

/-- Every `Runs` postcondition may be strengthened by strict cost growth. -/
theorem Runs.cost_lt {c : Stmt} {st : State V} {Q : State V → Prop} (h : Runs ops c st Q) :
    Runs ops c st (fun r => Q r ∧ st.cost + 1 ≤ r.cost) := by
  obtain ⟨f, r, h1, hQ⟩ := h
  exact ⟨f, r, h1, hQ, exec_cost_lt ops f c st r h1⟩

end CostLt

/-! ### Frame helpers -/

section FrameH

open Frontier.RAM

variable {V : Type} {st0 st : State V} {wa va wr vr : List String}

theorem unch_setW' (h : Unchanged st0 st wa va wr vr) {x : String} (hx : x ∈ wr) (a : ℕ) :
    Unchanged st0 (st.setW x a) wa va wr vr := by
  refine ⟨h.warr, h.varr, fun y hy => ?_, h.vreg, h.cap, h.procs⟩
  have hyx : y ≠ x := fun e => hy (e ▸ hx)
  simp only [State.setW, hyx, if_false]
  exact h.wreg y hy

theorem unch_storeW' (h : Unchanged st0 st wa va wr vr) {arr : String} (ha : arr ∈ wa) (i a : ℕ) :
    Unchanged st0 (st.storeW arr i a) wa va wr vr := by
  refine ⟨fun b hb => ?_, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩
  have hba : b ≠ arr := fun e => hb (e ▸ ha)
  refine ⟨?_, (h.warr b hb).2⟩
  funext j
  simp only [State.storeW, hba, false_and, if_false]
  exact congrFun (h.warr b hb).1 j

theorem unch_charge' (h : Unchanged st0 st wa va wr vr) (k : ℕ) : Unchanged st0 (st.charge k) wa va wr vr :=
  ⟨h.warr, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩

end FrameH


/-! ### Straight-line fragments -/

section Frag

open Frontier.RAM

variable {V : Type} {ops : VOps V}

theorem evalW_div' (s : State V) (a b : WExpr) :
    evalW s (.div a b) = (evalW s a).bind (fun x => (evalW s b).bind
      (fun y => if y = 0 then none else some (x / y))) := rfl

/-- Register-only update. -/
def RegOnly (st r : State V) (ws : List String) : Prop :=
  r.wa = st.wa ∧ r.va = st.va ∧ r.wlen = st.wlen ∧ r.vlen = st.vlen ∧ r.cap = st.cap ∧
    r.procs = st.procs ∧ r.v = st.v ∧ ∀ y, y ∉ ws → r.w y = st.w y

theorem runs_upPre {st : State V} (hj : 0 < st.w "hp_j") (hjA : st.w "hp_j" < st.wlen "hp_A")
    (h2 : 2 < st.cap) :
    Runs ops upPre st (fun r => RegOnly st r ["hp_p", "hp_x", "hp_y"] ∧ r.w "hp_p" = par (st.w "hp_j") ∧
      r.w "hp_x" = st.wa "hp_A" (st.w "hp_j") ∧ r.w "hp_y" = st.wa "hp_A" (par (st.w "hp_j")) ∧
      r.cost = st.cost + 3) := by
  apply wp_sound
  have h1 : 1 < st.cap := by omega
  have hp : (st.w "hp_j" - 1) / 2 < st.wlen "hp_A" := by omega
  simp +contextual [upPre, wp, evalW_sub', evalW_div', evalW_lit', fit_of_lt h1, fit_of_lt h2, RegOnly, par,
    hjA, hp]

theorem runs_downPre1 {st : State V} (hp1 : st.w "hp_p" + 1 < st.wlen "hp_A") (hc : st.w "hp_p" + 1 < st.cap)
    (h1 : 1 < st.cap) :
    Runs ops downPre1 st (fun r => RegOnly st r ["hp_x", "hp_y"] ∧
      r.w "hp_x" = st.wa "hp_A" (st.w "hp_p" + 1) ∧ r.w "hp_y" = st.wa "hp_A" (st.w "hp_p") ∧
      r.cost = st.cost + 2) := by
  apply wp_sound
  have hp : st.w "hp_p" < st.wlen "hp_A" := by omega
  simp +contextual [downPre1, wp, evalW_add', evalW_lit', fit_of_lt h1, fit_of_lt hc, RegOnly, hp1, hp]

theorem runs_downPre2 {st : State V} (hp : st.w "hp_p" < st.wlen "hp_A") (hj : st.w "hp_j" < st.wlen "hp_A") :
    Runs ops downPre2 st (fun r => RegOnly st r ["hp_x", "hp_y"] ∧
      r.w "hp_x" = st.wa "hp_A" (st.w "hp_p") ∧ r.w "hp_y" = st.wa "hp_A" (st.w "hp_j") ∧
      r.cost = st.cost + 2) := by
  apply wp_sound
  simp +contextual [downPre2, wp, RegOnly, hp, hj]

theorem runs_setChild {st : State V} (hc : st.w "hp_j" + st.w "hp_j" + 1 < st.cap) (h1 : 1 < st.cap) :
    Runs ops (.wset "hp_p" (.add (.add (.var "hp_j") (.var "hp_j")) (.lit 1))) st
      (fun r => RegOnly st r ["hp_p"] ∧ r.w "hp_p" = 2 * st.w "hp_j" + 1 ∧ r.cost = st.cost + 1) := by
  apply wp_sound
  have hc' : st.w "hp_j" + st.w "hp_j" < st.cap := by omega
  simp +contextual [wp, evalW_add', evalW_lit', fit_of_lt h1, fit_of_lt hc, fit_of_lt hc', RegOnly]
  omega

/-- the state after `swapS a b` -/
def swapState (a b : String) (st : State V) : State V :=
  ((((((((st.storeW "hp_A" (st.w "hp_j") (st.w b)).charge 1).storeW "hp_A" (st.w "hp_p") (st.w a)).charge 1).storeW
    "hp_P" (st.w b) (st.w "hp_j" + 1)).charge 1).storeW "hp_P" (st.w a) (st.w "hp_p" + 1)).charge 1)

theorem runs_swapS {a b : String} {st : State V} {Q : State V → Prop}
    (hj : st.w "hp_j" < st.wlen "hp_A") (hp : st.w "hp_p" < st.wlen "hp_A") (ha : st.w a < st.wlen "hp_P")
    (hb : st.w b < st.wlen "hp_P") (hj1 : st.w "hp_j" + 1 < st.cap) (hp1 : st.w "hp_p" + 1 < st.cap)
    (h1 : 1 < st.cap) (hQ : Q (swapState a b st)) : Runs ops (swapS a b) st Q := by
  unfold swapS
  apply runs_seq
  refine runs_wstore (j := st.w "hp_j") (a := st.w b) rfl rfl hj ?_
  apply runs_seq
  refine runs_wstore (j := st.w "hp_p") (a := st.w a) rfl rfl hp ?_
  apply runs_seq
  refine runs_wstore (j := st.w b) (a := st.w "hp_j" + 1) rfl (evalW_add_of rfl (evalW_lit_of h1) hj1) hb ?_
  exact runs_wstore (j := st.w a) (a := st.w "hp_p" + 1) rfl (evalW_add_of rfl (evalW_lit_of h1) hp1) ha hQ

section SwapState

variable {a b : String} {st : State V}

@[simp] theorem swapState_w : (swapState a b st).w = st.w := rfl
@[simp] theorem swapState_v : (swapState a b st).v = st.v := rfl
@[simp] theorem swapState_va : (swapState a b st).va = st.va := rfl
@[simp] theorem swapState_wlen : (swapState a b st).wlen = st.wlen := rfl
@[simp] theorem swapState_vlen : (swapState a b st).vlen = st.vlen := rfl
@[simp] theorem swapState_cap : (swapState a b st).cap = st.cap := rfl
@[simp] theorem swapState_procs : (swapState a b st).procs = st.procs := rfl
@[simp] theorem swapState_cost : (swapState a b st).cost = st.cost + 4 := rfl

theorem swapState_A (hjp : st.w "hp_j" ≠ st.w "hp_p") (ha : st.w a = st.wa "hp_A" (st.w "hp_j"))
    (hb : st.w b = st.wa "hp_A" (st.w "hp_p")) :
    (swapState a b st).wa "hp_A" = swapA (st.wa "hp_A") (st.w "hp_j") (st.w "hp_p") := by
  funext q
  simp only [swapState, State.charge_wa, State.storeW_wa, swapA]
  by_cases hq1 : q = st.w "hp_j"
  · subst hq1; simp [hjp, hb]
  · by_cases hq2 : q = st.w "hp_p"
    · subst hq2; simp [hq1, ha]
    · simp [hq1, hq2]

theorem swapState_P (ha : st.w a = st.wa "hp_A" (st.w "hp_j"))
    (hb : st.w b = st.wa "hp_A" (st.w "hp_p")) :
    (swapState a b st).wa "hp_P" = swapP (st.wa "hp_A") (st.wa "hp_P") (st.w "hp_j") (st.w "hp_p") := by
  funext v
  simp only [swapState, State.charge_wa, State.storeW_wa, swapP]
  rw [← ha, ← hb]
  by_cases hv1 : v = st.w a
  · subst hv1; simp
  · by_cases hv2 : v = st.w b
    · subst hv2; simp [hv1]
    · simp [hv1, hv2]

theorem swapState_other {arr : String} (h1 : arr ≠ "hp_A") (h2 : arr ≠ "hp_P") :
    (swapState a b st).wa arr = st.wa arr := by
  funext q
  simp [swapState, h1, h2]

theorem unch_swapState {st0 : State V} {wa va wr vr : List String} (h : Unchanged st0 st wa va wr vr)
    (hA : "hp_A" ∈ wa) (hP : "hp_P" ∈ wa) : Unchanged st0 (swapState a b st) wa va wr vr := by
  unfold swapState
  exact unch_charge' (unch_storeW' (unch_charge' (unch_storeW' (unch_charge' (unch_storeW'
    (unch_charge' (unch_storeW' h hA _ _) 1) hA _ _) 1) hP _ _) 1) hP _ _) 1

end SwapState

end Frag


/-! ### Sift-up -/

section SiftUp

open Frontier.RAM

variable {V : Type} {K : Type*} [LinearOrder K] {ops : VOps V} {lessS : Stmt} {KeyRep : State V → Prop}
  {key : ℕ → K} {N Cl : ℕ} {lwr lvr : List String}

theorem Unchanged.of_regOnly {st0 s r : State V} {wa va wr vr ws : List String}
    (h : Unchanged st0 s wa va wr vr) (hr : RegOnly s r ws) (hws : ∀ y ∈ ws, y ∈ wr) :
    Unchanged st0 r wa va wr vr := by
  obtain ⟨hwa, hva, hwlen, hvlen, hcap, hprocs, hv, hw⟩ := hr
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun y hy => ?_, fun y hy => ?_, ?_, ?_⟩
  · rw [hwa, hwlen]; exact h.warr b hb
  · rw [hva, hvlen]; exact h.varr b hb
  · rw [hw y (fun e => hy (hws y e))]; exact h.wreg y hy
  · rw [hv]; exact h.vreg y hy
  · rw [hcap]; exact h.cap
  · rw [hprocs]; exact h.procs

theorem Unchanged.chain {st0 s r : State V} {wa va wr vr wa' va' wr' vr' : List String}
    (h : Unchanged st0 s wa va wr vr) (h' : Unchanged s r wa' va' wr' vr') (h1 : wa' ⊆ wa) (h2 : va' ⊆ va)
    (h3 : wr' ⊆ wr) (h4 : vr' ⊆ vr) : Unchanged st0 r wa va wr vr :=
  h.trans (h'.mono h1 h2 h3 h4)

/-- Invariant of the sift-up loop. -/
structure UpInv (KeyRep : State V → Prop) (key : ℕ → K) (N Cl : ℕ) (lwr lvr : List String)
    (st0 : State V) (n : ℕ) (T0 : Finset ℕ) (j0 c0 : ℕ) (st : State V) : Prop where
  keyrep : KeyRep st
  rn : st.w "hp_n" = n
  nN : n ≤ N
  lenA : st.wlen "hp_A" = N
  lenP : st.wlen "hp_P" = N
  cap : 2 * N + 3 < st.cap
  pos : PosOK N (st.wa "hp_A") (st.wa "hp_P") n
  set : T (st.wa "hp_A") n = T0
  jn : st.w "hp_j" < n
  jj0 : st.w "hp_j" ≤ j0
  go : (st.w "hp_go" = 1 ∧ HeapUp key (st.wa "hp_A") n (st.w "hp_j")) ∨
    (st.w "hp_go" = 0 ∧ HeapOK key (st.wa "hp_A") n)
  unch : Unchanged st0 st ["hp_A", "hp_P"] [] (siftRegs ++ lwr) lvr
  cost : st.cost ≤ c0 + (Cl + 12) * (Nat.log 2 (j0 + 1) - Nat.log 2 (st.w "hp_j" + 1)) +
    (if st.w "hp_go" = 0 then Cl + 12 else 0)

/-- Final state of the sift-up loop. -/
def UpDone (KeyRep : State V → Prop) (key : ℕ → K) (N Cl : ℕ) (lwr lvr : List String)
    (st0 : State V) (n : ℕ) (T0 : Finset ℕ) (j0 c0 : ℕ) (r : State V) : Prop :=
  KeyRep r ∧ r.w "hp_n" = n ∧ r.wlen "hp_A" = N ∧ r.wlen "hp_P" = N ∧ PosOK N (r.wa "hp_A") (r.wa "hp_P") n ∧
    T (r.wa "hp_A") n = T0 ∧ HeapOK key (r.wa "hp_A") n ∧
    Unchanged st0 r ["hp_A", "hp_P"] [] (siftRegs ++ lwr) lvr ∧
    r.cost ≤ c0 + (Cl + 12) * (Nat.log 2 (j0 + 1) + 1) + 1

theorem log_par {j : ℕ} (hj : 0 < j) : Nat.log 2 (par j + 1) = Nat.log 2 (j + 1) - 1 := by
  have e : par j + 1 = (j + 1) / 2 := by unfold par; omega
  rw [e, Nat.log_div_base]

theorem runs_upLoop (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st0 : State V} {n : ℕ} {T0 : Finset ℕ}
    {j0 c0 : ℕ} (st : State V) (h0 : UpInv KeyRep key N Cl lwr lvr st0 n T0 j0 c0 st) :
    Runs ops (.while (.var "hp_go") (upBody lessS)) st (UpDone KeyRep key N Cl lwr lvr st0 n T0 j0 c0) := by
  have hnotl : ∀ y ∈ hpRegs, y ≠ "hp_lt" → y ∉ lwr := fun y hy hne hyl => hne (hL.regs y hyl hy)
  refine runs_while_var (fun st => UpInv KeyRep key N Cl lwr lvr st0 n T0 j0 c0 st)
    (fun st => 2 * st.w "hp_j" + st.w "hp_go") _ ?_ st h0
  intro s hs
  refine ⟨s.w "hp_go", rfl, ?_, ?_⟩
  · -- the body
    intro hgo
    have hgo1 : s.w "hp_go" = 1 ∧ HeapUp key (s.wa "hp_A") n (s.w "hp_j") := by
      rcases hs.go with h | h
      · exact h
      · exact absurd h.1 hgo
    have hc := hs.cap
    have hjn := hs.jn
    have hnN := hs.nN
    have hlog : Nat.log 2 (s.w "hp_j" + 1) ≤ Nat.log 2 (j0 + 1) := Nat.log_mono_right (by have := hs.jj0; omega)
    have hscost := hs.cost
    rw [if_neg (by omega)] at hscost
    unfold upBody
    by_cases hj0 : s.w "hp_j" = 0
    · -- at the root: stop
      have hc1' : 1 < (s.charge 1).cap := by simp only [State.charge_cap]; omega
      have hc0' : 0 < (s.charge 1).cap := by omega
      have hgo := hgo1.1
      refine runs_ite_false (by rw [evalW_lt_of (evalW_lit_of hc0') rfl hc1', if_neg (by simp [hj0])]) ?_
      refine runs_wset (evalW_lit_of (by simp only [State.charge_cap]; omega)) ?_
      refine ⟨⟨hL.frame s _ hs.keyrep ?_ (by (try simp) <;> omega), by simp [hs.rn], hnN, by simp [hs.lenA], by simp [hs.lenP],
        by simp only [State.charge_cap, State.setW_cap]; exact hc, by simpa using hs.pos, by simpa using hs.set,
        by simp; omega, by simp; exact hs.jj0, Or.inr ⟨by simp, by
          have := hgo1.2; rw [hj0] at this; simpa using this.done⟩,
        unch_charge' (unch_setW' (unch_charge' (unch_charge' hs.unch 1) 1) (by simp [siftRegs]) 0) 1, ?_⟩, ?_⟩
      · exact unch_charge' (unch_setW' (unch_charge' (unch_charge' (Unchanged.refl s _ _ _ _) 1) 1)
          (by simp [hpRegs]) 0) 1
      · rw [hj0] at hscost
        simp at hscost
        simp [hj0]
        omega
      · simp [hgo]
    · -- compare with the parent
      have hc1' : 1 < (s.charge 1).cap := by simp only [State.charge_cap]; omega
      have hc0' : 0 < (s.charge 1).cap := by omega
      have hgo := hgo1.1
      have hjpos : 0 < s.w "hp_j" := Nat.pos_of_ne_zero hj0
      refine runs_ite_true (evalW_lt_of (evalW_lit_of hc0') rfl hc1') (by simp [hjpos]) ?_
      apply runs_seq
      refine (runs_upPre (st := (s.charge 1).charge 1) (by simpa using hjpos) (by simp [hs.lenA]; omega)
        (by simp only [State.charge_cap]; omega)).mono ?_
      rintro r1 ⟨hr1, hp1, hx1, hy1, hc1⟩
      have hr1' := hr1
      obtain ⟨h1wa, h1va, h1wlen, h1vlen, h1cap, h1procs, h1v, h1w⟩ := hr1'
      simp only [State.charge_wa, State.charge_wlen, State.charge_cap, State.charge_w, State.charge_cost]
        at h1wa h1wlen h1cap h1w hp1 hx1 hy1 hc1
      have hpj : par (s.w "hp_j") < s.w "hp_j" := par_lt hjpos
      have hAj : s.wa "hp_A" (s.w "hp_j") < N := (hs.pos.slots _ hjn).1
      have hAp : s.wa "hp_A" (par (s.w "hp_j")) < N := (hs.pos.slots _ (by omega)).1
      have hxN : r1.w "hp_x" < N := by rw [hx1]; exact hAj
      have hyN : r1.w "hp_y" < N := by rw [hy1]; exact hAp
      have hK1 : KeyRep r1 := hL.frame s r1 hs.keyrep
        (Unchanged.of_regOnly (unch_charge' (unch_charge' (Unchanged.refl s _ _ _ _) 1) 1)
          hr1 (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [hpRegs])) (by (try simp) <;> omega)
      apply runs_seq
      refine (hL.run r1 hK1 hxN hyN).mono ?_
      rintro r2 ⟨hlt, hu2, hc2, hK2⟩
      have r2w : ∀ y ∈ hpRegs, y ≠ "hp_lt" → r2.w y = r1.w y := fun y hy hne => hu2.wreg y (hnotl y hy hne)
      have r2wa : r2.wa = r1.wa := funext fun a => (hu2.warr a (by simp)).1
      have r2wlen : r2.wlen = r1.wlen := funext fun a => (hu2.warr a (by simp)).2
      have r2cap : r2.cap = r1.cap := hu2.cap
      have ej : r2.w "hp_j" = s.w "hp_j" := by
        rw [r2w "hp_j" (by simp [hpRegs]) (by decide)]; exact h1w "hp_j" (by simp)
      have ep : r2.w "hp_p" = par (s.w "hp_j") := by rw [r2w "hp_p" (by simp [hpRegs]) (by decide)]; exact hp1
      have ex : r2.w "hp_x" = s.wa "hp_A" (s.w "hp_j") := by
        rw [r2w "hp_x" (by simp [hpRegs]) (by decide)]; exact hx1
      have ey : r2.w "hp_y" = s.wa "hp_A" (par (s.w "hp_j")) := by
        rw [r2w "hp_y" (by simp [hpRegs]) (by decide)]; exact hy1
      have en : r2.w "hp_n" = n := by
        rw [r2w "hp_n" (by simp [hpRegs]) (by decide), h1w "hp_n" (by simp)]; exact hs.rn
      have ego : r2.w "hp_go" = 1 := by
        rw [r2w "hp_go" (by simp [hpRegs]) (by decide), h1w "hp_go" (by simp)]; exact hgo
      have eA : r2.wa "hp_A" = s.wa "hp_A" := by rw [r2wa, h1wa]
      have eP : r2.wa "hp_P" = s.wa "hp_P" := by rw [r2wa, h1wa]
      have eAl : r2.wlen "hp_A" = N := by rw [r2wlen, h1wlen]; exact hs.lenA
      have ePl : r2.wlen "hp_P" = N := by rw [r2wlen, h1wlen]; exact hs.lenP
      have ecap : r2.cap = s.cap := by rw [r2cap, h1cap]
      -- the frame so far
      have hu12 : Unchanged st0 r2 ["hp_A", "hp_P"] [] (siftRegs ++ lwr) lvr :=
        Unchanged.chain (Unchanged.of_regOnly (unch_charge' (unch_charge' hs.unch 1) 1) hr1
          (by intro y hy; simp at hy; rcases hy with rfl | rfl | rfl <;> simp [siftRegs])) hu2
          (by simp) (by simp) (List.subset_append_right _ _) (List.Subset.refl _)
      have hscost2 : r2.cost ≤ s.cost + 5 + Cl := by omega
      unfold upPost
      by_cases hl : key (s.wa "hp_A" (s.w "hp_j")) < key (s.wa "hp_A" (par (s.w "hp_j")))
      · -- swap
        have hlt1 : r2.w "hp_lt" = 1 := by rw [hlt, hx1, hy1, if_pos hl]
        refine runs_ite_true (show evalW r2 (.var "hp_lt") = some (r2.w "hp_lt") from rfl) (by omega) ?_
        apply runs_seq
        refine runs_swapS (a := "hp_x") (b := "hp_y") ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
          try simp only [State.charge_w, State.charge_wlen, State.charge_cap, ej, ep, ex, ey, eAl, ePl, ecap]
        · omega
        · omega
        · exact hAj
        · exact hAp
        · omega
        · omega
        · omega
        · refine runs_wset rfl ?_
          have hjp : s.w "hp_j" ≠ par (s.w "hp_j") := by omega
          have eA' : (swapState "hp_x" "hp_y" (r2.charge 1)).wa "hp_A" =
              swapA (s.wa "hp_A") (s.w "hp_j") (par (s.w "hp_j")) := by
            rw [swapState_A (by simp [ej, ep, hjp]) (by simp [ex, ej, eA]) (by simp [ey, ep, eA])]
            simp [ej, ep, eA]
          have eP' : (swapState "hp_x" "hp_y" (r2.charge 1)).wa "hp_P" =
              swapP (s.wa "hp_A") (s.wa "hp_P") (s.w "hp_j") (par (s.w "hp_j")) := by
            rw [swapState_P (by simp [ex, ej, eA]) (by simp [ey, ep, eA])]
            simp [ej, ep, eA, eP]
          have hLj : 1 ≤ Nat.log 2 (s.w "hp_j" + 1) := Nat.le_log_of_pow_le (by norm_num) (by omega)
          have eL : Nat.log 2 (j0 + 1) - Nat.log 2 (par (s.w "hp_j") + 1) =
              (Nat.log 2 (j0 + 1) - Nat.log 2 (s.w "hp_j" + 1)) + 1 := by
            rw [log_par hjpos]; omega
          refine ⟨⟨hL.frame r2 _ hK2 ?_ (by (try simp) <;> omega), by simp [en], hnN, by simp [eAl], by simp [ePl], by simp [ecap]; omega,
            ?_, ?_, by simp [ep]; omega, by simp [ep]; have := hs.jj0; omega, Or.inl ⟨by simp [ego], ?_⟩,
            unch_charge' (unch_setW' (unch_swapState (unch_charge' hu12 1) (by simp) (by simp))
              (by simp [siftRegs]) _) 1, ?_⟩, ?_⟩
          · exact unch_charge' (unch_setW' (unch_swapState (unch_charge' (Unchanged.refl r2 _ _ _ _) 1)
              (by simp) (by simp)) (by simp [hpRegs]) _) 1
          · simp only [State.charge_wa, State.setW_wa]
            rw [eA', eP']
            exact hs.pos.swap hjn (by omega) hjp
          · simp only [State.charge_wa, State.setW_wa]
            rw [eA', T_swap hjn (by omega)]
            exact hs.set
          · simp only [State.charge_wa, State.setW_wa, State.charge_w, State.setW_w, if_true, swapState_w, ep]
            rw [eA']
            exact HeapUp.swap hgo1.2 hjpos hjn hl
          · simp only [State.charge_cost, State.setW_cost, swapState_cost, State.charge_w, State.setW_w,
              swapState_w, ep, if_true, ego]
            rw [eL, Nat.mul_add]
            split_ifs <;> omega
          · simp only [State.charge_w, State.setW_w, swapState_w, ep, if_true]
            rw [if_neg (by decide : ¬ ("hp_go" = "hp_j")), ego, hgo]
            omega
      · -- stop
        have hlt0 : r2.w "hp_lt" = 0 := by rw [hlt, hx1, hy1, if_neg hl]
        refine runs_ite_false (show evalW r2 (.var "hp_lt") = some 0 by rw [evalW_var, hlt0]) ?_
        refine runs_wset (evalW_lit_of (by simp only [State.charge_cap]; rw [ecap]; omega)) ?_
        refine ⟨⟨hL.frame r2 _ hK2 ?_ (by (try simp) <;> omega), by simp [en], hnN, by simp [eAl], by simp [ePl], by simp [ecap]; omega,
          by simp [eA, eP]; exact hs.pos, by simp [eA]; exact hs.set, by simp [ej]; omega,
          by simp [ej]; exact hs.jj0, Or.inr ⟨by simp, ?_⟩,
          unch_charge' (unch_setW' (unch_charge' hu12 1) (by simp [siftRegs]) _) 1, ?_⟩, ?_⟩
        · exact unch_charge' (unch_setW' (unch_charge' (Unchanged.refl r2 _ _ _ _) 1) (by simp [hpRegs]) _) 1
        · simp only [State.charge_wa, State.setW_wa, eA]
          exact hgo1.2.stop (not_lt.mp hl)
        · simp only [State.charge_cost, State.setW_cost, State.charge_w, State.setW_w, if_true, ej]
          rw [if_neg (by decide : ¬ ("hp_j" = "hp_go"))]
          omega
        · simp only [State.charge_w, State.setW_w, if_true]
          rw [if_neg (by decide : ¬ ("hp_j" = "hp_go")), ej, hgo]
          omega
  · -- exit
    intro hgo
    have hgo0 : s.w "hp_go" = 0 := hgo
    rcases hs.go with h | h
    · exact absurd h.1 (by omega)
    · have hcost := hs.cost
      rw [if_pos hgo0] at hcost
      refine ⟨hL.frame s _ hs.keyrep (unch_charge' (Unchanged.refl s _ _ _ _) 1) (by (try simp) <;> omega), by simp [hs.rn],
        by simp [hs.lenA], by simp [hs.lenP], by simpa using hs.pos, by simpa using hs.set, by simpa using h.2,
        unch_charge' hs.unch 1, ?_⟩
      simp only [State.charge_cost]
      have : Nat.log 2 (j0 + 1) - Nat.log 2 (s.w "hp_j" + 1) ≤ Nat.log 2 (j0 + 1) := Nat.sub_le _ _
      nlinarith


theorem runs_siftUp (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st : State V} {n : ℕ}
    (hK : KeyRep st) (hn : st.w "hp_n" = n) (hnN : n ≤ N) (hlA : st.wlen "hp_A" = N)
    (hlP : st.wlen "hp_P" = N) (hcap : 2 * N + 3 < st.cap) (hpos : PosOK N (st.wa "hp_A") (st.wa "hp_P") n)
    (hj : st.w "hp_j" < n) (hU : HeapUp key (st.wa "hp_A") n (st.w "hp_j")) :
    Runs ops (siftUp lessS) st
      (UpDone KeyRep key N Cl lwr lvr st n (T (st.wa "hp_A") n) (st.w "hp_j") (st.cost + 1)) := by
  unfold siftUp
  apply runs_seq
  refine runs_wset (evalW_lit_of (by omega)) ?_
  refine runs_upLoop hL _ ⟨hL.frame st _ hK ?_ (by (try simp) <;> omega), by simp [hn], hnN, by simp [hlA], by simp [hlP],
    by simp; omega, by simpa using hpos, by simp, by simp; omega, by simp, Or.inl ⟨by simp, by simpa using hU⟩,
    unch_charge' (unch_setW' (Unchanged.refl st _ _ _ _) (by simp [siftRegs]) _) 1, ?_⟩
  · exact unch_charge' (unch_setW' (Unchanged.refl st _ _ _ _) (by simp [hpRegs]) _) 1
  · simp

end SiftUp


/-! ### Sift-down -/

section SiftDown

open Frontier.RAM

variable {V : Type} {K : Type*} [LinearOrder K] {ops : VOps V} {lessS : Stmt} {KeyRep : State V → Prop}
  {key : ℕ → K} {N Cl : ℕ} {lwr lvr : List String}

/-- Choosing the smaller child of `j` (slot `p = 2j+1` on entry). -/
theorem runs_downChoose (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st : State V} {n j : ℕ}
    (hK : KeyRep st) (hp : st.w "hp_p" = 2 * j + 1) (hpn : 2 * j + 1 < n) (hn : st.w "hp_n" = n)
    (hnN : n ≤ N) (hlA : st.wlen "hp_A" = N) (hcap : 2 * N + 3 < st.cap)
    (hpos : PosOK N (st.wa "hp_A") (st.wa "hp_P") n) :
    Runs ops (downChoose lessS) st (fun r => KeyRep r ∧ r.wa = st.wa ∧ r.wlen = st.wlen ∧ r.cap = st.cap ∧
      Unchanged st r [] [] (["hp_p", "hp_x", "hp_y"] ++ lwr) lvr ∧
      r.w "hp_p" < n ∧ par (r.w "hp_p") = j ∧ 0 < r.w "hp_p" ∧
      (∀ i, 0 < i → i < n → par i = j → key (st.wa "hp_A" (r.w "hp_p")) ≤ key (st.wa "hp_A" i)) ∧
      r.cost ≤ st.cost + Cl + 6) := by
  have hnotl : ∀ y ∈ hpRegs, y ≠ "hp_lt" → y ∉ lwr := fun y hy hne hyl => hne (hL.regs y hyl hy)
  have h1 : 1 < st.cap := by omega
  have hchild : ∀ i, 0 < i → i < n → par i = j → i = 2 * j + 1 ∨ i = 2 * j + 2 :=
    fun i hi _ hpi => (par_eq_iff hi).mp hpi
  unfold downChoose
  by_cases h2 : 2 * j + 2 < n
  · -- two children: compare them
    refine runs_ite_true (evalW_lt_of (evalW_add_of rfl (evalW_lit_of h1) (by rw [hp]; omega)) rfl h1)
      (by rw [hp, hn]; simp; omega) ?_
    apply runs_seq
    refine (runs_downPre1 (st := st.charge 1) (by simp [hp, hlA]; omega) (by simp [hp]; omega)
      (by simp; omega)).mono ?_
    rintro r1 ⟨hr1, hx1, hy1, hc1⟩
    have hr1' := hr1
    obtain ⟨h1wa, h1va, h1wlen, h1vlen, h1cap, h1procs, h1v, h1w⟩ := hr1'
    simp only [State.charge_wa, State.charge_wlen, State.charge_cap, State.charge_w, State.charge_cost,
      State.charge_procs, State.charge_va, State.charge_vlen, State.charge_v] at h1wa h1va h1wlen h1vlen h1cap h1procs h1v h1w hx1 hy1 hc1
    have hxN : r1.w "hp_x" < N := by rw [hx1, hp]; exact (hpos.slots _ h2).1
    have hyN : r1.w "hp_y" < N := by rw [hy1, hp]; exact (hpos.slots _ hpn).1
    have hK1 : KeyRep r1 := hL.frame st r1 hK
      (Unchanged.of_regOnly (unch_charge' (Unchanged.refl st _ _ _ _) 1)
        hr1 (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [hpRegs])) (by (try simp) <;> omega)
    apply runs_seq
    refine (hL.run r1 hK1 hxN hyN).mono ?_
    rintro r2 ⟨hlt, hu2, hc2, hK2⟩
    have r2w : ∀ y ∈ hpRegs, y ≠ "hp_lt" → r2.w y = r1.w y := fun y hy hne => hu2.wreg y (hnotl y hy hne)
    have r2wa : r2.wa = r1.wa := funext fun a => (hu2.warr a (by simp)).1
    have r2wlen : r2.wlen = r1.wlen := funext fun a => (hu2.warr a (by simp)).2
    have ep : r2.w "hp_p" = 2 * j + 1 := by
      rw [r2w "hp_p" (by simp [hpRegs]) (by decide), h1w "hp_p" (by simp)]; exact hp
    have hu12 : Unchanged st r2 [] [] (["hp_p", "hp_x", "hp_y"] ++ lwr) lvr :=
      Unchanged.chain (Unchanged.of_regOnly (unch_charge' (Unchanged.refl st _ _ _ _) 1) hr1
        (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp)) hu2
        (by simp) (by simp) (List.subset_append_right _ _) (List.Subset.refl _)
    have eA : r2.wa = st.wa := by rw [r2wa, h1wa]
    by_cases hl : key (st.wa "hp_A" (2 * j + 2)) < key (st.wa "hp_A" (2 * j + 1))
    · have hlt1 : r2.w "hp_lt" = 1 := by rw [hlt, hx1, hy1, hp, if_pos hl]
      refine runs_ite_true (show evalW r2 (.var "hp_lt") = some (r2.w "hp_lt") from rfl) (by omega) ?_
      refine runs_wset (evalW_add_of rfl (evalW_lit_of (by simp; rw [hu2.cap, h1cap]; omega))
        (by simp [ep]; rw [hu2.cap, h1cap]; omega)) ?_
      refine ⟨hL.frame r2 _ hK2 (unch_charge' (unch_setW' (unch_charge' (Unchanged.refl r2 _ _ _ _) 1)
          (by simp [hpRegs]) _) 1) (by (try simp) <;> omega),
        by simp [eA], by simp [r2wlen, h1wlen], by simp [hu2.cap, h1cap],
        unch_charge' (unch_setW' (unch_charge' hu12 1) (by simp) _) 1, by simp [ep]; omega, ?_, by simp [ep], ?_, ?_⟩
      · simp only [State.charge_w, State.setW_w, if_true, ep]
        exact (par_eq_iff (by omega)).mpr (Or.inr rfl)
      · intro i hi hin hpi
        simp only [State.charge_w, State.setW_w, if_true, ep]
        rcases hchild i hi hin hpi with rfl | rfl
        · exact hl.le
        · exact le_rfl
      · simp only [State.charge_cost, State.setW_cost]
        omega
    · have hlt0 : r2.w "hp_lt" = 0 := by rw [hlt, hx1, hy1, hp, if_neg hl]
      refine runs_ite_false (show evalW r2 (.var "hp_lt") = some 0 by rw [evalW_var, hlt0]) ?_
      refine runs_skip ?_
      refine ⟨hL.frame r2 _ hK2 (unch_charge' (unch_charge' (Unchanged.refl r2 _ _ _ _) 1) 1) (by (try simp) <;> omega), by simp [eA],
        by simp [r2wlen, h1wlen], by simp [hu2.cap, h1cap], unch_charge' (unch_charge' hu12 1) 1,
        by simp [ep]; omega, ?_, by simp [ep], ?_, ?_⟩
      · simp only [State.charge_w, ep]
        exact (par_eq_iff (by omega)).mpr (Or.inl rfl)
      · intro i hi hin hpi
        simp only [State.charge_w, ep]
        rcases hchild i hi hin hpi with rfl | rfl
        · exact le_rfl
        · exact not_lt.mp hl
      · simp only [State.charge_cost]
        omega
  · -- one child only
    refine runs_ite_false (by rw [evalW_lt_of (evalW_add_of rfl (evalW_lit_of h1) (by rw [hp]; omega)) rfl h1,
      hp, hn, if_neg (by omega)]) ?_
    refine runs_skip ?_
    refine ⟨hL.frame st _ hK (unch_charge' (unch_charge' (Unchanged.refl st _ _ _ _) 1) 1) (by (try simp) <;> omega), by simp, by simp,
      by simp, unch_charge' (unch_charge' (Unchanged.refl st _ _ _ _) 1) 1, by simp [hp]; omega, ?_,
      by simp [hp], ?_, ?_⟩
    · simp only [State.charge_w, hp]
      exact (par_eq_iff (by omega)).mpr (Or.inl rfl)
    · intro i hi hin hpi
      simp only [State.charge_w, hp]
      rcases hchild i hi hin hpi with rfl | rfl
      · exact le_rfl
      · omega
    · simp only [State.charge_cost]
      omega


/-- Invariant of the sift-down loop. -/
structure DownInv (KeyRep : State V → Prop) (key : ℕ → K) (N Cl : ℕ) (lwr lvr : List String)
    (st0 : State V) (n : ℕ) (T0 : Finset ℕ) (j0 c0 : ℕ) (st : State V) : Prop where
  keyrep : KeyRep st
  rn : st.w "hp_n" = n
  nN : n ≤ N
  lenA : st.wlen "hp_A" = N
  lenP : st.wlen "hp_P" = N
  cap : 2 * N + 3 < st.cap
  pos : PosOK N (st.wa "hp_A") (st.wa "hp_P") n
  set : T (st.wa "hp_A") n = T0
  jn : st.w "hp_j" < n
  j0j : j0 ≤ st.w "hp_j"
  go : (st.w "hp_go" = 1 ∧ HeapDown key (st.wa "hp_A") n (st.w "hp_j")) ∨
    (st.w "hp_go" = 0 ∧ HeapOK key (st.wa "hp_A") n)
  unch : Unchanged st0 st ["hp_A", "hp_P"] [] (siftRegs ++ lwr) lvr
  cost : st.cost ≤ c0 + (2 * Cl + 20) * (Nat.log 2 (st.w "hp_j" + 1) - Nat.log 2 (j0 + 1)) +
    (if st.w "hp_go" = 0 then 2 * Cl + 20 else 0)

/-- Final state of the sift-down loop. -/
def DownDone (KeyRep : State V → Prop) (key : ℕ → K) (N Cl : ℕ) (lwr lvr : List String)
    (st0 : State V) (n : ℕ) (T0 : Finset ℕ) (c0 : ℕ) (r : State V) : Prop :=
  KeyRep r ∧ r.w "hp_n" = n ∧ r.wlen "hp_A" = N ∧ r.wlen "hp_P" = N ∧ PosOK N (r.wa "hp_A") (r.wa "hp_P") n ∧
    T (r.wa "hp_A") n = T0 ∧ HeapOK key (r.wa "hp_A") n ∧
    Unchanged st0 r ["hp_A", "hp_P"] [] (siftRegs ++ lwr) lvr ∧
    r.cost ≤ c0 + (2 * Cl + 20) * (Nat.log 2 n + 1) + 1

theorem log_child {j c : ℕ} (hc : 2 * j + 1 ≤ c) : Nat.log 2 (j + 1) + 1 ≤ Nat.log 2 (c + 1) := by
  have h1 : Nat.log 2 ((j + 1) * 2) = Nat.log 2 (j + 1) + 1 := Nat.log_mul_base (by norm_num) (by omega)
  rw [← h1]
  exact Nat.log_mono_right (by omega)

theorem runs_downLoop (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st0 : State V} {n : ℕ} {T0 : Finset ℕ}
    {j0 c0 : ℕ} (st : State V) (h0 : DownInv KeyRep key N Cl lwr lvr st0 n T0 j0 c0 st) :
    Runs ops (.while (.var "hp_go") (downBody lessS)) st (DownDone KeyRep key N Cl lwr lvr st0 n T0 c0) := by
  have hnotl : ∀ y ∈ hpRegs, y ≠ "hp_lt" → y ∉ lwr := fun y hy hne hyl => hne (hL.regs y hyl hy)
  refine runs_while_var (fun st => DownInv KeyRep key N Cl lwr lvr st0 n T0 j0 c0 st)
    (fun st => 2 * (n - st.w "hp_j") + st.w "hp_go") _ ?_ st h0
  intro s hs
  refine ⟨s.w "hp_go", rfl, ?_, ?_⟩
  · intro hgo
    have hgo1 : s.w "hp_go" = 1 ∧ HeapDown key (s.wa "hp_A") n (s.w "hp_j") := by
      rcases hs.go with h | h
      · exact h
      · exact absurd h.1 hgo
    have hc := hs.cap
    have hjn := hs.jn
    have hnN := hs.nN
    have hgo' := hgo1.1
    have hlog : Nat.log 2 (j0 + 1) ≤ Nat.log 2 (s.w "hp_j" + 1) := Nat.log_mono_right (by have := hs.j0j; omega)
    have hscost := hs.cost
    rw [if_neg (by omega)] at hscost
    have hc1' : 1 < (s.charge 1).cap := by simp only [State.charge_cap]; omega
    unfold downBody
    apply runs_seq
    refine (runs_setChild (st := s.charge 1) (by simp; omega) hc1').mono ?_
    rintro t1 ⟨ht1, hp1, hct1⟩
    have ht1' := ht1
    obtain ⟨t1wa, t1va, t1wlen, t1vlen, t1cap, t1procs, t1v, t1w⟩ := ht1'
    simp only [State.charge_wa, State.charge_wlen, State.charge_cap, State.charge_w, State.charge_cost,
      State.charge_va, State.charge_vlen, State.charge_v, State.charge_procs] at t1wa t1va t1wlen t1vlen t1cap t1procs t1v t1w hp1 hct1
    have et1n : t1.w "hp_n" = n := by rw [t1w "hp_n" (by simp)]; exact hs.rn
    have et1j : t1.w "hp_j" = s.w "hp_j" := t1w "hp_j" (by simp)
    have et1go : t1.w "hp_go" = 1 := by rw [t1w "hp_go" (by simp)]; exact hgo'
    have hut1 : Unchanged st0 t1 ["hp_A", "hp_P"] [] (siftRegs ++ lwr) lvr :=
      Unchanged.of_regOnly (unch_charge' hs.unch 1) ht1 (by simp [siftRegs])
    have hKt1 : KeyRep t1 := hL.frame s t1 hs.keyrep
      (Unchanged.of_regOnly (unch_charge' (Unchanged.refl s _ _ _ _) 1) ht1 (by simp [hpRegs])) (by (try simp) <;> omega)
    set j := s.w "hp_j" with hjdef
    have ht1c : 1 < t1.cap := by rw [t1cap]; omega
    by_cases hleaf : n ≤ 2 * j + 1
    · -- no child: stop
      refine runs_ite_false (by rw [evalW_lt_of rfl rfl ht1c, hp1, et1n, if_neg (by omega)]) ?_
      refine runs_wset (evalW_lit_of (by simp; omega)) ?_
      refine ⟨⟨hL.frame t1 _ hKt1 ?_ (by (try simp) <;> omega), by simp [et1n], hnN, by simp [t1wlen, hs.lenA], by simp [t1wlen, hs.lenP],
        by simp [t1cap]; omega, by simpa [t1wa] using hs.pos, by simpa [t1wa] using hs.set, by simp [et1j]; omega,
        by simp [et1j]; exact hs.j0j, Or.inr ⟨by simp, by simpa [t1wa] using hgo1.2.leaf (by omega)⟩,
        unch_charge' (unch_setW' (unch_charge' hut1 1) (by simp [siftRegs]) _) 1, ?_⟩, ?_⟩
      · exact unch_charge' (unch_setW' (unch_charge' (Unchanged.refl t1 _ _ _ _) 1) (by simp [hpRegs]) _) 1
      · simp [et1j]; omega
      · simp [et1j]; omega
    · -- a child exists
      refine runs_ite_true (evalW_lt_of rfl rfl ht1c) (by rw [hp1, et1n]; simp; omega) ?_
      apply runs_seq
      refine (runs_downChoose hL (st := t1.charge 1) (j := j) (n := n)
        (hL.frame t1 _ hKt1 (unch_charge' (Unchanged.refl t1 _ _ _ _) 1) (by (try simp) <;> omega)) (by simp [hp1]) (by omega)
        (by simp [et1n]) hnN (by simp [t1wlen, hs.lenA]) (by simp [t1cap]; omega)
        (by simpa [t1wa] using hs.pos)).mono ?_
      rintro r1 ⟨hK1, h1wa, h1wlen, h1cap, hu1, hcn, hpar, hc0, hmin, hc1⟩
      simp only [State.charge_wa, State.charge_wlen, State.charge_cap, State.charge_cost, t1wa, t1wlen, t1cap]
        at h1wa h1wlen h1cap hmin hc1
      have r1w : ∀ y ∈ hpRegs, y ≠ "hp_p" → y ≠ "hp_x" → y ≠ "hp_y" → y ≠ "hp_lt" → r1.w y = t1.w y := by
        intro y hy h1 h2 h3 h4
        rw [hu1.wreg y ?_]
        · rfl
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨⟨h1, h2, h3⟩, hnotl y hy h4⟩
      have e1j : r1.w "hp_j" = j := by
        rw [r1w "hp_j" (by simp [hpRegs]) (by decide) (by decide) (by decide) (by decide), et1j]
      have e1n : r1.w "hp_n" = n := by
        rw [r1w "hp_n" (by simp [hpRegs]) (by decide) (by decide) (by decide) (by decide), et1n]
      have e1go : r1.w "hp_go" = 1 := by
        rw [r1w "hp_go" (by simp [hpRegs]) (by decide) (by decide) (by decide) (by decide), et1go]
      set c := r1.w "hp_p" with hcdef
      have hjc : j < c := by have := par_lt hc0; omega
      have hcj2 : 2 * j + 1 ≤ c := by have := (par_eq_iff hc0).mp hpar; omega
      apply runs_seq
      refine (runs_downPre2 (st := r1) (by rw [h1wlen, hs.lenA]; omega)
        (by rw [e1j, h1wlen, hs.lenA]; omega)).mono ?_
      rintro r2 ⟨hr2, hx2, hy2, hc2⟩
      have hr2' := hr2
      obtain ⟨h2wa, h2va, h2wlen, h2vlen, h2cap, h2procs, h2v, h2w⟩ := hr2'
      rw [h1wa] at hx2 hy2
      rw [e1j] at hy2
      have hxN : r2.w "hp_x" < N := by rw [hx2]; exact (hs.pos.slots _ hcn).1
      have hyN : r2.w "hp_y" < N := by rw [hy2]; exact (hs.pos.slots _ hjn).1
      have hK2 : KeyRep r2 := hL.frame r1 r2 hK1
        (Unchanged.of_regOnly (Unchanged.refl r1 _ _ _ _) hr2
          (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [hpRegs])) (by (try simp) <;> omega)
      apply runs_seq
      refine (hL.run r2 hK2 hxN hyN).mono ?_
      rintro r3 ⟨hlt, hu3, hc3, hK3⟩
      have r3w : ∀ y ∈ hpRegs, y ≠ "hp_lt" → r3.w y = r2.w y := fun y hy hne => hu3.wreg y (hnotl y hy hne)
      have r3wa : r3.wa = r2.wa := funext fun a => (hu3.warr a (by simp)).1
      have r3wlen : r3.wlen = r2.wlen := funext fun a => (hu3.warr a (by simp)).2
      have ej : r3.w "hp_j" = j := by
        rw [r3w "hp_j" (by simp [hpRegs]) (by decide), h2w "hp_j" (by simp)]; exact e1j
      have ep : r3.w "hp_p" = c := by
        rw [r3w "hp_p" (by simp [hpRegs]) (by decide), h2w "hp_p" (by simp)]
      have ex : r3.w "hp_x" = s.wa "hp_A" c := by rw [r3w "hp_x" (by simp [hpRegs]) (by decide)]; exact hx2
      have ey : r3.w "hp_y" = s.wa "hp_A" j := by rw [r3w "hp_y" (by simp [hpRegs]) (by decide)]; exact hy2
      have en : r3.w "hp_n" = n := by
        rw [r3w "hp_n" (by simp [hpRegs]) (by decide), h2w "hp_n" (by simp)]; exact e1n
      have ego : r3.w "hp_go" = 1 := by
        rw [r3w "hp_go" (by simp [hpRegs]) (by decide), h2w "hp_go" (by simp)]; exact e1go
      have eA : r3.wa "hp_A" = s.wa "hp_A" := by rw [r3wa, h2wa, h1wa]
      have eP : r3.wa "hp_P" = s.wa "hp_P" := by rw [r3wa, h2wa, h1wa]
      have eAl : r3.wlen "hp_A" = N := by rw [r3wlen, h2wlen, h1wlen]; exact hs.lenA
      have ePl : r3.wlen "hp_P" = N := by rw [r3wlen, h2wlen, h1wlen]; exact hs.lenP
      have ecap : r3.cap = s.cap := by rw [hu3.cap, h2cap, h1cap]
      have hB : Unchanged st0 r1 ["hp_A", "hp_P"] [] (siftRegs ++ lwr) lvr :=
        Unchanged.chain (unch_charge' hut1 1) hu1 (by simp) (by simp)
          (by intro y hy; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
              rcases hy with (rfl | rfl | rfl) | hy
              · simp [siftRegs]
              · simp [siftRegs]
              · simp [siftRegs]
              · exact Or.inr hy) (List.Subset.refl _)
      have hC : Unchanged st0 r2 ["hp_A", "hp_P"] [] (siftRegs ++ lwr) lvr :=
        Unchanged.of_regOnly hB hr2 (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [siftRegs])
      have hu13 : Unchanged st0 r3 ["hp_A", "hp_P"] [] (siftRegs ++ lwr) lvr :=
        Unchanged.chain hC hu3 (by simp) (by simp) (List.subset_append_right _ _) (List.Subset.refl _)
      have hscost3 : r3.cost ≤ s.cost + 2 * Cl + 12 := by
        omega
      unfold downPost
      by_cases hl : key (s.wa "hp_A" c) < key (s.wa "hp_A" j)
      · -- swap
        have hlt1 : r3.w "hp_lt" = 1 := by rw [hlt, hx2, hy2, if_pos hl]
        refine runs_ite_true (show evalW r3 (.var "hp_lt") = some (r3.w "hp_lt") from rfl) (by omega) ?_
        apply runs_seq
        refine runs_swapS (a := "hp_y") (b := "hp_x") ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
          try simp only [State.charge_w, State.charge_wlen, State.charge_cap, ej, ep, ex, ey, eAl, ePl, ecap]
        · omega
        · omega
        · exact (hs.pos.slots _ hjn).1
        · exact (hs.pos.slots _ hcn).1
        · omega
        · omega
        · omega
        · refine runs_wset rfl ?_
          have hjc' : j ≠ c := by omega
          have eA' : (swapState "hp_y" "hp_x" (r3.charge 1)).wa "hp_A" = swapA (s.wa "hp_A") j c := by
            rw [swapState_A (by simp [ej, ep, hjc']) (by simp [ey, ej, eA]) (by simp [ex, ep, eA])]
            simp [ej, ep, eA]
          have eP' : (swapState "hp_y" "hp_x" (r3.charge 1)).wa "hp_P" = swapP (s.wa "hp_A") (s.wa "hp_P") j c := by
            rw [swapState_P (by simp [ey, ej, eA]) (by simp [ex, ep, eA])]
            simp [ej, ep, eA, eP]
          have hLc := log_child hcj2
          refine ⟨⟨hL.frame r3 _ hK3 ?_ (by (try simp) <;> omega), by simp [en], hnN, by simp [eAl], by simp [ePl], by simp [ecap]; omega,
            ?_, ?_, by simp [ep]; omega, by simp [ep]; have := hs.j0j; omega, Or.inl ⟨by simp [ego], ?_⟩,
            unch_charge' (unch_setW' (unch_swapState (unch_charge' hu13 1) (by simp) (by simp))
              (by simp [siftRegs]) _) 1, ?_⟩, ?_⟩
          · exact unch_charge' (unch_setW' (unch_swapState (unch_charge' (Unchanged.refl r3 _ _ _ _) 1)
              (by simp) (by simp)) (by simp [hpRegs]) _) 1
          · simp only [State.charge_wa, State.setW_wa]
            rw [eA', eP']
            exact hs.pos.swap hjn hcn hjc'
          · simp only [State.charge_wa, State.setW_wa]
            rw [eA', T_swap hjn hcn]
            exact hs.set
          · simp only [State.charge_wa, State.setW_wa, State.charge_w, State.setW_w, if_true, swapState_w, ep]
            rw [eA']
            exact HeapDown.swap hgo1.2 hpar hc0 hcn hmin hl
          · simp only [State.charge_cost, State.setW_cost, swapState_cost, State.charge_w, State.setW_w,
              swapState_w, ep, if_true]
            rw [if_neg (by decide : ¬ ("hp_go" = "hp_j")), ego]
            have e2 : Nat.log 2 (c + 1) - Nat.log 2 (j0 + 1) ≥ (Nat.log 2 (j + 1) - Nat.log 2 (j0 + 1)) + 1 := by
              omega
            have e3 := Nat.mul_le_mul_left (2 * Cl + 20) e2
            rw [Nat.mul_add] at e3
            split_ifs <;> omega
          · simp only [State.charge_w, State.setW_w, swapState_w, ep, if_true]
            rw [if_neg (by decide : ¬ ("hp_go" = "hp_j")), ego, hgo']
            omega
      · -- stop
        have hlt0 : r3.w "hp_lt" = 0 := by rw [hlt, hx2, hy2, if_neg hl]
        refine runs_ite_false (show evalW r3 (.var "hp_lt") = some 0 by rw [evalW_var, hlt0]) ?_
        refine runs_wset (evalW_lit_of (by simp only [State.charge_cap]; rw [ecap]; omega)) ?_
        refine ⟨⟨hL.frame r3 _ hK3 ?_ (by (try simp) <;> omega), by simp [en], hnN, by simp [eAl], by simp [ePl], by simp [ecap]; omega,
          by simp [eA, eP]; exact hs.pos, by simp [eA]; exact hs.set, by simp [ej]; omega,
          by simp [ej]; exact hs.j0j, Or.inr ⟨by simp, ?_⟩,
          unch_charge' (unch_setW' (unch_charge' hu13 1) (by simp [siftRegs]) _) 1, ?_⟩, ?_⟩
        · exact unch_charge' (unch_setW' (unch_charge' (Unchanged.refl r3 _ _ _ _) 1) (by simp [hpRegs]) _) 1
        · simp only [State.charge_wa, State.setW_wa, eA]
          exact hgo1.2.stop (fun i hi hin hpi => le_trans (not_lt.mp hl) (hmin i hi hin hpi))
        · simp only [State.charge_cost, State.setW_cost, State.charge_w, State.setW_w, if_true]
          rw [if_neg (by decide : ¬ ("hp_j" = "hp_go"))]
          rw [ej]
          omega
        · simp only [State.charge_w, State.setW_w, if_true]
          rw [if_neg (by decide : ¬ ("hp_j" = "hp_go")), ej, hgo']
          omega
  · -- exit
    intro hgo
    have hgo0 : s.w "hp_go" = 0 := hgo
    rcases hs.go with h | h
    · exact absurd h.1 (by omega)
    · have hcost := hs.cost
      rw [if_pos hgo0] at hcost
      refine ⟨hL.frame s _ hs.keyrep (unch_charge' (Unchanged.refl s _ _ _ _) 1) (by (try simp) <;> omega), by simp [hs.rn],
        by simp [hs.lenA], by simp [hs.lenP], by simpa using hs.pos, by simpa using hs.set, by simpa using h.2,
        unch_charge' hs.unch 1, ?_⟩
      simp only [State.charge_cost]
      have hjn := hs.jn
      have : Nat.log 2 (s.w "hp_j" + 1) ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
      have : Nat.log 2 (s.w "hp_j" + 1) - Nat.log 2 (j0 + 1) ≤ Nat.log 2 n := by omega
      nlinarith

theorem runs_siftDown (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st : State V} {n : ℕ}
    (hK : KeyRep st) (hn : st.w "hp_n" = n) (hnN : n ≤ N) (hlA : st.wlen "hp_A" = N)
    (hlP : st.wlen "hp_P" = N) (hcap : 2 * N + 3 < st.cap) (hpos : PosOK N (st.wa "hp_A") (st.wa "hp_P") n)
    (hj : st.w "hp_j" < n) (hD : HeapDown key (st.wa "hp_A") n (st.w "hp_j")) :
    Runs ops (siftDown lessS) st
      (DownDone KeyRep key N Cl lwr lvr st n (T (st.wa "hp_A") n) (st.cost + 1)) := by
  unfold siftDown
  apply runs_seq
  refine runs_wset (evalW_lit_of (by omega)) ?_
  refine runs_downLoop hL (j0 := st.w "hp_j") _ ⟨hL.frame st _ hK ?_ (by (try simp) <;> omega), by simp [hn], hnN, by simp [hlA],
    by simp [hlP], by simp; omega, by simpa using hpos, by simp, by simp; omega, by simp,
    Or.inl ⟨by simp, by simpa using hD⟩,
    unch_charge' (unch_setW' (Unchanged.refl st _ _ _ _) (by simp [siftRegs]) _) 1, ?_⟩
  · exact unch_charge' (unch_setW' (Unchanged.refl st _ _ _ _) (by simp [hpRegs]) _) 1
  · simp

end SiftDown


/-! ### Heap operations -/

section Ops

open Frontier.RAM

/-- `A[n] := v; P[v] := n + 1; j := n; n := n + 1` -/
def pushPre : Stmt :=
  .seq (.wstore "hp_A" (.var "hp_n") (.var "hp_v"))
    (.seq (.wstore "hp_P" (.var "hp_v") (.add (.var "hp_n") (.lit 1)))
      (.seq (.wset "hp_j" (.var "hp_n")) (.wset "hp_n" (.add (.var "hp_n") (.lit 1)))))

/-- push the (absent) vertex `hp_v` -/
def pushS (lessS : Stmt) : Stmt := .seq pushPre (siftUp lessS)

/-- the key of the (present) vertex `hp_v` went down: sift it up -/
def decS (lessS : Stmt) : Stmt :=
  .seq (.wset "hp_j" (.sub (.load "hp_P" (.var "hp_v")) (.lit 1))) (siftUp lessS)

/-- push `hp_v` if absent, else decrease its key -/
def pushOrDecS (lessS : Stmt) : Stmt :=
  .ite (.eq (.load "hp_P" (.var "hp_v")) (.lit 0)) (pushS lessS) (decS lessS)

/-- `v := A[0]; n := n - 1; P[v] := 0` -/
def popPre1 : Stmt :=
  .seq (.wset "hp_v" (.load "hp_A" (.lit 0)))
    (.seq (.wset "hp_n" (.sub (.var "hp_n") (.lit 1))) (.wstore "hp_P" (.var "hp_v") (.lit 0)))

/-- `c := A[n]; A[0] := c; P[c] := 1; j := 0` -/
def popPre2 : Stmt :=
  .seq (.wset "hp_c" (.load "hp_A" (.var "hp_n")))
    (.seq (.wstore "hp_A" (.lit 0) (.var "hp_c"))
      (.seq (.wstore "hp_P" (.var "hp_c") (.lit 1)) (.wset "hp_j" (.lit 0))))

/-- pop the minimum into `hp_v` -/
def popS (lessS : Stmt) : Stmt :=
  .seq popPre1 (.ite (.lt (.lit 0) (.var "hp_n")) (.seq popPre2 (siftDown lessS)) .skip)

variable {V : Type} {K : Type*} [LinearOrder K] {ops : VOps V} {lessS : Stmt} {KeyRep : State V → Prop}
  {key : ℕ → K} {N Cl : ℕ} {lwr lvr : List String}

/-- Only the word arrays `was` and word registers `ws` changed. -/
def WOnly (st r : State V) (was ws : List String) : Prop :=
  r.va = st.va ∧ r.vlen = st.vlen ∧ r.wlen = st.wlen ∧ r.cap = st.cap ∧ r.procs = st.procs ∧ r.v = st.v ∧
    (∀ a, a ∉ was → r.wa a = st.wa a) ∧ (∀ y, y ∉ ws → r.w y = st.w y)

theorem WOnly.unch {st r : State V} {was ws : List String} (h : WOnly st r was ws) :
    Unchanged st r was [] ws [] := by
  obtain ⟨hva, hvlen, hwlen, hcap, hprocs, hv, hwa, hw⟩ := h
  refine ⟨fun a ha => ⟨hwa a ha, by rw [hwlen]⟩, fun a _ => ⟨by rw [hva], by rw [hvlen]⟩,
    fun y hy => hw y hy, fun y _ => by rw [hv], hcap, hprocs⟩

theorem runs_pushPre {st : State V} {n v : ℕ} (hn : st.w "hp_n" = n) (hv : st.w "hp_v" = v)
    (hnA : n < st.wlen "hp_A") (hvP : v < st.wlen "hp_P") (hc : n + 1 < st.cap) :
    Runs ops pushPre st (fun r => WOnly st r ["hp_A", "hp_P"] ["hp_j", "hp_n"] ∧
      (∀ q, r.wa "hp_A" q = if q = n then v else st.wa "hp_A" q) ∧
      (∀ q, r.wa "hp_P" q = if q = v then n + 1 else st.wa "hp_P" q) ∧
      r.w "hp_j" = n ∧ r.w "hp_n" = n + 1 ∧ r.cost = st.cost + 4) := by
  apply wp_sound
  have h1 : 1 < st.cap := by omega
  simp +contextual [pushPre, wp, evalW_add', evalW_lit', fit_of_lt h1, fit_of_lt hc, hn, hv, hnA, hvP, WOnly]
  intro a h1 h2; funext q; simp [h1, h2]

theorem runs_popPre1 {st : State V} {n : ℕ} (hn : st.w "hp_n" = n + 1) (hA : 0 < st.wlen "hp_A")
    (hvP : st.wa "hp_A" 0 < st.wlen "hp_P") (h1 : 1 < st.cap) :
    Runs ops popPre1 st (fun r => WOnly st r ["hp_P"] ["hp_v", "hp_n"] ∧
      (∀ q, r.wa "hp_P" q = if q = st.wa "hp_A" 0 then 0 else st.wa "hp_P" q) ∧
      r.w "hp_v" = st.wa "hp_A" 0 ∧ r.w "hp_n" = n ∧ r.cost = st.cost + 3) := by
  apply wp_sound
  have h0 : 0 < st.cap := by omega
  simp +contextual [popPre1, wp, evalW_sub', evalW_lit', fit_of_lt h1, fit_of_lt h0, hn, hA, hvP, WOnly]
  intro a h1; funext q; simp [h1]

theorem runs_popPre2 {st : State V} {n : ℕ} (hn : st.w "hp_n" = n) (hnA : n < st.wlen "hp_A")
    (hcP : st.wa "hp_A" n < st.wlen "hp_P") (h1 : 1 < st.cap) :
    Runs ops popPre2 st (fun r => WOnly st r ["hp_A", "hp_P"] ["hp_c", "hp_j"] ∧
      (∀ q, r.wa "hp_A" q = if q = 0 then st.wa "hp_A" n else st.wa "hp_A" q) ∧
      (∀ q, r.wa "hp_P" q = if q = st.wa "hp_A" n then 1 else st.wa "hp_P" q) ∧
      r.w "hp_j" = 0 ∧ r.cost = st.cost + 4) := by
  apply wp_sound
  have h0 : 0 < st.cap := by omega
  have hA0 : 0 < st.wlen "hp_A" := by omega
  simp +contextual [popPre2, wp, evalW_lit', fit_of_lt h1, fit_of_lt h0, hn, hnA, hcP, hA0, WOnly]
  intro a h1 h2; funext q; simp [h1, h2]

/-- The heap representation. -/
structure HeapRep (KeyRep : State V → Prop) (key : ℕ → K) (N : ℕ) (st : State V) (n : ℕ) : Prop where
  keyrep : KeyRep st
  rn : st.w "hp_n" = n
  nN : n ≤ N
  lenA : st.wlen "hp_A" = N
  lenP : st.wlen "hp_P" = N
  pos : PosOK N (st.wa "hp_A") (st.wa "hp_P") n
  heap : HeapOK key (st.wa "hp_A") n

theorem upDone_frame {st0 r : State V} {n : ℕ} {T0 : Finset ℕ} {j0 c0 : ℕ}
    (h : UpDone KeyRep key N Cl lwr lvr st0 n T0 j0 c0 r) :
    Unchanged st0 r ["hp_A", "hp_P"] [] (hpRegs ++ lwr) lvr :=
  h.2.2.2.2.2.2.2.1.mono (List.Subset.refl _) (List.Subset.refl _)
    (by intro y hy; simp only [siftRegs, hpRegs, List.mem_append, List.mem_cons] at hy ⊢; tauto)
    (List.Subset.refl _)

theorem downDone_frame {st0 r : State V} {n : ℕ} {T0 : Finset ℕ} {c0 : ℕ}
    (h : DownDone KeyRep key N Cl lwr lvr st0 n T0 c0 r) :
    Unchanged st0 r ["hp_A", "hp_P"] [] (hpRegs ++ lwr) lvr :=
  h.2.2.2.2.2.2.2.1.mono (List.Subset.refl _) (List.Subset.refl _)
    (by intro y hy; simp only [siftRegs, hpRegs, List.mem_append, List.mem_cons] at hy ⊢; tauto)
    (List.Subset.refl _)

theorem notl_of (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) : ∀ y ∈ hpRegs, y ≠ "hp_lt" → y ∉ lwr :=
  fun y hy hne hyl => hne (hL.regs y hyl hy)

/-- **Push** an absent vertex. -/
theorem runs_push (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st : State V} {n v : ℕ}
    (hH : HeapRep KeyRep key N st n) (hnN : n < N) (hv : st.w "hp_v" = v) (hvN : v < N)
    (hvT : v ∉ T (st.wa "hp_A") n) (hcap : 2 * N + 3 < st.cap) :
    Runs ops (pushS lessS) st (fun r => HeapRep KeyRep key N r (n + 1) ∧
      T (r.wa "hp_A") (n + 1) = insert v (T (st.wa "hp_A") n) ∧ r.w "hp_v" = v ∧
      Unchanged st r ["hp_A", "hp_P"] [] (hpRegs ++ lwr) lvr ∧
      r.cost ≤ st.cost + (Cl + 12) * (Nat.log 2 (n + 1) + 1) + 6) := by
  have hnotl := notl_of hL
  have hPv : st.wa "hp_P" v = 0 := by
    by_contra h; exact hvT ((hH.pos.mem_T hvN).mpr h)
  unfold pushS
  apply runs_seq
  refine (runs_pushPre hH.rn hv (by rw [hH.lenA]; exact hnN) (by rw [hH.lenP]; exact hvN) (by omega)).mono ?_
  rintro t ⟨ht, hA, hP, hj, hn', hc⟩
  have ht' := ht
  obtain ⟨tva, tvlen, twlen, tcap, tprocs, tv, twa, tw⟩ := ht'
  have eA : t.wa "hp_A" = Function.update (st.wa "hp_A") n v := by
    funext q; rw [hA q]; by_cases hq : q = n <;> simp [hq, Function.update]
  have eP : t.wa "hp_P" = Function.update (st.wa "hp_P") v (n + 1) := by
    funext q; rw [hP q]; by_cases hq : q = v <;> simp [hq, Function.update]
  have hunt : Unchanged st t ["hp_A", "hp_P"] [] (hpRegs ++ lwr) lvr :=
    ht.unch.mono (List.Subset.refl _) (by simp) (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [hpRegs])
      (by simp)
  have hKt : KeyRep t := hL.frame st t hH.keyrep
    (ht.unch.mono (List.Subset.refl _) (List.Subset.refl _)
      (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [hpRegs]) (by simp)) (by (try simp) <;> omega)
  refine (runs_siftUp hL (n := n + 1) hKt hn' (by omega) (by rw [twlen, hH.lenA]) (by rw [twlen, hH.lenP])
    (by rw [tcap]; omega) (by rw [eA, eP]; exact hH.pos.push hvN hPv) (by rw [hj]; omega)
    (by rw [eA, hj]; exact hH.heap.push v)).mono ?_
  rintro r hr
  have hfr := upDone_frame hr
  obtain ⟨hK, hrn, hlA, hlP, hpos, hT, hheap, hunch, hcost⟩ := hr
  refine ⟨⟨hK, hrn, by omega, hlA, hlP, hpos, hheap⟩, ?_, ?_, ?_, ?_⟩
  · rw [hT, eA]; exact T_push (fun _ _ => Or.inr trivial)
  · rw [hunch.wreg "hp_v" (by simp [siftRegs, hnotl "hp_v" (by simp [hpRegs]) (by decide)]),
      tw "hp_v" (by simp), hv]
  · exact Unchanged.chain hunt hfr (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)
      (List.Subset.refl _)
  · rw [hj, hc] at hcost
    omega

/-- **Decrease-key**: the key of the present vertex `hp_v` went down (from `key0` to `key`). -/
theorem runs_dec (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st : State V} {n v : ℕ} {key0 : ℕ → K}
    (hK : KeyRep st) (hn : st.w "hp_n" = n) (hnN : n ≤ N) (hlA : st.wlen "hp_A" = N)
    (hlP : st.wlen "hp_P" = N) (hpos : PosOK N (st.wa "hp_A") (st.wa "hp_P") n)
    (hH0 : HeapOK key0 (st.wa "hp_A") n) (hv : st.w "hp_v" = v) (hvT : v ∈ T (st.wa "hp_A") n)
    (hk : ∀ u, u ≠ v → key u = key0 u) (hkv : key v ≤ key0 v) (hcap : 2 * N + 3 < st.cap) :
    Runs ops (decS lessS) st (fun r => HeapRep KeyRep key N r n ∧ T (r.wa "hp_A") n = T (st.wa "hp_A") n ∧
      r.w "hp_v" = v ∧ Unchanged st r ["hp_A", "hp_P"] [] (hpRegs ++ lwr) lvr ∧
      r.cost ≤ st.cost + (Cl + 12) * (Nat.log 2 n + 1) + 3) := by
  have hnotl := notl_of hL
  have hvN : v < N := hpos.lt_N hvT
  have hPv : st.wa "hp_P" v ≠ 0 := (hpos.mem_T hvN).mp hvT
  obtain ⟨hPn, hAv⟩ := hpos.back v hvN hPv
  set j := st.wa "hp_P" v - 1 with hjdef
  have hjn : j < n := by omega
  unfold decS
  apply runs_seq
  refine runs_wset (a := j) (by simp [evalW_sub', evalW_load', evalW_lit', fit_of_lt (show 1 < st.cap by omega),
    hv, hlP, hvN, hjdef]) ?_
  have hinj : ∀ i < n, st.wa "hp_A" i = st.wa "hp_A" j → i = j := fun i hi e => hpos.inj hi hjn e
  have hU : HeapUp key (st.wa "hp_A") n j := hH0.decrease hjn hinj (by rw [hAv]; exact hk) (by rw [hAv]; exact hkv)
  have hunt : Unchanged st ((st.setW "hp_j" j).charge 1) ["hp_A", "hp_P"] [] (hpRegs ++ lwr) lvr :=
    unch_charge' (unch_setW' (Unchanged.refl st _ _ _ _) (by simp [hpRegs]) _) 1
  refine (runs_siftUp hL (n := n) (hL.frame st _ hK (unch_charge' (unch_setW' (Unchanged.refl st _ _ _ _)
    (by simp [hpRegs]) _) 1) (by (try simp) <;> omega)) (by simp [hn]) hnN (by simp [hlA]) (by simp [hlP]) (by simp; omega)
    (by simpa using hpos) (by simp; omega) (by simpa using hU)).mono ?_
  rintro r hr
  have hfr := upDone_frame hr
  obtain ⟨hK', hrn, hlA', hlP', hpos', hT, hheap, hunch, hcost⟩ := hr
  refine ⟨⟨hK', hrn, hnN, hlA', hlP', hpos', hheap⟩, by rw [hT]; simp, ?_, ?_, ?_⟩
  · rw [hunch.wreg "hp_v" (by simp [siftRegs, hnotl "hp_v" (by simp [hpRegs]) (by decide)])]
    simp [hv]
  · exact Unchanged.chain hunt hfr (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)
      (List.Subset.refl _)
  · simp only [State.charge_cost, State.setW_cost, State.charge_w, State.setW_w, if_true] at hcost
    have : Nat.log 2 (j + 1) ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
    have := Nat.mul_le_mul_left (Cl + 12) (Nat.add_le_add_right this 1)
    omega

/-- **Pop** the minimum (heap of size `n + 1`). -/
theorem runs_pop (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st : State V} {n : ℕ}
    (hH : HeapRep KeyRep key N st (n + 1)) (hcap : 2 * N + 3 < st.cap) :
    Runs ops (popS lessS) st (fun r => HeapRep KeyRep key N r n ∧ r.w "hp_v" = st.wa "hp_A" 0 ∧
      (∀ u ∈ T (st.wa "hp_A") (n + 1), key (st.wa "hp_A" 0) ≤ key u) ∧
      T (r.wa "hp_A") n = (T (st.wa "hp_A") (n + 1)).erase (st.wa "hp_A" 0) ∧
      Unchanged st r ["hp_A", "hp_P"] [] (hpRegs ++ lwr) lvr ∧
      r.cost ≤ st.cost + (2 * Cl + 20) * (Nat.log 2 n + 1) + 12) := by
  have hnotl := notl_of hL
  have hnN := hH.nN
  have hmin : ∀ u ∈ T (st.wa "hp_A") (n + 1), key (st.wa "hp_A" 0) ≤ key u := by
    intro u hu
    simp only [T, Finset.mem_image, Finset.mem_range] at hu
    obtain ⟨i, hi, rfl⟩ := hu
    exact hH.heap.root_le i hi
  have hA0N : st.wa "hp_A" 0 < N := (hH.pos.slots 0 (by omega)).1
  unfold popS
  apply runs_seq
  refine (runs_popPre1 hH.rn (by rw [hH.lenA]; omega) (by rw [hH.lenP]; exact hA0N) (by omega)).mono ?_
  rintro t1 ⟨ht1, hP1, hv1, hn1, hc1⟩
  have ht1' := ht1
  obtain ⟨t1va, t1vlen, t1wlen, t1cap, t1procs, t1v, t1wa, t1w⟩ := ht1'
  have eA1 : t1.wa "hp_A" = st.wa "hp_A" := t1wa "hp_A" (by simp)
  have eP1 : t1.wa "hp_P" = Function.update (st.wa "hp_P") (st.wa "hp_A" 0) 0 := by
    funext q; rw [hP1 q]; by_cases hq : q = st.wa "hp_A" 0 <;> simp [hq, Function.update]
  have hunt1 : Unchanged st t1 ["hp_A", "hp_P"] [] (hpRegs ++ lwr) lvr :=
    ht1.unch.mono (by simp) (by simp) (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [hpRegs])
      (by simp)
  have hKt1 : KeyRep t1 := hL.frame st t1 hH.keyrep
    (ht1.unch.mono (by simp) (List.Subset.refl _)
      (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [hpRegs]) (by simp)) (by (try simp) <;> omega)
  have hc1' : 1 < t1.cap := by rw [t1cap]; omega
  by_cases hn0 : n = 0
  · -- the heap becomes empty
    subst hn0
    refine runs_ite_false (by rw [evalW_lt_of (evalW_lit_of (by omega)) rfl hc1', hn1]; simp) ?_
    refine runs_skip ?_
    refine ⟨⟨hL.frame t1 _ hKt1 (unch_charge' (unch_charge' (Unchanged.refl t1 _ _ _ _) 1) 1) (by (try simp) <;> omega), by simp [hn1],
      by omega, by simp [t1wlen, hH.lenA], by simp [t1wlen, hH.lenP], ?_, fun i hi hin => by omega⟩,
      by simp [hv1], hmin, ?_, unch_charge' (unch_charge' hunt1 1) 1, by simp; omega⟩
    · simp only [State.charge_wa]
      rw [eA1, eP1]
      exact hH.pos.pop_last
    · simp only [State.charge_wa, eA1]
      ext u
      simp only [T, Finset.mem_image, Finset.mem_range, Finset.mem_erase]
      constructor
      · rintro ⟨i, hi, _⟩; omega
      · rintro ⟨hu, i, hi, rfl⟩
        exact absurd (by rw [show i = 0 by omega]) hu
  · -- move the last vertex to the root and sift it down
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    refine runs_ite_true (evalW_lt_of (evalW_lit_of (by omega)) rfl hc1') (by rw [hn1]; simp [hnpos]) ?_
    apply runs_seq
    have hAnN : st.wa "hp_A" n < N := (hH.pos.slots n (by omega)).1
    refine (runs_popPre2 (st := t1.charge 1) (n := n) (by simp [hn1]) (by simp [t1wlen, hH.lenA]; omega)
      (by simp [eA1, t1wlen, hH.lenP]; exact hAnN) (by simp; omega)).mono ?_
    rintro t2 ⟨ht2, hA2, hP2, hj2, hc2⟩
    have ht2' := ht2
    obtain ⟨t2va, t2vlen, t2wlen, t2cap, t2procs, t2v, t2wa, t2w⟩ := ht2'
    simp only [State.charge_wa, State.charge_wlen, State.charge_cap, State.charge_w, State.charge_cost, eA1] at hA2 hP2 t2wlen t2cap t2w hc2
    have eA2 : t2.wa "hp_A" = Function.update (st.wa "hp_A") 0 (st.wa "hp_A" n) := by
      funext q; rw [hA2 q]; by_cases hq : q = 0 <;> simp [hq, Function.update]
    have eP2 : t2.wa "hp_P" = Function.update (Function.update (st.wa "hp_P") (st.wa "hp_A" 0) 0)
        (st.wa "hp_A" n) 1 := by
      funext q; rw [hP2 q, eP1]; by_cases hq : q = st.wa "hp_A" n <;> simp [hq, Function.update]
    have hunt2 : Unchanged st t2 ["hp_A", "hp_P"] [] (hpRegs ++ lwr) lvr :=
      Unchanged.chain (unch_charge' hunt1 1) ht2.unch (List.Subset.refl _) (by simp)
        (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [hpRegs]) (by simp)
    have hKt2 : KeyRep t2 := hL.frame t1 t2 hKt1
      (Unchanged.chain (unch_charge' (Unchanged.refl t1 _ _ _ _) 1) ht2.unch (List.Subset.refl _) (by simp)
        (by intro y hy; simp at hy; rcases hy with rfl | rfl <;> simp [hpRegs]) (by simp)) (by (try simp) <;> omega)
    have e2n : t2.w "hp_n" = n := by rw [t2w "hp_n" (by simp)]; exact hn1
    refine (runs_siftDown hL (n := n) hKt2 e2n (by omega) (by rw [t2wlen, t1wlen, hH.lenA])
      (by rw [t2wlen, t1wlen, hH.lenP]) (by rw [t2cap, t1cap]; omega)
      (by rw [eA2, eP2]; exact hH.pos.pop hnpos) (by rw [hj2]; exact hnpos)
      (by rw [eA2, hj2]; exact hH.heap.pop)).mono ?_
    rintro r hr
    have hfr := downDone_frame hr
    obtain ⟨hK', hrn, hlA', hlP', hpos', hT, hheap, hunch, hcost⟩ := hr
    refine ⟨⟨hK', hrn, by omega, hlA', hlP', hpos', hheap⟩, ?_, hmin, ?_, ?_, ?_⟩
    · rw [hunch.wreg "hp_v" (by simp [siftRegs, hnotl "hp_v" (by simp [hpRegs]) (by decide)]),
        t2w "hp_v" (by simp)]
      simp [hv1]
    · rw [hT, eA2]; exact T_pop hH.pos
    · exact Unchanged.chain hunt2 hfr (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _)
        (List.Subset.refl _)
    · omega

/-- **Push or decrease**: `hp_v` is inserted if absent; if present its key went down (from `key0`). -/
theorem runs_pushOrDec (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st : State V} {n v : ℕ} {key0 : ℕ → K}
    (hK : KeyRep st) (hn : st.w "hp_n" = n) (hnN : n ≤ N) (hlA : st.wlen "hp_A" = N)
    (hlP : st.wlen "hp_P" = N) (hpos : PosOK N (st.wa "hp_A") (st.wa "hp_P") n)
    (hH0 : HeapOK key0 (st.wa "hp_A") n) (hv : st.w "hp_v" = v) (hvN : v < N)
    (hk : ∀ u, u ≠ v → key u = key0 u) (hkv : v ∈ T (st.wa "hp_A") n → key v ≤ key0 v)
    (hcap : 2 * N + 3 < st.cap) :
    Runs ops (pushOrDecS lessS) st (fun r => ∃ n', HeapRep KeyRep key N r n' ∧
      T (r.wa "hp_A") n' = insert v (T (st.wa "hp_A") n) ∧ r.w "hp_v" = v ∧
      Unchanged st r ["hp_A", "hp_P"] [] (hpRegs ++ lwr) lvr ∧
      r.cost ≤ st.cost + (Cl + 12) * (Nat.log 2 (n + 1) + 1) + 8) := by
  have h1 : 1 < st.cap := by omega
  have hev : evalW st (.eq (.load "hp_P" (.var "hp_v")) (.lit 0)) =
      some (if st.wa "hp_P" v = 0 then 1 else 0) :=
    evalW_eq_of (evalW_load_of (by rw [evalW_var, hv]) (by rw [hlP]; exact hvN)) (evalW_lit_of (by omega)) h1
  unfold pushOrDecS
  by_cases hP0 : st.wa "hp_P" v = 0
  · -- absent: push
    have hvT : v ∉ T (st.wa "hp_A") n := fun h => ((hpos.mem_T hvN).mp h) hP0
    have hnN' : n < N := hpos.lt_of_not_mem hvN hvT
    have hHk : HeapOK key (st.wa "hp_A") n := hH0.congr (fun i hi => hk _ (fun e => hvT (by
      rw [← e]; simp only [T, Finset.mem_image, Finset.mem_range]; exact ⟨i, hi, rfl⟩)))
    refine runs_ite_true hev (by simp [hP0]) ?_
    refine (runs_push hL (n := n) ⟨hL.frame st _ hK (unch_charge' (Unchanged.refl st _ _ _ _) 1) (by (try simp) <;> omega), by simp [hn],
      hnN, by simp [hlA], by simp [hlP], by simpa using hpos, by simpa using hHk⟩ hnN' (by simp [hv]) hvN
      (by simpa using hvT) (by simp; omega)).mono ?_
    rintro r ⟨hR, hT, hrv, hunch, hcost⟩
    refine ⟨n + 1, hR, by simpa using hT, hrv, Unchanged.chain (unch_charge' (Unchanged.refl st _ _ _ _) 1) hunch
      (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _), ?_⟩
    simp at hcost; omega
  · -- present: decrease
    have hvT : v ∈ T (st.wa "hp_A") n := (hpos.mem_T hvN).mpr hP0
    refine runs_ite_false (by rw [hev, if_neg hP0]) ?_
    refine (runs_dec hL (n := n) (key0 := key0) (hL.frame st _ hK (unch_charge' (Unchanged.refl st _ _ _ _) 1) (by (try simp) <;> omega))
      (by simp [hn]) hnN (by simp [hlA]) (by simp [hlP]) (by simpa using hpos) (by simpa using hH0) (by simp [hv])
      (by simpa using hvT) hk (hkv hvT) (by simp; omega)).mono ?_
    rintro r ⟨hR, hT, hrv, hunch, hcost⟩
    refine ⟨n, hR, by rw [hT]; simp [Finset.insert_eq_of_mem hvT], hrv,
      Unchanged.chain (unch_charge' (Unchanged.refl st _ _ _ _) 1) hunch
      (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _), ?_⟩
    have : Nat.log 2 n ≤ Nat.log 2 (n + 1) := Nat.log_mono_right (by omega)
    have := Nat.mul_le_mul_left (Cl + 12) (Nat.add_le_add_right this 1)
    simp at hcost; omega

/-- one step of `clearS` -/
def clearBody : Stmt :=
  .seq (.wset "hp_n" (.sub (.var "hp_n") (.lit 1))) (.wstore "hp_P" (.load "hp_A" (.var "hp_n")) (.lit 0))

/-- empty the heap (resets `P` on the remaining vertices) -/
def clearS : Stmt := .while (.lt (.lit 0) (.var "hp_n")) clearBody

/-- allocate an empty heap for vertices `< N` (register `x` holds `N`) -/
def initS (x : String) : Stmt :=
  .seq (.walloc "hp_A" (.var x)) (.seq (.walloc "hp_P" (.var x)) (.wset "hp_n" (.lit 0)))

theorem runs_clearBody {t : State V} {m : ℕ} (htn : t.w "hp_n" = m + 1) (hA : m < t.wlen "hp_A")
    (hP : t.wa "hp_A" m < t.wlen "hp_P") (h1 : 1 < t.cap) :
    Runs ops clearBody t (fun r => WOnly t r ["hp_P"] ["hp_n"] ∧
      (∀ q, r.wa "hp_P" q = if q = t.wa "hp_A" m then 0 else t.wa "hp_P" q) ∧ r.w "hp_n" = m ∧
      r.cost = t.cost + 2) := by
  apply wp_sound
  have h0 : 0 < t.cap := by omega
  simp +contextual [clearBody, wp, evalW_sub', evalW_lit', evalW_load', fit_of_lt h1, fit_of_lt h0, htn, hA, hP,
    WOnly]
  intro a ha; funext q; simp [ha]

/-- **Clear.** -/
theorem runs_clear (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st : State V} {n : ℕ}
    (hK : KeyRep st) (hn : st.w "hp_n" = n) (hnN : n ≤ N) (hlA : st.wlen "hp_A" = N)
    (hlP : st.wlen "hp_P" = N) (hpos : PosOK N (st.wa "hp_A") (st.wa "hp_P") n) (hcap : 2 * N + 3 < st.cap) :
    Runs ops clearS st (fun r => HeapRep KeyRep key N r 0 ∧ (∀ v < N, r.wa "hp_P" v = 0) ∧
      r.wa "hp_A" = st.wa "hp_A" ∧ Unchanged st r ["hp_P"] [] ["hp_n"] [] ∧ r.cost ≤ st.cost + 3 * n + 1) := by
  refine runs_while (fun k t => t.w "hp_n" = n - k ∧ t.wa "hp_A" = st.wa "hp_A" ∧ t.wlen = st.wlen ∧
      t.cap = st.cap ∧ PosOK N (t.wa "hp_A") (t.wa "hp_P") (n - k) ∧ Unchanged st t ["hp_P"] [] ["hp_n"] [] ∧
      st.cost ≤ t.cost ∧ t.cost ≤ st.cost + 3 * k) n _ ?_ ?_ st ⟨by simp [hn], rfl, rfl, rfl, by simpa using hpos,
      Unchanged.refl st _ _ _ _, le_rfl, by simp⟩
  · rintro k hk t ⟨htn, htA, htlen, htcap, htpos, htu, htc0, htc⟩
    have h1 : 1 < t.cap := by rw [htcap]; omega
    refine ⟨1, by rw [evalW_lt_of (evalW_lit_of (by omega)) rfl h1, htn, if_pos (show 0 < n - k by omega)],
      one_ne_zero, ?_⟩
    have e1 : n - k = (n - (k + 1)) + 1 := by omega
    have hm : n - (k + 1) < n - k := by omega
    have hAm : t.wa "hp_A" (n - (k + 1)) < N := (htpos.slots _ hm).1
    refine (runs_clearBody (t := t.charge 1) (m := n - (k + 1)) (by simp [htn]; omega)
      (by simp [htlen, hlA]; omega) (by simp [htlen, hlP]; exact hAm) (by simpa using h1)).mono ?_
    rintro r ⟨hr, hrP, hrn, hrc⟩
    have hr' := hr
    obtain ⟨rva, rvlen, rwlen, rcap, rprocs, rv, rwa, rw⟩ := hr'
    have eA : r.wa "hp_A" = t.wa "hp_A" := by rw [rwa "hp_A" (by simp)]; rfl
    have eP : r.wa "hp_P" = Function.update (t.wa "hp_P") (t.wa "hp_A" (n - (k + 1))) 0 := by
      funext q; rw [hrP q]; by_cases hq : q = t.wa "hp_A" (n - (k + 1)) <;> simp [hq, Function.update]
    refine ⟨hrn, by rw [eA, htA], by rw [rwlen]; exact htlen, by rw [rcap]; exact htcap, ?_,
      Unchanged.chain (unch_charge' htu 1) hr.unch (List.Subset.refl _) (List.Subset.refl _)
        (List.Subset.refl _) (List.Subset.refl _), by simp at hrc; omega, by simp at hrc; omega⟩
    rw [eA, eP]
    exact (e1 ▸ htpos).shrink
  · rintro t ⟨htn, htA, htlen, htcap, htpos, htu, htc0, htc⟩
    have h1 : 1 < t.cap := by rw [htcap]; omega
    refine ⟨by rw [evalW_lt_of (evalW_lit_of (by omega)) rfl h1, htn]; simp, ?_⟩
    refine ⟨⟨hL.frame st _ hK ?_ (by (try simp) <;> omega), by simp [htn], by omega, by simp [htlen, hlA], by simp [htlen, hlP],
      by simpa using htpos, fun i hi hin => by simp at hin⟩, ?_, by simp [htA], unch_charge' htu 1,
      by simp; omega⟩
    · exact (unch_charge' htu 1).mono (by simp) (List.Subset.refl _) (by simp [hpRegs]) (List.Subset.refl _)
    · intro v hv
      simp only [State.charge_wa]
      by_contra hne
      have := (htpos.back v hv hne).1
      simp at this
      omega

/-- **Init.** -/
theorem runs_init (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st : State V} {x : String}
    (hK : KeyRep st) (hx : st.w x = N) (hcap : 2 * N + 3 < st.cap) :
    Runs ops (initS x) st (fun r => HeapRep KeyRep key N r 0 ∧
      Unchanged st r ["hp_A", "hp_P"] [] ["hp_n"] [] ∧ r.cost = st.cost + 2 * N + 3) := by
  apply wp_sound
  have h0 : 0 < st.cap := by omega
  simp only [initS, wp, evalW_var, evalW_lit', State.charge_w, State.allocW_w, hx, State.charge_cap,
    State.allocW_cap, fit_of_lt h0]
  refine ⟨⟨hL.frame st _ hK ?_ (by (try simp) <;> omega), by simp, Nat.zero_le _, by simp, by simp, ⟨fun i hi => by omega, fun v _ hv => ?_⟩,
    fun i hi hin => by omega⟩, ?_, by simp; omega⟩
  · refine ⟨fun b hb => ?_, fun b _ => ⟨rfl, rfl⟩, fun y hy => ?_, fun y _ => rfl, rfl, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
      refine ⟨funext fun j => ?_, ?_⟩ <;> simp [hb.1, hb.2]
    · have : y ≠ "hp_n" := fun e => hy (by simp [hpRegs, e])
      simp [this]
  · simp at hv
  · refine ⟨fun b hb => ?_, fun b _ => ⟨rfl, rfl⟩, fun y hy => ?_, fun y _ => rfl, rfl, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
      refine ⟨funext fun j => ?_, ?_⟩ <;> simp [hb.1, hb.2]
    · have : y ≠ "hp_n" := fun e => hy (by simp [e])
      simp [this]

/-- `hp_v := A[0]` (the minimum; heap unchanged) -/
def topS : Stmt := .wset "hp_v" (.load "hp_A" (.lit 0))

/-- push-or-decrease with the vertex in `hp_x` (agent-08's base-loop interface) -/
def pushOrDecX (lessS : Stmt) : Stmt := .seq (.wset "hp_v" (.var "hp_x")) (pushOrDecS lessS)

/-- **Top**: read the minimum. -/
theorem runs_top {st : State V} {n : ℕ} (hH : HeapRep KeyRep key N st (n + 1)) (hcap : 2 * N + 3 < st.cap) :
    Runs ops topS st (fun r => r.w "hp_v" = st.wa "hp_A" 0 ∧
      (∀ u ∈ T (st.wa "hp_A") (n + 1), key (st.wa "hp_A" 0) ≤ key u) ∧
      RegOnly st r ["hp_v"] ∧ r.cost = st.cost + 1) := by
  have hmin : ∀ u ∈ T (st.wa "hp_A") (n + 1), key (st.wa "hp_A" 0) ≤ key u := by
    intro u hu
    simp only [T, Finset.mem_image, Finset.mem_range] at hu
    obtain ⟨i, hi, rfl⟩ := hu
    exact hH.heap.root_le i hi
  have hnN := hH.nN
  refine runs_wset (evalW_load_of (evalW_lit_of (by omega)) (by rw [hH.lenA]; omega)) ?_
  refine ⟨by simp, hmin, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩, by simp⟩
  have : y ≠ "hp_v" := fun e => hy (by simp [e])
  simp [this]

/-- **Push or decrease** with the vertex in `hp_x`. -/
theorem runs_pushOrDecX (hL : LessOK ops lessS KeyRep key N Cl lwr lvr) {st : State V} {n v : ℕ}
    {key0 : ℕ → K} (hK : KeyRep st) (hn : st.w "hp_n" = n) (hnN : n ≤ N) (hlA : st.wlen "hp_A" = N)
    (hlP : st.wlen "hp_P" = N) (hpos : PosOK N (st.wa "hp_A") (st.wa "hp_P") n)
    (hH0 : HeapOK key0 (st.wa "hp_A") n) (hx : st.w "hp_x" = v) (hvN : v < N)
    (hk : ∀ u, u ≠ v → key u = key0 u) (hkv : v ∈ T (st.wa "hp_A") n → key v ≤ key0 v)
    (hcap : 2 * N + 3 < st.cap) :
    Runs ops (pushOrDecX lessS) st (fun r => ∃ n', HeapRep KeyRep key N r n' ∧
      T (r.wa "hp_A") n' = insert v (T (st.wa "hp_A") n) ∧ r.w "hp_v" = v ∧
      Unchanged st r ["hp_A", "hp_P"] [] (hpRegs ++ lwr) lvr ∧
      r.cost ≤ st.cost + (Cl + 12) * (Nat.log 2 (n + 1) + 1) + 9) := by
  unfold pushOrDecX
  apply runs_seq
  refine runs_wset rfl ?_
  refine (runs_pushOrDec hL (n := n) (v := v) (key0 := key0)
    (hL.frame st _ hK (unch_charge' (unch_setW' (Unchanged.refl st _ _ _ _) (by simp [hpRegs]) _) 1) (by (try simp) <;> omega))
    (by simp [hn]) hnN (by simp [hlA]) (by simp [hlP]) (by simpa using hpos) (by simpa using hH0)
    (by simp [hx]) hvN hk (by simpa using hkv) (by simp; omega)).mono ?_
  rintro r ⟨n', hR, hT, hrv, hunch, hcost⟩
  refine ⟨n', hR, by simpa using hT, hrv, Unchanged.chain
    (unch_charge' (unch_setW' (Unchanged.refl st _ _ _ _) (by simp [hpRegs]) _) 1) hunch
    (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _) (List.Subset.refl _), ?_⟩
  simp at hcost; omega

end Ops

end Frontier.CHD.IHeap
