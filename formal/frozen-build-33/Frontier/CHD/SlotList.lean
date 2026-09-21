import Frontier.RAMRep

/-!
# Frontier.CHD.SlotList — singly linked slot lists in a RAM word array (owner agent-09, B-L2, NON-GATE)

`Seg st nxt E a L b`: starting at slot `a` and following the word array `nxt`, the slots visited
are `L` (each `< E` and inside the array), arriving at `b`.  A complete list is `Seg … a L E`
(`E` = end marker, e.g. `gM`).  Used for the live out-lists (`gHd` / `gNxt`) of FindPivots-HD:
FH.9 unlinks a slot in `O(1)` through the predecessor cell.
-/

namespace Frontier.RAM

variable {V : Type}

/-- Linked-list segment from `a` visiting `L`, arriving at `b`. -/
inductive Seg (st : State V) (nxt : String) (E : ℕ) : ℕ → List ℕ → ℕ → Prop
  | nil (a : ℕ) : Seg st nxt E a [] a
  | cons (q : ℕ) (L : List ℕ) (b : ℕ) : q < E → q < st.wlen nxt →
      Seg st nxt E (st.wa nxt q) L b → Seg st nxt E q (q :: L) b

namespace Seg

variable {st st' : State V} {nxt : String} {E : ℕ}

theorem append {a b c : ℕ} {L₁ L₂ : List ℕ} (h₁ : Seg st nxt E a L₁ b) (h₂ : Seg st nxt E b L₂ c) :
    Seg st nxt E a (L₁ ++ L₂) c := by
  induction h₁ with
  | nil => simpa using h₂
  | cons q L b' hq hl _ ih => exact .cons q (L ++ L₂) c hq hl (ih h₂)

theorem split {a c : ℕ} {L₁ L₂ : List ℕ} (h : Seg st nxt E a (L₁ ++ L₂) c) :
    ∃ b, Seg st nxt E a L₁ b ∧ Seg st nxt E b L₂ c := by
  induction L₁ generalizing a with
  | nil => exact ⟨a, .nil a, by simpa using h⟩
  | cons q L ih =>
    cases h with
    | cons _ _ _ hq hl h' =>
      obtain ⟨b, h1, h2⟩ := ih h'
      exact ⟨b, .cons q L b hq hl h1, h2⟩

theorem head {a b q : ℕ} {L : List ℕ} (h : Seg st nxt E a (q :: L) b) : a = q := by
  cases h; rfl

theorem cons_inv {a b q : ℕ} {L : List ℕ} (h : Seg st nxt E a (q :: L) b) :
    a = q ∧ q < E ∧ q < st.wlen nxt ∧ Seg st nxt E (st.wa nxt q) L b := by
  cases h with
  | cons _ _ _ hq hl h' => exact ⟨rfl, hq, hl, h'⟩

theorem nil_inv {a b : ℕ} (h : Seg st nxt E a [] b) : a = b := by
  cases h; rfl

theorem snoc_iff {a b q : ℕ} {L : List ℕ} :
    Seg st nxt E a (L ++ [q]) b ↔
      Seg st nxt E a L q ∧ q < E ∧ q < st.wlen nxt ∧ b = st.wa nxt q := by
  constructor
  · intro h
    obtain ⟨c, h1, h2⟩ := split h
    obtain ⟨rfl, hq, hl, h3⟩ := cons_inv h2
    exact ⟨h1, hq, hl, (nil_inv h3).symm⟩
  · rintro ⟨h1, hq, hl, rfl⟩
    exact append h1 (.cons q [] _ hq hl (.nil _))

/-- Every visited slot is below the end marker. -/
theorem lt_of_mem {a b : ℕ} {L : List ℕ} (h : Seg st nxt E a L b) {q : ℕ} (hq : q ∈ L) : q < E := by
  induction h with
  | nil => simp at hq
  | cons q' L b' hq' _ _ ih =>
    rcases List.mem_cons.mp hq with rfl | h
    · exact hq'
    · exact ih h

/-- A complete list starting below the end marker is nonempty. -/
theorem ne_nil_of_lt {a : ℕ} {L : List ℕ} (h : Seg st nxt E a L E) (ha : a < E) : L ≠ [] := by
  rintro rfl
  have := nil_inv h
  omega

/-- A complete list starting at the end marker is empty. -/
theorem eq_nil_of_end {L : List ℕ} (h : Seg st nxt E E L E) : L = [] := by
  cases h with
  | nil => rfl
  | cons _ _ _ hq _ _ => omega

/-- Segments only depend on the `nxt` cells they visit (and the array length). -/
theorem congr {a b : ℕ} {L : List ℕ} (h : Seg st nxt E a L b)
    (hc : ∀ q ∈ L, st'.wa nxt q = st.wa nxt q) (hl : st'.wlen nxt = st.wlen nxt) :
    Seg st' nxt E a L b := by
  induction h with
  | nil => exact .nil _
  | cons q L b' hq hql _ ih =>
    refine .cons q L b' hq (hl ▸ hql) ?_
    rw [hc q List.mem_cons_self]
    exact ih (fun q' hq' => hc q' (List.mem_cons_of_mem _ hq'))

/-- `congr` with a rewritten start point. -/
theorem congr_start {a a' b : ℕ} {L : List ℕ} (h : Seg st nxt E a L b) (ha : a' = a)
    (hc : ∀ q ∈ L, st'.wa nxt q = st.wa nxt q) (hl : st'.wlen nxt = st.wlen nxt) :
    Seg st' nxt E a' L b := ha ▸ congr h hc hl

/-- Segments survive any update that keeps the `nxt` array. -/
theorem of_eq {a b : ℕ} {L : List ℕ} (h : Seg st nxt E a L b)
    (hc : st'.wa nxt = st.wa nxt) (hl : st'.wlen nxt = st.wlen nxt) : Seg st' nxt E a L b :=
  congr h (fun q _ => by rw [hc]) hl

/-- A store into `nxt` outside the visited slots keeps the segment. -/
theorem storeW_out {a b j x : ℕ} {L : List ℕ} (h : Seg st nxt E a L b) (hj : j ∉ L) :
    Seg (st.storeW nxt j x) nxt E a L b := by
  refine congr h (fun q hq => ?_) rfl
  have : q ≠ j := fun h' => hj (h' ▸ hq)
  simp [State.storeW, this]

end Seg

end Frontier.RAM
