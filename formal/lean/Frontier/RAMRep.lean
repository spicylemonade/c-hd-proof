import Frontier.RAMLogic

/-!
# Frontier.RAMRep — representation predicates: RAM array segments ↔ Layer-A arrays

Owner: agent-08 (Layer B).  NON-GATE infrastructure.

`WSeg st arr b n f` : the word-array segment `arr[b], …, arr[b + n - 1]` holds `f 0, …, f (n-1)`
(and lies inside the allocated array); `VSeg` is the value-array analogue.  Frame lemmas state
which machine updates preserve a segment, and how a store inside it updates the represented
function (`Function.update`).  Layer-A arrays over `Fin n` are represented at base `0` via
`finExt`.  These are the building blocks of the `Rep` predicates of `Frontier.Refine`.

Per-call data of recursive procedures (BMSSP) is laid out in per-LEVEL static regions: at most one
call per level is active at a time, so a level-indexed base offset replaces a general stack.
-/

namespace Frontier.RAM

variable {V : Type}

/-- The word-array segment `[b, b + n)` of `arr` holds `f 0, …, f (n - 1)`. -/
def WSeg (st : State V) (arr : String) (b n : ℕ) (f : ℕ → ℕ) : Prop :=
  b + n ≤ st.wlen arr ∧ ∀ i < n, st.wa arr (b + i) = f i

/-- The value-array segment `[b, b + n)` of `arr` holds `f 0, …, f (n - 1)`. -/
def VSeg (st : State V) (arr : String) (b n : ℕ) (f : ℕ → V) : Prop :=
  b + n ≤ st.vlen arr ∧ ∀ i < n, st.va arr (b + i) = f i

/-- Extend a `Fin n`-indexed array to `ℕ` (default outside the range). -/
def finExt {α : Type} {n : ℕ} (f : Fin n → α) (dflt : α) : ℕ → α :=
  fun i => if h : i < n then f ⟨i, h⟩ else dflt

@[simp] theorem finExt_apply {α : Type} {n : ℕ} (f : Fin n → α) (dflt : α) (i : Fin n) :
    finExt f dflt i = f i := by simp [finExt, i.isLt]

section Frame

variable {st : State V} {arr : String} {b n : ℕ} {f : ℕ → ℕ} {g : ℕ → V}

/-! ### Word segments -/

theorem WSeg.charge (h : WSeg st arr b n f) (k : ℕ) : WSeg (st.charge k) arr b n f := h

theorem WSeg.enter (h : WSeg st arr b n f) : WSeg st.enter arr b n f := h

theorem WSeg.setW (h : WSeg st arr b n f) (x : String) (a : ℕ) : WSeg (st.setW x a) arr b n f := h

theorem WSeg.setV (h : WSeg st arr b n f) (x : String) (a : V) : WSeg (st.setV x a) arr b n f := h

theorem WSeg.storeV (h : WSeg st arr b n f) (arr' : String) (j : ℕ) (a : V) :
    WSeg (st.storeV arr' j a) arr b n f := h

theorem WSeg.allocV (h : WSeg st arr b n f) (arr' : String) (k : ℕ) (z : V) :
    WSeg (st.allocV arr' k z) arr b n f := h

theorem WSeg.storeW_ne (h : WSeg st arr b n f) {arr' : String} (hne : arr' ≠ arr) (j a : ℕ) :
    WSeg (st.storeW arr' j a) arr b n f := by
  refine ⟨h.1, fun i hi => ?_⟩
  simp only [State.storeW]
  rw [if_neg (by rintro ⟨h1, -⟩; exact hne h1.symm)]
  exact h.2 i hi

theorem WSeg.storeW_out (h : WSeg st arr b n f) {j : ℕ} (hj : j < b ∨ b + n ≤ j) (a : ℕ) :
    WSeg (st.storeW arr j a) arr b n f := by
  refine ⟨h.1, fun i hi => ?_⟩
  simp only [State.storeW]
  rw [if_neg (by rintro ⟨-, h2⟩; omega)]
  exact h.2 i hi

theorem WSeg.storeW_in (h : WSeg st arr b n f) {j : ℕ} (hj₁ : b ≤ j) (hj₂ : j < b + n) (a : ℕ) :
    WSeg (st.storeW arr j a) arr b n (Function.update f (j - b) a) := by
  refine ⟨h.1, fun i hi => ?_⟩
  simp only [State.storeW, true_and]
  by_cases hij : b + i = j
  · rw [if_pos hij]
    have : i = j - b := by omega
    subst this
    simp
  · rw [if_neg hij]
    have : i ≠ j - b := by omega
    rw [Function.update_of_ne this]
    exact h.2 i hi

theorem WSeg.allocW_ne (h : WSeg st arr b n f) {arr' : String} (hne : arr' ≠ arr) (k : ℕ) :
    WSeg (st.allocW arr' k) arr b n f := by
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [State.allocW]; rw [if_neg (Ne.symm hne)]; exact h.1
  · simp only [State.allocW]; rw [if_neg (Ne.symm hne)]; exact h.2 i hi

theorem WSeg.of_allocW (st : State V) (arr : String) (k : ℕ) :
    WSeg (st.allocW arr k) arr 0 k (fun _ => 0) := by
  refine ⟨by simp [State.allocW], fun i _ => by simp [State.allocW]⟩

/-- Reading a represented word. -/
theorem WSeg.evalW_load (h : WSeg st arr b n f) {e : WExpr} {i : ℕ} (he : evalW st e = some (b + i))
    (hi : i < n) : evalW st (.load arr e) = some (f i) := by
  rw [evalW_load_of he (by have := h.1; omega), h.2 i hi]

/-! ### Value segments -/

theorem VSeg.charge (h : VSeg st arr b n g) (k : ℕ) : VSeg (st.charge k) arr b n g := h

theorem VSeg.enter (h : VSeg st arr b n g) : VSeg st.enter arr b n g := h

theorem VSeg.setW (h : VSeg st arr b n g) (x : String) (a : ℕ) : VSeg (st.setW x a) arr b n g := h

theorem VSeg.setV (h : VSeg st arr b n g) (x : String) (a : V) : VSeg (st.setV x a) arr b n g := h

theorem VSeg.storeW (h : VSeg st arr b n g) (arr' : String) (j a : ℕ) :
    VSeg (st.storeW arr' j a) arr b n g := h

theorem VSeg.allocW (h : VSeg st arr b n g) (arr' : String) (k : ℕ) :
    VSeg (st.allocW arr' k) arr b n g := h

theorem VSeg.storeV_ne (h : VSeg st arr b n g) {arr' : String} (hne : arr' ≠ arr) (j : ℕ) (a : V) :
    VSeg (st.storeV arr' j a) arr b n g := by
  refine ⟨h.1, fun i hi => ?_⟩
  simp only [State.storeV]
  rw [if_neg (by rintro ⟨h1, -⟩; exact hne h1.symm)]
  exact h.2 i hi

theorem VSeg.storeV_out (h : VSeg st arr b n g) {j : ℕ} (hj : j < b ∨ b + n ≤ j) (a : V) :
    VSeg (st.storeV arr j a) arr b n g := by
  refine ⟨h.1, fun i hi => ?_⟩
  simp only [State.storeV]
  rw [if_neg (by rintro ⟨-, h2⟩; omega)]
  exact h.2 i hi

theorem VSeg.storeV_in (h : VSeg st arr b n g) {j : ℕ} (hj₁ : b ≤ j) (hj₂ : j < b + n) (a : V) :
    VSeg (st.storeV arr j a) arr b n (Function.update g (j - b) a) := by
  refine ⟨h.1, fun i hi => ?_⟩
  simp only [State.storeV, true_and]
  by_cases hij : b + i = j
  · rw [if_pos hij]
    have : i = j - b := by omega
    subst this
    simp
  · rw [if_neg hij]
    have : i ≠ j - b := by omega
    rw [Function.update_of_ne this]
    exact h.2 i hi

theorem VSeg.allocV_ne (h : VSeg st arr b n g) {arr' : String} (hne : arr' ≠ arr) (k : ℕ) (z : V) :
    VSeg (st.allocV arr' k z) arr b n g := by
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [State.allocV]; rw [if_neg (Ne.symm hne)]; exact h.1
  · simp only [State.allocV]; rw [if_neg (Ne.symm hne)]; exact h.2 i hi

theorem VSeg.of_allocV (st : State V) (arr : String) (k : ℕ) (z : V) :
    VSeg (st.allocV arr k z) arr 0 k (fun _ => z) := by
  refine ⟨by simp [State.allocV], fun i _ => by simp [State.allocV]⟩

/-- Reading a represented value. -/
theorem VSeg.evalV_load (ops : VOps V) (h : VSeg st arr b n g) {e : WExpr} {i : ℕ}
    (he : evalW st e = some (b + i)) (hi : i < n) : evalV ops st (.load arr e) = some (g i) := by
  rw [evalV_load_of he (by have := h.1; omega), h.2 i hi]

end Frame

/-! ## Layer-A arrays over `Fin n` -/

/-- A word array `arr` (from index `0`) represents the Layer-A array `f : Fin n → ℕ`. -/
def WArr (st : State V) (arr : String) {n : ℕ} (f : Fin n → ℕ) : Prop :=
  WSeg st arr 0 n (finExt f 0)

/-- A value array `arr` (from index `0`) represents the Layer-A array `f : Fin n → V`. -/
def VArr (st : State V) (arr : String) {n : ℕ} (f : Fin n → V) (dflt : V) : Prop :=
  VSeg st arr 0 n (finExt f dflt)

theorem WArr.read {st : State V} {arr : String} {n : ℕ} {f : Fin n → ℕ} (h : WArr st arr f)
    (i : Fin n) : st.wa arr i = f i := by
  have := h.2 i i.isLt
  simpa using this

theorem WArr.storeW_self {st : State V} {arr : String} {n : ℕ} {f : Fin n → ℕ} (h : WArr st arr f)
    (i : Fin n) (a : ℕ) : WArr (st.storeW arr i a) arr (Function.update f i a) := by
  have h2 := WSeg.storeW_in (j := (i : ℕ)) h (Nat.zero_le _) (by simpa using i.isLt) a
  refine ⟨h2.1, fun j hj => ?_⟩
  rw [h2.2 j hj]
  simp only [finExt, Nat.sub_zero, hj, dite_true]
  by_cases hji : j = (i : ℕ)
  · subst hji; simp
  · rw [Function.update_of_ne hji, Function.update_of_ne (fun h => hji (congrArg Fin.val h))]
    simp [finExt, hj]

theorem VArr.read {st : State V} {arr : String} {n : ℕ} {f : Fin n → V} {dflt : V}
    (h : VArr st arr f dflt) (i : Fin n) : st.va arr i = f i := by
  have := h.2 i i.isLt
  simpa using this

theorem VArr.storeV_self {st : State V} {arr : String} {n : ℕ} {f : Fin n → V} {dflt : V}
    (h : VArr st arr f dflt) (i : Fin n) (a : V) :
    VArr (st.storeV arr i a) arr (Function.update f i a) dflt := by
  have h2 := VSeg.storeV_in (j := (i : ℕ)) h (Nat.zero_le _) (by simpa using i.isLt) a
  refine ⟨h2.1, fun j hj => ?_⟩
  rw [h2.2 j hj]
  simp only [finExt, Nat.sub_zero, hj, dite_true]
  by_cases hji : j = (i : ℕ)
  · subst hji; simp
  · rw [Function.update_of_ne hji, Function.update_of_ne (fun h => hji (congrArg Fin.val h))]
    simp [finExt, hj]


/-! ## Frame conditions for fragment specifications

Every Layer-B fragment spec states which arrays and registers it may write; everything else is
unchanged.  `Unchanged st st' wa va wr vr` : outside the word arrays `wa`, value arrays `va`,
word registers `wr` and value registers `vr`, the two states agree (contents and lengths), and the
word cap and procedure table are equal.  It is reflexive, transitive, monotone in the write sets,
and preserves every segment of an array outside the write sets. -/

/-- `st'` agrees with `st` outside the given write sets. -/
structure Unchanged (st st' : State V) (wa va wr vr : List String) : Prop where
  warr : ∀ a, a ∉ wa → st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a
  varr : ∀ a, a ∉ va → st'.va a = st.va a ∧ st'.vlen a = st.vlen a
  wreg : ∀ x, x ∉ wr → st'.w x = st.w x
  vreg : ∀ x, x ∉ vr → st'.v x = st.v x
  cap : st'.cap = st.cap
  procs : st'.procs = st.procs

theorem Unchanged.refl (st : State V) (wa va wr vr : List String) :
    Unchanged st st wa va wr vr :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Unchanged.trans {st₁ st₂ st₃ : State V} {wa va wr vr : List String}
    (h₁ : Unchanged st₁ st₂ wa va wr vr) (h₂ : Unchanged st₂ st₃ wa va wr vr) :
    Unchanged st₁ st₃ wa va wr vr where
  warr a ha := ⟨(h₂.warr a ha).1.trans (h₁.warr a ha).1, (h₂.warr a ha).2.trans (h₁.warr a ha).2⟩
  varr a ha := ⟨(h₂.varr a ha).1.trans (h₁.varr a ha).1, (h₂.varr a ha).2.trans (h₁.varr a ha).2⟩
  wreg x hx := (h₂.wreg x hx).trans (h₁.wreg x hx)
  vreg x hx := (h₂.vreg x hx).trans (h₁.vreg x hx)
  cap := h₂.cap.trans h₁.cap
  procs := h₂.procs.trans h₁.procs

theorem Unchanged.mono {st st' : State V} {wa va wr vr wa' va' wr' vr' : List String}
    (h : Unchanged st st' wa va wr vr) (hwa : wa ⊆ wa') (hva : va ⊆ va') (hwr : wr ⊆ wr')
    (hvr : vr ⊆ vr') : Unchanged st st' wa' va' wr' vr' where
  warr a ha := h.warr a (fun h' => ha (hwa h'))
  varr a ha := h.varr a (fun h' => ha (hva h'))
  wreg x hx := h.wreg x (fun h' => hx (hwr h'))
  vreg x hx := h.vreg x (fun h' => hx (hvr h'))
  cap := h.cap
  procs := h.procs

theorem Unchanged.charge (st : State V) (k : ℕ) (wa va wr vr : List String) :
    Unchanged st (st.charge k) wa va wr vr :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- A segment of a word array outside the write set survives. -/
theorem WSeg.of_unchanged {st st' : State V} {wa va wr vr : List String} {arr : String}
    {b n : ℕ} {f : ℕ → ℕ} (h : WSeg st arr b n f) (hu : Unchanged st st' wa va wr vr)
    (ha : arr ∉ wa) : WSeg st' arr b n f := by
  obtain ⟨h1, h2⟩ := hu.warr arr ha
  refine ⟨by rw [h2]; exact h.1, fun i hi => ?_⟩
  rw [h1]; exact h.2 i hi

/-- A segment of a value array outside the write set survives. -/
theorem VSeg.of_unchanged {st st' : State V} {wa va wr vr : List String} {arr : String}
    {b n : ℕ} {g : ℕ → V} (h : VSeg st arr b n g) (hu : Unchanged st st' wa va wr vr)
    (ha : arr ∉ va) : VSeg st' arr b n g := by
  obtain ⟨h1, h2⟩ := hu.varr arr ha
  refine ⟨by rw [h2]; exact h.1, fun i hi => ?_⟩
  rw [h1]; exact h.2 i hi

end Frontier.RAM
