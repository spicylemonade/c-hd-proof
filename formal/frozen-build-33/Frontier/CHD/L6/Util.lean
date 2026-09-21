import Frontier.RAMRep
import Frontier.RAMWP

/-! # L6 utilities (agent-10, scratch): frame lemmas for single updates, extra `simp` lemmas -/

namespace Frontier.RAM

variable {V : Type} {ops : VOps V}

@[simp] theorem evalW_div' (s : State V) (a b : WExpr) :
    evalW s (.div a b) = (evalW s a).bind (fun x => (evalW s b).bind
      (fun y => if y = 0 then none else some (x / y))) := rfl

@[simp] theorem realOps_zero : realOps.zero = (0 : NNReal) := rfl
@[simp] theorem realOps_le (a b : NNReal) : realOps.le a b = decide (a ≤ b) := rfl
@[simp] theorem realOps_add (a b : NNReal) : realOps.add a b = a + b := rfl

@[simp] theorem evalW_var' (s : State V) (x : String) : evalW s (.var x) = some (s.w x) := rfl

theorem Unchanged.allocW' {st : State V} {wa va wr vr : List String} {a : String} (ha : a ∈ wa)
    (k : ℕ) : Unchanged st (st.allocW a k) wa va wr vr := by
  refine ⟨fun b hb => ?_, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  have : b ≠ a := fun h => hb (h ▸ ha)
  simp [State.allocW, this]

theorem Unchanged.allocV' {st : State V} {wa va wr vr : List String} {a : String} (ha : a ∈ va)
    (k : ℕ) (z : V) : Unchanged st (st.allocV a k z) wa va wr vr := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun b hb => ?_, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
  have : b ≠ a := fun h => hb (h ▸ ha)
  simp [State.allocV, this]

theorem Unchanged.setW' {st : State V} {wa va wr vr : List String} {x : String} (hx : x ∈ wr)
    (a : ℕ) : Unchanged st (st.setW x a) wa va wr vr := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun y hy => ?_, fun _ _ => rfl, rfl, rfl⟩
  have : y ≠ x := fun h => hy (h ▸ hx)
  simp [State.setW, this]

theorem Unchanged.setV' {st : State V} {wa va wr vr : List String} {x : String} (hx : x ∈ vr)
    (a : V) : Unchanged st (st.setV x a) wa va wr vr := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun y hy => ?_, rfl, rfl⟩
  have : y ≠ x := fun h => hy (h ▸ hx)
  simp [State.setV, this]

theorem Unchanged.storeW' {st : State V} {wa va wr vr : List String} {a : String} (ha : a ∈ wa)
    (j x : ℕ) : Unchanged st (st.storeW a j x) wa va wr vr := by
  refine ⟨fun b hb => ⟨funext fun i => ?_, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl,
    fun _ _ => rfl, rfl, rfl⟩
  have : b ≠ a := fun h => hb (h ▸ ha)
  simp [State.storeW, this]

theorem Unchanged.storeV' {st : State V} {wa va wr vr : List String} {a : String} (ha : a ∈ va)
    (j : ℕ) (x : V) : Unchanged st (st.storeV a j x) wa va wr vr := by
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun b hb => ⟨funext fun i => ?_, rfl⟩, fun _ _ => rfl,
    fun _ _ => rfl, rfl, rfl⟩
  have : b ≠ a := fun h => hb (h ▸ ha)
  simp [State.storeV, this]

/-- Registers written, all arrays kept: the frame of straight-line register code. -/
theorem Unchanged.regs {st st' : State V} {wa va wr vr : List String}
    (hwa : st'.wa = st.wa) (hwl : st'.wlen = st.wlen) (hva : st'.va = st.va)
    (hvl : st'.vlen = st.vlen) (hw : ∀ x, x ∉ wr → st'.w x = st.w x)
    (hv : ∀ x, x ∉ vr → st'.v x = st.v x) (hc : st'.cap = st.cap) (hp : st'.procs = st.procs) :
    Unchanged st st' wa va wr vr :=
  ⟨fun a _ => ⟨by rw [hwa], by rw [hwl]⟩, fun a _ => ⟨by rw [hva], by rw [hvl]⟩, hw, hv, hc, hp⟩

/-! ### `simp` normal forms for frames and segments across primitive updates -/

section SimpFrames

variable {st t : State V} {wa va wr vr : List String}

@[simp] theorem unchanged_self_iff : Unchanged st st wa va wr vr ↔ True :=
  ⟨fun _ => trivial, fun _ => Unchanged.refl _ _ _ _ _⟩

@[simp] theorem unchanged_charge_iff (k : ℕ) :
    Unchanged st (t.charge k) wa va wr vr ↔ Unchanged st t wa va wr vr :=
  ⟨fun h => ⟨h.warr, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩,
   fun h => ⟨h.warr, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩⟩

@[simp] theorem unchanged_enter_iff :
    Unchanged st t.enter wa va wr vr ↔ Unchanged st t wa va wr vr :=
  ⟨fun h => ⟨h.warr, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩,
   fun h => ⟨h.warr, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩⟩

@[simp] theorem unchanged_setW_iff {x : String} (hx : x ∈ wr) (a : ℕ) :
    Unchanged st (t.setW x a) wa va wr vr ↔ Unchanged st t wa va wr vr := by
  constructor
  · intro h
    refine ⟨h.warr, h.varr, fun y hy => ?_, h.vreg, h.cap, h.procs⟩
    have hne : y ≠ x := fun e => hy (e ▸ hx)
    have := h.wreg y hy
    simpa [State.setW, hne] using this
  · intro h; exact h.trans (Unchanged.setW' hx a)

@[simp] theorem unchanged_setV_iff {x : String} (hx : x ∈ vr) (a : V) :
    Unchanged st (t.setV x a) wa va wr vr ↔ Unchanged st t wa va wr vr := by
  constructor
  · intro h
    refine ⟨h.warr, h.varr, h.wreg, fun y hy => ?_, h.cap, h.procs⟩
    have hne : y ≠ x := fun e => hy (e ▸ hx)
    have := h.vreg y hy
    simpa [State.setV, hne] using this
  · intro h; exact h.trans (Unchanged.setV' hx a)

@[simp] theorem unchanged_storeW_iff {a : String} (ha : a ∈ wa) (j x : ℕ) :
    Unchanged st (t.storeW a j x) wa va wr vr ↔ Unchanged st t wa va wr vr := by
  constructor
  · intro h
    refine ⟨fun b hb => ?_, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩
    have hne : b ≠ a := fun e => hb (e ▸ ha)
    have := h.warr b hb
    refine ⟨funext fun i => ?_, ?_⟩
    · have h1 := congrFun this.1 i
      simpa [State.storeW, hne] using h1
    · simpa [State.storeW] using this.2
  · intro h; exact h.trans (Unchanged.storeW' ha j x)

@[simp] theorem unchanged_storeV_iff {a : String} (ha : a ∈ va) (j : ℕ) (x : V) :
    Unchanged st (t.storeV a j x) wa va wr vr ↔ Unchanged st t wa va wr vr := by
  constructor
  · intro h
    refine ⟨h.warr, fun b hb => ?_, h.wreg, h.vreg, h.cap, h.procs⟩
    have hne : b ≠ a := fun e => hb (e ▸ ha)
    have := h.varr b hb
    refine ⟨funext fun i => ?_, ?_⟩
    · have h1 := congrFun this.1 i
      simpa [State.storeV, hne] using h1
    · simpa [State.storeV] using this.2
  · intro h; exact h.trans (Unchanged.storeV' ha j x)

@[simp] theorem unchanged_allocW_iff {a : String} (ha : a ∈ wa) (k : ℕ) :
    Unchanged st (t.allocW a k) wa va wr vr ↔ Unchanged st t wa va wr vr := by
  constructor
  · intro h
    refine ⟨fun b hb => ?_, h.varr, h.wreg, h.vreg, h.cap, h.procs⟩
    have hne : b ≠ a := fun e => hb (e ▸ ha)
    have := h.warr b hb
    simpa [State.allocW, hne] using this
  · intro h; exact h.trans (Unchanged.allocW' ha k)

@[simp] theorem unchanged_allocV_iff {a : String} (ha : a ∈ va) (k : ℕ) (z : V) :
    Unchanged st (t.allocV a k z) wa va wr vr ↔ Unchanged st t wa va wr vr := by
  constructor
  · intro h
    refine ⟨h.warr, fun b hb => ?_, h.wreg, h.vreg, h.cap, h.procs⟩
    have hne : b ≠ a := fun e => hb (e ▸ ha)
    have := h.varr b hb
    simpa [State.allocV, hne] using this
  · intro h; exact h.trans (Unchanged.allocV' ha k z)

variable {arr : String} {b n : ℕ} {f : ℕ → ℕ} {g : ℕ → V}

@[simp] theorem wseg_charge_iff (k : ℕ) : WSeg (t.charge k) arr b n f ↔ WSeg t arr b n f := Iff.rfl
@[simp] theorem wseg_enter_iff : WSeg t.enter arr b n f ↔ WSeg t arr b n f := Iff.rfl
@[simp] theorem wseg_setW_iff (x : String) (a : ℕ) : WSeg (t.setW x a) arr b n f ↔ WSeg t arr b n f :=
  Iff.rfl
@[simp] theorem wseg_setV_iff (x : String) (a : V) : WSeg (t.setV x a) arr b n f ↔ WSeg t arr b n f :=
  Iff.rfl
@[simp] theorem wseg_storeV_iff (a : String) (j : ℕ) (x : V) :
    WSeg (t.storeV a j x) arr b n f ↔ WSeg t arr b n f := Iff.rfl
@[simp] theorem wseg_allocV_iff (a : String) (k : ℕ) (z : V) :
    WSeg (t.allocV a k z) arr b n f ↔ WSeg t arr b n f := Iff.rfl
@[simp] theorem wseg_storeW_ne_iff {a : String} (hne : a ≠ arr) (j x : ℕ) :
    WSeg (t.storeW a j x) arr b n f ↔ WSeg t arr b n f := by
  unfold WSeg; simp [State.storeW, Ne.symm hne]
@[simp] theorem wseg_allocW_ne_iff {a : String} (hne : a ≠ arr) (k : ℕ) :
    WSeg (t.allocW a k) arr b n f ↔ WSeg t arr b n f := by
  unfold WSeg; simp [State.allocW, Ne.symm hne]

@[simp] theorem vseg_charge_iff (k : ℕ) : VSeg (t.charge k) arr b n g ↔ VSeg t arr b n g := Iff.rfl
@[simp] theorem vseg_enter_iff : VSeg t.enter arr b n g ↔ VSeg t arr b n g := Iff.rfl
@[simp] theorem vseg_setW_iff (x : String) (a : ℕ) : VSeg (t.setW x a) arr b n g ↔ VSeg t arr b n g :=
  Iff.rfl
@[simp] theorem vseg_setV_iff (x : String) (a : V) : VSeg (t.setV x a) arr b n g ↔ VSeg t arr b n g :=
  Iff.rfl
@[simp] theorem vseg_storeW_iff (a : String) (j x : ℕ) :
    VSeg (t.storeW a j x) arr b n g ↔ VSeg t arr b n g := Iff.rfl
@[simp] theorem vseg_allocW_iff (a : String) (k : ℕ) :
    VSeg (t.allocW a k) arr b n g ↔ VSeg t arr b n g := Iff.rfl
@[simp] theorem vseg_storeV_ne_iff {a : String} (hne : a ≠ arr) (j : ℕ) (x : V) :
    VSeg (t.storeV a j x) arr b n g ↔ VSeg t arr b n g := by
  unfold VSeg; simp [State.storeV, Ne.symm hne]
@[simp] theorem vseg_allocV_ne_iff {a : String} (hne : a ≠ arr) (k : ℕ) (z : V) :
    VSeg (t.allocV a k z) arr b n g ↔ VSeg t arr b n g := by
  unfold VSeg; simp [State.allocV, Ne.symm hne]

end SimpFrames

end Frontier.RAM
