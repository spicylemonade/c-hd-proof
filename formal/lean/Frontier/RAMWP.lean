import Frontier.RAMLogic

/-!
# RAMWP — a weakest-precondition VCG for the `Frontier.RAM` machine (agent-02, Layer B tooling)

NON-GATE infrastructure.  `wp ops c Q s` is a verification condition that implies
`Runs ops c s Q` (`wp_sound`).  For loop-free code it is an explicit formula about the state that
`simp` can compute from the program text (expression evaluation, register/array updates and the
cost counter all reduce by `rfl`-lemmas below).  At a `while` loop `wp` simply *is* `Runs`, so a
loop is discharged separately with `RAM.runs_while` and plugged in.

Intended use in Layer B: a straight-line fragment `F` implementing a Layer-A step is verified by
`apply wp_sound; simp only [wp, <eval lemmas>, <state lemmas>]; <close arithmetic>`.
-/

namespace Frontier.RAM

variable {V : Type} (ops : VOps V)

/-- Weakest precondition (total correctness, cost visible through the state's `cost` field).
Loops are not unfolded: `wp` of a `while` is the `Runs` predicate itself. -/
def wp : Stmt → (State V → Prop) → State V → Prop
  | .skip, Q, s => Q (s.charge 1)
  | .wset x e, Q, s => match evalW s e with
      | some a => Q ((s.setW x a).charge 1)
      | none => False
  | .vset x e, Q, s => match evalV ops s e with
      | some a => Q ((s.setV x a).charge 1)
      | none => False
  | .vle x a b, Q, s => match evalV ops s a, evalV ops s b with
      | some p, some q => 1 < s.cap ∧ Q ((s.setW x (if ops.le p q then 1 else 0)).charge 1)
      | _, _ => False
  | .wstore arr i e, Q, s => match evalW s i, evalW s e with
      | some j, some a => j < s.wlen arr ∧ Q ((s.storeW arr j a).charge 1)
      | _, _ => False
  | .vstore arr i e, Q, s => match evalW s i, evalV ops s e with
      | some j, some a => j < s.vlen arr ∧ Q ((s.storeV arr j a).charge 1)
      | _, _ => False
  | .walloc arr e, Q, s => match evalW s e with
      | some k => Q ((s.allocW arr k).charge (k + 1))
      | none => False
  | .valloc arr e, Q, s => match evalW s e with
      | some k => Q ((s.allocV arr k ops.zero).charge (k + 1))
      | none => False
  | .seq a b, Q, s => wp a (wp b Q) s
  | .ite c a b, Q, s => match evalW s c with
      | some x => (x ≠ 0 → wp a Q (s.charge 1)) ∧ (x = 0 → wp b Q (s.charge 1))
      | none => False
  | .while c b, Q, s => Runs ops (.while c b) s Q
  | .call p, Q, s => Runs ops (.call p) s Q

variable {ops}

/-- Soundness of the VCG. -/
theorem wp_sound : ∀ (c : Stmt) (Q : State V → Prop) (s : State V), wp ops c Q s → Runs ops c s Q
  | .skip, _, _, h => runs_skip h
  | .wset x e, Q, s, h => by
      simp only [wp] at h
      split at h
      · next a he => exact runs_wset he h
      · exact h.elim
  | .vset x e, Q, s, h => by
      simp only [wp] at h
      split at h
      · next a he => exact runs_vset he h
      · exact h.elim
  | .vle x a b, Q, s, h => by
      simp only [wp] at h
      split at h
      · next p q ha hb => exact runs_vle ha hb h.1 h.2
      · exact h.elim
  | .wstore arr i e, Q, s, h => by
      simp only [wp] at h
      split at h
      · next j a hi he => exact runs_wstore hi he h.1 h.2
      · exact h.elim
  | .vstore arr i e, Q, s, h => by
      simp only [wp] at h
      split at h
      · next j a hi he => exact runs_vstore hi he h.1 h.2
      · exact h.elim
  | .walloc arr e, Q, s, h => by
      simp only [wp] at h
      split at h
      · next k he => exact runs_walloc he h
      · exact h.elim
  | .valloc arr e, Q, s, h => by
      simp only [wp] at h
      split at h
      · next k he => exact runs_valloc he h
      · exact h.elim
  | .seq a b, Q, s, h =>
      runs_seq ((wp_sound a _ s h).mono (fun r hr => wp_sound b Q r hr))
  | .ite c a b, Q, s, h => by
      simp only [wp] at h
      split at h
      · next x hc =>
        by_cases hx : x = 0
        · subst hx; exact runs_ite_false hc (wp_sound b Q _ (h.2 rfl))
        · exact runs_ite_true hc hx (wp_sound a Q _ (h.1 hx))
      · exact h.elim
  | .while _ _, _, _, h => h
  | .call _, _, _, h => h

/-- Monotonicity of `wp` in the postcondition (for composing fragment specs stated in wp form). -/
theorem wp_mono : ∀ (c : Stmt) {Q Q' : State V → Prop} (_ : ∀ r, Q r → Q' r) (s : State V),
    wp ops c Q s → wp ops c Q' s
  | .skip, _, _, hQ, _, h => hQ _ h
  | .wset x e, _, _, hQ, s, h => by
      simp only [wp] at h ⊢; split at h <;> simp_all
  | .vset x e, _, _, hQ, s, h => by
      simp only [wp] at h ⊢; split at h <;> simp_all
  | .vle x a b, _, _, hQ, s, h => by
      simp only [wp] at h ⊢; split at h <;> simp_all
  | .wstore arr i e, _, _, hQ, s, h => by
      simp only [wp] at h ⊢; split at h <;> simp_all
  | .vstore arr i e, _, _, hQ, s, h => by
      simp only [wp] at h ⊢; split at h <;> simp_all
  | .walloc arr e, _, _, hQ, s, h => by
      simp only [wp] at h ⊢; split at h <;> simp_all
  | .valloc arr e, _, _, hQ, s, h => by
      simp only [wp] at h ⊢; split at h <;> simp_all
  | .seq a b, _, _, hQ, s, h => wp_mono a (fun r hr => wp_mono b hQ r hr) s h
  | .ite c a b, _, _, hQ, s, h => by
      simp only [wp] at h ⊢
      split at h
      · next x hc =>
        exact ⟨fun hx => wp_mono a hQ _ (h.1 hx), fun hx => wp_mono b hQ _ (h.2 hx)⟩
      · exact h.elim
  | .while _ _, _, _, hQ, _, h => h.mono hQ
  | .call _, _, _, hQ, _, h => h.mono hQ

/-! ### State projections (all `rfl`; tagged `simp` so VCs normalize) -/

namespace State

variable (s : State V)

@[simp] theorem charge_w (k : ℕ) : (s.charge k).w = s.w := rfl
@[simp] theorem charge_v (k : ℕ) : (s.charge k).v = s.v := rfl
@[simp] theorem charge_wa (k : ℕ) : (s.charge k).wa = s.wa := rfl
@[simp] theorem charge_va (k : ℕ) : (s.charge k).va = s.va := rfl
@[simp] theorem charge_wlen (k : ℕ) : (s.charge k).wlen = s.wlen := rfl
@[simp] theorem charge_vlen (k : ℕ) : (s.charge k).vlen = s.vlen := rfl
@[simp] theorem charge_cap (k : ℕ) : (s.charge k).cap = s.cap := rfl
@[simp] theorem charge_cost (k : ℕ) : (s.charge k).cost = s.cost + k := rfl
@[simp] theorem charge_space (k : ℕ) : (s.charge k).space = s.space := rfl
@[simp] theorem charge_procs (k : ℕ) : (s.charge k).procs = s.procs := rfl
@[simp] theorem setW_procs (x : String) (a : ℕ) : (s.setW x a).procs = s.procs := rfl
@[simp] theorem setV_procs (x : String) (a : V) : (s.setV x a).procs = s.procs := rfl
@[simp] theorem storeW_procs (arr : String) (i a : ℕ) : (s.storeW arr i a).procs = s.procs := rfl
@[simp] theorem storeV_procs (arr : String) (i : ℕ) (a : V) :
    (s.storeV arr i a).procs = s.procs := rfl
@[simp] theorem allocW_procs (arr : String) (k : ℕ) : (s.allocW arr k).procs = s.procs := rfl
@[simp] theorem allocV_procs (arr : String) (k : ℕ) (z : V) :
    (s.allocV arr k z).procs = s.procs := rfl
@[simp] theorem enter_w : s.enter.w = s.w := rfl
@[simp] theorem enter_v : s.enter.v = s.v := rfl
@[simp] theorem enter_wa : s.enter.wa = s.wa := rfl
@[simp] theorem enter_va : s.enter.va = s.va := rfl
@[simp] theorem enter_wlen : s.enter.wlen = s.wlen := rfl
@[simp] theorem enter_vlen : s.enter.vlen = s.vlen := rfl
@[simp] theorem enter_cap : s.enter.cap = s.cap := rfl
@[simp] theorem enter_cost : s.enter.cost = s.cost + 1 := rfl
@[simp] theorem enter_procs : s.enter.procs = s.procs := rfl

@[simp] theorem setW_w (x : String) (a : ℕ) (y : String) :
    (s.setW x a).w y = if y = x then a else s.w y := rfl
@[simp] theorem setW_v (x : String) (a : ℕ) : (s.setW x a).v = s.v := rfl
@[simp] theorem setW_wa (x : String) (a : ℕ) : (s.setW x a).wa = s.wa := rfl
@[simp] theorem setW_va (x : String) (a : ℕ) : (s.setW x a).va = s.va := rfl
@[simp] theorem setW_wlen (x : String) (a : ℕ) : (s.setW x a).wlen = s.wlen := rfl
@[simp] theorem setW_vlen (x : String) (a : ℕ) : (s.setW x a).vlen = s.vlen := rfl
@[simp] theorem setW_cap (x : String) (a : ℕ) : (s.setW x a).cap = s.cap := rfl
@[simp] theorem setW_cost (x : String) (a : ℕ) : (s.setW x a).cost = s.cost := rfl

@[simp] theorem setV_w (x : String) (a : V) : (s.setV x a).w = s.w := rfl
@[simp] theorem setV_v (x : String) (a : V) (y : String) :
    (s.setV x a).v y = if y = x then a else s.v y := rfl
@[simp] theorem setV_wa (x : String) (a : V) : (s.setV x a).wa = s.wa := rfl
@[simp] theorem setV_va (x : String) (a : V) : (s.setV x a).va = s.va := rfl
@[simp] theorem setV_wlen (x : String) (a : V) : (s.setV x a).wlen = s.wlen := rfl
@[simp] theorem setV_vlen (x : String) (a : V) : (s.setV x a).vlen = s.vlen := rfl
@[simp] theorem setV_cap (x : String) (a : V) : (s.setV x a).cap = s.cap := rfl
@[simp] theorem setV_cost (x : String) (a : V) : (s.setV x a).cost = s.cost := rfl

@[simp] theorem storeW_w (arr : String) (i a : ℕ) : (s.storeW arr i a).w = s.w := rfl
@[simp] theorem storeW_v (arr : String) (i a : ℕ) : (s.storeW arr i a).v = s.v := rfl
@[simp] theorem storeW_wa (arr : String) (i a : ℕ) (b : String) (j : ℕ) :
    (s.storeW arr i a).wa b j = if b = arr ∧ j = i then a else s.wa b j := rfl
@[simp] theorem storeW_va (arr : String) (i a : ℕ) : (s.storeW arr i a).va = s.va := rfl
@[simp] theorem storeW_wlen (arr : String) (i a : ℕ) : (s.storeW arr i a).wlen = s.wlen := rfl
@[simp] theorem storeW_vlen (arr : String) (i a : ℕ) : (s.storeW arr i a).vlen = s.vlen := rfl
@[simp] theorem storeW_cap (arr : String) (i a : ℕ) : (s.storeW arr i a).cap = s.cap := rfl
@[simp] theorem storeW_cost (arr : String) (i a : ℕ) : (s.storeW arr i a).cost = s.cost := rfl

@[simp] theorem storeV_w (arr : String) (i : ℕ) (a : V) : (s.storeV arr i a).w = s.w := rfl
@[simp] theorem storeV_v (arr : String) (i : ℕ) (a : V) : (s.storeV arr i a).v = s.v := rfl
@[simp] theorem storeV_wa (arr : String) (i : ℕ) (a : V) : (s.storeV arr i a).wa = s.wa := rfl
@[simp] theorem storeV_va (arr : String) (i : ℕ) (a : V) (b : String) (j : ℕ) :
    (s.storeV arr i a).va b j = if b = arr ∧ j = i then a else s.va b j := rfl
@[simp] theorem storeV_wlen (arr : String) (i : ℕ) (a : V) :
    (s.storeV arr i a).wlen = s.wlen := rfl
@[simp] theorem storeV_vlen (arr : String) (i : ℕ) (a : V) :
    (s.storeV arr i a).vlen = s.vlen := rfl
@[simp] theorem storeV_cap (arr : String) (i : ℕ) (a : V) : (s.storeV arr i a).cap = s.cap := rfl
@[simp] theorem storeV_cost (arr : String) (i : ℕ) (a : V) :
    (s.storeV arr i a).cost = s.cost := rfl

@[simp] theorem allocW_w (arr : String) (k : ℕ) : (s.allocW arr k).w = s.w := rfl
@[simp] theorem allocW_v (arr : String) (k : ℕ) : (s.allocW arr k).v = s.v := rfl
@[simp] theorem allocW_wa (arr : String) (k : ℕ) (b : String) (j : ℕ) :
    (s.allocW arr k).wa b j = if b = arr then 0 else s.wa b j := rfl
@[simp] theorem allocW_va (arr : String) (k : ℕ) : (s.allocW arr k).va = s.va := rfl
@[simp] theorem allocW_wlen (arr : String) (k : ℕ) (b : String) :
    (s.allocW arr k).wlen b = if b = arr then k else s.wlen b := rfl
@[simp] theorem allocW_vlen (arr : String) (k : ℕ) : (s.allocW arr k).vlen = s.vlen := rfl
@[simp] theorem allocW_cap (arr : String) (k : ℕ) : (s.allocW arr k).cap = s.cap := rfl
@[simp] theorem allocW_cost (arr : String) (k : ℕ) : (s.allocW arr k).cost = s.cost := rfl

@[simp] theorem allocV_w (arr : String) (k : ℕ) (z : V) : (s.allocV arr k z).w = s.w := rfl
@[simp] theorem allocV_v (arr : String) (k : ℕ) (z : V) : (s.allocV arr k z).v = s.v := rfl
@[simp] theorem allocV_wa (arr : String) (k : ℕ) (z : V) : (s.allocV arr k z).wa = s.wa := rfl
@[simp] theorem allocV_va (arr : String) (k : ℕ) (z : V) (b : String) (j : ℕ) :
    (s.allocV arr k z).va b j = if b = arr then z else s.va b j := rfl
@[simp] theorem allocV_wlen (arr : String) (k : ℕ) (z : V) :
    (s.allocV arr k z).wlen = s.wlen := rfl
@[simp] theorem allocV_vlen (arr : String) (k : ℕ) (z : V) (b : String) :
    (s.allocV arr k z).vlen b = if b = arr then k else s.vlen b := rfl
@[simp] theorem allocV_cap (arr : String) (k : ℕ) (z : V) : (s.allocV arr k z).cap = s.cap := rfl
@[simp] theorem allocV_cost (arr : String) (k : ℕ) (z : V) :
    (s.allocV arr k z).cost = s.cost := rfl

end State

/-! ### Expression evaluation as `simp` lemmas -/

@[simp] theorem evalW_lit' (s : State V) (a : ℕ) : evalW s (.lit a) = fit s.cap a := rfl
@[simp] theorem evalW_add' (s : State V) (a b : WExpr) :
    evalW s (.add a b) = (evalW s a).bind (fun x => (evalW s b).bind (fun y => fit s.cap (x + y))) :=
  rfl
@[simp] theorem evalW_sub' (s : State V) (a b : WExpr) :
    evalW s (.sub a b) = (evalW s a).bind (fun x => (evalW s b).bind (fun y => some (x - y))) := rfl
@[simp] theorem evalW_mul' (s : State V) (a b : WExpr) :
    evalW s (.mul a b) = (evalW s a).bind (fun x => (evalW s b).bind (fun y => fit s.cap (x * y))) :=
  rfl
@[simp] theorem evalW_lt' (s : State V) (a b : WExpr) :
    evalW s (.lt a b) = (evalW s a).bind (fun x => (evalW s b).bind
      (fun y => fit s.cap (if x < y then 1 else 0))) := rfl
@[simp] theorem evalW_eq' (s : State V) (a b : WExpr) :
    evalW s (.eq a b) = (evalW s a).bind (fun x => (evalW s b).bind
      (fun y => fit s.cap (if x = y then 1 else 0))) := rfl
@[simp] theorem evalW_load' (s : State V) (arr : String) (i : WExpr) :
    evalW s (.load arr i) = (evalW s i).bind
      (fun j => if j < s.wlen arr then some (s.wa arr j) else none) := rfl
@[simp] theorem evalV_zero' (s : State V) : evalV ops s .zero = some ops.zero := rfl
@[simp] theorem evalV_var' (s : State V) (x : String) : evalV ops s (.var x) = some (s.v x) := rfl
@[simp] theorem evalV_add' (s : State V) (a b : VExpr) :
    evalV ops s (.add a b) = (evalV ops s a).bind (fun x => (evalV ops s b).bind
      (fun y => some (ops.add x y))) := rfl
@[simp] theorem evalV_load' (s : State V) (arr : String) (i : WExpr) :
    evalV ops s (.load arr i) = (evalW s i).bind
      (fun j => if j < s.vlen arr then some (s.va arr j) else none) := rfl

theorem fit_of_lt {cap a : ℕ} (h : a < cap) : fit cap a = some a := by simp [fit, h]

/-! ### Smoke test: a two-statement fragment verified by `simp` alone -/

example (s : State V) (hcap : 10 < s.cap) (hx : s.w "x" = 3) :
    Runs ops (.seq (.wset "y" (.add (.var "x") (.lit 1))) (.wset "z" (.add (.var "y") (.var "x"))))
      s (fun r => r.w "z" = 7 ∧ r.cost = s.cost + 2) := by
  apply wp_sound
  simp [wp, fit, hx, show 1 < s.cap by omega, show 4 < s.cap by omega, show 7 < s.cap by omega]

end Frontier.RAM
