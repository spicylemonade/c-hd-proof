import Frontier.RAMLogic

/-!
# ExecLen — allocation-free programs keep all array lengths (agent-02)

`noAlloc c` holds for statement texts without `walloc`, `valloc` and `call`.  Such a program never
changes `wlen`/`vlen` (`exec_len`, `Runs.len`).
-/

namespace Frontier.RAM

open Stmt

variable {V : Type} {ops : VOps V}

/-- The text allocates nothing and calls no procedure. -/
def noAlloc : Stmt → Bool
  | .walloc _ _ => false
  | .valloc _ _ => false
  | .call _ => false
  | .seq a b => noAlloc a && noAlloc b
  | .ite _ a b => noAlloc a && noAlloc b
  | .while _ b => noAlloc b
  | _ => true

theorem exec_len : ∀ (f : ℕ) (c : Stmt) (s r : State V), noAlloc c = true →
    exec ops f c s = some r → r.wlen = s.wlen ∧ r.vlen = s.vlen := by
  intro f
  induction f with
  | zero => intro c s r _ h; simp [exec] at h
  | succ f ih =>
    intro c s r hc h
    cases c with
    | skip =>
      simp only [exec, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
    | wset x e =>
      simp only [exec] at h
      cases he : evalW s e with
      | none => simp [he] at h
      | some a => simp [he] at h; subst h; exact ⟨rfl, rfl⟩
    | vset x e =>
      simp only [exec] at h
      cases he : evalV ops s e with
      | none => simp [he] at h
      | some a => simp [he] at h; subst h; exact ⟨rfl, rfl⟩
    | vle x a b =>
      simp only [exec] at h
      cases ha : evalV ops s a with
      | none => simp [ha] at h
      | some p =>
        cases hb : evalV ops s b with
        | none => simp [ha, hb] at h
        | some q =>
          cases hf : fit s.cap (if ops.le p q then 1 else 0) with
          | none => simp [ha, hb, hf] at h
          | some bit => simp [ha, hb, hf] at h; subst h; exact ⟨rfl, rfl⟩
    | wstore arr i e =>
      simp only [exec] at h
      cases hi : evalW s i with
      | none => simp [hi] at h
      | some j =>
        cases he : evalW s e with
        | none => simp [hi, he] at h
        | some a =>
          simp [hi, he] at h
          obtain ⟨-, h⟩ := h
          subst h; exact ⟨rfl, rfl⟩
    | vstore arr i e =>
      simp only [exec] at h
      cases hi : evalW s i with
      | none => simp [hi] at h
      | some j =>
        cases he : evalV ops s e with
        | none => simp [hi, he] at h
        | some a =>
          simp [hi, he] at h
          obtain ⟨-, h⟩ := h
          subst h; exact ⟨rfl, rfl⟩
    | walloc arr e => simp [noAlloc] at hc
    | valloc arr e => simp [noAlloc] at hc
    | call p => simp [noAlloc] at hc
    | seq a b =>
      simp only [noAlloc, Bool.and_eq_true] at hc
      rw [exec_seq] at h
      cases h1 : exec ops f a s with
      | none => simp [h1] at h
      | some s' =>
        simp only [h1, Option.bind_some] at h
        obtain ⟨e1, e2⟩ := ih a s s' hc.1 h1
        obtain ⟨e3, e4⟩ := ih b s' r hc.2 h
        exact ⟨e3.trans e1, e4.trans e2⟩
    | ite c a b =>
      simp only [noAlloc, Bool.and_eq_true] at hc
      rw [exec_ite] at h
      cases hx : evalW s c with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, Option.bind_some] at h
        split_ifs at h
        · exact ih a (s.charge 1) r hc.1 h
        · exact ih b (s.charge 1) r hc.2 h
    | «while» c b =>
      rw [exec_while] at h
      cases hx : evalW s c with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, Option.bind_some] at h
        split_ifs at h
        · cases h1 : exec ops f b (s.charge 1) with
          | none => simp [h1] at h
          | some s' =>
            simp only [h1, Option.bind_some] at h
            obtain ⟨e1, e2⟩ := ih b (s.charge 1) s' hc h1
            obtain ⟨e3, e4⟩ := ih (.while c b) s' r hc h
            exact ⟨e3.trans e1, e4.trans e2⟩
        · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-- **Attach length preservation to a `Runs` postcondition.** -/
theorem Runs.len {c : Stmt} {s : State V} {Q : State V → Prop} (hc : noAlloc c = true)
    (h : Runs ops c s Q) : Runs ops c s (fun r => Q r ∧ r.wlen = s.wlen ∧ r.vlen = s.vlen) := by
  obtain ⟨f, r, hex, hQ⟩ := h
  exact ⟨f, r, hex, hQ, exec_len f c s r hc hex⟩

end Frontier.RAM
