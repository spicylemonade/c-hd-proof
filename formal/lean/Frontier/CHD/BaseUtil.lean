import Frontier.CHD.RamSlot
import Frontier.CHD.RamBaseCase

/-!
# Frontier.CHD.BaseUtil — small generic RAM facts (owner agent-03)

**NON-GATE** (Layer B tooling).  `noAl` / `exec_noAl` / `Runs.noAl`: allocation- and call-free
statements keep all array lengths; `SlotHolds.of_idx` / `SlotLens.of_len`: slot facts from cell and
length equalities.
-/

open scoped ENNReal NNReal

namespace Frontier.RAM

open Stmt

variable {V : Type} {ops : VOps V}

/-- Statements without allocation or procedure calls. -/
def noAl : Stmt → Bool
  | .walloc _ _ => false
  | .valloc _ _ => false
  | .call _ => false
  | .seq a b => noAl a && noAl b
  | .ite _ a b => noAl a && noAl b
  | .while _ b => noAl b
  | _ => true

/-- A run of an allocation-free statement keeps all array lengths. -/
theorem exec_noAl : ∀ (f : ℕ) (c : Stmt) (s r : State V), noAl c = true → exec ops f c s = some r →
    r.wlen = s.wlen ∧ r.vlen = s.vlen
  | 0, _, _, _, _, h => by simp [exec] at h
  | f + 1, c, s, r, hc, h => by
    cases c with
    | skip => simp only [exec, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
    | wset x e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, _, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    | vset x e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, _, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    | vle x a b =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨p, _, q, _, bit, _, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    | wstore arr i e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
      obtain ⟨j, _, a, _, h⟩ := h
      split_ifs at h with hj
      simp only [Option.some.injEq] at h
      subst h; exact ⟨rfl, rfl⟩
    | vstore arr i e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
      obtain ⟨j, _, a, _, h⟩ := h
      split_ifs at h with hj
      simp only [Option.some.injEq] at h
      subst h; exact ⟨rfl, rfl⟩
    | seq a b =>
      simp only [noAl, Bool.and_eq_true] at hc
      rw [exec_seq, Option.bind_eq_some_iff] at h
      obtain ⟨s', h1, h2⟩ := h
      obtain ⟨e1, e2⟩ := exec_noAl f a s s' hc.1 h1
      obtain ⟨e3, e4⟩ := exec_noAl f b s' r hc.2 h2
      exact ⟨e3.trans e1, e4.trans e2⟩
    | ite c a b =>
      simp only [noAl, Bool.and_eq_true] at hc
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h⟩ := h
      split_ifs at h
      · have := exec_noAl f a (s.charge 1) r hc.1 h; exact this
      · have := exec_noAl f b (s.charge 1) r hc.2 h; exact this
    | «while» c b =>
      have hb : noAl b = true := hc
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h⟩ := h
      split_ifs at h
      · rw [Option.bind_eq_some_iff] at h
        obtain ⟨s', h1, h2⟩ := h
        obtain ⟨e1, e2⟩ := exec_noAl f b _ s' hb h1
        obtain ⟨e3, e4⟩ := exec_noAl f (.while c b) s' r hc h2
        exact ⟨e3.trans e1, e4.trans e2⟩
      · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
    | walloc _ _ => simp [noAl] at hc
    | valloc _ _ => simp [noAl] at hc
    | call _ => simp [noAl] at hc

/-- Add the length frame to any postcondition of an allocation-free statement. -/
theorem Runs.noAl {c : Stmt} {s : State V} {Q : State V → Prop} (hc : noAl c = true)
    (h : Runs ops c s Q) : Runs ops c s (fun r => Q r ∧ r.wlen = s.wlen ∧ r.vlen = s.vlen) := by
  obtain ⟨f, r, h1, h2⟩ := h
  exact ⟨f, r, h1, h2, exec_noAl f c s r hc h1⟩

end Frontier.RAM

namespace Frontier.CHD.RamSpine

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamBaseCase

variable {G : Graph} {s : Fin G.n}


/-- A slot is kept when its cells are. -/
theorem SlotHolds.of_idx {st r : State ℝ≥0} {i : ℕ} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {b : WLab G s}
    (h : SlotHolds st i H V b) (hv : r.va "sl.l" i = st.va "sl.l" i)
    (hw : ∀ a ∈ slotW, r.wa a i = st.wa a i) : SlotHolds r i H V b := by
  refine ⟨by rw [hw "sl.f" (by simp [slotW])]; exact h.1, fun q hq => ?_⟩
  obtain ⟨x, ⟨h1, h2, h3, h4, h5⟩, hxq⟩ := h.2 q hq
  exact ⟨x, ⟨by rw [hv]; exact h1, by rw [hw "sl.h" (by simp [slotW])]; exact h2,
    by rw [hw "sl.v" (by simp [slotW])]; exact h3, by rw [hw "sl.e" (by simp [slotW])]; exact h4,
    by rw [hw "sl.r" (by simp [slotW])]; exact h5⟩, hxq⟩

/-- Slot sizes only depend on the array lengths. -/
theorem SlotLens.of_len {st r : State ℝ≥0} {i : ℕ} (h : SlotLens st i) (hwl : r.wlen = st.wlen)
    (hvl : r.vlen = st.vlen) : SlotLens r i :=
  ⟨by rw [hvl]; exact h.l, by rw [hwl]; exact h.h, by rw [hwl]; exact h.v, by rw [hwl]; exact h.e,
    by rw [hwl]; exact h.r, by rw [hwl]; exact h.f⟩

end Frontier.CHD.RamSpine
