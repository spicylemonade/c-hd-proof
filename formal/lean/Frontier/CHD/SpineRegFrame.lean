import Frontier.CHD.WFrame
import Frontier.CHD.SpineFirst

/-!
# SpineRegFrame — the syntactic word-register frame of programs with calls (agent-08, NON-GATE)

A word register that is assigned (by `wset` / `vle`, agent-03's `wregsOf`) neither by the program
nor by any procedure body of the table keeps its value in every run — calls included (the table
never changes, `exec_cap_procs`).  For concrete programs both conditions are decidable, so e.g. the
registers `core.n/s/m` saved by `coreTop` are framed across the whole spine by `decide`.
-/

namespace Frontier.RAM

variable {V : Type} {ops : VOps V}

open Frontier.CHD.RamSpine

theorem exec_wreg_frame (z : String) : ∀ (f : ℕ) (c : Stmt) (s r : State V), exec ops f c s = some r →
    (∀ (p : ℕ) (body : Stmt), s.procs[p]? = some body → z ∉ wregsOf body) → z ∉ wregsOf c → r.w z = s.w z
  | 0, _, _, _, h, _, _ => by simp [exec] at h
  | f + 1, c, s, r, h, hp, hz => by
    cases c with
    | skip => simp [exec] at h; subst h; simp [State.charge]
    | wset x e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, _, h⟩ := h; simp at h; subst h
      have : z ≠ x := fun e => hz (by simp [wregsOf, e])
      simp [State.charge, State.setW, this]
    | vset x e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, _, h⟩ := h; simp at h; subst h; simp [State.charge, State.setV]
    | vle x a b =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨p, _, q, _, bit, _, h⟩ := h; simp at h; subst h
      have : z ≠ x := fun e => hz (by simp [wregsOf, e])
      simp [State.charge, State.setW, this]
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
      have hza : z ∉ wregsOf a := fun h => hz (List.mem_append_left _ h)
      have hzb : z ∉ wregsOf b := fun h => hz (List.mem_append_right _ h)
      have e1 := exec_wreg_frame z f a s s' h1 hp hza
      have hpr : s'.procs = s.procs := (exec_cap_procs f a s s' h1).2
      have e2 := exec_wreg_frame z f b s' r h2 (by rw [hpr]; exact hp) hzb
      rw [e2, e1]
    | ite c a b =>
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · have := exec_wreg_frame z f a _ r h2 (by simpa [State.charge] using hp)
          (fun h => hz (List.mem_append_left _ h))
        simpa [State.charge] using this
      · have := exec_wreg_frame z f b _ r h2 (by simpa [State.charge] using hp)
          (fun h => hz (List.mem_append_right _ h))
        simpa [State.charge] using this
    | «while» c b =>
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · rw [Option.bind_eq_some_iff] at h2
        obtain ⟨s', h3, h4⟩ := h2
        have hzb : z ∉ wregsOf b := hz
        have e1 := exec_wreg_frame z f b _ s' h3 (by simpa [State.charge] using hp) hzb
        have hpr : s'.procs = s.procs := by
          have := (exec_cap_procs f b _ s' h3).2; simpa [State.charge] using this
        have e2 := exec_wreg_frame z f (.while c b) s' r h4 (by rw [hpr]; exact hp) hz
        rw [e2, e1]; simp [State.charge]
      · simp at h2; subst h2; simp [State.charge]
    | call p =>
      rw [exec_call] at h
      cases hq : s.procs[p]? with
      | none => rw [hq] at h; exact absurd h (by simp)
      | some body =>
        rw [hq] at h
        have := exec_wreg_frame z f body s.enter r h (by simpa [State.enter] using hp) (hp p body hq)
        simpa [State.enter] using this

/-- **Syntactic register frame of a run**, calls included. -/
theorem Runs.wreg_frame {c : Stmt} {s : State V} {Q : State V → Prop} (z : String)
    (h : Runs ops c s Q) (hp : ∀ (p : ℕ) (body : Stmt), s.procs[p]? = some body → z ∉ wregsOf body)
    (hz : z ∉ wregsOf c) : Runs ops c s (fun r => Q r ∧ r.w z = s.w z) := by
  obtain ⟨f, r, h1, hQ⟩ := h
  exact ⟨f, r, h1, hQ, exec_wreg_frame z f c s r h1 hp hz⟩

/-- The same for a procedure table given as a list. -/
theorem Runs.wreg_frame_list {c : Stmt} {s : State V} {Q : State V → Prop} (z : String)
    (ps : List Stmt) (hps : s.procs = ps) (h : Runs ops c s Q)
    (hp : ∀ body ∈ ps, z ∉ wregsOf body) (hz : z ∉ wregsOf c) :
    Runs ops c s (fun r => Q r ∧ r.w z = s.w z) :=
  Runs.wreg_frame z h (fun p body hb => by
    rw [hps] at hb; exact hp body (List.mem_of_getElem? hb)) hz

end Frontier.RAM
