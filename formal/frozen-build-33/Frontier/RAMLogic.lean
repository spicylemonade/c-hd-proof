import Frontier.CostModel

/-!
# Frontier.RAMLogic — a small program logic for the `Frontier.RAM` machine

Owner: agent-08.  Total-correctness reasoning about `RAM.exec`: `Runs ops c s Q` says that `c`
started in `s` terminates (for some fuel) in a state satisfying `Q`.  Rules for every statement
form, sequencing, conditionals and counted `while` loops.  Used by non-vacuity witnesses and by
any verified `Program`.  No algorithm and no gate result here.
-/

namespace Frontier.RAM

variable {V : Type} (ops : VOps V)

/-- `c` run from `s` terminates in a state satisfying `Q`. -/
def Runs (c : Stmt) (s : State V) (Q : State V → Prop) : Prop :=
  ∃ f r, exec ops f c s = some r ∧ Q r

variable {ops}

theorem Runs.mono {c : Stmt} {s : State V} {Q Q' : State V → Prop} (h : Runs ops c s Q)
    (hQ : ∀ r, Q r → Q' r) : Runs ops c s Q' := by
  obtain ⟨f, r, h1, h2⟩ := h
  exact ⟨f, r, h1, hQ r h2⟩


/-! ### Evaluation lemmas (generic in the value type, so `simp` never sees `Option ℝ≥0 = ℝ≥0∞`) -/

@[simp] theorem evalW_var (s : State V) (x : String) : evalW s (.var x) = some (s.w x) := rfl

theorem evalW_lit_of {s : State V} {a : ℕ} (h : a < s.cap) : evalW s (.lit a) = some a := by
  simp [evalW, fit, h]

theorem evalW_load_of {s : State V} {arr : String} {i : WExpr} {j : ℕ}
    (hi : evalW s i = some j) (hj : j < s.wlen arr) : evalW s (.load arr i) = some (s.wa arr j) := by
  simp [evalW, hi, hj]

theorem evalW_eq_of {s : State V} {a b : WExpr} {x y : ℕ} (ha : evalW s a = some x)
    (hb : evalW s b = some y) (hc : 1 < s.cap) :
    evalW s (.eq a b) = some (if x = y then 1 else 0) := by
  have h0 : 0 < s.cap := by omega
  simp only [evalW, ha, hb, Option.bind_some, fit]
  by_cases h : x = y <;> simp [h, hc, h0]

theorem evalW_lt_of {s : State V} {a b : WExpr} {x y : ℕ} (ha : evalW s a = some x)
    (hb : evalW s b = some y) (hc : 1 < s.cap) :
    evalW s (.lt a b) = some (if x < y then 1 else 0) := by
  have h0 : 0 < s.cap := by omega
  simp only [evalW, ha, hb, Option.bind_some, fit]
  by_cases h : x < y <;> simp [h, hc, h0]

theorem evalW_add_of {s : State V} {a b : WExpr} {x y : ℕ} (ha : evalW s a = some x)
    (hb : evalW s b = some y) (hc : x + y < s.cap) :
    evalW s (.add a b) = some (x + y) := by
  simp [evalW, ha, hb, fit, hc]

theorem evalV_load_of {s : State V} {arr : String} {i : WExpr} {j : ℕ}
    (hi : evalW s i = some j) (hj : j < s.vlen arr) :
    evalV ops s (.load arr i) = some (s.va arr j) := by
  simp [evalV, hi, hj]

theorem evalV_add_of {s : State V} {a b : VExpr} {x y : V} (ha : evalV ops s a = some x)
    (hb : evalV ops s b = some y) : evalV ops s (.add a b) = some (ops.add x y) := by
  simp [evalV, ha, hb]

theorem evalW_charge (s : State V) (k : ℕ) (e : WExpr) : evalW (s.charge k) e = evalW s e := by
  induction e with
  | load arr i ih => simp only [evalW, ih]; rfl
  | add a b iha ihb => simp only [evalW, iha, ihb]; rfl
  | sub a b iha ihb => simp only [evalW, iha, ihb]
  | mul a b iha ihb => simp only [evalW, iha, ihb]; rfl
  | div a b iha ihb => simp only [evalW, iha, ihb]
  | lt a b iha ihb => simp only [evalW, iha, ihb]; rfl
  | eq a b iha ihb => simp only [evalW, iha, ihb]; rfl
  | lit a => rfl
  | var x => rfl

theorem evalV_charge (s : State V) (k : ℕ) (e : VExpr) :
    evalV ops (s.charge k) e = evalV ops s e := by
  induction e with
  | load arr i => simp only [evalV, evalW_charge]; rfl
  | add a b iha ihb => simp only [evalV, iha, ihb]
  | zero => rfl
  | var x => rfl

theorem runs_skip {s : State V} {Q : State V → Prop} (hQ : Q (s.charge 1)) :
    Runs ops .skip s Q := ⟨1, _, rfl, hQ⟩

theorem runs_wset {x : String} {e : WExpr} {s : State V} {Q : State V → Prop} {a : ℕ}
    (he : evalW s e = some a) (hQ : Q ((s.setW x a).charge 1)) :
    Runs ops (.wset x e) s Q :=
  ⟨1, _, by simp [exec, he], hQ⟩

theorem runs_vset {x : String} {e : VExpr} {s : State V} {Q : State V → Prop} {a : V}
    (he : evalV ops s e = some a) (hQ : Q ((s.setV x a).charge 1)) :
    Runs ops (.vset x e) s Q :=
  ⟨1, _, by simp [exec, he], hQ⟩

theorem runs_vle {x : String} {a b : VExpr} {s : State V} {Q : State V → Prop} {p q : V}
    (ha : evalV ops s a = some p) (hb : evalV ops s b = some q) (hcap : 1 < s.cap)
    (hQ : Q ((s.setW x (if ops.le p q then 1 else 0)).charge 1)) :
    Runs ops (.vle x a b) s Q := by
  refine ⟨1, _, ?_, hQ⟩
  have hfit : fit s.cap (if ops.le p q then 1 else 0) = some (if ops.le p q then 1 else 0) := by
    unfold fit
    split_ifs <;> simp_all
  simp [exec, ha, hb, hfit]

theorem runs_wstore {arr : String} {i e : WExpr} {s : State V} {Q : State V → Prop} {j a : ℕ}
    (hi : evalW s i = some j) (he : evalW s e = some a) (hj : j < s.wlen arr)
    (hQ : Q ((s.storeW arr j a).charge 1)) : Runs ops (.wstore arr i e) s Q :=
  ⟨1, _, by simp [exec, hi, he, hj], hQ⟩

theorem runs_vstore {arr : String} {i : WExpr} {e : VExpr} {s : State V} {Q : State V → Prop}
    {j : ℕ} {a : V} (hi : evalW s i = some j) (he : evalV ops s e = some a) (hj : j < s.vlen arr)
    (hQ : Q ((s.storeV arr j a).charge 1)) : Runs ops (.vstore arr i e) s Q :=
  ⟨1, _, by simp [exec, hi, he, hj], hQ⟩

theorem runs_walloc {arr : String} {e : WExpr} {s : State V} {Q : State V → Prop} {k : ℕ}
    (he : evalW s e = some k) (hQ : Q ((s.allocW arr k).charge (k + 1))) :
    Runs ops (.walloc arr e) s Q :=
  ⟨1, _, by simp [exec, he], hQ⟩

theorem runs_valloc {arr : String} {e : WExpr} {s : State V} {Q : State V → Prop} {k : ℕ}
    (he : evalW s e = some k) (hQ : Q ((s.allocV arr k ops.zero).charge (k + 1))) :
    Runs ops (.valloc arr e) s Q :=
  ⟨1, _, by simp [exec, he], hQ⟩

theorem runs_seq {a b : Stmt} {s : State V} {Q : State V → Prop}
    (h : Runs ops a s (fun s' => Runs ops b s' Q)) : Runs ops (.seq a b) s Q := by
  obtain ⟨f₁, s', h₁, f₂, r, h₂, hQ⟩ := h
  refine ⟨max f₁ f₂ + 1, r, ?_, hQ⟩
  rw [exec_seq, exec_mono ops h₁ (le_max_left _ _)]
  exact exec_mono ops h₂ (le_max_right _ _)

theorem runs_ite_true {c : WExpr} {a b : Stmt} {s : State V} {Q : State V → Prop} {x : ℕ}
    (hc : evalW s c = some x) (hx : x ≠ 0) (h : Runs ops a (s.charge 1) Q) :
    Runs ops (.ite c a b) s Q := by
  obtain ⟨f, r, h₁, hQ⟩ := h
  exact ⟨f + 1, r, by rw [exec_ite, hc]; simpa [hx] using h₁, hQ⟩

theorem runs_ite_false {c : WExpr} {a b : Stmt} {s : State V} {Q : State V → Prop}
    (hc : evalW s c = some 0) (h : Runs ops b (s.charge 1) Q) :
    Runs ops (.ite c a b) s Q := by
  obtain ⟨f, r, h₁, hQ⟩ := h
  exact ⟨f + 1, r, by rw [exec_ite, hc]; simpa using h₁, hQ⟩

/-- Procedure call: run the body of procedure `p` (charged `1` cost and `1` space). -/
theorem runs_call {p : ℕ} {s : State V} {Q : State V → Prop} {body : Stmt}
    (hp : s.procs[p]? = some body) (h : Runs ops body s.enter Q) : Runs ops (.call p) s Q := by
  obtain ⟨f, r, h₁, hQ⟩ := h
  exact ⟨f + 1, r, by rw [exec_call, hp]; exact h₁, hQ⟩

/-- Counted `while` loop: an invariant `I k` indexed by the number of completed iterations,
exactly `K` iterations, then exit with `Q`. -/
theorem runs_while {c : WExpr} {b : Stmt} (I : ℕ → State V → Prop) (K : ℕ)
    (Q : State V → Prop)
    (hstep : ∀ k < K, ∀ s, I k s →
      ∃ x, evalW s c = some x ∧ x ≠ 0 ∧ Runs ops b (s.charge 1) (I (k + 1)))
    (hexit : ∀ s, I K s → evalW s c = some 0 ∧ Q (s.charge 1)) :
    ∀ s, I 0 s → Runs ops (.while c b) s Q := by
  have key : ∀ j, j ≤ K → ∀ s, I (K - j) s → Runs ops (.while c b) s Q := by
    intro j
    induction j with
    | zero =>
      intro _ s hs
      obtain ⟨hc, hQ⟩ := hexit s (by simpa using hs)
      exact ⟨1, s.charge 1, by rw [exec_while, hc]; simp, hQ⟩
    | succ j ih =>
      intro hj s hs
      obtain ⟨x, hc, hx, f₁, s', h₁, hs'⟩ := hstep (K - (j + 1)) (by omega) s hs
      have hs'' : I (K - j) s' := by
        have : K - (j + 1) + 1 = K - j := by omega
        rwa [this] at hs'
      obtain ⟨f₂, r, h₂, hQ⟩ := ih (by omega) s' hs''
      refine ⟨max f₁ f₂ + 1, r, ?_, hQ⟩
      rw [exec_while, hc]
      simp only [Option.bind_some, ne_eq, hx, not_false_eq_true, ite_true]
      rw [exec_mono ops h₁ (le_max_left _ _)]
      exact exec_mono ops h₂ (le_max_right _ _)
  intro s hs
  exact key K le_rfl s (by simpa using hs)

/-- Measure-based `while` rule (written by agent-09, installed here to avoid duplicates): a
`while` loop terminates in `Q` if an invariant `I` holds, every iteration from an `I`-state with
nonzero test re-establishes `I` and strictly decreases a measure `μ`, and a zero test implies `Q`
after the test charge.  No iteration count is needed in advance. -/
theorem runs_while_var {c : WExpr} {b : Stmt} (I : State V → Prop) (μ : State V → ℕ)
    (Q : State V → Prop)
    (hstep : ∀ s, I s → ∃ x, evalW s c = some x ∧
      (x ≠ 0 → Runs ops b (s.charge 1) (fun s' => I s' ∧ μ s' < μ s)) ∧
      (x = 0 → Q (s.charge 1))) :
    ∀ s, I s → Runs ops (.while c b) s Q := by
  have key : ∀ N, ∀ s, μ s ≤ N → I s → Runs ops (.while c b) s Q := by
    intro N
    induction N with
    | zero =>
      intro s hμ hs
      obtain ⟨x, hc, hbody, hexit⟩ := hstep s hs
      by_cases hx : x = 0
      · subst hx
        exact ⟨1, s.charge 1, by rw [exec_while, hc]; simp, hexit rfl⟩
      · obtain ⟨f, s', h1, -, hμ'⟩ := hbody hx
        omega
    | succ N ih =>
      intro s hμ hs
      obtain ⟨x, hc, hbody, hexit⟩ := hstep s hs
      by_cases hx : x = 0
      · subst hx
        exact ⟨1, s.charge 1, by rw [exec_while, hc]; simp, hexit rfl⟩
      · obtain ⟨f₁, s', h₁, hs', hμ'⟩ := hbody hx
        obtain ⟨f₂, r, h₂, hQ⟩ := ih s' (by omega) hs'
        refine ⟨max f₁ f₂ + 1, r, ?_, hQ⟩
        rw [exec_while, hc]
        simp only [Option.bind_some, ne_eq, hx, not_false_eq_true, ite_true]
        rw [exec_mono ops h₁ (le_max_left _ _)]
        exact exec_mono ops h₂ (le_max_right _ _)
  intro s hs
  exact key (μ s) s le_rfl hs

/-- `while` with an invariant indexed by a natural-number measure (agent-09): every iteration
moves from `I n` to some `I n'` with `n' < n`. -/
theorem runs_while_nat {c : WExpr} {b : Stmt} (I : ℕ → State V → Prop) (Q : State V → Prop)
    (hstep : ∀ n s, I n s → ∃ x, evalW s c = some x ∧
      (x ≠ 0 → Runs ops b (s.charge 1) (fun s' => ∃ n', n' < n ∧ I n' s')) ∧
      (x = 0 → Q (s.charge 1))) :
    ∀ n s, I n s → Runs ops (.while c b) s Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    obtain ⟨x, hc, hbody, hexit⟩ := hstep n s hs
    by_cases hx : x = 0
    · subst hx
      exact ⟨1, s.charge 1, by rw [exec_while, hc]; simp, hexit rfl⟩
    · obtain ⟨f₁, s', h₁, n', hn', hs'⟩ := hbody hx
      obtain ⟨f₂, r, h₂, hQ⟩ := ih n' hn' s' hs'
      refine ⟨max f₁ f₂ + 1, r, ?_, hQ⟩
      rw [exec_while, hc]
      simp only [Option.bind_some, ne_eq, hx, not_false_eq_true, ite_true]
      rw [exec_mono ops h₁ (le_max_left _ _)]
      exact exec_mono ops h₂ (le_max_right _ _)

/-- The cost counter never decreases along a successful run. -/
theorem exec_cost_mono : ∀ (f : ℕ) (c : Stmt) (s r : State V), exec ops f c s = some r →
    s.cost ≤ r.cost
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
      exact (exec_cost_mono f a s s' h1).trans (exec_cost_mono f b s' r h2)
    | ite c a b =>
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · have := exec_cost_mono f a _ r h2; simp [State.charge] at this; omega
      · have := exec_cost_mono f b _ r h2; simp [State.charge] at this; omega
    | «while» c b =>
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · rw [Option.bind_eq_some_iff] at h2
        obtain ⟨s', h3, h4⟩ := h2
        have i1 := exec_cost_mono f b _ s' h3
        have i2 := exec_cost_mono f (.while c b) s' r h4
        simp [State.charge] at i1; omega
      · simp at h2; subst h2; simp [State.charge]
    | call p =>
      rw [exec_call] at h
      cases hp : s.procs[p]? with
      | none => rw [hp] at h; exact absurd h (by simp)
      | some body =>
        rw [hp] at h
        have := exec_cost_mono f body _ r h; simp [State.enter] at this; omega

/-- Every `Runs` postcondition may be strengthened by cost monotonicity. -/
theorem Runs.cost_mono {c : Stmt} {st : State V} {Q : State V → Prop} (h : Runs ops c st Q) :
    Runs ops c st (fun r => Q r ∧ st.cost ≤ r.cost) := by
  obtain ⟨f, r, h1, hQ⟩ := h
  exact ⟨f, r, h1, hQ, exec_cost_mono f c st r h1⟩

end Frontier.RAM
