import Frontier.Refine

/-!
# SpineRule — the tight budgeted loop rule (agent-08, B-L4, NON-GATE)

`RefinesB.loopVar` pays for the loop test by a factor `K + 1`.  Nested inside a recursion over the
levels this would add `1` to the cost constant per level.  Here the body pays for its own test (its
cost bound is measured from the state *before* the test), so the loop keeps the factor `K`: one
constant serves every level.
-/

namespace Frontier.RAM

variable {V : Type} {ops : VOps V} {σ : Type}

/-- A loop run costs at least `1` (its final test). -/
theorem RelLoop.one_le {R : σ → σ → ℕ → Prop} {done : σ → Prop} {a a' : σ} {k : ℕ}
    (h : RelLoop R done a a' k) : 1 ≤ k := by
  induction h with
  | stop => exact le_rfl
  | step _ _ _ _ _ _ _ _ ih => omega

/-- **Tight budgeted `while` loop with a variant.**  The body, started after the test of a
non-final state `a` at `st`, ends in some `R`-successor within `K` per unit of its abstract cost,
counted from `st` (so the test is paid by the step); it may use the budget of the rest of the loop,
which is at least `K` (the final test).  Then the loop refines `RelLoop R done` with the same
factor `K`, and leaves `K - 1` of the final test's charge unused (for code run before the loop). -/
theorem loopTight {Rep : σ → State V → Prop} {Inv : σ → Prop} {e : WExpr} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K Lim : ℕ} (done : σ → Prop) (μ : σ → ℕ) (hK : 1 ≤ K)
    (htest : ∀ a st, Inv a → Rep a st → ∃ x, evalW st e = some x ∧ (x ≠ 0 ↔ ¬ done a))
    (hcharge : ∀ a st, Rep a st → Rep a (st.charge 1))
    (hbody : ∀ a st, Inv a → ¬ done a → Rep a st →
      (∀ a' k, R a a' k → st.cost + K * k + K ≤ Lim) →
      Runs ops c (st.charge 1) (fun st' => ∃ a' k, R a a' k ∧ Rep a' st' ∧
        st'.cost ≤ st.cost + K * k))
    (hstep : ∀ a a' k, Inv a → ¬ done a → R a a' k → Inv a' ∧ μ a' < μ a)
    (htot : ∀ a, Inv a → ¬ done a → ∃ a' k, R a a' k)
    (a0 : σ) (st0 : State V) (hI0 : Inv a0) (hRep0 : Rep a0 st0)
    (hbud0 : ∀ a'' k, RelLoop R done a0 a'' k → st0.cost + K * k ≤ Lim) :
    Runs ops (.while e c) st0 (fun st' => ∃ a' k, RelLoop R done a0 a' k ∧ Rep a' st' ∧
      st'.cost + (K - 1) ≤ st0.cost + K * k) := by
  have hLtot : Total Inv (RelLoop R done) := RelLoop.total Inv μ hstep htot
  refine runs_while_nat (fun n st => ∃ a k, μ a = n ∧ Inv a ∧ Rep a st ∧
      st.cost ≤ st0.cost + K * k ∧
      (∀ a'' k'', RelLoop R done a a'' k'' → RelLoop R done a0 a'' (k + k''))) _ ?_ (μ a0) st0
    ⟨a0, 0, rfl, hI0, hRep0, by simp, fun a'' k'' h => by simpa using h⟩
  rintro n st ⟨a, k, rfl, hI, hRep, hc, hpref⟩
  obtain ⟨x, hx, hxd⟩ := htest a st hI hRep
  refine ⟨x, hx, fun hx0 => ?_, fun hx0 => ?_⟩
  · have hnd : ¬ done a := hxd.mp hx0
    refine (hbody a st hI hnd hRep ?_).mono ?_
    · intro a' k' hR
      obtain ⟨hI', -⟩ := hstep a a' k' hI hnd hR
      obtain ⟨a'', k'', hL⟩ := hLtot a' hI'
      have h1 := hL.one_le
      have hb := hbud0 a'' (k + (k' + k'')) (hpref a'' (k' + k'') (.step a a' a'' k' k'' hnd hR hL))
      have e1 : K * (k + (k' + k'')) = K * k + K * k' + K * k'' := by ring
      have e2 : K ≤ K * k'' := Nat.le_mul_of_pos_right _ h1
      omega
    · rintro st' ⟨a', k', hR, hRep', hc'⟩
      obtain ⟨hI', hμ⟩ := hstep a a' k' hI hnd hR
      refine ⟨μ a', hμ, a', k + k', rfl, hI', hRep', ?_, ?_⟩
      · have e1 : K * (k + k') = K * k + K * k' := by ring
        omega
      · intro a'' k'' hL
        have := hpref a'' (k' + k'') (.step a a' a'' k' k'' hnd hR hL)
        rwa [← Nat.add_assoc] at this
  · have hd : done a := by
      by_contra h; exact hxd.mpr h hx0
    refine ⟨a, k + 1, hpref a 1 (.stop a hd), hcharge a st hRep, ?_⟩
    have e1 : K * (k + 1) = K * k + K := by ring
    simp only [State.charge]
    omega

/-- The inverse of `runs_seq` (executions are deterministic). -/
theorem Runs.seq_inv {a b : Stmt} {st : State V} {Q : State V → Prop}
    (h : Runs ops (.seq a b) st Q) : Runs ops a st (fun s' => Runs ops b s' Q) := by
  obtain ⟨f, r, h1, hQ⟩ := h
  cases f with
  | zero => simp [exec] at h1
  | succ f =>
    rw [exec_seq, Option.bind_eq_some_iff] at h1
    obtain ⟨s', h2, h3⟩ := h1
    exact ⟨f, s', h2, f, r, h3, hQ⟩

/-- Re-association of sequential composition. -/
theorem Runs.seq_assoc {a b c : Stmt} {st : State V} {Q : State V → Prop}
    (h : Runs ops (.seq a (.seq b c)) st Q) : Runs ops (.seq (.seq a b) c) st Q := by
  refine runs_seq (runs_seq ((Runs.seq_inv h).mono fun s1 h1 => Runs.seq_inv h1))

end Frontier.RAM
