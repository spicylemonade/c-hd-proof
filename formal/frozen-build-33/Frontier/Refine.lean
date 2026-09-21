import Frontier.RAMLogic

/-!
# Frontier.Refine — Layer-B refinement framework (RAM fragments implement Layer-A steps)

Owner: agent-08 (Layer B, COORD G2-3).  NON-GATE infrastructure.

Layer A describes C-HD as cost-indexed relations `R : σ → σ → ℕ → Prop` over abstract states
(`R a a' k`: one step from `a` to `a'` of abstract cost `k` under the operation table).  Layer B
must show that a concrete RAM fragment `c` implements `R`:

  `Refines ops Rep Pre c R K` :  from every machine state `st` representing an abstract state `a`
  satisfying `Pre`, `c` terminates in a state `st'` representing some `a'` with `R a a' k`, and
  the machine cost grows by at most `K * k`.

Composition rules proved here: sequencing (`Refines.seq`), consequence (`Refines.mono`,
`Refines.weaken`), conditionals on a represented predicate (`Refines.ite`), procedure calls
(`Refines.call`) and counted loops (`Refines.loop`, iterating a relation `n` times with the costs
summed).  The top-level transfer theorem `exact_of_refines` turns a refinement of an abstract
algorithm whose every execution is correct and cheap into `Program.Exact` and `RunsWithin`.

Budgeted refinement (`RefinesB`, word-cap discipline): a fragment may assume that every abstract
outcome of its step keeps the machine cost within a limit `Lim`; composition rules `RefinesB.seq`
(needs the continuation relation to be `Total`), `.ite`, `.call`, `.loopVar` (loops with a stop
predicate and a variant, abstract runs `RelLoop`, totality `RelLoop.total`).  Amortized version
`RefinesP` (machine cost plus an abstract potential `Φ`; same rules, potentials telescope).

Convention (to keep the machine cost honest): each abstract step must be charged at least as much
as the constant RAM work of its fragment divided by `K`; in particular loop iterations must have
abstract cost `≥ 1` so that loop tests are paid for (`Refines.loop` requires it).
-/

open scoped NNReal

namespace Frontier.RAM

variable {V : Type} {ops : VOps V} {σ : Type}

/-- `c` refines the cost-indexed relation `R` under the representation `Rep`, from abstract states
satisfying `Pre`, with cost factor `K`. -/
def Refines (ops : VOps V) (Rep : σ → State V → Prop) (Pre : σ → Prop) (c : Stmt)
    (R : σ → σ → ℕ → Prop) (K : ℕ) : Prop :=
  ∀ a st, Pre a → Rep a st →
    Runs ops c st (fun st' => ∃ a' k, R a a' k ∧ Rep a' st' ∧ st'.cost ≤ st.cost + K * k)

/-- Sequential composition of cost-indexed relations (costs add). -/
def RelSeq (R₁ R₂ : σ → σ → ℕ → Prop) : σ → σ → ℕ → Prop :=
  fun a a'' k => ∃ a' k₁ k₂, R₁ a a' k₁ ∧ R₂ a' a'' k₂ ∧ k = k₁ + k₂

/-- `n`-fold iteration of a cost-indexed relation (costs add). -/
def RelIter (R : σ → σ → ℕ → Prop) : ℕ → σ → σ → ℕ → Prop
  | 0 => fun a a' k => a' = a ∧ k = 0
  | n + 1 => RelSeq (RelIter R n) R

theorem Refines.mono {Rep : σ → State V → Prop} {Pre : σ → Prop} {c : Stmt}
    {R R' : σ → σ → ℕ → Prop} {K K' : ℕ} (h : Refines ops Rep Pre c R K)
    (hR : ∀ a a' k, Pre a → R a a' k → ∃ k', R' a a' k' ∧ K * k ≤ K' * k') :
    Refines ops Rep Pre c R' K' := by
  intro a st hPre hRep
  refine (h a st hPre hRep).mono ?_
  rintro st' ⟨a', k, hR1, hRep', hc⟩
  obtain ⟨k', hR', hk⟩ := hR a a' k hPre hR1
  exact ⟨a', k', hR', hRep', by omega⟩

/-- Strengthening the precondition. -/
theorem Refines.weaken {Rep : σ → State V → Prop} {Pre Pre' : σ → Prop} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K : ℕ} (h : Refines ops Rep Pre c R K)
    (hP : ∀ a, Pre' a → Pre a) : Refines ops Rep Pre' c R K :=
  fun a st hPre hRep => h a st (hP a hPre) hRep

/-- **Sequencing**: if `c₁` refines `R₁`, every `R₁`-successor satisfies `Pre₂`, and `c₂` refines
`R₂` from `Pre₂`, then `c₁; c₂` refines `R₁ ; R₂`. -/
theorem Refines.seq {Rep : σ → State V → Prop} {Pre₁ Pre₂ : σ → Prop} {c₁ c₂ : Stmt}
    {R₁ R₂ : σ → σ → ℕ → Prop} {K : ℕ} (h₁ : Refines ops Rep Pre₁ c₁ R₁ K)
    (hmid : ∀ a a' k, Pre₁ a → R₁ a a' k → Pre₂ a') (h₂ : Refines ops Rep Pre₂ c₂ R₂ K) :
    Refines ops Rep Pre₁ (.seq c₁ c₂) (RelSeq R₁ R₂) K := by
  intro a st hPre hRep
  refine runs_seq ((h₁ a st hPre hRep).mono ?_)
  rintro st' ⟨a', k₁, hR₁, hRep', hc₁⟩
  refine (h₂ a' st' (hmid a a' k₁ hPre hR₁) hRep').mono ?_
  rintro st'' ⟨a'', k₂, hR₂, hRep'', hc₂⟩
  exact ⟨a'', k₁ + k₂, ⟨a', k₁, k₂, hR₁, hR₂, rfl⟩, hRep'', by rw [Nat.mul_add]; omega⟩

/-- **Conditional** on a word expression whose value is determined by an abstract predicate `b`:
the test costs `1`, paid by the branches' abstract costs being `≥ 1` (hypotheses `hk₁`, `hk₂`);
the cost factor grows from `K` to `K + 1`. -/
theorem Refines.ite {Rep : σ → State V → Prop} {Pre : σ → Prop} {e : WExpr} {c₁ c₂ : Stmt}
    {R₁ R₂ : σ → σ → ℕ → Prop} {K : ℕ} (b : σ → Prop) [DecidablePred b]
    (htest : ∀ a st, Pre a → Rep a st → ∃ x, evalW st e = some x ∧ (x ≠ 0 ↔ b a))
    (hcharge : ∀ a st, Rep a st → Rep a (st.charge 1))
    (h₁ : Refines ops Rep (fun a => Pre a ∧ b a) c₁ R₁ K)
    (h₂ : Refines ops Rep (fun a => Pre a ∧ ¬ b a) c₂ R₂ K)
    (hk₁ : ∀ a a' k, Pre a → b a → R₁ a a' k → 1 ≤ k)
    (hk₂ : ∀ a a' k, Pre a → ¬ b a → R₂ a a' k → 1 ≤ k) :
    Refines ops Rep Pre (.ite e c₁ c₂) (fun a a' k => (b a ∧ R₁ a a' k) ∨ (¬ b a ∧ R₂ a a' k))
      (K + 1) := by
  intro a st hPre hRep
  obtain ⟨x, hx, hxb⟩ := htest a st hPre hRep
  by_cases hb : b a
  · have hx0 : x ≠ 0 := hxb.mpr hb
    refine runs_ite_true hx hx0 ((h₁ a (st.charge 1) ⟨hPre, hb⟩ (hcharge a st hRep)).mono ?_)
    rintro st' ⟨a', k, hR, hRep', hc⟩
    have := hk₁ a a' k hPre hb hR
    refine ⟨a', k, Or.inl ⟨hb, hR⟩, hRep', ?_⟩
    simp [State.charge] at hc
    nlinarith
  · have hx0 : x = 0 := by
      by_contra h; exact hb (hxb.mp h)
    subst hx0
    refine runs_ite_false hx ((h₂ a (st.charge 1) ⟨hPre, hb⟩ (hcharge a st hRep)).mono ?_)
    rintro st' ⟨a', k, hR, hRep', hc⟩
    have := hk₂ a a' k hPre hb hR
    refine ⟨a', k, Or.inr ⟨hb, hR⟩, hRep', ?_⟩
    simp [State.charge] at hc
    nlinarith

/-- **Procedure call**: if the body of procedure `p` refines `R`, so does `call p` (factor
`K + 1`), provided the call's unit cost is paid by abstract costs `≥ 1`. -/
theorem Refines.call {Rep : σ → State V → Prop} {Pre : σ → Prop} {p : ℕ} {body : Stmt}
    {R : σ → σ → ℕ → Prop} {K : ℕ}
    (hp : ∀ a st, Pre a → Rep a st → st.procs[p]? = some body)
    (henter : ∀ a st, Rep a st → Rep a st.enter)
    (h : Refines ops Rep Pre body R K) (hk : ∀ a a' k, Pre a → R a a' k → 1 ≤ k) :
    Refines ops Rep Pre (.call p) R (K + 1) := by
  intro a st hPre hRep
  refine runs_call (hp a st hPre hRep) ((h a st.enter hPre (henter a st hRep)).mono ?_)
  rintro st' ⟨a', k, hR, hRep', hc⟩
  have := hk a a' k hPre hR
  refine ⟨a', k, hR, hRep', ?_⟩
  simp [State.enter] at hc
  nlinarith

/-- **Counted loop**: a `while` loop whose test is `≠ 0` exactly while an abstract counter is below
`n`, and whose body refines one step `R` (abstract cost `≥ 1`, paying for the test), refines the
`n`-fold iteration of `R`; the final test is paid by an extra `K` units. -/
theorem Refines.loop {Rep : σ → State V → Prop} {Pre : σ → Prop} {e : WExpr} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K : ℕ} (n : ℕ) (cnt : σ → ℕ)
    (htest : ∀ a st, Pre a → Rep a st → ∃ x, evalW st e = some x ∧ (x ≠ 0 ↔ cnt a < n))
    (hcharge : ∀ a st, Rep a st → Rep a (st.charge 1))
    (hbody : Refines ops Rep (fun a => Pre a ∧ cnt a < n) c R K)
    (hstep : ∀ a a' k, Pre a → cnt a < n → R a a' k → Pre a' ∧ cnt a' = cnt a + 1 ∧ 1 ≤ k) :
    Refines ops Rep (fun a => Pre a ∧ cnt a = 0) (.while e c)
      (fun a a' k => ∃ k', RelIter R n a a' k' ∧ k = k' + 1) (K + 1) := by
  intro a0 st0 ⟨hPre0, hcnt0⟩ hRep0
  -- invariant after `j` iterations
  refine runs_while (fun j st => ∃ a k, RelIter R j a0 a k ∧ Pre a ∧ cnt a = j ∧ Rep a st ∧
      st.cost ≤ st0.cost + (K + 1) * k) n _ ?_ ?_ st0
      ⟨a0, 0, ⟨rfl, rfl⟩, hPre0, hcnt0, hRep0, by simp⟩
  · intro j hj st ⟨a, k, hIt, hPre, hcnt, hRep, hc⟩
    obtain ⟨x, hx, hxb⟩ := htest a st hPre hRep
    refine ⟨x, hx, hxb.mpr (by omega), ?_⟩
    refine (hbody a (st.charge 1) ⟨hPre, by omega⟩ (hcharge a st hRep)).mono ?_
    rintro st' ⟨a', k', hR, hRep', hc'⟩
    obtain ⟨hPre', hcnt', hk'⟩ := hstep a a' k' hPre (by omega) hR
    refine ⟨a', k + k', ⟨a, k, k', hIt, hR, rfl⟩, hPre', by omega, hRep', ?_⟩
    simp [State.charge] at hc'
    rw [Nat.mul_add]
    nlinarith
  · intro st ⟨a, k, hIt, hPre, hcnt, hRep, hc⟩
    obtain ⟨x, hx, hxb⟩ := htest a st hPre hRep
    have hx0 : x = 0 := by
      by_contra h; exact absurd (hxb.mp h) (by omega)
    refine ⟨by rw [hx, hx0], a, k + 1, ⟨k, hIt, rfl⟩, hcharge a st hRep, ?_⟩
    simp [State.charge]
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-! ## Top-level transfer to the gate statements -/

/-- If the program body, run from the initial state, refines an abstract algorithm relation
`Alg G s` from an abstract initial state (represented by `initState`), and every abstract
execution produces a final state whose decoded output solves SSSP and whose abstract cost is at
most `T n m`, then the program is exact and runs within `K * T n m`. -/
theorem exact_of_refines {σ : Graph → Type} (P : Program)
    (Rep : ∀ G, σ G → State ℝ≥0 → Prop) (Pre : ∀ G, σ G → Prop)
    (Alg : ∀ (G : Graph) (s : Fin G.n), σ G → σ G → ℕ → Prop) (K : ℕ)
    (init : ∀ (G : Graph) (s : Fin G.n), σ G)
    (hinit : ∀ G s, Pre G (init G s) ∧ Rep G (init G s) (initState P G s))
    (href : ∀ G s, Refines realOps (Rep G) (Pre G) P.body (Alg G s) K)
    (hout : ∀ G s a' k st', Alg G s (init G s) a' k → Rep G a' st' → st'.Solves G s)
    (T : ℕ → ℕ → ℝ)
    (hcost : ∀ G s a' k, Alg G s (init G s) a' k → (K * k : ℝ) ≤ T G.n G.m) :
    P.Exact ∧ ∀ (G : Graph) (s : Fin G.n), P.RunsWithin G s (T G.n G.m) := by
  have key : ∀ G s, ∃ fuel r, P.run fuel G s = some r ∧ r.Solves G s ∧ (r.cost : ℝ) ≤ T G.n G.m := by
    intro G s
    obtain ⟨hPre, hRep⟩ := hinit G s
    obtain ⟨fuel, r, hr, a', k, hAlg, hRep', hc⟩ := href G s (init G s) _ hPre hRep
    refine ⟨fuel, r, hr, hout G s a' k r hAlg hRep', ?_⟩
    have h0 : (initState P G s).cost = 0 := rfl
    rw [h0, zero_add] at hc
    calc (r.cost : ℝ) ≤ (K * k : ℕ) := by exact_mod_cast hc
      _ = (K * k : ℝ) := by push_cast; ring
      _ ≤ T G.n G.m := hcost G s a' k hAlg
  refine ⟨fun G s => ?_, fun G s => ?_⟩
  · obtain ⟨fuel, r, hr, hsol, -⟩ := key G s
    exact ⟨fuel, r, hr, hsol⟩
  · obtain ⟨fuel, r, hr, -, hc⟩ := key G s
    exact ⟨fuel, r, hr, hc⟩

/-! ## Budgeted refinement (word-cap discipline)

Counters whose values grow with the elapsed running time (label version counters) can only be
kept below the word cap if the elapsed cost is known to stay below a limit.  The limit comes from
the Layer-A cost bound of *complete* runs, so a fragment may assume that **every** abstract outcome
of its step stays within the limit (`RefinesB`).  Sequencing then needs the continuation relation
to be **total** (every prefix of a run extends to a complete run); plain `Refines` embeds into
`RefinesB` for every limit (`Refines.toB`). -/

/-- **Budgeted refinement**: as `Refines`, but the concrete run may assume that every abstract
outcome `(a', k)` of the step satisfies `st.cost + K * k ≤ Lim`. -/
def RefinesB (ops : VOps V) (Rep : σ → State V → Prop) (Pre : σ → Prop) (c : Stmt)
    (R : σ → σ → ℕ → Prop) (K Lim : ℕ) : Prop :=
  ∀ a st, Pre a → Rep a st → (∀ a' k, R a a' k → st.cost + K * k ≤ Lim) →
    Runs ops c st (fun st' => ∃ a' k, R a a' k ∧ Rep a' st' ∧ st'.cost ≤ st.cost + K * k)

/-- The relation `R` has an outcome from every state satisfying `Pre`. -/
def Total (Pre : σ → Prop) (R : σ → σ → ℕ → Prop) : Prop := ∀ a, Pre a → ∃ a' k, R a a' k

theorem Refines.toB {Rep : σ → State V → Prop} {Pre : σ → Prop} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K : ℕ} (h : Refines ops Rep Pre c R K) (Lim : ℕ) :
    RefinesB ops Rep Pre c R K Lim :=
  fun a st hPre hRep _ => h a st hPre hRep

/-- Consequence rule (larger relation and factor); the budget is inherited backwards. -/
theorem RefinesB.mono {Rep : σ → State V → Prop} {Pre : σ → Prop} {c : Stmt}
    {R R' : σ → σ → ℕ → Prop} {K K' Lim : ℕ} (h : RefinesB ops Rep Pre c R K Lim)
    (hR : ∀ a a' k, Pre a → R a a' k → ∃ k', R' a a' k' ∧ K * k ≤ K' * k') :
    RefinesB ops Rep Pre c R' K' Lim := by
  intro a st hPre hRep hbud
  refine (h a st hPre hRep ?_).mono ?_
  · intro a' k hR1
    obtain ⟨k', hR', hk⟩ := hR a a' k hPre hR1
    have := hbud a' k' hR'
    omega
  · rintro st' ⟨a', k, hR1, hRep', hc⟩
    obtain ⟨k', hR', hk⟩ := hR a a' k hPre hR1
    exact ⟨a', k', hR', hRep', by omega⟩

theorem RefinesB.weaken {Rep : σ → State V → Prop} {Pre Pre' : σ → Prop} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K Lim : ℕ} (h : RefinesB ops Rep Pre c R K Lim)
    (hP : ∀ a, Pre' a → Pre a) : RefinesB ops Rep Pre' c R K Lim :=
  fun a st hPre hRep hbud => h a st (hP a hPre) hRep hbud

/-- A smaller limit is a stronger budget hypothesis. -/
theorem RefinesB.lim {Rep : σ → State V → Prop} {Pre : σ → Prop} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K Lim Lim' : ℕ} (h : RefinesB ops Rep Pre c R K Lim)
    (hL : Lim' ≤ Lim) : RefinesB ops Rep Pre c R K Lim' :=
  fun a st hPre hRep hbud => h a st hPre hRep (fun a' k hR => (hbud a' k hR).trans hL)

/-- **Budgeted sequencing**: needs the second relation to be total on `Pre₂`, so that every
outcome of the first step extends to an outcome of the composite (whose budget is assumed). -/
theorem RefinesB.seq {Rep : σ → State V → Prop} {Pre₁ Pre₂ : σ → Prop} {c₁ c₂ : Stmt}
    {R₁ R₂ : σ → σ → ℕ → Prop} {K Lim : ℕ} (h₁ : RefinesB ops Rep Pre₁ c₁ R₁ K Lim)
    (hmid : ∀ a a' k, Pre₁ a → R₁ a a' k → Pre₂ a') (h₂ : RefinesB ops Rep Pre₂ c₂ R₂ K Lim)
    (htot : Total Pre₂ R₂) :
    RefinesB ops Rep Pre₁ (.seq c₁ c₂) (RelSeq R₁ R₂) K Lim := by
  intro a st hPre hRep hbud
  refine runs_seq ((h₁ a st hPre hRep ?_).mono ?_)
  · intro a' k₁ hR₁
    obtain ⟨a'', k₂, hR₂⟩ := htot a' (hmid a a' k₁ hPre hR₁)
    have := hbud a'' (k₁ + k₂) ⟨a', k₁, k₂, hR₁, hR₂, rfl⟩
    rw [Nat.mul_add] at this
    omega
  · rintro st' ⟨a', k₁, hR₁, hRep', hc₁⟩
    refine (h₂ a' st' (hmid a a' k₁ hPre hR₁) hRep' ?_).mono ?_
    · intro a'' k₂ hR₂
      have := hbud a'' (k₁ + k₂) ⟨a', k₁, k₂, hR₁, hR₂, rfl⟩
      rw [Nat.mul_add] at this
      omega
    · rintro st'' ⟨a'', k₂, hR₂, hRep'', hc₂⟩
      exact ⟨a'', k₁ + k₂, ⟨a', k₁, k₂, hR₁, hR₂, rfl⟩, hRep'', by rw [Nat.mul_add]; omega⟩

/-- Sequential composition of total relations is total. -/
theorem Total.seq {Pre₁ Pre₂ : σ → Prop} {R₁ R₂ : σ → σ → ℕ → Prop} (h₁ : Total Pre₁ R₁)
    (hmid : ∀ a a' k, Pre₁ a → R₁ a a' k → Pre₂ a') (h₂ : Total Pre₂ R₂) :
    Total Pre₁ (RelSeq R₁ R₂) := by
  intro a hPre
  obtain ⟨a', k₁, hR₁⟩ := h₁ a hPre
  obtain ⟨a'', k₂, hR₂⟩ := h₂ a' (hmid a a' k₁ hPre hR₁)
  exact ⟨a'', k₁ + k₂, a', k₁, k₂, hR₁, hR₂, rfl⟩

/-- **Budgeted conditional** (as `Refines.ite`; no totality needed). -/
theorem RefinesB.ite {Rep : σ → State V → Prop} {Pre : σ → Prop} {e : WExpr} {c₁ c₂ : Stmt}
    {R₁ R₂ : σ → σ → ℕ → Prop} {K Lim : ℕ} (b : σ → Prop) [DecidablePred b]
    (htest : ∀ a st, Pre a → Rep a st → ∃ x, evalW st e = some x ∧ (x ≠ 0 ↔ b a))
    (hcharge : ∀ a st, Rep a st → Rep a (st.charge 1))
    (h₁ : RefinesB ops Rep (fun a => Pre a ∧ b a) c₁ R₁ K Lim)
    (h₂ : RefinesB ops Rep (fun a => Pre a ∧ ¬ b a) c₂ R₂ K Lim)
    (hk₁ : ∀ a a' k, Pre a → b a → R₁ a a' k → 1 ≤ k)
    (hk₂ : ∀ a a' k, Pre a → ¬ b a → R₂ a a' k → 1 ≤ k) :
    RefinesB ops Rep Pre (.ite e c₁ c₂) (fun a a' k => (b a ∧ R₁ a a' k) ∨ (¬ b a ∧ R₂ a a' k))
      (K + 1) Lim := by
  intro a st hPre hRep hbud
  obtain ⟨x, hx, hxb⟩ := htest a st hPre hRep
  by_cases hb : b a
  · have hx0 : x ≠ 0 := hxb.mpr hb
    refine runs_ite_true hx hx0 ((h₁ a (st.charge 1) ⟨hPre, hb⟩ (hcharge a st hRep) ?_).mono ?_)
    · intro a' k hR
      have h1 := hbud a' k (Or.inl ⟨hb, hR⟩)
      have := hk₁ a a' k hPre hb hR
      simp only [State.charge]
      nlinarith
    · rintro st' ⟨a', k, hR, hRep', hc⟩
      have := hk₁ a a' k hPre hb hR
      refine ⟨a', k, Or.inl ⟨hb, hR⟩, hRep', ?_⟩
      simp [State.charge] at hc
      nlinarith
  · have hx0 : x = 0 := by
      by_contra h; exact hb (hxb.mp h)
    subst hx0
    refine runs_ite_false hx ((h₂ a (st.charge 1) ⟨hPre, hb⟩ (hcharge a st hRep) ?_).mono ?_)
    · intro a' k hR
      have h1 := hbud a' k (Or.inr ⟨hb, hR⟩)
      have := hk₂ a a' k hPre hb hR
      simp only [State.charge]
      nlinarith
    · rintro st' ⟨a', k, hR, hRep', hc⟩
      have := hk₂ a a' k hPre hb hR
      refine ⟨a', k, Or.inr ⟨hb, hR⟩, hRep', ?_⟩
      simp [State.charge] at hc
      nlinarith

/-- **Budgeted procedure call** (as `Refines.call`). -/
theorem RefinesB.call {Rep : σ → State V → Prop} {Pre : σ → Prop} {p : ℕ} {body : Stmt}
    {R : σ → σ → ℕ → Prop} {K Lim : ℕ}
    (hp : ∀ a st, Pre a → Rep a st → st.procs[p]? = some body)
    (henter : ∀ a st, Rep a st → Rep a st.enter)
    (h : RefinesB ops Rep Pre body R K Lim) (hk : ∀ a a' k, Pre a → R a a' k → 1 ≤ k) :
    RefinesB ops Rep Pre (.call p) R (K + 1) Lim := by
  intro a st hPre hRep hbud
  refine runs_call (hp a st hPre hRep) ((h a st.enter hPre (henter a st hRep) ?_).mono ?_)
  · intro a' k hR
    have h1 := hbud a' k hR
    have := hk a a' k hPre hR
    simp only [State.enter]
    nlinarith
  · rintro st' ⟨a', k, hR, hRep', hc⟩
    have := hk a a' k hPre hR
    refine ⟨a', k, hR, hRep', ?_⟩
    simp [State.enter] at hc
    nlinarith

/-! ### Loops with a stop predicate and a variant -/

/-- Abstract loop runs: iterate the step relation `R` while `¬ done`; the costs add, and the final
(failed) test costs `1`. -/
inductive RelLoop (R : σ → σ → ℕ → Prop) (done : σ → Prop) : σ → σ → ℕ → Prop
  | stop (a : σ) : done a → RelLoop R done a a 1
  | step (a a' a'' : σ) (k k' : ℕ) : ¬ done a → R a a' k → RelLoop R done a' a'' k' →
      RelLoop R done a a'' (k + k')

/-- Loop runs are total if the step relation is total on non-final `Inv` states, preserves `Inv`,
and decreases a variant `μ`. -/
theorem RelLoop.total {R : σ → σ → ℕ → Prop} {done : σ → Prop} (Inv : σ → Prop) (μ : σ → ℕ)
    (hstep : ∀ a a' k, Inv a → ¬ done a → R a a' k → Inv a' ∧ μ a' < μ a)
    (htot : ∀ a, Inv a → ¬ done a → ∃ a' k, R a a' k) :
    Total Inv (RelLoop R done) := by
  have key : ∀ N a, μ a ≤ N → Inv a → ∃ a' k, RelLoop R done a a' k := by
    intro N
    induction N with
    | zero =>
      intro a hμ hI
      by_cases hd : done a
      · exact ⟨a, 1, .stop a hd⟩
      · obtain ⟨a', k, hR⟩ := htot a hI hd
        have := (hstep a a' k hI hd hR).2
        omega
    | succ N ih =>
      intro a hμ hI
      by_cases hd : done a
      · exact ⟨a, 1, .stop a hd⟩
      · obtain ⟨a', k, hR⟩ := htot a hI hd
        obtain ⟨hI', hμ'⟩ := hstep a a' k hI hd hR
        obtain ⟨a'', k', hL⟩ := ih a' (by omega) hI'
        exact ⟨a'', k + k', .step a a' a'' k k' hd hR hL⟩
  intro a hI
  exact key (μ a) a le_rfl hI

/-- **Budgeted `while` loop with a variant**: the test is `≠ 0` exactly on non-final states, the body
refines one step `R` (abstract cost `≥ 1`, paying for the test), `R` is total on non-final `Inv`
states, preserves `Inv` and decreases the variant `μ`.  Then the loop refines `RelLoop R done`
with factor `K + 1`. -/
theorem RefinesB.loopVar {Rep : σ → State V → Prop} {Inv : σ → Prop} {e : WExpr} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K Lim : ℕ} (done : σ → Prop) (μ : σ → ℕ)
    (htest : ∀ a st, Inv a → Rep a st → ∃ x, evalW st e = some x ∧ (x ≠ 0 ↔ ¬ done a))
    (hcharge : ∀ a st, Rep a st → Rep a (st.charge 1))
    (hbody : RefinesB ops Rep (fun a => Inv a ∧ ¬ done a) c R K Lim)
    (hstep : ∀ a a' k, Inv a → ¬ done a → R a a' k → Inv a' ∧ μ a' < μ a ∧ 1 ≤ k)
    (htot : ∀ a, Inv a → ¬ done a → ∃ a' k, R a a' k) :
    RefinesB ops Rep Inv (.while e c) (RelLoop R done) (K + 1) Lim := by
  have hLtot : Total Inv (RelLoop R done) :=
    RelLoop.total Inv μ (fun a a' k h1 h2 h3 => ⟨(hstep a a' k h1 h2 h3).1,
      (hstep a a' k h1 h2 h3).2.1⟩) htot
  intro a0 st0 hI0 hRep0 hbud0
  -- invariant (indexed by the variant): the run so far is an abstract prefix of cost `k`, so every
  -- completion from the current state `a` is a completion from `a0` of cost `k + _`
  refine runs_while_nat (fun n st => ∃ a k, μ a = n ∧ Inv a ∧ Rep a st ∧
      st.cost ≤ st0.cost + (K + 1) * k ∧
      (∀ a'' k'', RelLoop R done a a'' k'' → RelLoop R done a0 a'' (k + k''))) _ ?_ (μ a0) st0
    ⟨a0, 0, rfl, hI0, hRep0, by simp, fun a'' k'' h => by simpa using h⟩
  rintro n st ⟨a, k, rfl, hI, hRep, hc, hpref⟩
  obtain ⟨x, hx, hxd⟩ := htest a st hI hRep
  refine ⟨x, hx, fun hx0 => ?_, fun hx0 => ?_⟩
  · have hnd : ¬ done a := hxd.mp hx0
    refine (hbody a (st.charge 1) ⟨hI, hnd⟩ (hcharge a st hRep) ?_).mono ?_
    · intro a' k' hR
      obtain ⟨hI', -, hk1⟩ := hstep a a' k' hI hnd hR
      obtain ⟨a'', k'', hL⟩ := hLtot a' hI'
      have hb := hbud0 a'' (k + (k' + k'')) (hpref a'' (k' + k'') (.step a a' a'' k' k'' hnd hR hL))
      have e1 : (K + 1) * (k + (k' + k'')) = (K + 1) * k + K * k' + k' + (K + 1) * k'' := by ring
      simp only [State.charge]
      omega
    · rintro st' ⟨a', k', hR, hRep', hc'⟩
      obtain ⟨hI', hμ, hk1⟩ := hstep a a' k' hI hnd hR
      refine ⟨μ a', hμ, a', k + k', rfl, hI', hRep', ?_, ?_⟩
      · have e1 : (K + 1) * (k + k') = (K + 1) * k + K * k' + k' := by ring
        simp only [State.charge] at hc'
        omega
      · intro a'' k'' hL
        have := hpref a'' (k' + k'') (.step a a' a'' k' k'' hnd hR hL)
        rwa [← Nat.add_assoc] at this
  · have hd : done a := by
      by_contra h; exact hxd.mpr h hx0
    refine ⟨a, k + 1, hpref a 1 (.stop a hd), hcharge a st hRep, ?_⟩
    have e1 : (K + 1) * (k + 1) = (K + 1) * k + K + 1 := by ring
    simp only [State.charge]
    omega

/-! ### Amortized (potential-aware) budgeted refinement

For structures with amortized costs (package L3, `D`), the machine cost of a step plus the change
of a potential `Φ` (a function of the abstract state; concrete layouts enter through ghost fields
of the abstract state) is bounded by `K` times the step's amortized abstract cost.  With `Φ = 0`
this is `RefinesB`. -/

/-- **Amortized budgeted refinement**. -/
def RefinesP (ops : VOps V) (Rep : σ → State V → Prop) (Pre : σ → Prop) (c : Stmt)
    (R : σ → σ → ℕ → Prop) (K Lim : ℕ) (Φ : σ → ℕ) : Prop :=
  ∀ a st, Pre a → Rep a st → (∀ a' k, R a a' k → st.cost + Φ a + K * k ≤ Lim) →
    Runs ops c st (fun st' => ∃ a' k, R a a' k ∧ Rep a' st' ∧
      st'.cost + Φ a' ≤ st.cost + Φ a + K * k)

/-- A budgeted refinement of a step that does not increase the potential is amortized. -/
theorem RefinesB.toP {Rep : σ → State V → Prop} {Pre : σ → Prop} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K Lim : ℕ} (Φ : σ → ℕ) (h : RefinesB ops Rep Pre c R K Lim)
    (hΦ : ∀ a a' k, Pre a → R a a' k → Φ a' ≤ Φ a) : RefinesP ops Rep Pre c R K Lim Φ := by
  intro a st hPre hRep hbud
  refine (h a st hPre hRep (fun a' k hR => ?_)).mono ?_
  · have := hbud a' k hR; omega
  · rintro st' ⟨a', k, hR, hRep', hc⟩
    have := hΦ a a' k hPre hR
    exact ⟨a', k, hR, hRep', by omega⟩

/-- With zero potential, amortized refinement is budgeted refinement. -/
theorem RefinesP.toB {Rep : σ → State V → Prop} {Pre : σ → Prop} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K Lim : ℕ} (h : RefinesP ops Rep Pre c R K Lim (fun _ => 0)) :
    RefinesB ops Rep Pre c R K Lim := by
  intro a st hPre hRep hbud
  refine (h a st hPre hRep (fun a' k hR => by have := hbud a' k hR; omega)).mono ?_
  rintro st' ⟨a', k, hR, hRep', hc⟩
  exact ⟨a', k, hR, hRep', by omega⟩

theorem RefinesP.mono {Rep : σ → State V → Prop} {Pre : σ → Prop} {c : Stmt}
    {R R' : σ → σ → ℕ → Prop} {K K' Lim : ℕ} {Φ : σ → ℕ} (h : RefinesP ops Rep Pre c R K Lim Φ)
    (hR : ∀ a a' k, Pre a → R a a' k → ∃ k', R' a a' k' ∧ K * k ≤ K' * k') :
    RefinesP ops Rep Pre c R' K' Lim Φ := by
  intro a st hPre hRep hbud
  refine (h a st hPre hRep ?_).mono ?_
  · intro a' k hR1
    obtain ⟨k', hR', hk⟩ := hR a a' k hPre hR1
    have := hbud a' k' hR'
    omega
  · rintro st' ⟨a', k, hR1, hRep', hc⟩
    obtain ⟨k', hR', hk⟩ := hR a a' k hPre hR1
    exact ⟨a', k', hR', hRep', by omega⟩

theorem RefinesP.weaken {Rep : σ → State V → Prop} {Pre Pre' : σ → Prop} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K Lim : ℕ} {Φ : σ → ℕ} (h : RefinesP ops Rep Pre c R K Lim Φ)
    (hP : ∀ a, Pre' a → Pre a) : RefinesP ops Rep Pre' c R K Lim Φ :=
  fun a st hPre hRep hbud => h a st (hP a hPre) hRep hbud

theorem RefinesP.lim {Rep : σ → State V → Prop} {Pre : σ → Prop} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K Lim Lim' : ℕ} {Φ : σ → ℕ} (h : RefinesP ops Rep Pre c R K Lim Φ)
    (hL : Lim' ≤ Lim) : RefinesP ops Rep Pre c R K Lim' Φ :=
  fun a st hPre hRep hbud => h a st hPre hRep (fun a' k hR => (hbud a' k hR).trans hL)

/-- **Amortized budgeted sequencing** (potentials telescope). -/
theorem RefinesP.seq {Rep : σ → State V → Prop} {Pre₁ Pre₂ : σ → Prop} {c₁ c₂ : Stmt}
    {R₁ R₂ : σ → σ → ℕ → Prop} {K Lim : ℕ} {Φ : σ → ℕ} (h₁ : RefinesP ops Rep Pre₁ c₁ R₁ K Lim Φ)
    (hmid : ∀ a a' k, Pre₁ a → R₁ a a' k → Pre₂ a') (h₂ : RefinesP ops Rep Pre₂ c₂ R₂ K Lim Φ)
    (htot : Total Pre₂ R₂) :
    RefinesP ops Rep Pre₁ (.seq c₁ c₂) (RelSeq R₁ R₂) K Lim Φ := by
  intro a st hPre hRep hbud
  refine runs_seq ((h₁ a st hPre hRep ?_).mono ?_)
  · intro a' k₁ hR₁
    obtain ⟨a'', k₂, hR₂⟩ := htot a' (hmid a a' k₁ hPre hR₁)
    have := hbud a'' (k₁ + k₂) ⟨a', k₁, k₂, hR₁, hR₂, rfl⟩
    rw [Nat.mul_add] at this
    omega
  · rintro st' ⟨a', k₁, hR₁, hRep', hc₁⟩
    refine (h₂ a' st' (hmid a a' k₁ hPre hR₁) hRep' ?_).mono ?_
    · intro a'' k₂ hR₂
      have := hbud a'' (k₁ + k₂) ⟨a', k₁, k₂, hR₁, hR₂, rfl⟩
      rw [Nat.mul_add] at this
      omega
    · rintro st'' ⟨a'', k₂, hR₂, hRep'', hc₂⟩
      exact ⟨a'', k₁ + k₂, ⟨a', k₁, k₂, hR₁, hR₂, rfl⟩, hRep'', by rw [Nat.mul_add]; omega⟩

/-- **Amortized budgeted conditional**. -/
theorem RefinesP.ite {Rep : σ → State V → Prop} {Pre : σ → Prop} {e : WExpr} {c₁ c₂ : Stmt}
    {R₁ R₂ : σ → σ → ℕ → Prop} {K Lim : ℕ} {Φ : σ → ℕ} (b : σ → Prop) [DecidablePred b]
    (htest : ∀ a st, Pre a → Rep a st → ∃ x, evalW st e = some x ∧ (x ≠ 0 ↔ b a))
    (hcharge : ∀ a st, Rep a st → Rep a (st.charge 1))
    (h₁ : RefinesP ops Rep (fun a => Pre a ∧ b a) c₁ R₁ K Lim Φ)
    (h₂ : RefinesP ops Rep (fun a => Pre a ∧ ¬ b a) c₂ R₂ K Lim Φ)
    (hk₁ : ∀ a a' k, Pre a → b a → R₁ a a' k → 1 ≤ k)
    (hk₂ : ∀ a a' k, Pre a → ¬ b a → R₂ a a' k → 1 ≤ k) :
    RefinesP ops Rep Pre (.ite e c₁ c₂) (fun a a' k => (b a ∧ R₁ a a' k) ∨ (¬ b a ∧ R₂ a a' k))
      (K + 1) Lim Φ := by
  intro a st hPre hRep hbud
  obtain ⟨x, hx, hxb⟩ := htest a st hPre hRep
  by_cases hb : b a
  · have hx0 : x ≠ 0 := hxb.mpr hb
    refine runs_ite_true hx hx0 ((h₁ a (st.charge 1) ⟨hPre, hb⟩ (hcharge a st hRep) ?_).mono ?_)
    · intro a' k hR
      have h1 := hbud a' k (Or.inl ⟨hb, hR⟩)
      have := hk₁ a a' k hPre hb hR
      simp only [State.charge]
      nlinarith
    · rintro st' ⟨a', k, hR, hRep', hc⟩
      have := hk₁ a a' k hPre hb hR
      refine ⟨a', k, Or.inl ⟨hb, hR⟩, hRep', ?_⟩
      simp [State.charge] at hc
      nlinarith
  · have hx0 : x = 0 := by
      by_contra h; exact hb (hxb.mp h)
    subst hx0
    refine runs_ite_false hx ((h₂ a (st.charge 1) ⟨hPre, hb⟩ (hcharge a st hRep) ?_).mono ?_)
    · intro a' k hR
      have h1 := hbud a' k (Or.inr ⟨hb, hR⟩)
      have := hk₂ a a' k hPre hb hR
      simp only [State.charge]
      nlinarith
    · rintro st' ⟨a', k, hR, hRep', hc⟩
      have := hk₂ a a' k hPre hb hR
      refine ⟨a', k, Or.inr ⟨hb, hR⟩, hRep', ?_⟩
      simp [State.charge] at hc
      nlinarith

/-- **Amortized budgeted procedure call**. -/
theorem RefinesP.call {Rep : σ → State V → Prop} {Pre : σ → Prop} {p : ℕ} {body : Stmt}
    {R : σ → σ → ℕ → Prop} {K Lim : ℕ} {Φ : σ → ℕ}
    (hp : ∀ a st, Pre a → Rep a st → st.procs[p]? = some body)
    (henter : ∀ a st, Rep a st → Rep a st.enter)
    (h : RefinesP ops Rep Pre body R K Lim Φ) (hk : ∀ a a' k, Pre a → R a a' k → 1 ≤ k) :
    RefinesP ops Rep Pre (.call p) R (K + 1) Lim Φ := by
  intro a st hPre hRep hbud
  refine runs_call (hp a st hPre hRep) ((h a st.enter hPre (henter a st hRep) ?_).mono ?_)
  · intro a' k hR
    have h1 := hbud a' k hR
    have := hk a a' k hPre hR
    simp only [State.enter]
    nlinarith
  · rintro st' ⟨a', k, hR, hRep', hc⟩
    have := hk a a' k hPre hR
    refine ⟨a', k, hR, hRep', ?_⟩
    simp [State.enter] at hc
    nlinarith

/-- **Amortized budgeted `while` loop with a variant**. -/
theorem RefinesP.loopVar {Rep : σ → State V → Prop} {Inv : σ → Prop} {e : WExpr} {c : Stmt}
    {R : σ → σ → ℕ → Prop} {K Lim : ℕ} {Φ : σ → ℕ} (done : σ → Prop) (μ : σ → ℕ)
    (htest : ∀ a st, Inv a → Rep a st → ∃ x, evalW st e = some x ∧ (x ≠ 0 ↔ ¬ done a))
    (hcharge : ∀ a st, Rep a st → Rep a (st.charge 1))
    (hbody : RefinesP ops Rep (fun a => Inv a ∧ ¬ done a) c R K Lim Φ)
    (hstep : ∀ a a' k, Inv a → ¬ done a → R a a' k → Inv a' ∧ μ a' < μ a ∧ 1 ≤ k)
    (htot : ∀ a, Inv a → ¬ done a → ∃ a' k, R a a' k) :
    RefinesP ops Rep Inv (.while e c) (RelLoop R done) (K + 1) Lim Φ := by
  have hLtot : Total Inv (RelLoop R done) :=
    RelLoop.total Inv μ (fun a a' k h1 h2 h3 => ⟨(hstep a a' k h1 h2 h3).1,
      (hstep a a' k h1 h2 h3).2.1⟩) htot
  intro a0 st0 hI0 hRep0 hbud0
  refine runs_while_nat (fun n st => ∃ a k, μ a = n ∧ Inv a ∧ Rep a st ∧
      st.cost + Φ a ≤ st0.cost + Φ a0 + (K + 1) * k ∧
      (∀ a'' k'', RelLoop R done a a'' k'' → RelLoop R done a0 a'' (k + k''))) _ ?_ (μ a0) st0
    ⟨a0, 0, rfl, hI0, hRep0, by simp, fun a'' k'' h => by simpa using h⟩
  rintro n st ⟨a, k, rfl, hI, hRep, hc, hpref⟩
  obtain ⟨x, hx, hxd⟩ := htest a st hI hRep
  refine ⟨x, hx, fun hx0 => ?_, fun hx0 => ?_⟩
  · have hnd : ¬ done a := hxd.mp hx0
    refine (hbody a (st.charge 1) ⟨hI, hnd⟩ (hcharge a st hRep) ?_).mono ?_
    · intro a' k' hR
      obtain ⟨hI', -, hk1⟩ := hstep a a' k' hI hnd hR
      obtain ⟨a'', k'', hL⟩ := hLtot a' hI'
      have hb := hbud0 a'' (k + (k' + k'')) (hpref a'' (k' + k'') (.step a a' a'' k' k'' hnd hR hL))
      have e1 : (K + 1) * (k + (k' + k'')) = (K + 1) * k + K * k' + k' + (K + 1) * k'' := by ring
      simp only [State.charge]
      omega
    · rintro st' ⟨a', k', hR, hRep', hc'⟩
      obtain ⟨hI', hμ, hk1⟩ := hstep a a' k' hI hnd hR
      refine ⟨μ a', hμ, a', k + k', rfl, hI', hRep', ?_, ?_⟩
      · have e1 : (K + 1) * (k + k') = (K + 1) * k + K * k' + k' := by ring
        simp only [State.charge] at hc'
        omega
      · intro a'' k'' hL
        have := hpref a'' (k' + k'') (.step a a' a'' k' k'' hnd hR hL)
        rwa [← Nat.add_assoc] at this
  · have hd : done a := by
      by_contra h; exact hxd.mpr h hx0
    refine ⟨a, k + 1, hpref a 1 (.stop a hd), hcharge a st hRep, ?_⟩
    have e1 : (K + 1) * (k + 1) = (K + 1) * k + K + 1 := by ring
    simp only [State.charge]
    omega

end Frontier.RAM
