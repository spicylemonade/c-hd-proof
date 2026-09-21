import Frontier.CHD.FPBind
import Frontier.CHD.BMTrace

/-!
# Frontier.CHD.FPDel — the FindPivots deletion counter of a traced run (`Valid.del_disj`)

Owner: agent-05 (C-HD package L2).  NON-GATE (Layer A, L5 glue).

The persistent FindPivots state of `BM.BMSSPC` is the deleted-edge set `φ`, threaded through all
calls in execution order.  Each call record's FindPivots data carries its deletion interval
`din ω ⊆ dout ω` (for `fpC`: `ω.Din`, `ω.Dout`).  The call's deletion counter is
`delOf r := dout ω \ din ω` (`∅` for base calls).

* `bmsspC_chain`: in EVERY derivation of `BMSSPC` from `φ` to `φ'`, the deletion intervals of the
  log are chained in log order from `φ` to `φ'` (the log lists calls in execution order);
* `Chain.pairwise`: chained intervals have pairwise disjoint differences;
* `counters_del_disj`: the field `CostAggregate.CallCounters.Valid.del_disj` for
  `Log.counters hL Fo Cr Be (delOf …)`;
* `fpC_chain_hyp`: `fpC` satisfies the interval hypothesis.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n} {Ω : Type}

section Chain

variable (din dout : Ω → Finset (Fin G.m))

/-- The FindPivots deletion counter of a call record (`∅` for base calls). -/
def delOf (r : CallRec G s Ω) : Finset (Fin G.m) :=
  match r.fp with
  | none => ∅
  | some ω => dout ω \ din ω

/-- The deletion intervals of a log are chained, in log order, from `a` to `b`. -/
def Chain : Finset (Fin G.m) → Log G s Ω → Finset (Fin G.m) → Prop
  | a, [], b => a ⊆ b
  | a, x :: rest, b =>
    match x.2.fp with
    | none => Chain a rest b
    | some ω => a ⊆ din ω ∧ din ω ⊆ dout ω ∧ Chain (dout ω) rest b

variable {din dout}

theorem chain_nil {a b : Finset (Fin G.m)} : Chain din dout a ([] : Log G s Ω) b ↔ a ⊆ b := Iff.rfl

theorem chain_cons_none {a b : Finset (Fin G.m)} {x : List ℕ × CallRec G s Ω}
    {rest : Log G s Ω} (hx : x.2.fp = none) :
    Chain din dout a (x :: rest) b ↔ Chain din dout a rest b := by
  simp only [Chain, hx]

theorem chain_cons_some {a b : Finset (Fin G.m)} {x : List ℕ × CallRec G s Ω}
    {rest : Log G s Ω} {ω : Ω} (hx : x.2.fp = some ω) :
    Chain din dout a (x :: rest) b ↔ a ⊆ din ω ∧ din ω ⊆ dout ω ∧ Chain din dout (dout ω) rest b := by
  simp only [Chain, hx]

theorem Chain.le : ∀ {a b : Finset (Fin G.m)} {lg : Log G s Ω}, Chain din dout a lg b → a ⊆ b
  | _, _, [], h => h
  | _, _, x :: rest, h => by
    cases hx : x.2.fp with
    | none => exact Chain.le ((chain_cons_none hx).mp h)
    | some ω =>
      obtain ⟨h1, h2, h3⟩ := (chain_cons_some hx).mp h
      exact h1.trans (h2.trans (Chain.le h3))

theorem Chain.mono_left : ∀ {a a' b : Finset (Fin G.m)} {lg : Log G s Ω}, a' ⊆ a →
    Chain din dout a lg b → Chain din dout a' lg b
  | _, _, _, [], ha, h => ha.trans h
  | _, _, _, x :: rest, ha, h => by
    cases hx : x.2.fp with
    | none => exact (chain_cons_none hx).mpr (Chain.mono_left ha ((chain_cons_none hx).mp h))
    | some ω =>
      obtain ⟨h1, h2, h3⟩ := (chain_cons_some hx).mp h
      exact (chain_cons_some hx).mpr ⟨ha.trans h1, h2, h3⟩

theorem Chain.append : ∀ {a b c : Finset (Fin G.m)} {l1 : Log G s Ω} {l2 : Log G s Ω},
    Chain din dout a l1 b → Chain din dout b l2 c → Chain din dout a (l1 ++ l2) c
  | _, _, _, [], _, h1, h2 => Chain.mono_left h1 h2
  | _, _, _, x :: rest, _, h1, h2 => by
    cases hx : x.2.fp with
    | none =>
      exact (chain_cons_none hx).mpr (Chain.append ((chain_cons_none hx).mp h1) h2)
    | some ω =>
      obtain ⟨g1, g2, g3⟩ := (chain_cons_some hx).mp h1
      exact (chain_cons_some hx).mpr ⟨g1, g2, Chain.append g3 h2⟩

theorem Chain.shift (i : ℕ) : ∀ {a b : Finset (Fin G.m)} {lg : Log G s Ω},
    Chain din dout a lg b → Chain din dout a (lg.shift i) b
  | _, _, [], h => h
  | _, _, x :: rest, h => by
    have hs : Log.shift i (x :: rest) = (i :: x.1, x.2) :: Log.shift i rest := rfl
    rw [hs]
    cases hx : x.2.fp with
    | none =>
      exact (chain_cons_none (x := (i :: x.1, x.2)) hx).mpr
        (Chain.shift i ((chain_cons_none hx).mp h))
    | some ω =>
      obtain ⟨g1, g2, g3⟩ := (chain_cons_some hx).mp h
      exact (chain_cons_some (x := (i :: x.1, x.2)) hx).mpr ⟨g1, g2, Chain.shift i g3⟩

/-- Every later deletion counter is disjoint from the chain's start. -/
theorem Chain.disj_start : ∀ {a b : Finset (Fin G.m)} {lg : Log G s Ω},
    Chain din dout a lg b → ∀ y ∈ lg, Disjoint a (delOf din dout y.2)
  | _, _, [], _, y, hy => absurd hy List.not_mem_nil
  | _, _, x :: rest, h, y, hy => by
    cases hx : x.2.fp with
    | none =>
      have h' := (chain_cons_none hx).mp h
      rcases List.mem_cons.mp hy with rfl | hy
      · simp [delOf, hx]
      · exact Chain.disj_start h' y hy
    | some ω =>
      obtain ⟨g1, g2, g3⟩ := (chain_cons_some hx).mp h
      rcases List.mem_cons.mp hy with rfl | hy
      · simp only [delOf, hx]
        exact Finset.disjoint_of_subset_left g1 Finset.disjoint_sdiff
      · exact (Chain.disj_start g3 y hy).mono_left (g1.trans g2)

/-- **Chained intervals have pairwise disjoint deletion counters.** -/
theorem Chain.pairwise : ∀ {a b : Finset (Fin G.m)} {lg : Log G s Ω},
    Chain din dout a lg b → lg.Pairwise (fun x y => Disjoint (delOf din dout x.2) (delOf din dout y.2))
  | _, _, [], _ => List.Pairwise.nil
  | _, _, x :: rest, h => by
    cases hx : x.2.fp with
    | none =>
      refine List.Pairwise.cons (fun y _ => ?_) (Chain.pairwise ((chain_cons_none hx).mp h))
      simp [delOf, hx]
    | some ω =>
      obtain ⟨g1, g2, g3⟩ := (chain_cons_some hx).mp h
      refine List.Pairwise.cons (fun y hy => ?_) (Chain.pairwise g3)
      have hd : delOf din dout x.2 ⊆ dout ω := by simp only [delOf, hx]; exact Finset.sdiff_subset
      exact (Chain.disj_start g3 y hy).mono_left hd

end Chain

theorem pairwise_mem_ne {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {x y : α}, x ∈ l → y ∈ l → x ≠ y → R x y ∨ R y x
  | [], _, _, _, hx, _, _ => absurd hx List.not_mem_nil
  | a :: l, h, x, y, hx, hy, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp hx with h1 | h1 <;> rcases List.mem_cons.mp hy with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · subst h1; exact Or.inl (h.1 y h2)
    · subst h2; exact Or.inr (h.1 x h1)
    · exact pairwise_mem_ne h.2 h1 h2 hne

/-! ## The chain holds for every traced derivation -/

section Run

variable {din dout : Ω → Finset (Fin G.m)} {DC : DCost}

theorem loopC_chain {sub : SubRelC G s (Finset (Fin G.m)) Ω} {lv : ℕ} {B : WLab G s} {τ : ℕ}
    (hsub : ∀ Blow B S d φ res φ' lg, sub Blow B S d φ res φ' lg → Chain din dout φ lg φ')
    {p : ℕ} : ∀ {i : ℕ} {σ : LState G s p} {φ : Finset (Fin G.m)} {σ' : LState G s p}
      {φ' : Finset (Fin G.m)} {lg : Log G s Ω} {J : Finset (Fin G.m)} {cm c : ℕ},
      LoopC G s DC sub lv B τ i σ φ σ' φ' lg J cm c → Chain din dout φ lg φ' := by
  intro i σ φ σ' φ' lg J cm c h
  induction h with
  | stop => exact subset_rfl
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di d1 L' piv' lg lg' J' cm c =>
    -- premises are fetched by type, so extra `LoopC.step` premises do not break this proof
    have hs : sub σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, d1) φ1 lg := by assumption
    have ih : Chain din dout φ1 lg' φ' := by assumption
    exact (Chain.shift i (hsub _ _ _ _ _ _ _ _ hs)).append ih

/-- **Execution-order chain** of every derivation of the traced relation, for any cost-indexed
FindPivots relation that records its deletion interval. -/
theorem bmsspC_chain {FPC : FPRelC G s (Finset (Fin G.m)) Ω}
    (hFPC : ∀ l Blow B S d0 φ d1 p P Q W φ' ω c, FPC l Blow B S d0 φ d1 p P Q W φ' ω c →
      din ω = φ ∧ dout ω = φ' ∧ φ ⊆ φ') (τ : ℕ → ℕ) :
    ∀ (l : ℕ) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (φ : Finset (Fin G.m))
      (res : Result G s) (φ' : Finset (Fin G.m)) (lg : Log G s Ω),
      BMSSPC G s FPC DC τ l Blow B S d φ res φ' lg → Chain din dout φ lg φ'
  | 0, Blow, B, S, d, φ, res, φ', lg, hrel => by
    obtain ⟨st, c, -, -, -, -, -, -, rfl, rfl⟩ := hrel
    exact (chain_cons_none rfl).mpr subset_rfl
  | l + 1, Blow, B, S, d, φ, res, φ', lg, hrel => by
    obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L, B'f, T6, W', hfp, -, hloop,
      -, -, -, -, -, -, rfl⟩ := hrel
    obtain ⟨h1, h2, h3⟩ := hFPC _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfp
    have hc := loopC_chain (din := din) (dout := dout) (bmsspC_chain hFPC τ l) hloop
    refine (chain_cons_some rfl).mpr ⟨h1 ▸ subset_rfl, h1 ▸ h2 ▸ h3, h2 ▸ hc⟩

/-- **`Valid.del_disj`** for the counters of a traced run whose log is chained. -/
theorem counters_del_disj {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s Ω} (hL : LogInv τ L0 lg)
    {a b : Finset (Fin G.m)} (hc : Chain din dout a lg b)
    (Fo : CallRec G s Ω → Finset (Fin G.n)) (Cr Be : CallRec G s Ω → Finset (Fin G.m)) :
    ∀ X X', X ≠ X' → Disjoint ((Log.counters hL Fo Cr Be (delOf din dout)).Del X)
      ((Log.counters hL Fo Cr Be (delOf din dout)).Del X') := by
  intro X X' hne
  show Disjoint (delOf din dout (lg.recOf X)) (delOf din dout (lg.recOf X'))
  have hx := recOf_mem X
  have hx' := recOf_mem X'
  have hne' : (X.1, lg.recOf X) ≠ (X'.1, lg.recOf X') := fun h =>
    hne (Subtype.ext (congrArg Prod.fst h))
  rcases pairwise_mem_ne hc.pairwise hx hx' hne' with h | h
  · exact h
  · exact h.symm

end Run

/-! ## The FindPivots-HD instance -/

/-- `fpC` records its deletion interval. -/
theorem fpC_chain_hyp {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}
    (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s)) :
    ∀ l Blow B S d0 φ d1 p P Q W φ' ω c, fpC G s out k hins hext l Blow B S d0 φ d1 p P Q W φ' ω c →
      (fun ω : FPData G s => ω.Din) ω = φ ∧ (fun ω : FPData G s => ω.Dout) ω = φ' ∧ φ ⊆ φ' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => fpC_interval hout hsort h

end BM
end CHD
end Frontier
