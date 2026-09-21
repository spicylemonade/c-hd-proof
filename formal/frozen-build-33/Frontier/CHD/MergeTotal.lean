import Frontier.CHD.BMTrace
import Frontier.CostSkeleton

/-!
# Frontier.CHD.MergeTotal — the `D`-merge total (tracker O23, `total_le_Tchd`'s `hM0`)

Owner: agent-05 (COORD G2-5 D5(b)).  NON-GATE (Layer A counting).

Under agent-04's lazy-split DS' (L3-4: stack index, `Merge` pushes groups, its actual work is paid
by the child's block potential) every `Merge` has amortized cost `O(1)`, so a call's merge cost is
at most `cm · #children`.  Every call returns a nonempty `U`, and calls of one depth have disjoint
`U`'s, so there are at most `(Lmax + 1) · |V|` calls:

* `card_level_le`: at most `|V|` calls per depth (nonempty disjoint `U`'s);
* `card_calls_le`: at most `(Lmax + 1) · |V|` calls;
* `sum_children_le`: `Σ_X #children X ≤ #calls`;
* `merge_total_le`: `Σ_X mergeCost X ≤ cm · (Lmax + 1) · |V|`;
* `hM0_of_children`: the hypothesis `hM0 : M0 ≤ a (n · LF + m)` of `CostFinal.total_le_Tchd` for
  `M0 := cm · (Lmax + 1) · |V|`, from `Lmax + 1 ≤ 2 LF` and `|V| ≤ a' n`.
-/

namespace Frontier.CHD.MergeTotal

open Finset Frontier.CostCharging

variable {ι V α : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] [DecidableEq V] [LinearOrder α]

variable (F : CallForest ι V α)

/-- At most `|V|` calls per depth when every `U` is nonempty. -/
theorem card_level_le (hne : ∀ X, (F.U X).Nonempty) (j : ℕ) :
    (univ.filter (fun X => F.depth X = j)).card ≤ Fintype.card V := by
  calc (univ.filter (fun X => F.depth X = j)).card
      = ∑ X ∈ univ.filter (fun X => F.depth X = j), 1 := by simp
    _ ≤ ∑ X ∈ univ.filter (fun X => F.depth X = j), (F.U X).card :=
        Finset.sum_le_sum fun X _ => Finset.card_pos.mpr (hne X)
    _ ≤ Fintype.card V := F.level_card_sum_le j

/-- At most `(Lmax + 1) · |V|` calls. -/
theorem card_calls_le (hne : ∀ X, (F.U X).Nonempty) {Lmax : ℕ} (hd : ∀ X, F.depth X ≤ Lmax) :
    Fintype.card ι ≤ (Lmax + 1) * Fintype.card V := by
  classical
  have hmaps : ∀ X ∈ (univ : Finset ι), F.depth X ∈ Finset.range (Lmax + 1) := by
    intro X _; simp only [Finset.mem_range]; have := hd X; omega
  have hsplit := (Finset.card_eq_sum_card_fiberwise hmaps)
  rw [Finset.card_univ] at hsplit
  rw [hsplit]
  calc ∑ j ∈ Finset.range (Lmax + 1), (univ.filter (fun X => F.depth X = j)).card
      ≤ ∑ _j ∈ Finset.range (Lmax + 1), Fintype.card V :=
        Finset.sum_le_sum fun j _ => card_level_le F hne j
    _ = (Lmax + 1) * Fintype.card V := by simp

/-- Every call is the child of at most one call: `Σ_X #children X ≤ #calls`. -/
theorem sum_children_le :
    ∑ X, (univ.filter (fun Y => F.parent Y = some X)).card ≤ Fintype.card ι := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro X _ X' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro Y hY hY'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY hY'
    rw [hY] at hY'
    exact hne (Option.some.inj hY')

/-- **Merge total**: if every call's merge cost is at most `cm` per child, the total is at most
`cm · (Lmax + 1) · |V|`. -/
theorem merge_total_le (hne : ∀ X, (F.U X).Nonempty) {Lmax : ℕ} (hd : ∀ X, F.depth X ≤ Lmax)
    (mergeCost : ι → ℕ) (cm : ℕ)
    (hm : ∀ X, mergeCost X ≤ cm * (univ.filter (fun Y => F.parent Y = some X)).card) :
    ∑ X, mergeCost X ≤ cm * ((Lmax + 1) * Fintype.card V) := by
  calc ∑ X, mergeCost X ≤ ∑ X, cm * (univ.filter (fun Y => F.parent Y = some X)).card :=
        Finset.sum_le_sum fun X _ => hm X
    _ = cm * ∑ X, (univ.filter (fun Y => F.parent Y = some X)).card := by rw [Finset.mul_sum]
    _ ≤ cm * Fintype.card ι := Nat.mul_le_mul_left _ (sum_children_le F)
    _ ≤ cm * ((Lmax + 1) * Fintype.card V) := Nat.mul_le_mul_left _ (card_calls_le F hne hd)

/-- **`hM0` of `CostFinal.total_le_Tchd`** for `M0 := cm · (Lmax + 1) · |V|`. -/
theorem hM0_of_children {n m Lmax cm a' : ℕ} (hL : Lmax + 1 ≤ 2 * Frontier.CostSkeleton.LF n m)
    (hV : Fintype.card V ≤ a' * n) :
    cm * ((Lmax + 1) * Fintype.card V) ≤ (2 * cm * a') * (n * Frontier.CostSkeleton.LF n m + m) := by
  calc cm * ((Lmax + 1) * Fintype.card V) ≤ cm * ((2 * Frontier.CostSkeleton.LF n m) * (a' * n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hL hV)
    _ = (2 * cm * a') * (n * Frontier.CostSkeleton.LF n m) := by ring
    _ ≤ (2 * cm * a') * (n * Frontier.CostSkeleton.LF n m + m) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)

end Frontier.CHD.MergeTotal


/-! ## The trace facts, for every derivation of the traced relation `BM.BMSSPC` -/

namespace Frontier.CHD.BM

open Frontier Graph Finset

variable {G : Graph} {s : Fin G.n} {Φ Ω : Type} {DC : DCost}

/-- (T1) Every sub-call has a nonempty frontier (`S0 ⊆ expand σ S0 Bi` and a nonempty `D` pulls a
key). -/
theorem loopC_S_ne {sub : SubRelC G s Φ Ω} {lv : ℕ} {B : WLab G s} {τ : ℕ}
    (hsub : ∀ Blow B S d φ res φ' lg, sub Blow B S d φ res φ' lg → S.Nonempty →
      ∀ q r, (q, r) ∈ lg → r.S.Nonempty) {p : ℕ} :
    ∀ {i : ℕ} {σ : LState G s p} {φ : Φ} {σ' : LState G s p} {φ' : Φ} {lg : Log G s Ω}
      {J : Finset (Fin G.m)} {cm c : ℕ},
      LoopC G s DC sub lv B τ i σ φ σ' φ' lg J cm c → ∀ q r, (q, r) ∈ lg → r.S.Nonempty := by
  intro i σ φ σ' φ' lg J cm c h
  induction h with
  | stop => intro q r hq; exact absurd hq List.not_mem_nil
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di d1 L' piv' lg lg' J' cm c =>
    have hne : ¬ σ.D.IsEmpty := by assumption
    have hpull : PullSpec σ.D B S0 Bi D1 := by assumption
    have hs : sub σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, d1) φ1 lg := by assumption
    have ih : ∀ q r, (q, r) ∈ lg' → r.S.Nonempty := by assumption
    intro q r hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨q', rfl, hq'⟩ := mem_shift.mp hq
      have hS0 : S0.Nonempty := hpull.nonempty (by
        simp only [DS.IsEmpty, not_forall] at hne; exact hne)
      obtain ⟨x, hx⟩ := hS0
      exact hsub _ _ _ _ _ _ _ _ hs ⟨x, mem_expand.mpr (Or.inl hx)⟩ q' r hq'
    · exact ih q r hq

theorem bmsspC_S_ne {FPC : FPRelC G s Φ Ω} (τ : ℕ → ℕ) :
    ∀ (l : ℕ) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (φ : Φ)
      (res : Result G s) (φ' : Φ) (lg : Log G s Ω),
      BMSSPC G s FPC DC τ l Blow B S d φ res φ' lg → S.Nonempty →
        ∀ q r, (q, r) ∈ lg → r.S.Nonempty
  | 0, Blow, B, S, d, φ, res, φ', lg, hrel, hS => by
    obtain ⟨st, c, -, -, -, -, -, -, -, rfl⟩ := hrel
    intro q r hq
    simp only [List.mem_singleton, Prod.mk.injEq] at hq
    obtain ⟨-, rfl⟩ := hq
    exact hS
  | l + 1, Blow, B, S, d, φ, res, φ', lg, hrel, hS => by
    obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L, B'f, T6, W', -, -, hloop,
      -, -, -, -, -, -, rfl⟩ := hrel
    intro q r hq
    rcases List.mem_cons.mp hq with h | h
    · rw [(Prod.mk.inj h).2]; exact hS
    · exact loopC_S_ne (bmsspC_S_ne τ l) hloop q r h

/-- Every record's merge cost is covered by `cmax` per child record present in the log. -/
def MergeOK (cmax : ℕ) (lg : Log G s Ω) : Prop :=
  ∀ q r, (q, r) ∈ lg → ∃ k, r.cMerge ≤ cmax * k ∧ ∀ a < k, ∃ r', (q ++ [a], r') ∈ lg

theorem MergeOK.shift {cmax : ℕ} {lg : Log G s Ω} (h : MergeOK cmax lg) (i : ℕ) :
    MergeOK cmax (lg.shift i) := by
  intro q r hq
  obtain ⟨q', rfl, hq'⟩ := mem_shift.mp hq
  obtain ⟨k, hk, hch⟩ := h q' r hq'
  refine ⟨k, hk, fun a ha => ?_⟩
  obtain ⟨r', hr'⟩ := hch a ha
  exact ⟨r', mem_shift.mpr ⟨q' ++ [a], by simp, hr'⟩⟩

theorem MergeOK.append {cmax : ℕ} {l1 l2 : Log G s Ω} (h1 : MergeOK cmax l1)
    (h2 : MergeOK cmax l2) : MergeOK cmax (l1 ++ l2) := by
  intro q r hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨k, hk, hch⟩ := h1 q r hq
    exact ⟨k, hk, fun a ha => let ⟨r', h⟩ := hch a ha; ⟨r', List.mem_append_left _ h⟩⟩
  · obtain ⟨k, hk, hch⟩ := h2 q r hq
    exact ⟨k, hk, fun a ha => let ⟨r', h⟩ := hch a ha; ⟨r', List.mem_append_right _ h⟩⟩

/-- (T2) for the loop: the loop's merge total is covered by one child record per iteration. -/
theorem loopC_merge {cmax : ℕ} (hDC : ∀ l k, DC.merge l k ≤ cmax) {sub : SubRelC G s Φ Ω}
    {lv : ℕ} {B : WLab G s} {τ : ℕ}
    (hsub : ∀ Blow B S d φ res φ' lg, sub Blow B S d φ res φ' lg →
      MergeOK cmax lg ∧ ∃ r, ([], r) ∈ lg) {p : ℕ} :
    ∀ {i : ℕ} {σ : LState G s p} {φ : Φ} {σ' : LState G s p} {φ' : Φ} {lg : Log G s Ω}
      {J : Finset (Fin G.m)} {cm c : ℕ},
      LoopC G s DC sub lv B τ i σ φ σ' φ' lg J cm c →
        MergeOK cmax lg ∧ ∃ k, cm ≤ cmax * k ∧ ∀ j < k, ∃ r', ([i + j], r') ∈ lg := by
  intro i σ φ σ' φ' lg J cm c h
  induction h with
  | stop => exact ⟨fun q r h => absurd h List.not_mem_nil, 0, le_rfl,
      fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di d1 L' piv' lg lg' J' cm c =>
    have hs : sub σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, d1) φ1 lg := by assumption
    have ih : MergeOK cmax lg' ∧ ∃ k, cm ≤ cmax * k ∧ ∀ j < k, ∃ r', ([i + 1 + j], r') ∈ lg' := by
      assumption
    obtain ⟨hOK, r0, hr0⟩ := hsub _ _ _ _ _ _ _ _ hs
    obtain ⟨hOK', k', hk', hch'⟩ := ih
    refine ⟨(hOK.shift i).append hOK', k' + 1, ?_, fun j hj => ?_⟩
    · calc DC.merge lv (keyCount G s Di) + cm ≤ cmax + cmax * k' := Nat.add_le_add (hDC _ _) hk'
        _ = cmax * (k' + 1) := by ring
    · rcases j with _ | j
      · exact ⟨r0, List.mem_append_left _ (mem_shift.mpr ⟨[], by simp, hr0⟩)⟩
      · obtain ⟨r', h'⟩ := hch' j (by omega)
        refine ⟨r', List.mem_append_right _ ?_⟩
        have : i + (j + 1) = i + 1 + j := by omega
        rw [this]; exact h'

/-- (T2) for every derivation: every record's `cMerge` is at most `cmax` per child record, and
the log has a root record. -/
theorem bmsspC_merge {FPC : FPRelC G s Φ Ω} {cmax : ℕ} (hDC : ∀ l k, DC.merge l k ≤ cmax)
    (τ : ℕ → ℕ) :
    ∀ (l : ℕ) (Blow B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (φ : Φ)
      (res : Result G s) (φ' : Φ) (lg : Log G s Ω),
      BMSSPC G s FPC DC τ l Blow B S d φ res φ' lg → MergeOK cmax lg ∧ ∃ r, ([], r) ∈ lg
  | 0, Blow, B, S, d, φ, res, φ', lg, hrel => by
    obtain ⟨st, c, -, -, -, -, -, -, -, rfl⟩ := hrel
    refine ⟨fun q r hq => ?_, _, List.mem_singleton_self _⟩
    simp only [List.mem_singleton, Prod.mk.injEq] at hq
    obtain ⟨-, rfl⟩ := hq
    exact ⟨0, le_rfl, fun a ha => absurd ha (Nat.not_lt_zero a)⟩
  | l + 1, Blow, B, S, d, φ, res, φ', lg, hrel => by
    obtain ⟨d1, p, P, Q, W, φ1, ω, cfp, piv, σ, lgc, J, cm, cl, L, B'f, T6, W', -, -, hloop,
      -, -, -, -, -, -, rfl⟩ := hrel
    obtain ⟨hOK, k, hk, hch⟩ := loopC_merge hDC (bmsspC_merge hDC τ l) hloop
    refine ⟨fun q r hq => ?_, _, List.mem_cons_self⟩
    rcases List.mem_cons.mp hq with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      refine ⟨k, hk, fun a ha => ?_⟩
      obtain ⟨r', hr'⟩ := hch a ha
      exact ⟨r', List.mem_cons_of_mem _ (by simpa using hr')⟩
    · obtain ⟨k', hk', hch'⟩ := hOK q r h
      exact ⟨k', hk', fun a ha => let ⟨r', h'⟩ := hch' a ha; ⟨r', List.mem_cons_of_mem _ h'⟩⟩

variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s Ω}

/-- Nonempty `U` for every record, from nonempty `S` (T1), `RecFacts` and `τ ≥ 1`. -/
theorem U_ne_of_S_ne (hL : LogInv τ L0 lg) (hτ : ∀ l, 1 ≤ τ l)
    (hS : ∀ q r, (q, r) ∈ lg → r.S.Nonempty) : ∀ q r, (q, r) ∈ lg → r.U.Nonempty := by
  intro q r hq
  have hf := hL.facts q r hq
  rcases lt_or_eq_of_le hf.B'_le with hlt | heq
  · exact Finset.card_pos.mp (lt_of_lt_of_le (hτ r.lvl) (hf.partial_card hlt))
  · obtain ⟨x, hx⟩ := hS q r hq
    exact ⟨x, hf.full_S heq hx⟩

/-- **`Valid.merge_total`** (tracker O23) for the counters of a traced run: with every `Merge`
charged at most `cmax` (L3-4's `O(1)` amortized merge), the total merge cost is at most
`cmax · (Lmax + 1) · |V|`. -/
theorem counters_merge_total (hL : LogInv τ L0 lg) {cmax : ℕ} (hOK : MergeOK cmax lg)
    (hne : ∀ q r, (q, r) ∈ lg → r.U.Nonempty) {Lmax : ℕ} (hd : ∀ X : lg.Call, X.1.length ≤ Lmax)
    (Fo : CallRec G s Ω → Finset (Fin G.n)) (Cr Be Del : CallRec G s Ω → Finset (Fin G.m)) :
    ∑ X, (Log.counters hL Fo Cr Be Del).mergeCost X ≤
      cmax * ((Lmax + 1) * Fintype.card (Fin G.n)) := by
  classical
  refine Frontier.CHD.MergeTotal.merge_total_le (Log.forest hL)
    (fun X => hne X.1 (lg.recOf X) (recOf_mem X)) hd _ cmax (fun X => ?_)
  show (lg.recOf X).cMerge ≤ cmax * (univ.filter (fun Y => Log.parentOf hL Y = some X)).card
  obtain ⟨k, hk, hch⟩ := hOK X.1 (lg.recOf X) (recOf_mem X)
  let f : Fin k → lg.Call := fun a => ⟨X.1 ++ [a.1], mem_paths.mpr (hch a.1 a.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : X.1 ++ [a.1] = X.1 ++ [b.1] := congrArg Subtype.val hab
    exact Fin.ext (by simpa using h1)
  have himg : univ.image f ⊆ univ.filter (fun Y => Log.parentOf hL Y = some X) := by
    intro Y hY
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hY
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [parentOf_some]
    exact ⟨by simp [f], by simp [f]⟩
  have hcard : k ≤ (univ.filter (fun Y => Log.parentOf hL Y = some X)).card := by
    have := Finset.card_le_card himg
    rwa [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin] at this
  exact hk.trans (Nat.mul_le_mul_left _ hcard)

end Frontier.CHD.BM
