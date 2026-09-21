import Frontier.CHD.LoopCost
import Frontier.CHD.CrBe
import Mathlib.Algebra.BigOperators.Fin

/-!
# Frontier.CHD.CostLog — per-record cost facts of the traced run (tracker O10; owner agent-03)

**NON-GATE** (Layer A).  Children of a record in a log, and the transport of child sums through the loop log's
structure (shifted sub-call logs).  Used to record `callC_cost` as a log invariant of every `BMSSPC` derivation.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n} {Ω : Type}

/-- Sum of `f` over the records at the child paths `q ++ [j]` of `q`. -/
def childSumAt (f : CallRec G s Ω → ℕ) (q : List ℕ) (lg : Log G s Ω) : ℕ :=
  ((lg.filter (fun x => decide (x.1.length = q.length + 1 ∧ q <+: x.1))).map (fun x => f x.2)).sum

theorem childSumAt_nil (f : CallRec G s Ω → ℕ) (lg : Log G s Ω) : childSumAt f [] lg = childSum f lg := by
  unfold childSumAt childSum
  congr 2
  apply List.filter_congr
  intro x _
  simp

theorem childSumAt_append (f : CallRec G s Ω → ℕ) (q : List ℕ) (a b : Log G s Ω) :
    childSumAt f q (a ++ b) = childSumAt f q a + childSumAt f q b := by
  simp [childSumAt, List.filter_append, List.map_append, List.sum_append]

theorem childSumAt_shift (f : CallRec G s Ω → ℕ) (i : ℕ) (q : List ℕ) (lg : Log G s Ω) :
    childSumAt f (i :: q) (lg.shift i) = childSumAt f q lg := by
  unfold childSumAt Log.shift
  rw [List.filter_map, List.map_map]
  congr 2
  apply List.filter_congr
  intro x _
  simp [List.cons_prefix_cons]

/-- Records whose paths do not start with `i` contribute nothing to children of `i :: q`. -/
theorem childSumAt_of_shape (f : CallRec G s Ω → ℕ) (i : ℕ) (q : List ℕ) (lg : Log G s Ω)
    (hsh : ∀ q' r, (q', r) ∈ lg → ∃ j q'', q' = j :: q'' ∧ j ≠ i) : childSumAt f (i :: q) lg = 0 := by
  unfold childSumAt
  have : lg.filter (fun x => decide (x.1.length = (i :: q).length + 1 ∧ (i :: q) <+: x.1)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    obtain ⟨j, q'', hq, hj⟩ := hsh x.1 x.2 hx
    simp only [decide_eq_true_eq, not_and]
    intro _ hpre
    rw [hq] at hpre
    exact hj (List.cons_prefix_cons.mp hpre).1.symm
  rw [this]; rfl

/-- Per-record cost facts of a log: every recursive record's cost is within its budget, where the budget may
depend on the record and on a sum over its children (with a record-dependent child charge). -/
def RecCost (chg : CallRec G s Ω → CallRec G s Ω → ℕ) (bud : CallRec G s Ω → ℕ → ℕ) (lg : Log G s Ω) : Prop :=
  ∀ q r, (q, r) ∈ lg → r.base = false → r.cost ≤ bud r (childSumAt (chg r) q lg)

theorem RecCost.nil (chg : CallRec G s Ω → CallRec G s Ω → ℕ) (bud : CallRec G s Ω → ℕ → ℕ) :
    RecCost chg bud ([] : Log G s Ω) := fun _ _ h => absurd h (List.not_mem_nil)

/-- Shifting a log keeps its cost facts. -/
theorem RecCost.shift {chg : CallRec G s Ω → CallRec G s Ω → ℕ} {bud : CallRec G s Ω → ℕ → ℕ}
    {lg : Log G s Ω} (h : RecCost chg bud lg) (i : ℕ) (lg' : Log G s Ω)
    (hsh : ∀ q r, (q, r) ∈ lg' → ∃ j q', q = j :: q' ∧ j ≠ i) :
    ∀ q r, (q, r) ∈ lg.shift i → r.base = false →
      r.cost ≤ bud r (childSumAt (chg r) q (lg.shift i ++ lg')) := by
  intro q r hqr hb
  obtain ⟨q', rfl, hq'⟩ := mem_shift.mp hqr
  rw [childSumAt_append, childSumAt_shift, childSumAt_of_shape _ i q' lg' hsh, Nat.add_zero]
  exact h q' r hq' hb

section LoopRec

variable {Φ : Type} {DC : DCost}
variable {B : WLab G s} {S : Finset (Fin G.n)} {d0 d1 : Labels G s} {p : ℕ}
  {P0 : Fin p → Finset (Fin G.n)} {Q W : Finset (Fin G.n)} {B'0 : WLab G s}

/-- Sub-calls whose logs carry the cost facts. -/
def SubCost (chg : CallRec G s Ω → CallRec G s Ω → ℕ) (bud : CallRec G s Ω → ℕ → ℕ)
    (sub : SubRelC G s Φ Ω) (Inv : Φ → Prop) : Prop :=
  ∀ Blow B S d φ res φ' lg, CallPre B S d → Inv φ → (∀ x ∈ S, Blow ≤ dis (s := s) x) → Blow ≤ B →
    sub Blow B S d φ res φ' lg → RecCost chg bud lg

/-- **The loop log carries the sub-calls' cost facts** (transported through the shifts). -/
theorem loopC_reccost (hpre : CallPre B S d0) (hfp : FPContract B S d0 d1 p P0 Q W)
    {τ : ℕ → ℕ} {Inv : Φ → Prop} {sub : SubRelC G s Φ Ω} {l : ℕ} (hsub : GoodSub G s τ Inv l sub)
    {chg : CallRec G s Ω → CallRec G s Ω → ℕ} {bud : CallRec G s Ω → ℕ → ℕ}
    (hsubc : SubCost chg bud sub Inv) {τl : ℕ} :
    ∀ i (σ : LState G s p) φ σ' φ' lg J cm c,
      LoopC G s DC sub (l + 1) B τl i σ φ σ' φ' lg J cm c →
      LInv G s B S d0 d1 P0 B'0 σ → Inv φ →
      RecCost chg bud lg ∧ ∀ q r, (q, r) ∈ lg → ∃ j q', q = j :: q' ∧ i ≤ j := by
  intro i σ φ σ' φ' lg J cm c hloop
  induction hloop with
  | stop i σ φ hstop =>
    intro _ _
    exact ⟨RecCost.nil chg bud, fun q r h => absurd h List.not_mem_nil⟩
  | step i σ σ' φ φ1 φ' S0 Bi D1 B'i Ui Di dsub L' piv' lg lg' J' cm c _ hne hpull' _ _ hsubrel
      hnd hmem hres _ ih =>
    intro h hI
    have hsp : CallPre Bi (expand σ S0 Bi) σ.d := step_pre hpre hfp h hpull'
    have hlowdis : ∀ x ∈ expand σ S0 Bi, σ.B' ≤ dis (s := s) x :=
      fun x hx => (Si_facts h hpull' hx).1.2.2
    have hSne : S0.Nonempty := by
      apply hpull'.nonempty
      simp only [DS.IsEmpty, not_forall] at hne
      exact hne
    obtain ⟨x0, hx0⟩ := hSne
    have hx0S : x0 ∈ expand σ S0 Bi := mem_expand.mpr (Or.inl hx0)
    have hBlt : σ.B' < Bi := by
      obtain ⟨⟨-, -, hB⟩, hlt⟩ := Si_facts h hpull' hx0S
      exact lt_of_le_of_lt (hB.trans (h.walk.sound x0)) hlt
    obtain ⟨hpost, hI1, hlog⟩ := hsub σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, dsub) φ1 lg
      hsp hI hlowdis hBlt.le hsubrel
    have hrc := hsubc σ.B' Bi (expand σ S0 Bi) σ.d φ (B'i, Ui, Di, dsub) φ1 lg
      hsp hI hlowdis hBlt.le hsubrel
    have hmem' : ∀ e, e ∈ L' ↔ G.src e ∈ Ui ∧ Bi ≤ ext (dis (s := s) (G.src e)) e ∧
        ext (dis (s := s) (G.src e)) e < B := by
      intro e
      rw [hmem e]
      constructor
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [hc] at h1 h2
        exact ⟨hu, h1, h2⟩
      · rintro ⟨hu, h1, h2⟩
        have hc : dsub (G.src e) = dis (s := s) (G.src e) := hpost.U_complete _ hu
        rw [← hc] at h1 h2
        exact ⟨hu, h1, h2⟩
    obtain ⟨L, hL, hfold⟩ :=
      window_scan_step hpull'.bound hpost ((D1.merge Di).deleteSet Ui) hnd hmem'
    have hres' : Reselect σ Ui
        (L.foldl (relaxIns G s B (some Bi)) (dsub, (D1.merge Di).deleteSet Ui)).1 piv' := by
      rw [hfold]; exact hres
    have hnext := step_post hpre hfp h hne hpull' hpost hL hres'
    rw [hfold] at hnext
    obtain ⟨hrc', hsh'⟩ := ih hnext hI1
    have hsh'' : ∀ q r, (q, r) ∈ lg' → ∃ j q', q = j :: q' ∧ j ≠ i := by
      intro q r hqr
      obtain ⟨j, q', hq, hj⟩ := hsh' q r hqr
      exact ⟨j, q', hq, by omega⟩
    refine ⟨fun q r hqr hb => ?_, fun q r hqr => ?_⟩
    · rcases List.mem_append.mp hqr with h1 | h2
      · exact RecCost.shift hrc i lg' hsh'' q r h1 hb
      · -- a record of the tail: the shifted sub-log contributes no children to it
        obtain ⟨j, q', hq, hj⟩ := hsh' q r h2
        subst hq
        have h0 : childSumAt (chg r) (j :: q') (lg.shift i) = 0 := by
          apply childSumAt_of_shape
          intro q'' r'' h''
          obtain ⟨q3, rfl, -⟩ := mem_shift.mp h''
          exact ⟨i, q3, rfl, by omega⟩
        rw [childSumAt_append, h0, Nat.zero_add]
        exact hrc' _ r h2 hb
    · rcases List.mem_append.mp hqr with h1 | h2
      · obtain ⟨q', rfl, -⟩ := mem_shift.mp h1
        exact ⟨i, q', rfl, le_rfl⟩
      · obtain ⟨j, q', hq, hj⟩ := hsh' q r h2
        exact ⟨j, q', hq, by omega⟩

end LoopRec

section CallRec

variable {k hins hext : ℕ}

/-- `#tv` of a record's FindPivots output. -/
def tvLen (r : CallRec G s (FPData G s)) : ℕ :=
  match r.fp with
  | none => 0
  | some ω => (ω.trees.flatMap (fun T => T.ord)).length

/-- `|Del|` of a record (the edges deleted by its FindPivots). -/
def delCard (r : CallRec G s (FPData G s)) : ℕ :=
  match r.fp with
  | none => 0
  | some ω => (ω.Dout \ ω.Din).card

/-- The record-dependent child charge (groups read from the record through `fpC`'s pinning). -/
noncomputable def chgOf (k C0 C1 C2 : ℕ) (r Y : CallRec G s (FPData G s)) : ℕ :=
  C0 + C1 * Y.U.card + C2 * (groupsOf k r).countP (fun g => decide (g.toFinset ∩ Y.U).Nonempty)

/-- The call budget (the right-hand side of `callC_cost`, as a function of the record and its child sum). -/
noncomputable def budOf (k hins hext ad bd I nw : ℕ) (r : CallRec G s (FPData G s)) (cs : ℕ) : ℕ :=
  scanC * delCard r + fpA k hins hext * (tvLen r + k * r.Q.card) + 3 * r.S.card
    + (nw + r.S.card + r.p * (2 + I))
    + (1 + 3 * k * r.p + cs + (1 + I) * r.J.card)
    + r.cMerge
    + (1 + r.S.card + (if r.B' = r.B then 0 else r.S.card) * I + r.W.card + r.W'.card + r.Wr.card * (1 + I)
        + (ad * r.W'.card + bd) + r.S.card)

theorem card_filter_get {β : Type*} (L : List β) (q : β → Prop) [DecidablePred q] :
    (Finset.univ.filter (fun j : Fin L.length => q (L.get j))).card = L.countP (fun x => decide (q x)) := by
  classical
  have h1 : (Finset.univ.filter (fun j : Fin L.length => q (L.get j))) =
      ((List.finRange L.length).filter (fun j => decide (q (L.get j)))).toFinset := by
    ext j; simp
  rw [h1, List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _), List.countP_eq_length_filter]
  have h2 : L.filter (fun x => decide (q x)) =
      ((List.finRange L.length).filter (fun j => decide (q (L.get j)))).map L.get := by
    have hL : (List.finRange L.length).map L.get = L := by rw [← List.ofFn_eq_map, List.ofFn_get]
    conv_lhs => rw [← hL]
    rw [List.filter_map]
    rfl
  rw [h2, List.length_map]

end CallRec

section CallRecCost

variable {DC : DCost} {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

/-- **One recursive call's log carries the cost facts**, given that its sub-calls' logs do. -/
theorem callC_reccost (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) (hk : 2 ≤ k)
    {τ : ℕ → ℕ} {sub : SubRelC G s (Finset (Fin G.m)) (FPData G s)} {l : ℕ}
    (hsub : GoodSub G s τ (DelInv G s) l sub)
    {ap bp ad bd I nw : ℕ}
    (hsubc : SubCost (chgOf k (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I))
      (budOf k hins hext ad bd I nw) sub (DelInv G s))
    {Blow B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {φ0 φ2 : Finset (Fin G.m)}
    {τl : ℕ} {res : Result G s} {lg : Log G s (FPData G s)}
    (hpre : CallPre B S d0) (hI : DelInv G s φ0) (hlow : ∀ x ∈ S, Blow ≤ dis (s := s) x)
    (hrel : CallC G s (fpC G s out k hins hext) DC sub (l + 1) Blow B S d0 φ0 τl res φ2 lg)
    (hpull : ∀ x, DC.pull (l + 1) x ≤ ap * x + bp) (hdel : ∀ x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : DC.ins (l + 1) ≤ I) (hnew : DC.new (l + 1) ≤ nw)
    (hMτ : DC.M (l + 1) ≤ τ l) (hgMτ : 3 * k * DC.M (l + 1) ≤ τ l) :
    RecCost (chgOf k (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I)) (budOf k hins hext ad bd I nw) lg := by
  classical
  obtain ⟨r, lgc, ω, p, P, T6, hlg, hω, hp, hPsub, ⟨hp', hP⟩, hPdisj, hT6S, hT6e, hcost⟩ :=
    callC_cost hout hsort hsimp hk hsub hpre hI hlow hrel hpull hdel hinsI hnew hMτ hgMτ
  -- the loop log
  obtain ⟨d1, p2, P2, Q2, W2, φ1, ω2, cfp, piv, σ, lgc2, J, cm, cl, L, B'f, T62, W', hfprel, hpiv,
    hloop, -, -, -, -, -, -, hlg2⟩ := hrel
  have hlow' : ∀ x ∈ S, Blow ≤ d0 x := fun x hx => (hlow x hx).trans (hpre.walk.sound x)
  obtain ⟨hfp, hI1⟩ := fpC_sound hout hsort hsimp hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ hpre hI hlow' hfprel
  have h0 := linv_init hpre hfp hpiv
  obtain ⟨hrcL, -⟩ := loopC_reccost (DC := DC) hpre hfp hsub hsubc _ _ _ _ _ _ _ _ _ hloop h0 hI1
  rw [hlg] at hlg2
  have hlgc : lgc = lgc2 := (List.cons.inj hlg2).2
  rw [← hlgc] at hrcL
  -- the head record contributes no children to any path
  have hhead : ∀ (f : CallRec G s (FPData G s) → ℕ) (q : List ℕ),
      childSumAt f q (([], r) :: lgc) = childSumAt f q lgc := by
    intro f q
    unfold childSumAt
    rw [List.filter_cons_of_neg (by simp)]
  rw [hlg]
  intro q r' hqr hb
  rcases List.mem_cons.mp hqr with heq | hmem
  · obtain ⟨hq, hr⟩ := Prod.mk.inj heq
    rw [hq, hr, hhead, childSumAt_nil]
    -- the child charges agree
    have hchg : childSum (childCharge P (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I)) lgc =
        childSum (chgOf k (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I) r) lgc := by
      unfold childSum
      congr 2
      funext x
      unfold childCharge chgOf groupsOf
      rw [hω]
      congr 2
      subst hp'
      have hPj : ∀ j, (P j ∩ x.2.U).Nonempty ↔
          ((((forestGroups r.S r.Q k ω.trees).get j).toFinset ∩ x.2.U).Nonempty) := by
        intro j; rw [hP j]; rfl
      rw [← card_filter_get (forestGroups r.S r.Q k ω.trees) (fun g => (g.toFinset ∩ x.2.U).Nonempty)]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hPj j
    have htv : tvLen r = (ω.trees.flatMap (fun T => T.ord)).length := by unfold tvLen; rw [hω]
    have hdl : delCard r = (ω.Dout \ ω.Din).card := by unfold delCard; rw [hω]
    have hT6 : T6.card * I ≤ (if r.B' = r.B then 0 else r.S.card) * I := by
      refine Nat.mul_le_mul_right _ ?_
      split_ifs with hB
      · rw [hT6e hB]; simp
      · exact Finset.card_le_card hT6S
    unfold budOf
    rw [htv, hdl, hp]
    rw [hchg] at hcost
    omega
  · rw [hhead]
    exact hrcL q r' hmem hb

end CallRecCost

section Levels

variable {DC : DCost} {out : Fin G.n → List (Fin G.m)} {k hins hext : ℕ}

/-- **Every derivation of the traced BMSSP recursion carries the per-record cost facts** (all levels). -/
theorem bmsspC_reccost (hout : ∀ u e, e ∈ out u ↔ G.src e = u) (hsort : ∀ u, (out u).Pairwise (SortedRel G s))
    (hsimp : ∀ u, ((out u).map G.dst).Nodup) (hk : 2 ≤ k) (τ : ℕ → ℕ)
    {ap bp ad bd I nw : ℕ}
    (hpull : ∀ l x, DC.pull (l + 1) x ≤ ap * x + bp) (hdel : ∀ l x, DC.del (l + 1) x ≤ ad * x + bd)
    (hinsI : ∀ l, DC.ins (l + 1) ≤ I) (hnew : ∀ l, DC.new (l + 1) ≤ nw)
    (hMτ : ∀ l, DC.M (l + 1) ≤ τ l) (hgMτ : ∀ l, 3 * k * DC.M (l + 1) ≤ τ l) :
    ∀ l, SubCost (chgOf k (1 + bp + bd) (ap + ad + 4) (2 * (3 * k) + 1 + I)) (budOf k hins hext ad bd I nw)
      (BMSSPC G s (fpC G s out k hins hext) DC τ l) (DelInv G s)
  | 0 => by
    intro Blow B S d φ res φ' lg _ _ _ _ hrel
    obtain ⟨st, c, -, -, -, -, -, -, -, rfl⟩ := hrel
    intro q r hqr hb
    rcases List.mem_singleton.mp hqr with heq
    obtain ⟨-, rfl⟩ := Prod.mk.inj heq
    simp at hb
  | l + 1 => by
    intro Blow B S d φ res φ' lg hpre hI hlow _ hrel
    exact callC_reccost hout hsort hsimp hk (bmsspC_log (fpC_sound hout hsort hsimp hk) τ l)
      (bmsspC_reccost hout hsort hsimp hk τ hpull hdel hinsI hnew hMτ hgMτ l) hpre hI hlow hrel
      (hpull l) (hdel l) (hinsI l) (hnew l) (hMτ l) (hgMτ l)

end Levels

section Forest

variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s Ω}

/-- **Child sums of the log are sums over the call forest's children.** -/
theorem childSumAt_eq_sum (hL : LogInv τ L0 lg) (f : CallRec G s Ω → ℕ) (X : lg.Call) :
    childSumAt f X.1 lg =
      ∑ Y ∈ Finset.univ.filter (fun Y => Log.parentOf hL Y = some X), f (lg.recOf Y) := by
  classical
  unfold childSumAt
  set P : List ℕ × CallRec G s Ω → Bool := fun x => decide (x.1.length = X.1.length + 1 ∧ X.1 <+: x.1) with hP
  have hnd : (lg.filter P).Nodup :=
    (List.Nodup.of_map _ hL.nodup).sublist List.filter_sublist
  rw [← List.sum_toFinset _ hnd]
  refine Finset.sum_bij' (fun x hx => ⟨x.1, mem_paths.mpr ⟨x.2, (List.mem_filter.mp (List.mem_toFinset.mp hx)).1⟩⟩)
    (fun Y _ => (Y.1, lg.recOf Y)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxl, hxP⟩ := List.mem_filter.mp (List.mem_toFinset.mp hx)
    simp only [hP, decide_eq_true_eq] at hxP
    obtain ⟨hlen, hpre⟩ := hxP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [parentOf_some]
    obtain ⟨t, ht⟩ := hpre
    have htl : t.length = 1 := by rw [← ht, List.length_append] at hlen; omega
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp htl
    refine ⟨by simp [← ht], ?_⟩
    simp [← ht]
  · intro Y hY
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
    obtain ⟨a, ha⟩ := parentOf_child hL hY
    refine List.mem_toFinset.mpr (List.mem_filter.mpr ⟨recOf_mem Y, ?_⟩)
    simp only [hP, decide_eq_true_eq]
    rw [ha]
    exact ⟨by simp, List.prefix_append _ _⟩
  · intro x hx
    obtain ⟨hxl, -⟩ := List.mem_filter.mp (List.mem_toFinset.mp hx)
    rw [recOf_eq hL.nodup hxl]
  · intro Y _
    rfl
  · intro x hx
    obtain ⟨hxl, -⟩ := List.mem_filter.mp (List.mem_toFinset.mp hx)
    rw [recOf_eq hL.nodup hxl]

end Forest

end BM
end CHD
end Frontier
