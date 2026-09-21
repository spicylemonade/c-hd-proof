import Frontier.CHD.BMTrace

/-!
# Frontier.CHD.QWit — the `Q`-witness of full calls (tracker O22(a); owner agent-03)

**NON-GATE** (Layer A).  DMSY26 Lemma 3.9 with reviewer #1's latest-inserting-event witness, on the call log.

* `evOf r`: the relaxation events of a record that can insert: the jump window edges `J`, the `W'` edges below
  `B`, and for base calls the edges out of `U` below `B`.
* **G2** (`ev_unique`): an edge is an event of at most one record.  The tail `u` of the edge lies in the `U` of a
  chain of calls, and the event windows (`[B_child, B)` for jumps, `(·, B)` for the call owning `u`) are disjoint
  along that chain.
* Events are anchored at a path (`Anchor`): a jump at the child that returned its tail, an own event at the record.
  `Before α y`: the paths diverge with `α` to the left, i.e. the event ended before the call `y` started.
* `LocalProv lg`: every member of a sub-call's `S` is in the parent's `S \ Q`, or is the head (`≠ s`) of an event
  anchored inside an earlier child subtree of the parent, or lies in `S` of a call of such a subtree.  Part 2
  proves it for every derivation.
* `qwit_of_prov`: from `LocalProv` and `S_root ⊆ {s}`: a witness `wit` with `wit_mem`, `wit_inj`, `src_once`.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace BM

open Frontier Graph

variable {G : Graph} {s : Fin G.n} {Ω : Type}

/-! ## Definitions -/

section Defs

/-- Relaxation events of a record that can insert. -/
noncomputable def evOf (r : CallRec G s Ω) : Finset (Fin G.m) := by
  classical
  exact if r.base = true then Finset.univ.filter (fun e => G.src e ∈ r.U ∧ eval G s e < r.B)
    else r.J ∪ r.Wr.filter (fun e => eval G s e < r.B)

/-- The anchor of an event: the returning child for a jump, the record itself for an own event. -/
def Anchor (lg : Log G s Ω) (q : List ℕ) (r : CallRec G s Ω) (e : Fin G.m) (α : List ℕ) : Prop :=
  (r.base = false ∧ e ∈ r.J ∧ ∃ a r', α = q ++ [a] ∧ (α, r') ∈ lg ∧ G.src e ∈ r'.U) ∨
  (α = q ∧ (r.base = true ∨ e ∈ r.Wr))

/-- `e` is an event of the log anchored at `α`. -/
def IsEvent (lg : Log G s Ω) (e : Fin G.m) (α : List ℕ) : Prop :=
  ∃ q r, (q, r) ∈ lg ∧ e ∈ evOf r ∧ Anchor lg q r e α

/-- `a` ended before `y` started: the paths diverge, `a` to the left. -/
def Before (a y : List ℕ) : Prop :=
  ∃ p i j a' y', a = p ++ i :: a' ∧ y = p ++ j :: y' ∧ i < j

/-- Provenance of `v` for the child `z ++ [i]`: the head `v ≠ s` of an event anchored inside an earlier child
subtree of `z` (or at an earlier child, for a jump of `z`), or a member of `S` of a call of such a subtree. -/
def Prov (lg : Log G s Ω) (z : List ℕ) (i : ℕ) (v : Fin G.n) : Prop :=
  (∃ e α, IsEvent lg e α ∧ G.dst e = v ∧ v ≠ s ∧ ∃ a α', α = z ++ a :: α' ∧ a < i) ∨
  (∃ y r', (y, r') ∈ lg ∧ v ∈ r'.S ∧ ∃ a y', y = z ++ a :: y' ∧ a < i)

/-- **Local provenance** of the frontiers of a log. -/
def LocalProv (lg : Log G s Ω) : Prop :=
  ∀ z i r, (z ++ [i], r) ∈ lg → ∀ v ∈ r.S,
    (∃ rz, (z, rz) ∈ lg ∧ v ∈ rz.S ∧ v ∉ rz.Q) ∨ Prov lg z i v

end Defs

/-! ## Paths -/

section Paths

theorem before_irrefl (a : List ℕ) : ¬ Before a a := by
  rintro ⟨p, i, j, a', y', h1, h2, hij⟩
  rw [h1] at h2
  obtain ⟨hij', -⟩ := List.cons_eq_cons.mp (List.append_cancel_left h2)
  omega

theorem before_of_child {z α' : List ℕ} {a i : ℕ} (h : a < i) (t : List ℕ) :
    Before (z ++ a :: α') (z ++ i :: t) :=
  ⟨z, a, i, α', t, rfl, rfl, h⟩

theorem before_append {a z : List ℕ} (h : Before a z) (t : List ℕ) : Before a (z ++ t) := by
  obtain ⟨p, i, j, a', y', h1, h2, hij⟩ := h
  exact ⟨p, i, j, a', y' ++ t, h1, by rw [h2]; simp, hij⟩

theorem not_before_of_prefix {z α : List ℕ} (h : z <+: α) : ¬ Before α z := by
  rintro ⟨p, i, j, a', y', h1, h2, hij⟩
  obtain ⟨t, rfl⟩ := h
  rw [h2] at h1
  simp only [List.append_assoc, List.cons_append] at h1
  obtain ⟨hji, -⟩ := List.cons_eq_cons.mp (List.append_cancel_left h1)
  omega

/-- Two lists neither of which is a prefix of the other diverge. -/
theorem diverge_of_not_prefix : ∀ (q q' : List ℕ), ¬ q <+: q' → ¬ q' <+: q →
    ∃ p a b ta tb, q = p ++ a :: ta ∧ q' = p ++ b :: tb ∧ a ≠ b
  | [], _, h, _ => absurd List.nil_prefix h
  | _ :: _, [], _, h' => absurd List.nil_prefix h'
  | a :: ta, b :: tb, h, h' => by
    by_cases hab : a = b
    · subst hab
      obtain ⟨p, a', b', ta', tb', h1, h2, hne⟩ := diverge_of_not_prefix ta tb
        (fun hp => h (List.cons_prefix_cons.mpr ⟨rfl, hp⟩))
        (fun hp => h' (List.cons_prefix_cons.mpr ⟨rfl, hp⟩))
      exact ⟨a :: p, a', b', ta', tb', by rw [h1]; rfl, by rw [h2]; rfl, hne⟩
    · exact ⟨[], a, b, ta, tb, rfl, rfl, hab⟩

theorem before_trans {a b c : List ℕ} (h1 : Before a b) (h2 : Before b c) : Before a c := by
  obtain ⟨p, i, j, a', b', ha, hb, hij⟩ := h1
  obtain ⟨p2, i2, j2, b2, c', hb2, hc, hij2⟩ := h2
  rw [hb] at hb2
  rcases Nat.lt_trichotomy p.length p2.length with hlt | heq | hgt
  · -- `p2 = p ++ j :: w`
    have h3 : p ++ [j] <+: p2 ++ i2 :: b2 := by rw [← hb2]; exact ⟨b', by simp⟩
    obtain ⟨w, hw⟩ := List.prefix_of_prefix_length_le h3 (List.prefix_append p2 (i2 :: b2))
      (by simp; omega)
    refine ⟨p, i, j, a', w ++ j2 :: c', ha, ?_, hij⟩
    rw [hc, ← hw]; simp
  · have hp : p = p2 := by
      have e := congrArg (List.take p.length) hb2
      have e2 : (p2 ++ i2 :: b2).take p.length = p2 := by rw [heq]; exact List.take_left
      rw [List.take_left, e2] at e
      exact e
    subst hp
    obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp (List.append_cancel_left hb2)
    exact ⟨_, _, _, _, _, ha, hc, lt_trans hij hij2⟩
  · -- `p = p2 ++ i2 :: w`
    have h3 : p2 ++ [i2] <+: p ++ j :: b' := by rw [hb2]; exact ⟨b2, by simp⟩
    obtain ⟨w, hw⟩ := List.prefix_of_prefix_length_le h3 (List.prefix_append p (j :: b'))
      (by simp; omega)
    refine ⟨p2, i2, j2, w ++ i :: a', c', ?_, hc, hij2⟩
    rw [ha, ← hw]; simp

theorem prefix_dropLast {q0 q : List ℕ} (h : q0 <+: q) (hne : q0 ≠ q) : q0 <+: q.dropLast := by
  obtain ⟨t, rfl⟩ := h
  have ht : t ≠ [] := fun ht => hne (by simp [ht])
  rw [List.dropLast_append_of_ne_nil ht]
  exact List.prefix_append _ _

end Paths

/-! ## G2: one event per edge -/

section G2

variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s Ω} (hL : LogInv τ L0 lg)
include hL

/-- Prefix closure: every prefix of a logged path is logged, with larger `U` and `B`. -/
theorem prefix_rec : ∀ (n : ℕ) (q : List ℕ) (r : CallRec G s Ω), (q, r) ∈ lg → ∀ q0, q0 <+: q →
    q.length - q0.length = n → ∃ r0, (q0, r0) ∈ lg ∧ r.U ⊆ r0.U ∧ r.B ≤ r0.B := by
  intro n
  induction n with
  | zero =>
    intro q r hq q0 h0 hlen
    have : q0 = q := h0.eq_of_length (by have := h0.length_le; omega)
    subst this
    exact ⟨r, hq, subset_rfl, le_rfl⟩
  | succ n ih =>
    intro q r hq q0 h0 hlen
    have hne : q0 ≠ q := by rintro rfl; omega
    have hqne : q ≠ [] := by rintro rfl; simp at hlen
    obtain ⟨r1, hr1, hpc⟩ := hL.parent q r hq hqne
    obtain ⟨r0, hr0, hU, hB⟩ := ih q.dropLast r1 hr1 q0 (prefix_dropLast h0 hne)
      (by rw [List.length_dropLast]; omega)
    exact ⟨r0, hr0, hpc.U_sub.trans hU, hpc.B_le.trans hB⟩

theorem prefix_rec' {q : List ℕ} {r : CallRec G s Ω} (hq : (q, r) ∈ lg) {q0 : List ℕ} (h0 : q0 <+: q) :
    ∃ r0, (q0, r0) ∈ lg ∧ r.U ⊆ r0.U ∧ r.B ≤ r0.B :=
  prefix_rec hL _ q r hq q0 h0 rfl

/-- **Chains**: calls whose `U` share a vertex are prefix-comparable. -/
theorem prefix_chain {q q' : List ℕ} {r r' : CallRec G s Ω} (h : (q, r) ∈ lg) (h' : (q', r') ∈ lg)
    {v : Fin G.n} (hv : v ∈ r.U) (hv' : v ∈ r'.U) : q <+: q' ∨ q' <+: q := by
  by_contra hc
  rw [not_or] at hc
  obtain ⟨p, a, b, ta, tb, rfl, rfl, hab⟩ := diverge_of_not_prefix q q' hc.1 hc.2
  obtain ⟨ra, hra, hUa, -⟩ := prefix_rec' hL h (q0 := p ++ [a]) ⟨ta, by simp⟩
  obtain ⟨rb, hrb, hUb, -⟩ := prefix_rec' hL h' (q0 := p ++ [b]) ⟨tb, by simp⟩
  exact Finset.disjoint_left.mp (sib_disjoint hL hra hrb hab) (hUa hv) (hUb hv')

/-- The two kinds of events. -/
theorem ev_kind {q : List ℕ} {r : CallRec G s Ω} (hq : (q, r) ∈ lg) {e : Fin G.m} (he : e ∈ evOf r) :
    (r.base = false ∧ e ∈ r.J ∧ ∃ a r', (q ++ [a], r') ∈ lg ∧ G.src e ∈ r'.U ∧ r'.B ≤ eval G s e ∧
      eval G s e < r.B) ∨
    (G.src e ∈ r.U ∧ (∀ a r', (q ++ [a], r') ∈ lg → G.src e ∉ r'.U) ∧ eval G s e < r.B ∧
      (r.base = true ∨ e ∈ r.Wr)) := by
  classical
  unfold evOf at he
  by_cases hb : r.base = true
  · rw [if_pos hb] at he
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp he
    exact Or.inr ⟨h1, fun a r' h' => absurd h' (hL.base q r hq hb a r'), h2, Or.inl hb⟩
  · rw [if_neg hb] at he
    rcases Finset.mem_union.mp he with hJ | hW
    · obtain ⟨a, r', h1, h2, h3, h4⟩ := hL.jump q r hq e hJ
      exact Or.inl ⟨by simpa using hb, hJ, a, r', h1, h2, h3, h4⟩
    · obtain ⟨hW, hlt⟩ := Finset.mem_filter.mp hW
      obtain ⟨h1, h2⟩ := hL.wr q r hq e hW
      exact Or.inr ⟨h1, h2, hlt, Or.inr hW⟩

/-- An own event at `q2` cannot lie on the chain strictly above a call `c` containing its tail. -/
theorem own_not_above {q2 c : List ℕ} {r2 rc : CallRec G s Ω} (h2 : (q2, r2) ∈ lg) (hc : (c, rc) ∈ lg)
    {u : Fin G.n} (hown : ∀ a r', (q2 ++ [a], r') ∈ lg → u ∉ r'.U) (huc : u ∈ rc.U)
    (hpre : q2 <+: c) (hne : q2 ≠ c) : False := by
  obtain ⟨t, rfl⟩ := hpre
  have ht : t ≠ [] := fun ht => hne (by simp [ht])
  obtain ⟨a, t', rfl⟩ := List.exists_cons_of_ne_nil ht
  obtain ⟨r', hr', hU, -⟩ := prefix_rec' hL hc (q0 := q2 ++ [a]) ⟨t', by simp⟩
  exact hown a r' hr' (hU huc)

/-- A value at least the bound of `c` is not below the bound of any call in the subtree of `c`. -/
theorem window_below {c q' : List ℕ} {rc r' : CallRec G s Ω} (hc : (c, rc) ∈ lg) (hq' : (q', r') ∈ lg)
    (hpre : c <+: q') {x : WLab G s} (hB : rc.B ≤ x) (hlt : x < r'.B) : False := by
  obtain ⟨r0, hr0, -, hB0⟩ := prefix_rec' hL hq' hpre
  have : r0 = rc := rec_unique hL.nodup hr0 hc
  subst this
  exact absurd (lt_of_lt_of_le hlt hB0) (not_lt.mpr hB)

/-- **G2**: an edge is an event of at most one record. -/
theorem ev_unique {q1 q2 : List ℕ} {r1 r2 : CallRec G s Ω} (h1 : (q1, r1) ∈ lg) (h2 : (q2, r2) ∈ lg)
    {e : Fin G.m} (he1 : e ∈ evOf r1) (he2 : e ∈ evOf r2) : q1 = q2 := by
  rcases ev_kind hL h1 he1 with ⟨-, -, a1, c1r, hc1, hu1, hB1, hlt1⟩ | ⟨hu1, hown1, hlt1, -⟩ <;>
  rcases ev_kind hL h2 he2 with ⟨-, -, a2, c2r, hc2, hu2, hB2, hlt2⟩ | ⟨hu2, hown2, hlt2, -⟩
  · -- jump / jump
    rcases prefix_chain hL hc1 hc2 hu1 hu2 with hp | hp
    · by_cases heq : q1 ++ [a1] = q2 ++ [a2]
      · exact (List.append_inj' heq (by simp)).1
      · have hp' : q1 ++ [a1] <+: q2 := by
          have := prefix_dropLast hp heq
          rwa [List.dropLast_concat] at this
        exact (window_below hL hc1 h2 hp' hB1 hlt2).elim
    · by_cases heq : q2 ++ [a2] = q1 ++ [a1]
      · exact ((List.append_inj' heq (by simp)).1).symm
      · have hp' : q2 ++ [a2] <+: q1 := by
          have := prefix_dropLast hp heq
          rwa [List.dropLast_concat] at this
        exact (window_below hL hc2 h1 hp' hB2 hlt1).elim
  · -- jump at `q1` / own at `q2`
    rcases prefix_chain hL hc1 h2 hu1 hu2 with hp | hp
    · exact (window_below hL hc1 h2 hp hB1 hlt2).elim
    · by_cases heq : q2 = q1 ++ [a1]
      · subst heq; exact (window_below hL hc1 h2 (List.prefix_refl _) hB1 hlt2).elim
      · exact (own_not_above hL h2 hc1 hown2 hu1 hp heq).elim
  · -- own at `q1` / jump at `q2`
    rcases prefix_chain hL hc2 h1 hu2 hu1 with hp | hp
    · exact (window_below hL hc2 h1 hp hB2 hlt1).elim
    · by_cases heq : q1 = q2 ++ [a2]
      · subst heq; exact (window_below hL hc2 h1 (List.prefix_refl _) hB2 hlt1).elim
      · exact (own_not_above hL h1 hc2 hown1 hu2 hp heq).elim
  · -- own / own
    rcases prefix_chain hL h1 h2 hu1 hu2 with hp | hp
    · by_cases heq : q1 = q2
      · exact heq
      · exact (own_not_above hL h1 h2 hown1 hu2 hp heq).elim
    · by_cases heq : q2 = q1
      · exact heq.symm
      · exact (own_not_above hL h2 h1 hown2 hu1 hp heq).elim

/-- The anchor of an event is unique. -/
theorem anchor_unique {q : List ℕ} {r : CallRec G s Ω} (hq : (q, r) ∈ lg) {e : Fin G.m} {α1 α2 : List ℕ}
    (h1 : Anchor lg q r e α1) (h2 : Anchor lg q r e α2) : α1 = α2 := by
  rcases h1 with ⟨hb1, hJ1, a1, r1, h1α, hr1, hu1⟩ | ⟨h1α, hk1⟩ <;>
  rcases h2 with ⟨hb2, hJ2, a2, r2, h2α, hr2, hu2⟩ | ⟨h2α, hk2⟩
  · rw [h1α] at hr1 ⊢
    rw [h2α] at hr2 ⊢
    by_cases hab : a1 = a2
    · rw [hab]
    · exact absurd (sib_disjoint hL hr1 hr2 hab) (Finset.not_disjoint_iff.mpr ⟨_, hu1, hu2⟩)
  · rw [h1α] at hr1
    rcases hk2 with hb | hW
    · rw [hb1] at hb; cases hb
    · exact absurd hu1 ((hL.wr q r hq e hW).2 a1 r1 hr1)
  · rw [h2α] at hr2
    rcases hk1 with hb | hW
    · rw [hb2] at hb; cases hb
    · exact absurd hu2 ((hL.wr q r hq e hW).2 a2 r2 hr2)
  · rw [h1α, h2α]

/-- **G2 for anchored events**: the same edge has the same anchor. -/
theorem isEvent_unique {e : Fin G.m} {α1 α2 : List ℕ} (h1 : IsEvent lg e α1) (h2 : IsEvent lg e α2) :
    α1 = α2 := by
  obtain ⟨q1, r1, hq1, he1, ha1⟩ := h1
  obtain ⟨q2, r2, hq2, he2, ha2⟩ := h2
  have hq := ev_unique hL hq1 hq2 he1 he2
  subst hq
  have hr := rec_unique hL.nodup hq1 hq2
  subst hr
  exact anchor_unique hL hq1 ha1 ha2

end G2

/-! ## The witness from local provenance -/

section Wit

variable {τ : ℕ → ℕ} {L0 : ℕ} {lg : Log G s Ω} (hL : LogInv τ L0 lg)

open Classical in
/-- The number of logged paths that ended before `y` started. -/
noncomputable def mu (lg : Log G s Ω) (y : List ℕ) : ℕ := (lg.paths.filter (fun p => Before p y)).card

theorem mu_le_of_imp {y y' : List ℕ} (h : ∀ p, Before p y' → Before p y) : mu lg y' ≤ mu lg y := by
  classical
  unfold mu
  exact Finset.card_le_card (fun p hp => by
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, h p hp.2⟩)

theorem mu_lt_of_before {y y' : List ℕ} (hy' : y' ∈ lg.paths) (h : Before y' y) : mu lg y' < mu lg y := by
  classical
  unfold mu
  apply Finset.card_lt_card
  refine ⟨fun p hp => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, before_trans hp.2 h⟩
  · have := hsub (Finset.mem_filter.mpr ⟨hy', h⟩)
    exact before_irrefl y' (Finset.mem_filter.mp this).2

include hL

/-- **Witness below a `Q`-ancestor**: if `v ∈ S_y` and `v ∈ Q_a` for a proper prefix `a` of `y`, some event with
head `v ≠ s` is anchored strictly inside `a` and ended before `y` started. -/
theorem wit_exists (hLP : LocalProv lg) :
    ∀ (n m : ℕ) (y : List ℕ) (ry : CallRec G s Ω), mu lg y = n → y.length = m → (y, ry) ∈ lg →
      ∀ v ∈ ry.S, ∀ a ra, a <+: y → a.length < y.length → (a, ra) ∈ lg → v ∈ ra.Q →
      ∃ e α, IsEvent lg e α ∧ G.dst e = v ∧ v ≠ s ∧ a <+: α ∧ a.length < α.length ∧ Before α y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro y ry hmu hlen hy v hv a ra ha hal hra hvQ
  have hyne : y ≠ [] := by rintro rfl; simp at hal
  obtain ⟨z, i, rfl⟩ := exists_concat_of_ne_nil hyne
  have haz : a <+: z := by
    have := prefix_dropLast ha (by rintro rfl; omega)
    rwa [List.dropLast_concat] at this
  have hzl : z.length < m := by rw [← hlen]; simp
  rcases hLP z i ry hy v hv with ⟨rz, hrz, hvS, hvQ'⟩ | hprov
  · have hza : a ≠ z := by
      rintro rfl
      have := rec_unique hL.nodup hra hrz
      subst this
      exact hvQ' hvQ
    have hal' : a.length < z.length := by
      have h1 := haz.length_le
      have h2 : a.length ≠ z.length := fun h => hza (haz.eq_of_length h)
      omega
    have hmu_le : mu lg z ≤ mu lg (z ++ [i]) := mu_le_of_imp (fun p hp => before_append hp [i])
    obtain ⟨e, α, hev, hd, hvs, h1, h2, h3⟩ : ∃ e α, IsEvent lg e α ∧ G.dst e = v ∧ v ≠ s ∧ a <+: α ∧
        a.length < α.length ∧ Before α z := by
      rcases Nat.lt_or_ge (mu lg z) n with hlt | hge
      · exact ihn _ hlt z.length z rz rfl rfl hrz v hvS a ra haz hal' hra hvQ
      · exact ihm z.length hzl z rz (by omega) rfl hrz v hvS a ra haz hal' hra hvQ
    exact ⟨e, α, hev, hd, hvs, h1, h2, before_append h3 [i]⟩
  · rcases hprov with ⟨e, α, hev, hd, hvs, b, α', rfl, hb⟩ | ⟨y', r', hy', hvS', b, y'', rfl, hb⟩
    · refine ⟨e, _, hev, hd, hvs, haz.trans (List.prefix_append _ _), ?_, before_of_child hb []⟩
      have := haz.length_le
      simp
      omega
    · have hbef : Before (z ++ b :: y'') (z ++ [i]) := before_of_child hb []
      have hmu' : mu lg (z ++ b :: y'') < n := by
        rw [← hmu]
        exact mu_lt_of_before (mem_paths.mpr ⟨r', hy'⟩) hbef
      have hlen' : a.length < (z ++ b :: y'').length := by
        have := haz.length_le
        simp
        omega
      obtain ⟨e, α, hev, hd, hvs, h1, h2, h3⟩ := ihn _ hmu' _ _ _ rfl rfl hy' v hvS' a ra
        (haz.trans (List.prefix_append _ _)) hlen' hra hvQ
      exact ⟨e, α, hev, hd, hvs, h1, h2, before_trans h3 hbef⟩

/-- **Witness without a `Q`-ancestor**: every `v ≠ s` in a frontier is the head of an event that ended before the
call started. -/
theorem wit0_exists (hLP : LocalProv lg) (hroot : ∀ r, ([], r) ∈ lg → r.S ⊆ {s}) :
    ∀ (n m : ℕ) (y : List ℕ) (ry : CallRec G s Ω), mu lg y = n → y.length = m → (y, ry) ∈ lg →
      ∀ v ∈ ry.S, v ≠ s → ∃ e α, IsEvent lg e α ∧ G.dst e = v ∧ Before α y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro y ry hmu hlen hy v hv hvs
  rcases eq_or_ne y [] with rfl | hyne
  · exact absurd (Finset.mem_singleton.mp (hroot ry hy hv)) hvs
  obtain ⟨z, i, rfl⟩ := exists_concat_of_ne_nil hyne
  have hzl : z.length < m := by rw [← hlen]; simp
  rcases hLP z i ry hy v hv with ⟨rz, hrz, hvS, -⟩ | hprov
  · have hmu_le : mu lg z ≤ mu lg (z ++ [i]) := mu_le_of_imp (fun p hp => before_append hp [i])
    obtain ⟨e, α, hev, hd, h3⟩ : ∃ e α, IsEvent lg e α ∧ G.dst e = v ∧ Before α z := by
      rcases Nat.lt_or_ge (mu lg z) n with hlt | hge
      · exact ihn _ hlt z.length z rz rfl rfl hrz v hvS hvs
      · exact ihm z.length hzl z rz (by omega) rfl hrz v hvS hvs
    exact ⟨e, α, hev, hd, before_append h3 [i]⟩
  · rcases hprov with ⟨e, α, hev, hd, -, b, α', rfl, hb⟩ | ⟨y', r', hy', hvS', b, y'', rfl, hb⟩
    · exact ⟨e, _, hev, hd, before_of_child hb []⟩
    · have hbef : Before (z ++ b :: y'') (z ++ [i]) := before_of_child hb []
      have hmu' : mu lg (z ++ b :: y'') < n := by
        rw [← hmu]
        exact mu_lt_of_before (mem_paths.mpr ⟨r', hy'⟩) hbef
      obtain ⟨e, α, hev, hd, h3⟩ := ihn _ hmu' _ _ _ rfl rfl hy' v hvS' hvs
      exact ⟨e, α, hev, hd, before_trans h3 hbef⟩

/-- **The `Q`-witness of full calls** (tracker O22(a), with O22(b)'s source exemption): an in-edge witness
`wit X v` of every `v ∈ Q_X \ {s}` of a full call `X`, injective over the full calls containing `v` in `Q`, and
the source in `Q` of at most one full call. -/
theorem qwit_of_prov (hLP : LocalProv lg) (hroot : ∀ r, ([], r) ∈ lg → r.S ⊆ {s}) (e0 : Fin G.m) :
    ∃ wit : lg.Call → Fin G.n → Fin G.m,
      (∀ X, (lg.recOf X).B' = (lg.recOf X).B → ∀ v ∈ (lg.recOf X).Q, v ≠ s → G.dst (wit X v) = v) ∧
      (∀ v X X', (lg.recOf X).B' = (lg.recOf X).B → (lg.recOf X').B' = (lg.recOf X').B →
        v ∈ (lg.recOf X).Q → v ∈ (lg.recOf X').Q → wit X v = wit X' v → X = X') ∧
      (∀ X X', (lg.recOf X).B' = (lg.recOf X).B → (lg.recOf X').B' = (lg.recOf X').B →
        s ∈ (lg.recOf X).Q → s ∈ (lg.recOf X').Q → X = X') := by
  classical
  let WP : lg.Call → Fin G.n → Fin G.m → Prop := fun X v e => G.dst e = v ∧ ∃ α, IsEvent lg e α ∧
    Before α X.1 ∧ ∀ a ra, a <+: X.1 → a.length < X.1.length → (a, ra) ∈ lg → v ∈ ra.Q →
      a <+: α ∧ a.length < α.length
  -- a `Q`-member of a call below a `Q`-ancestor forces an event strictly inside the ancestor
  have below : ∀ X v a ra, v ∈ (lg.recOf X).Q → a <+: X.1 → a.length < X.1.length → (a, ra) ∈ lg →
      v ∈ ra.Q → ∃ e α, IsEvent lg e α ∧ G.dst e = v ∧ v ≠ s ∧ a <+: α ∧ a.length < α.length ∧
        Before α X.1 := fun X v a ra hvQ ha hal hra hvQa =>
    wit_exists hL hLP _ _ X.1 (lg.recOf X) rfl rfl (recOf_mem X) v
      ((hL.facts _ _ (recOf_mem X)).Q_sub hvQ) a ra ha hal hra hvQa
  have hex : ∀ X v, v ∈ (lg.recOf X).Q → v ≠ s → ∃ e, WP X v e := by
    intro X v hvQ hvs
    have hvS : v ∈ (lg.recOf X).S := (hL.facts _ _ (recOf_mem X)).Q_sub hvQ
    set J := (Finset.range X.1.length).filter (fun j => ∃ ra, (X.1.take j, ra) ∈ lg ∧ v ∈ ra.Q) with hJ
    by_cases hJne : J.Nonempty
    · have hmem := J.max'_mem hJne
      obtain ⟨hjm', ra, hra, hvQa⟩ := Finset.mem_filter.mp hmem
      have hjm := Finset.mem_range.mp hjm'
      obtain ⟨e, α, hev, hd, -, h1, h2, h3⟩ := below X v (X.1.take (J.max' hJne)) ra hvQ
        (List.take_prefix _ _) (by rw [List.length_take]; omega) hra hvQa
      refine ⟨e, hd, α, hev, h3, fun a ra' ha hal hra' hvQ' => ?_⟩
      have ha' : a = X.1.take a.length := List.prefix_iff_eq_take.mp ha
      have hin : a.length ∈ J :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hal, ra', by rw [← ha']; exact hra', hvQ'⟩
      have hle : a.length ≤ J.max' hJne := J.le_max' _ hin
      have hpre : a <+: X.1.take (J.max' hJne) := by
        rw [ha']
        have e1 : (X.1.take (J.max' hJne)).take a.length = X.1.take a.length := by
          rw [List.take_take, min_eq_left hle]
        rw [← e1]
        exact List.take_prefix _ _
      exact ⟨hpre.trans h1, lt_of_le_of_lt hpre.length_le h2⟩
    · obtain ⟨e, α, hev, hd, h3⟩ := wit0_exists hL hLP hroot _ _ X.1 (lg.recOf X) rfl rfl (recOf_mem X) v
        hvS hvs
      refine ⟨e, hd, α, hev, h3, fun a ra ha hal hra hvQ' => ?_⟩
      refine absurd ⟨a.length, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hal, ra, ?_, hvQ'⟩⟩ hJne
      rw [← List.prefix_iff_eq_take.mp ha]
      exact hra
  let wit : lg.Call → Fin G.n → Fin G.m := fun X v => if h : ∃ e, WP X v e then h.choose else e0
  have hwit : ∀ X v, v ∈ (lg.recOf X).Q → v ≠ s → WP X v (wit X v) := by
    intro X v hvQ hvs
    have h := hex X v hvQ hvs
    simp only [wit, dif_pos h]
    exact h.choose_spec
  -- two full calls with `v` in `Q` are prefix-comparable
  have hcomp : ∀ v (X X' : lg.Call), (lg.recOf X).B' = (lg.recOf X).B → (lg.recOf X').B' = (lg.recOf X').B →
      v ∈ (lg.recOf X).Q → v ∈ (lg.recOf X').Q → X.1 <+: X'.1 ∨ X'.1 <+: X.1 := by
    intro v X X' hf hf' hv hv'
    have hU : v ∈ (lg.recOf X).U :=
      (hL.facts _ _ (recOf_mem X)).full_S hf ((hL.facts _ _ (recOf_mem X)).Q_sub hv)
    have hU' : v ∈ (lg.recOf X').U :=
      (hL.facts _ _ (recOf_mem X')).full_S hf' ((hL.facts _ _ (recOf_mem X')).Q_sub hv')
    exact prefix_chain hL (recOf_mem X) (recOf_mem X') hU hU'
  -- a strict prefix relation between two full `Q`-calls of `v`
  have strict : ∀ (X X' : lg.Call), X'.1 <+: X.1 → X ≠ X' → X'.1.length < X.1.length := by
    intro X X' h hne
    have h1 := h.length_le
    have h2 : X'.1.length ≠ X.1.length := fun heq => hne (Subtype.ext (h.eq_of_length heq).symm)
    omega
  -- the source is in `Q` of at most one full call
  have hsrc : ∀ (X X' : lg.Call), (lg.recOf X).B' = (lg.recOf X).B → (lg.recOf X').B' = (lg.recOf X').B →
      s ∈ (lg.recOf X).Q → s ∈ (lg.recOf X').Q → X = X' := by
    intro X X' hf hf' hs hs'
    by_contra hne
    rcases hcomp s X X' hf hf' hs hs' with h | h
    · obtain ⟨e, α, -, -, hvs, -⟩ := below X' s X.1 (lg.recOf X) hs' h
        (strict X' X h (fun h' => hne h'.symm)) (recOf_mem X) hs
      exact hvs rfl
    · obtain ⟨e, α, -, -, hvs, -⟩ := below X s X'.1 (lg.recOf X') hs h (strict X X' h hne)
        (recOf_mem X') hs'
      exact hvs rfl
  refine ⟨wit, fun X _ v hv hvs => (hwit X v hv hvs).1, fun v X X' hf hf' hv hv' heq => ?_, hsrc⟩
  by_cases hvs : v = s
  · subst hvs; exact hsrc X X' hf hf' hv hv'
  by_contra hne
  -- the deeper call's witness is anchored inside the shallower call; the shallower call's ended before it
  have key : ∀ (X X' : lg.Call), v ∈ (lg.recOf X).Q → v ∈ (lg.recOf X').Q → wit X v = wit X' v →
      X'.1 <+: X.1 → X ≠ X' → False := by
    intro X X' hv hv' heq h hne
    obtain ⟨-, α, hev, -, hall⟩ := hwit X v hv hvs
    obtain ⟨-, α', hev', hbef', -⟩ := hwit X' v hv' hvs
    have hin := hall X'.1 (lg.recOf X') h (strict X X' h hne) (recOf_mem X') hv'
    rw [heq] at hev
    have := isEvent_unique hL hev hev'
    subst this
    exact not_before_of_prefix hin.1 hbef'
  rcases hcomp v X X' hf hf' hv hv' with h | h
  · exact key X' X hv' hv heq.symm h (fun h' => hne h'.symm)
  · exact key X X' hv hv' heq h hne

end Wit

end BM
end CHD
end Frontier
