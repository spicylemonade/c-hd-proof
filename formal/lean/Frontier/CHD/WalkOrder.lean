import Frontier.Spec
import Mathlib.Data.List.Lex
import Mathlib.Data.Prod.Lex
import Mathlib.Order.Fin.Basic

/-!
# Frontier.CHD.WalkOrder — the full walk order `κ` and the canonical shortest-path tree

Owner: agent-08 (C-HD work package L1).  NON-GATE.

This is the semantic tie-breaking of the B1 core (S1 §A, "full walk order", KR26 Property 1
refined by edge ids) that the C-HD paper proof inherits.  For an edge list `p`, read as a walk
from the source `s`,

  `κ(p) = (len p, #edges p, end vertex, p reversed)`   compared lexicographically.

`κ` is injective, so it induces a linear order on edge lists (`WalkOrd`).  Proved here:

* (O2) suffix invariance `P < Q ⇒ P ++ R < Q ++ R` for walks ending at the same vertex;
* (O3) a proper extension is strictly larger;
* (O5) every walk can be shortcut to a vertex-simple walk that is not larger;
* (O4) every reachable `v` has a UNIQUE `κ`-minimum walk `path v` (`IsMinWalk`), prefixes of
  minimum walks are minimum walks (canonical arborescence), and vertices strictly before `v` on it
  have strictly smaller canonical walks;
* the canonical walk has length exactly `Graph.dist s v`, so exact real distances are read off.

Algorithm labels in Layer A are walks from `s` (`WithTop (WalkOrd G s)`); the relaxation
`λ ⊕ e` is `λ ++ [e]`.  The version-stamped 5-tuple representation of B1 (O(1) comparisons) is the
Layer-B implementation of these comparisons.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD

open Frontier Graph

variable (G : Graph) (s : Fin G.n)

/-- End vertex of an edge list read as a walk from `s` (`s` for the empty list). -/
def endV (p : List (Fin G.m)) : Fin G.n :=
  match p.getLast? with
  | none => s
  | some e => G.dst e

/-- The walk-order key `κ`. -/
def kap (p : List (Fin G.m)) : ℝ≥0 ×ₗ (ℕ ×ₗ (Fin G.n ×ₗ List (Fin G.m))) :=
  toLex (G.len p, toLex (p.length, toLex (endV G s p, p.reverse)))

theorem kap_injective : Function.Injective (kap G s) := by
  intro p q h
  simp only [kap, toLex_inj, Prod.mk.injEq] at h
  exact List.reverse_injective h.2.2.2

/-- Edge lists (walks from `s`) ordered by `κ`.  (The source `s` is a parameter because the
order depends on it through the end vertex of the empty walk.) -/
@[nolint unusedArguments]
def WalkOrd (G : Graph) (_s : Fin G.n) : Type := List (Fin G.m)

noncomputable instance : LinearOrder (WalkOrd G s) :=
  LinearOrder.lift' (kap G s) (kap_injective G s)

variable {G s}

/-- View an edge list in the walk order. -/
def toW {G : Graph} {s : Fin G.n} (p : List (Fin G.m)) : WalkOrd G s := p

theorem lt_iff_kap {p q : List (Fin G.m)} :
    (toW (s := s) p) < toW q ↔ kap G s p < kap G s q := Iff.rfl

theorem le_iff_kap {p q : List (Fin G.m)} :
    (toW (s := s) p) ≤ toW q ↔ kap G s p ≤ kap G s q := Iff.rfl

/-! ## End vertices of walks -/

theorem endV_append_ne {p r : List (Fin G.m)} (hr : r ≠ []) :
    endV G s (p ++ r) = endV G s r := by
  unfold endV
  rw [List.getLast?_append_of_ne_nil _ hr]

/-- For a nonempty list the end vertex does not depend on the start. -/
theorem endV_start_irrel {u w : Fin G.n} {p : List (Fin G.m)} (hp : p ≠ []) :
    endV G u p = endV G w p := by
  unfold endV
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp (mt List.getLast?_eq_none_iff.mp hp)
  rw [he]

/-- The end vertex of a walk from `u` to `v` is `v`. -/
theorem isWalk_endV {u v : Fin G.n} {p : List (Fin G.m)} (h : G.IsWalk u v p) :
    endV G u p = v := by
  induction h with
  | nil u => rfl
  | @cons e v p h ih =>
    cases p with
    | nil =>
      rw [isWalk_nil_iff] at h
      simp [endV, h]
    | cons e' p' =>
      have hne : (e' :: p') ≠ [] := List.cons_ne_nil _ _
      have h1 : endV G (G.src e) ([e] ++ e' :: p') = endV G (G.src e) (e' :: p') :=
        endV_append_ne hne
      simp only [List.singleton_append] at h1
      rw [h1, endV_start_irrel hne, ih]

theorem endV_of_isWalk {v : Fin G.n} {p : List (Fin G.m)} (h : G.IsWalk s v p) :
    endV G s p = v := isWalk_endV h

/-! ## (O2) suffix invariance and (O3) strict growth -/

/-- (O2) Appending the same walk preserves the strict order of two walks to the same vertex. -/
theorem append_lt_append {u w : Fin G.n} {P Q R : List (Fin G.m)} (hP : G.IsWalk s u P)
    (hQ : G.IsWalk s u Q) (hR : G.IsWalk u w R) (h : toW (s := s) P < toW Q) :
    toW (s := s) (P ++ R) < toW (Q ++ R) := by
  rw [lt_iff_kap] at h ⊢
  simp only [kap, Prod.Lex.toLex_lt_toLex] at h ⊢
  have hE : endV G s P = endV G s Q := by rw [endV_of_isWalk hP, endV_of_isWalk hQ]
  have hER : endV G s (P ++ R) = endV G s (Q ++ R) := by
    rw [endV_of_isWalk (hP.append hR), endV_of_isWalk (hQ.append hR)]
  simp only [len_append, List.length_append, List.reverse_append]
  rcases h with h | ⟨h1, h⟩
  · left; exact add_lt_add_of_lt_of_le h le_rfl
  · right
    refine ⟨by rw [h1], ?_⟩
    rcases h with h | ⟨h2, h⟩
    · left; omega
    · right
      refine ⟨by rw [h2], ?_⟩
      rcases h with h | ⟨_, h⟩
      · exact absurd hE (ne_of_lt h)
      · right
        refine ⟨hER, ?_⟩
        exact (List.lt_iff_lex_lt _ _).mpr (List.Lex.append_left _
          ((List.lt_iff_lex_lt _ _).mp h) _)

theorem append_le_append {u w : Fin G.n} {P Q R : List (Fin G.m)} (hP : G.IsWalk s u P)
    (hQ : G.IsWalk s u Q) (hR : G.IsWalk u w R) (h : toW (s := s) P ≤ toW Q) :
    toW (s := s) (P ++ R) ≤ toW (Q ++ R) := by
  rcases h.lt_or_eq with h | h
  · exact (append_lt_append hP hQ hR h).le
  · have : P = Q := h
    subst this; exact le_rfl

/-- (O3) A proper extension is strictly larger. -/
theorem lt_append {P R : List (Fin G.m)} (hR : R ≠ []) : toW (s := s) P < toW (P ++ R) := by
  rw [lt_iff_kap]
  simp only [kap, Prod.Lex.toLex_lt_toLex]
  have hlen : G.len P ≤ G.len (P ++ R) := by rw [len_append]; exact le_self_add
  rcases hlen.lt_or_eq with h | h
  · exact Or.inl h
  · right
    refine ⟨h, Or.inl ?_⟩
    have : R.length ≠ 0 := by simpa using hR
    simp only [List.length_append]
    omega

/-! ## (O5) shortcutting -/

/-- Every walk can be shortcut to a vertex-simple walk with the same endpoints that is either the
walk itself or has strictly fewer edges and no larger length. -/
theorem IsWalk.exists_path_sub {u v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk u v p) :
    ∃ q, G.IsWalk u v q ∧ (G.verts u q).Nodup ∧
      (q = p ∨ (G.len q ≤ G.len p ∧ q.length < p.length)) := by
  induction hp with
  | nil u => exact ⟨[], IsWalk.nil u, by simp, Or.inl rfl⟩
  | @cons e v p h ih =>
    obtain ⟨q, hq, hnd, hqp⟩ := ih
    by_cases hmem : G.src e ∈ G.verts (G.dst e) q
    · obtain ⟨pre, suf, rfl, _, hsuf, hsx⟩ := hq.split_at_mem hmem
      refine ⟨suf, hsuf, hnd.sublist hsx.sublist, Or.inr ⟨?_, ?_⟩⟩
      · rcases hqp with hqp | ⟨hl, _⟩
        · subst hqp
          simp only [len_cons, len_append]
          calc G.len suf ≤ G.len pre + G.len suf := le_add_self
            _ ≤ G.w e + (G.len pre + G.len suf) := le_add_self
        · simp only [len_cons, len_append] at hl ⊢
          calc G.len suf ≤ G.len pre + G.len suf := le_add_self
            _ ≤ G.len p := hl
            _ ≤ G.w e + G.len p := le_add_self
      · rcases hqp with hqp | ⟨_, hl⟩
        · subst hqp; simp only [List.length_cons, List.length_append]; omega
        · simp only [List.length_append] at hl; simp only [List.length_cons]; omega
    · refine ⟨e :: q, IsWalk.cons hq, ?_, ?_⟩
      · rw [verts_cons]; exact List.nodup_cons.mpr ⟨hmem, hnd⟩
      · rcases hqp with hqp | ⟨hl, hlen⟩
        · exact Or.inl (by rw [hqp])
        · right
          refine ⟨?_, ?_⟩
          · simp only [len_cons]; exact add_le_add le_rfl hl
          · simp only [List.length_cons]; omega

/-- (O5) in walk-order form: a vertex-simple walk that is not larger. -/
theorem IsWalk.exists_simple_le {v : Fin G.n} {p : List (Fin G.m)} (hp : G.IsWalk s v p) :
    ∃ q, G.IsWalk s v q ∧ (G.verts s q).Nodup ∧ toW (s := s) q ≤ toW p := by
  obtain ⟨q, hq, hnd, hqp⟩ := IsWalk.exists_path_sub hp
  refine ⟨q, hq, hnd, ?_⟩
  rcases hqp with rfl | ⟨hl, hlen⟩
  · exact le_rfl
  · refine le_of_lt ?_
    rw [lt_iff_kap]
    simp only [kap, Prod.Lex.toLex_lt_toLex]
    rcases hl.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inl hlen⟩

/-! ## (O4) the canonical minimum walk -/

/-- `p` is the `κ`-minimum walk from `s` to `v`. -/
def IsMinWalk (v : Fin G.n) (p : List (Fin G.m)) : Prop :=
  G.IsWalk s v p ∧ ∀ q, G.IsWalk s v q → toW (s := s) p ≤ toW q

theorem exists_minWalk {v : Fin G.n} (h : G.Reachable s v) : ∃ p, IsMinWalk (s := s) v p := by
  classical
  let S : Set (List (Fin G.m)) := {p | p.length < G.n ∧ G.IsWalk s v p ∧ (G.verts s p).Nodup}
  have hfin : S.Finite := (List.finite_length_lt (Fin G.m) G.n).subset fun p hp => hp.1
  obtain ⟨p0, hp0⟩ := h
  obtain ⟨q0, hq0, hnd0, -⟩ := IsWalk.exists_simple_le hp0
  have hne : S.Nonempty := ⟨q0, length_lt_of_nodup hnd0, hq0, hnd0⟩
  obtain ⟨p, ⟨-, hpw, -⟩, hmin⟩ := Set.exists_min_image S (fun p => toW (s := s) p) hfin hne
  refine ⟨p, hpw, fun q hq => ?_⟩
  obtain ⟨q', hq', hnd, hle⟩ := IsWalk.exists_simple_le hq
  exact (hmin q' ⟨length_lt_of_nodup hnd, hq', hnd⟩).trans hle

theorem IsMinWalk.unique {v : Fin G.n} {p q : List (Fin G.m)} (hp : IsMinWalk (s := s) v p)
    (hq : IsMinWalk (s := s) v q) : p = q :=
  (le_antisymm (hp.2 q hq.1) (hq.2 p hp.1) : (toW p : WalkOrd G s) = toW q)

/-- (O4) prefixes of minimum walks are minimum walks. -/
theorem IsMinWalk.prefix {u v : Fin G.n} {P R : List (Fin G.m)}
    (h : IsMinWalk (s := s) v (P ++ R)) (hP : G.IsWalk s u P) (hR : G.IsWalk u v R) :
    IsMinWalk (s := s) u P := by
  refine ⟨hP, fun Q hQ => ?_⟩
  by_contra hlt
  push Not at hlt
  have h1 := append_lt_append hQ hP hR hlt
  exact absurd (h.2 (Q ++ R) (hQ.append hR)) (not_le.mpr h1)

/-- The canonical path (noncomputable; used only in specifications). -/
noncomputable def path (v : Fin G.n) : List (Fin G.m) := by
  classical
  exact if h : G.Reachable s v then Classical.choose (exists_minWalk h) else []

theorem path_isMinWalk {v : Fin G.n} (h : G.Reachable s v) :
    IsMinWalk (s := s) v (path (s := s) v) := by
  classical
  simp only [path, h, dite_true]
  exact Classical.choose_spec (exists_minWalk h)

theorem path_eq_of_isMinWalk {v : Fin G.n} {p : List (Fin G.m)} (h : IsMinWalk (s := s) v p) :
    path (s := s) v = p :=
  (path_isMinWalk ⟨p, h.1⟩).unique h

/-- The canonical distance label: the minimum walk, `⊤` if unreachable. -/
noncomputable def dis (v : Fin G.n) : WithTop (WalkOrd G s) := by
  classical
  exact if G.Reachable s v then ((toW (s := s) (path (s := s) v) : WalkOrd G s) : WithTop _) else ⊤

theorem dis_of_reachable {v : Fin G.n} (h : G.Reachable s v) :
    dis (s := s) v = ((toW (path (s := s) v) : WalkOrd G s) : WithTop _) := by
  classical
  simp [dis, h]

theorem dis_of_not_reachable {v : Fin G.n} (h : ¬ G.Reachable s v) : dis (s := s) v = ⊤ := by
  classical
  simp [dis, h]

theorem dis_le_walk {v : Fin G.n} {q : List (Fin G.m)} (hq : G.IsWalk s v q) :
    dis (s := s) v ≤ ((toW q : WalkOrd G s) : WithTop _) := by
  rw [dis_of_reachable ⟨q, hq⟩]
  exact WithTop.coe_le_coe.mpr ((path_isMinWalk ⟨q, hq⟩).2 q hq)

/-- The canonical walk has length exactly the real distance. -/
theorem len_path {v : Fin G.n} (h : G.Reachable s v) :
    ((G.len (path (s := s) v) : ℝ≥0) : ℝ≥0∞) = G.dist s v := by
  have hmin := path_isMinWalk (s := s) h
  refine le_antisymm ?_ (dist_le_len hmin.1)
  obtain ⟨p, hp, hpe, -, -⟩ := exists_shortest_path h
  rw [← hpe]
  have hle := hmin.2 p hp
  rw [le_iff_kap] at hle
  simp only [kap, Prod.Lex.toLex_le_toLex] at hle
  refine ENNReal.coe_le_coe.mpr ?_
  rcases hle with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-- The source's canonical walk is empty. -/
theorem path_source : path (s := s) s = [] :=
  path_eq_of_isMinWalk ⟨IsWalk.nil s, fun q _ => by
    by_cases hq : q = []
    · subst hq; exact le_rfl
    · exact (lt_append (s := s) (P := []) hq).le⟩

/-! ## Canonical paths visiting vertices -/

/-- `y` lies on the canonical path of `v`: the canonical path of `v` extends a walk to `y`. -/
def OnPath (y v : Fin G.n) : Prop :=
  G.Reachable s v ∧ ∃ P R, path (s := s) v = P ++ R ∧ G.IsWalk s y P ∧ G.IsWalk y v R

/-- If `y` is on `v`'s canonical path, the prefix is `y`'s canonical path. -/
theorem OnPath.path_prefix {y v : Fin G.n} (h : OnPath (s := s) y v) :
    ∃ R, path (s := s) v = path (s := s) y ++ R ∧ G.IsWalk y v R := by
  obtain ⟨hv, P, R, hPR, hP, hR⟩ := h
  have hmin : IsMinWalk (s := s) v (P ++ R) := hPR ▸ path_isMinWalk hv
  have hPy : path (s := s) y = P := path_eq_of_isMinWalk (hmin.prefix hP hR)
  exact ⟨R, by rw [hPR, hPy], hR⟩

theorem onPath_self {v : Fin G.n} (h : G.Reachable s v) : OnPath (s := s) v v :=
  ⟨h, path (s := s) v, [], by simp, (path_isMinWalk h).1, IsWalk.nil v⟩

theorem OnPath.reachable_left {y v : Fin G.n} (h : OnPath (s := s) y v) : G.Reachable s y :=
  let ⟨_, P, _, _, hP, _⟩ := h; ⟨P, hP⟩

theorem OnPath.trans {x y v : Fin G.n} (h₁ : OnPath (s := s) x y) (h₂ : OnPath (s := s) y v) :
    OnPath (s := s) x v := by
  obtain ⟨R₁, hR₁, hw₁⟩ := h₁.path_prefix
  obtain ⟨R₂, hR₂, hw₂⟩ := h₂.path_prefix
  refine ⟨h₂.1, path (s := s) x, R₁ ++ R₂, by rw [hR₂, hR₁, List.append_assoc],
    (path_isMinWalk h₁.reachable_left).1, hw₁.append hw₂⟩

/-- Vertices strictly before `v` on its canonical path have strictly smaller canonical walks. -/
theorem OnPath.dis_lt {y v : Fin G.n} (h : OnPath (s := s) y v) (hyv : y ≠ v) :
    dis (s := s) y < dis (s := s) v := by
  obtain ⟨R, hR, hw⟩ := h.path_prefix
  have hRne : R ≠ [] := by
    rintro rfl
    exact hyv (by simpa [endV] using isWalk_endV hw)
  rw [dis_of_reachable h.reachable_left, dis_of_reachable h.1, hR]
  exact WithTop.coe_lt_coe.mpr (lt_append hRne)

theorem OnPath.dis_le {y v : Fin G.n} (h : OnPath (s := s) y v) :
    dis (s := s) y ≤ dis (s := s) v := by
  by_cases hyv : y = v
  · subst hyv; exact le_rfl
  · exact (h.dis_lt hyv).le

end CHD
end Frontier
