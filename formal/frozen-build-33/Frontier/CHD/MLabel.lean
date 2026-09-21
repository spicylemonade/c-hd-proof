import Frontier.CHD.WalkOrder

/-!
# MLabel — O(1) machine labels realize the full walk order κ (agent-02, Layer B, NON-GATE)

Layer A (Frontier.CHD.WalkOrder) compares labels as WALKS by `κ = (len, #edges, end vertex,
reversed walk)`.  A RAM implementation stores O(1)-size labels instead (B1 S1 §A):

  `(len, hops, v, e, ver)` = length, hop count, end vertex, last edge (`none` for the source),
  and the version of the tail's label at the moment the label was written.

A label represents the walk `H (src e) ver ++ [e]`, where the ghost history `H u a` is the walk
represented by `u`'s label at version `a`.  If every vertex's history is strictly κ-decreasing in
the version (a label version is bumped exactly on a strict decrease), then the O(1) comparison
`MLabel.lt` (one real comparison of `len` plus integer comparisons; a larger version is SMALLER)
agrees with κ, and equal machine labels represent equal walks.  This is the lemma every comparison
site of the RAM refinement (Relax, D keep-min on the same key, Pull separators, bound tests) uses.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace MLab

open Frontier Graph

variable {G : Graph} {s : Fin G.n}

/-- O(1)-size machine label. -/
structure MLabel (G : Graph) where
  len : ℝ≥0
  hops : ℕ
  v : Fin G.n
  e : Option (Fin G.m)
  ver : ℕ

/-- Order on the optional last edge: `none` (source) is smallest. -/
def OptLt : Option (Fin G.m) → Option (Fin G.m) → Prop
  | none, some _ => True
  | some a, some b => a < b
  | _, _ => False

/-- Machine comparison "strictly smaller" (a larger version means a strictly smaller walk). -/
def MLabel.lt (x y : MLabel G) : Prop :=
  x.len < y.len ∨ (x.len = y.len ∧ (x.hops < y.hops ∨ (x.hops = y.hops ∧
    (x.v < y.v ∨ (x.v = y.v ∧ (OptLt x.e y.e ∨ (x.e = y.e ∧ y.ver < x.ver)))))))

/-- The walk represented by a machine label, given the ghost history `H`. -/
def walkOf (H : Fin G.n → ℕ → List (Fin G.m)) (x : MLabel G) : List (Fin G.m) :=
  match x.e with
  | none => []
  | some e => H (G.src e) x.ver ++ [e]

/-- `x` represents walk `p` (from `s`): its first three fields are `p`'s κ-prefix and `p` is the
history walk of the tail extended by the last edge. -/
def Rep (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (x : MLabel G)
    (p : List (Fin G.m)) : Prop :=
  p = walkOf H x ∧ x.len = G.len p ∧ x.hops = p.length ∧ x.v = endV G s p ∧
    (x.e = none → x.ver = 0) ∧ (∀ e, x.e = some e → 1 ≤ x.ver ∧ x.ver ≤ V (G.src e))

/-- The history up to the current version counters `V`: the finite labels `u` has had are the
versions `1 .. V u` (`V u = 0`: never finite); they are walks from `s` to `u`, strictly
κ-decreasing in the version. -/
structure GoodHist (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) : Prop where
  walk : ∀ u a, 1 ≤ a → a ≤ V u → G.IsWalk s u (H u a)
  anti : ∀ u a b, 1 ≤ a → a < b → b ≤ V u → toW (s := s) (H u b) < toW (H u a)

/-! ### Auxiliary facts -/

theorem walkOf_ne_nil {H : Fin G.n → ℕ → List (Fin G.m)} {x : MLabel G} {e : Fin G.m}
    (he : x.e = some e) : walkOf H x ≠ [] := by
  simp [walkOf, he]

theorem walkOf_nil {H : Fin G.n → ℕ → List (Fin G.m)} {x : MLabel G} (he : x.e = none) :
    walkOf H x = [] := by
  simp [walkOf, he]

theorem hist_lt_iff {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    (hH : GoodHist (s := s) H V) (u : Fin G.n) {a b : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ V u)
    (hb1 : 1 ≤ b) (hb : b ≤ V u) :
    toW (s := s) (H u a) < toW (H u b) ↔ b < a := by
  constructor
  · intro h
    rcases lt_trichotomy a b with hab | hab | hab
    · exact absurd h (not_lt.mpr (hH.anti u a b ha1 hab hb).le)
    · subst hab; exact absurd h (lt_irrefl _)
    · exact hab
  · intro h; exact hH.anti u b a hb1 h ha

theorem hist_eq_iff {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    (hH : GoodHist (s := s) H V) (u : Fin G.n) {a b : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ V u)
    (hb1 : 1 ≤ b) (hb : b ≤ V u) :
    H u a = H u b ↔ a = b := by
  constructor
  · intro h
    rcases lt_trichotomy a b with hab | hab | hab
    · have := hH.anti u a b ha1 hab hb
      rw [show toW (s := s) (H u b) = toW (H u a) from congrArg toW h.symm] at this
      exact absurd this (lt_irrefl _)
    · exact hab
    · have := hH.anti u b a hb1 hab ha
      rw [show toW (s := s) (H u a) = toW (H u b) from congrArg toW h] at this
      exact absurd this (lt_irrefl _)
  · rintro rfl; rfl

/-- κ of equal-length, equal-hop, equal-endpoint walks is decided by the reversed walks. -/
theorem kap_lt_iff_rev {p q : List (Fin G.m)} (hl : G.len p = G.len q) (hh : p.length = q.length)
    (hv : endV G s p = endV G s q) : kap G s p < kap G s q ↔ p.reverse < q.reverse := by
  simp only [kap, Prod.Lex.toLex_lt_toLex, hl, hh, hv, lt_irrefl, false_or, true_and]

theorem walk_endV_append {P : List (Fin G.m)} (e : Fin G.m) :
    endV G s (P ++ [e]) = G.dst e := by
  rw [endV_append_ne (List.cons_ne_nil e [])]
  rfl

/-! ### Main theorem -/

/-- Lengths of two history walks agree when their one-edge extensions do. -/
theorem len_hist_eq {P Q : List (Fin G.m)} {e : Fin G.m}
    (h : G.len (P ++ [e]) = G.len (Q ++ [e])) : G.len P = G.len Q := by
  simp only [len_append, len_singleton] at h
  exact add_right_cancel h

/-- **Exactness of the O(1) comparison.**  If `x` and `y` represent walks `p` and `q` for a good
history, the machine comparison `x.lt y` holds iff `p < q` in the walk order κ. -/
theorem lt_iff {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} (hH : GoodHist (s := s) H V)
    {x y : MLabel G} {p q : List (Fin G.m)} (hx : Rep (s := s) H V x p) (hy : Rep (s := s) H V y q) :
    x.lt y ↔ toW (s := s) p < toW q := by
  obtain ⟨hpx, hlx, hhx, hvx, hx0, hxV⟩ := hx
  obtain ⟨hqy, hly, hhy, hvy, hy0, hyV⟩ := hy
  rw [lt_iff_kap]
  simp only [MLabel.lt, kap, Prod.Lex.toLex_lt_toLex, hlx, hhx, hvx, hly, hhy, hvy]
  -- after the first three κ-coordinates, compare the tails
  by_cases hl : G.len p = G.len q
  · by_cases hh : p.length = q.length
    · by_cases hv : endV G s p = endV G s q
      · simp only [hl, hh, hv, lt_irrefl, false_or, true_and]
        -- reversed walks vs (last edge, version)
        cases hxe : x.e with
        | none =>
          have hp0 : p = [] := by rw [hpx, walkOf_nil hxe]
          have hq0 : q = [] := by
            subst hp0; simpa using hh.symm
          cases hye : y.e with
          | none => simp [OptLt, hp0, hq0, hx0 hxe, hy0 hye]
          | some e' =>
            have := walkOf_ne_nil (H := H) hye
            rw [← hqy] at this; exact absurd hq0 this
        | some e =>
          cases hye : y.e with
          | none =>
            have hq0 : q = [] := by rw [hqy, walkOf_nil hye]
            have hp0 : p = [] := by subst hq0; simpa using hh
            have := walkOf_ne_nil (H := H) hxe
            rw [← hpx] at this; exact absurd hp0 this
          | some e' =>
            have hp : p = H (G.src e) x.ver ++ [e] := by rw [hpx]; simp [walkOf, hxe]
            have hq : q = H (G.src e') y.ver ++ [e'] := by rw [hqy]; simp [walkOf, hye]
            rw [hp, hq]
            simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
              OptLt, Option.some.injEq]
            rw [List.cons_lt_cons_iff]
            by_cases hee : e = e'
            · subst hee
              simp only [lt_irrefl, false_or, true_and]
              -- equal last edge: compare history walks of the same tail
              have hl' : G.len (H (G.src e) x.ver) = G.len (H (G.src e) y.ver) := by
                have := hl; rw [hp, hq] at this; exact len_hist_eq this
              have hh' : (H (G.src e) x.ver).length = (H (G.src e) y.ver).length := by
                have := hh; rw [hp, hq] at this; simpa using this
              have hv' : endV G s (H (G.src e) x.ver) = endV G s (H (G.src e) y.ver) := by
                rw [endV_of_isWalk (hH.walk _ _ (hxV e hxe).1 (hxV e hxe).2),
                  endV_of_isWalk (hH.walk _ _ (hyV e hye).1 (hyV e hye).2)]
              rw [← kap_lt_iff_rev hl' hh' hv', ← lt_iff_kap,
                hist_lt_iff hH _ (hxV e hxe).1 (hxV e hxe).2 (hyV e hye).1 (hyV e hye).2]
            · simp only [hee, false_and, or_false]
      · -- different end vertex: decided by `v`, both sides
        have hvlt : endV G s p < endV G s q ∨ endV G s q < endV G s p := lt_or_gt_of_ne hv
        simp only [hl, hh, lt_irrefl, false_or, true_and, hv, false_and, or_false]
    · simp only [hl, hh, lt_irrefl, false_or, true_and, false_and, or_false]
  · simp only [hl, false_and, or_false]

/-- **Equality**: equal machine labels represent equal walks and conversely. -/
theorem eq_iff {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} (hH : GoodHist (s := s) H V)
    {x y : MLabel G} {p q : List (Fin G.m)} (hx : Rep (s := s) H V x p) (hy : Rep (s := s) H V y q) :
    x = y ↔ p = q := by
  constructor
  · rintro rfl
    rw [hx.1, hy.1]
  · intro hpq
    subst hpq
    obtain ⟨hpx, hlx, hhx, hvx, hx0, hxV⟩ := hx
    obtain ⟨hqy, hly, hhy, hvy, hy0, hyV⟩ := hy
    cases x with
    | mk xl xh xv xe xver =>
    cases y with
    | mk yl yh yv ye yver =>
    simp only at hlx hhx hvx hly hhy hvy hpx hqy hx0 hy0 hxV hyV
    have hl : xl = yl := by rw [hlx, hly]
    have hh : xh = yh := by rw [hhx, hhy]
    have hv : xv = yv := by rw [hvx, hvy]
    cases xe with
    | none =>
      cases ye with
      | none =>
        have h1 := hx0 rfl
        have h2 := hy0 rfl
        subst h1 h2 hl hh hv
        rfl
      | some e' =>
        simp only [walkOf] at hpx hqy
        rw [hqy] at hpx; exact absurd hpx (by simp)
    | some e =>
      cases ye with
      | none =>
        simp only [walkOf] at hpx hqy
        rw [hqy] at hpx; exact absurd hpx (by simp)
      | some e' =>
        simp only [walkOf] at hpx hqy
        have h2 := hpx.symm.trans hqy
        have hlast := congrArg List.getLast? h2
        simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
          Option.some.injEq] at hlast
        subst hlast
        have htail := List.append_cancel_right h2
        have hver := (hist_eq_iff hH _ (hxV e rfl).1 (hxV e rfl).2 (hyV e rfl).1
          (hyV e rfl).2).mp htail
        subst hver hl hh hv
        rfl

/-! ### Maintaining the history: a strict decrease bumps the version -/

/-- Extending the history of `v` by a new walk to `v` keeps it good, provided the new walk is
strictly below `v`'s current label (or `v` never had a finite label, `V v = 0`). -/
theorem GoodHist.bump {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    (hH : GoodHist (s := s) H V) (v : Fin G.n) (W : List (Fin G.m)) (hW : G.IsWalk s v W)
    (hlt : V v = 0 ∨ toW (s := s) W < toW (H v (V v))) :
    GoodHist (s := s) (Function.update H v (Function.update (H v) (V v + 1) W))
      (Function.update V v (V v + 1)) := by
  constructor
  · intro u a ha1 ha
    by_cases hu : u = v
    · subst hu
      simp only [Function.update_self] at ha ⊢
      by_cases hav : a = V u + 1
      · subst hav; simpa using hW
      · rw [Function.update_of_ne hav]; exact hH.walk u a ha1 (by omega)
    · rw [Function.update_of_ne hu] at ha ⊢
      exact hH.walk u a ha1 ha
  · intro u a b ha1 hab hb
    by_cases hu : u = v
    · subst hu
      simp only [Function.update_self] at hb ⊢
      by_cases hbv : b = V u + 1
      · subst hbv
        have ha' : a ≠ V u + 1 := by omega
        rw [Function.update_self, Function.update_of_ne ha']
        rcases hlt with h0 | hlt
        · omega
        · rcases (show a ≤ V u by omega).lt_or_eq with ha2 | ha2
          · exact lt_trans hlt (hH.anti u a (V u) ha1 ha2 le_rfl)
          · subst ha2; exact hlt
      · have ha' : a ≠ V u + 1 := by omega
        rw [Function.update_of_ne hbv, Function.update_of_ne ha']
        exact hH.anti u a b ha1 hab (by omega)
    · rw [Function.update_of_ne hu] at hb ⊢
      exact hH.anti u a b ha1 hab hb

/-- Old representations survive a bump (histories are append-only). -/
theorem Rep.bump {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} {x : MLabel G}
    {p : List (Fin G.m)} (hx : Rep (s := s) H V x p) (v : Fin G.n) (W : List (Fin G.m)) :
    Rep (s := s) (Function.update H v (Function.update (H v) (V v + 1) W))
      (Function.update V v (V v + 1)) x p := by
  obtain ⟨hpx, hlx, hhx, hvx, hx0, hxV⟩ := hx
  refine ⟨?_, hlx, hhx, hvx, hx0, ?_⟩
  · rw [hpx]
    unfold walkOf
    cases hxe : x.e with
    | none => rfl
    | some e =>
      have hle := (hxV e hxe).2
      dsimp only
      by_cases hu : G.src e = v
      · subst hu
        simp only [Function.update_self]
        rw [Function.update_of_ne (by omega)]
      · rw [Function.update_of_ne hu]
  · intro e he
    have hle := hxV e he
    by_cases hu : G.src e = v
    · subst hu; simp only [Function.update_self]; omega
    · rw [Function.update_of_ne hu]; exact hle

end MLab
end CHD
end Frontier
