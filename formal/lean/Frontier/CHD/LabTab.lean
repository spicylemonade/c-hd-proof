import Frontier.CHD.WalkOrder
import Frontier.CHD.Basic
import Frontier.CHD.MLabel

/-!
# LabTab — the label table and its representation of Layer-A walk labels (agent-02, B-LAB)

NON-GATE.  The RAM stores, for every vertex `v`, the O(1) machine label of `d v`
(`MLab.MLabel`) in parallel arrays, plus a finiteness bit and the vertex's version counter:

  `dfin[v]` (1 iff `d v ≠ ⊤`), `dlen[v]` (value), `dhops[v]`, `de[v]` (0 = source, `e+1`),
  `dver[v]` (version of the tail when written), `vcnt[v]` (number of finite labels `v` had).

This file is machine-free: a table is given by its field functions (`Tab`), and `Represents T d H`
relates it to Layer-A labels `d : Labels G s` through a ghost history `H` (`MLab.GoodHist`).
The lemmas a relaxation needs:
* `cand_rep`: the candidate built from `u`'s fields and edge `e` represents `ext (d u) e`;
* `Represents.put`: writing the candidate at `dst e` after a STRICT decrease, with the version
  counter of `dst e` bumped, represents `Function.update d (dst e) (ext (d u) e)`;
* `HExt` / `Rep.ext`: the history only grows, so every other stored copy of a machine label
  (D entries, bounds, snapshots) keeps representing the same walk.
(Equal candidates need no write, see `update_eq_self_of_eq`.)
-/

open scoped ENNReal NNReal

namespace Frontier
namespace CHD
namespace LabTab

open Frontier Graph MLab

variable {G : Graph} {s : Fin G.n}

/-- Encoding of the optional last edge as a word. -/
def encE : Option (Fin G.m) → ℕ
  | none => 0
  | some e => (e : ℕ) + 1

/-- Decoding (total; junk outside the range). -/
def decE (G : Graph) (k : ℕ) : Option (Fin G.m) :=
  if h : 0 < k ∧ k - 1 < G.m then some ⟨k - 1, h.2⟩ else none

@[simp] theorem decE_encE (x : Option (Fin G.m)) : decE G (encE x) = x := by
  cases x with
  | none => simp [decE, encE]
  | some e => simp [decE, encE, e.isLt]

@[simp] theorem decE_succ (e : Fin G.m) : decE G ((e : ℕ) + 1) = some e := by
  simpa [encE] using decE_encE (G := G) (some e)

theorem encE_injective : Function.Injective (encE (G := G)) := by
  intro x y h
  have := congrArg (decE G) h
  simpa using this

/-- The optional-edge order is the order of the encodings. -/
theorem optLt_iff (x y : Option (Fin G.m)) : OptLt x y ↔ encE x < encE y := by
  cases x with
  | none => cases y with
    | none => simp [OptLt, encE]
    | some b => simp [OptLt, encE]
  | some a => cases y with
    | none => simp [OptLt, encE]
    | some b =>
      show a < b ↔ (a : ℕ) + 1 < (b : ℕ) + 1
      rw [Fin.lt_def]; omega

/-- The table, abstractly: its field functions (what the RAM arrays hold at `Fin n` indices). -/
structure Tab (G : Graph) where
  fin : Fin G.n → ℕ
  len : Fin G.n → ℝ≥0
  hops : Fin G.n → ℕ
  enc : Fin G.n → ℕ
  ver : Fin G.n → ℕ
  vcnt : Fin G.n → ℕ

/-- The machine label stored for `v`. -/
def Tab.lab (T : Tab G) (v : Fin G.n) : MLabel G :=
  ⟨T.len v, T.hops v, v, decE G (T.enc v), T.ver v⟩

/-- `T` represents the Layer-A labels `d` with ghost history `H` (counters `T.vcnt`). -/
structure Represents (T : Tab G) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) : Prop where
  hist : GoodHist (s := s) H T.vcnt
  fin_iff : ∀ v, T.fin v = 0 ↔ d v = ⊤
  top_iff : ∀ v, d v = ⊤ ↔ T.vcnt v = 0
  rep : ∀ v (p : List (Fin G.m)), d v = ((toW p : WalkOrd G s) : WLab G s) →
    Rep (s := s) H T.vcnt (T.lab v) p
  cur : ∀ v (p : List (Fin G.m)), d v = ((toW p : WalkOrd G s) : WLab G s) → H v (T.vcnt v) = p
  enc_lt : ∀ v, d v ≠ ⊤ → T.enc v ≤ G.m

theorem Represents.walk {T : Tab G} {d : Labels G s} {H : Fin G.n → ℕ → List (Fin G.m)}
    (hT : Represents (s := s) T d H) {v : Fin G.n} {p : List (Fin G.m)}
    (hp : d v = ((toW p : WalkOrd G s) : WLab G s)) : G.IsWalk s v p := by
  have hV : T.vcnt v ≠ 0 := by
    intro h0; have := (hT.top_iff v).mpr h0; rw [hp] at this; exact WithTop.coe_ne_top this
  have := hT.hist.walk v (T.vcnt v) (Nat.one_le_iff_ne_zero.mpr hV) le_rfl
  rwa [hT.cur v p hp] at this

theorem Represents.walkInv {T : Tab G} {d : Labels G s} {H : Fin G.n → ℕ → List (Fin G.m)}
    (hT : Represents (s := s) T d H) : WalkInv d :=
  fun _ _ hp => hT.walk hp

/-! ### The relaxation candidate -/

/-- The candidate machine label for `ext (d u) e` built from `u = src e`'s fields. -/
def cand (T : Tab G) (e : Fin G.m) : MLabel G :=
  ⟨T.len (G.src e) + G.w e, T.hops (G.src e) + 1, G.dst e, some e, T.vcnt (G.src e)⟩

theorem cand_rep {T : Tab G} {d : Labels G s} {H : Fin G.n → ℕ → List (Fin G.m)}
    (hT : Represents (s := s) T d H) (e : Fin G.m) {p : List (Fin G.m)}
    (hp : d (G.src e) = ((toW p : WalkOrd G s) : WLab G s)) :
    Rep (s := s) H T.vcnt (cand T e) (p ++ [e]) := by
  obtain ⟨_, hlx, hhx, _, _, _⟩ := hT.rep _ p hp
  have hcur := hT.cur _ p hp
  have hV : T.vcnt (G.src e) ≠ 0 := by
    intro h0; have := (hT.top_iff _).mpr h0; rw [hp] at this; exact WithTop.coe_ne_top this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [walkOf, cand, hcur]
  · simp only [cand, len_append, len_singleton]
    simp only [Tab.lab] at hlx
    rw [hlx]
  · simp only [cand, List.length_append, List.length_singleton]
    simp only [Tab.lab] at hhx
    rw [hhx]
  · simp only [cand]
    exact (walk_endV_append e).symm
  · simp [cand]
  · intro e' he'
    simp only [cand, Option.some.injEq] at he'
    subst he'
    simp only [cand]
    omega

/-- The candidate represents `ext (d u) e`, stated on labels. -/
theorem cand_ext {d : Labels G s} (e : Fin G.m) {p : List (Fin G.m)}
    (hp : d (G.src e) = ((toW p : WalkOrd G s) : WLab G s)) :
    ext (d (G.src e)) e = ((toW (p ++ [e]) : WalkOrd G s) : WLab G s) := by
  rw [hp, ext_coe]

/-! ### History extension -/

/-- `(H', V')` extends `(H, V)`: counters only grow and existing history entries are kept. -/
def HExt (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (H' : Fin G.n → ℕ → List (Fin G.m)) (V' : Fin G.n → ℕ) : Prop :=
  (∀ u, V u ≤ V' u) ∧ ∀ u a, 1 ≤ a → a ≤ V u → H' u a = H u a

theorem HExt.refl (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) : HExt H V H V :=
  ⟨fun _ => le_rfl, fun _ _ _ _ => rfl⟩

theorem HExt.trans {H₁ H₂ H₃ : Fin G.n → ℕ → List (Fin G.m)} {V₁ V₂ V₃ : Fin G.n → ℕ}
    (h₁ : HExt H₁ V₁ H₂ V₂) (h₂ : HExt H₂ V₂ H₃ V₃) : HExt H₁ V₁ H₃ V₃ :=
  ⟨fun u => (h₁.1 u).trans (h₂.1 u), fun u a ha1 ha =>
    (h₂.2 u a ha1 (ha.trans (h₁.1 u))).trans (h₁.2 u a ha1 ha)⟩

theorem HExt.bump (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ) (v : Fin G.n)
    (W : List (Fin G.m)) :
    HExt H V (Function.update H v (Function.update (H v) (V v + 1) W))
      (Function.update V v (V v + 1)) := by
  refine ⟨fun u => ?_, fun u a _ ha => ?_⟩
  · by_cases hu : u = v
    · subst hu; simp
    · rw [Function.update_of_ne hu]
  · by_cases hu : u = v
    · subst hu
      simp only [Function.update_self]
      rw [Function.update_of_ne (by omega)]
    · rw [Function.update_of_ne hu]

/-- Every stored machine label keeps representing its walk when the history is extended. -/
theorem Rep.ext {H H' : Fin G.n → ℕ → List (Fin G.m)} {V V' : Fin G.n → ℕ} {x : MLabel G}
    {p : List (Fin G.m)} (hx : Rep (s := s) H V x p) (hE : HExt H V H' V') :
    Rep (s := s) H' V' x p := by
  obtain ⟨hpx, hlx, hhx, hvx, hx0, hxV⟩ := hx
  refine ⟨?_, hlx, hhx, hvx, hx0, fun e he => ⟨(hxV e he).1, (hxV e he).2.trans (hE.1 _)⟩⟩
  rw [hpx]
  unfold walkOf
  cases hxe : x.e with
  | none => rfl
  | some e =>
    dsimp only
    rw [hE.2 _ _ (hxV e hxe).1 (hxV e hxe).2]

/-! ### Writing a strictly smaller candidate -/

/-- The table after writing the candidate for `e` at `dst e`, with `vcnt[dst e]` bumped. -/
def Tab.put (T : Tab G) (e : Fin G.m) : Tab G where
  fin := Function.update T.fin (G.dst e) 1
  len := Function.update T.len (G.dst e) (T.len (G.src e) + G.w e)
  hops := Function.update T.hops (G.dst e) (T.hops (G.src e) + 1)
  enc := Function.update T.enc (G.dst e) ((e : ℕ) + 1)
  ver := Function.update T.ver (G.dst e) (T.vcnt (G.src e))
  vcnt := Function.update T.vcnt (G.dst e) (T.vcnt (G.dst e) + 1)

/-- The ghost history after the write. -/
def Hput (H : Fin G.n → ℕ → List (Fin G.m)) (T : Tab G) (e : Fin G.m) (W : List (Fin G.m)) :
    Fin G.n → ℕ → List (Fin G.m) :=
  Function.update H (G.dst e) (Function.update (H (G.dst e)) (T.vcnt (G.dst e) + 1) W)

theorem put_lab_ne (T : Tab G) (e : Fin G.m) {w : Fin G.n} (hw : w ≠ G.dst e) :
    (T.put e).lab w = T.lab w := by
  simp [Tab.lab, Tab.put, Function.update_of_ne hw]

theorem put_lab_self (T : Tab G) (e : Fin G.m) : (T.put e).lab (G.dst e) = cand T e := by
  simp [Tab.lab, Tab.put, cand]

/-- A strict decrease forces `src e ≠ dst e` (self-loops never decrease a label). -/
theorem src_ne_dst_of_lt {d : Labels G s} {e : Fin G.m} (hne : d (G.src e) ≠ ⊤)
    (hlt : ext (d (G.src e)) e < d (G.dst e)) : G.src e ≠ G.dst e := by
  intro h
  have h1 := lt_ext_of_ne_top hne e
  rw [h] at h1 hlt
  exact absurd (lt_trans h1 hlt) (lt_irrefl _)

/-- **Strict relaxation on the table.**  If `d (src e)` is the finite label `p` and
`ext (d (src e)) e < d (dst e)`, then writing the candidate (`Tab.put`) represents the updated
labels, with the history extended by `p ++ [e]` at `dst e`. -/
theorem Represents.put {T : Tab G} {d : Labels G s} {H : Fin G.n → ℕ → List (Fin G.m)}
    (hT : Represents (s := s) T d H) (e : Fin G.m) {p : List (Fin G.m)}
    (hp : d (G.src e) = ((toW p : WalkOrd G s) : WLab G s))
    (hlt : ext (d (G.src e)) e < d (G.dst e)) :
    Represents (s := s) (T.put e) (Function.update d (G.dst e) (ext (d (G.src e)) e))
      (Hput H T e (p ++ [e])) := by
  have hne : d (G.src e) ≠ ⊤ := by rw [hp]; exact WithTop.coe_ne_top
  have huv : G.src e ≠ G.dst e := src_ne_dst_of_lt hne hlt
  have hW : G.IsWalk s (G.dst e) (p ++ [e]) := walk_ext (hT.walk hp) e rfl
  have hext : ext (d (G.src e)) e = ((toW (p ++ [e]) : WalkOrd G s) : WLab G s) := cand_ext e hp
  have hlt' : T.vcnt (G.dst e) = 0 ∨ toW (s := s) (p ++ [e]) < toW (H (G.dst e) (T.vcnt (G.dst e))) := by
    by_cases hv : d (G.dst e) = ⊤
    · exact Or.inl ((hT.top_iff _).mp hv)
    · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hv
      right
      rw [hT.cur _ q hq.symm]
      rw [hext, ← hq] at hlt
      exact WithTop.coe_lt_coe.mp hlt
  have hV' : (T.put e).vcnt = Function.update T.vcnt (G.dst e) (T.vcnt (G.dst e) + 1) := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV']; exact hT.hist.bump (G.dst e) (p ++ [e]) hW hlt'
  · intro w
    by_cases hw : w = G.dst e
    · subst hw
      simp only [Tab.put, Function.update_self, hext, one_ne_zero, false_iff]
      exact WithTop.coe_ne_top
    · simp only [Tab.put, Function.update_of_ne hw]; exact hT.fin_iff w
  · intro w
    by_cases hw : w = G.dst e
    · subst hw
      simp only [Tab.put, Function.update_self, hext, Nat.succ_ne_zero, iff_false]
      exact WithTop.coe_ne_top
    · simp only [Tab.put, Function.update_of_ne hw]; exact hT.top_iff w
  · intro w q hq
    rw [hV']
    by_cases hw : w = G.dst e
    · subst hw
      rw [Function.update_self, hext] at hq
      have hq' : q = p ++ [e] := (WithTop.coe_inj.mp hq).symm
      subst hq'
      rw [put_lab_self]
      exact (cand_rep hT e hp).bump (G.dst e) (p ++ [e])
    · rw [Function.update_of_ne hw] at hq
      rw [put_lab_ne T e hw]
      exact (hT.rep w q hq).bump (G.dst e) (p ++ [e])
  · intro w q hq
    by_cases hw : w = G.dst e
    · subst hw
      rw [Function.update_self, hext] at hq
      have hq' : q = p ++ [e] := (WithTop.coe_inj.mp hq).symm
      subst hq'
      simp [Hput, Tab.put]
    · rw [Function.update_of_ne hw] at hq
      simp only [Hput, Tab.put, Function.update_of_ne hw]
      exact hT.cur w q hq
  · intro w hw'
    by_cases hw : w = G.dst e
    · subst hw
      simp only [Tab.put, Function.update_self]
      exact e.isLt
    · simp only [Tab.put, Function.update_of_ne hw]
      rw [Function.update_of_ne hw] at hw'
      exact hT.enc_lt w hw'

theorem HExt.put (H : Fin G.n → ℕ → List (Fin G.m)) (T : Tab G) (e : Fin G.m)
    (W : List (Fin G.m)) : HExt H T.vcnt (Hput H T e W) (T.put e).vcnt :=
  HExt.bump H T.vcnt (G.dst e) W

/-- Equal candidate: nothing to write. -/
theorem update_eq_self_of_eq {d : Labels G s} {v : Fin G.n} {x : WLab G s} (h : x = d v) :
    Function.update d v x = d := by
  rw [h]; exact Function.update_eq_self v d

/-! ### Machine comparison = walk order, on represented labels -/

/-- The machine order spelled out on fields with the encoded edge (what the RAM macro tests). -/
theorem mlt_iff_fields (x y : MLabel G) :
    x.lt y ↔ x.len < y.len ∨ (x.len = y.len ∧ (x.hops < y.hops ∨ (x.hops = y.hops ∧
      ((x.v : ℕ) < y.v ∨ ((x.v : ℕ) = y.v ∧ (encE x.e < encE y.e ∨
        (encE x.e = encE y.e ∧ y.ver < x.ver))))))) := by
  simp only [MLabel.lt, optLt_iff, Fin.lt_def, Fin.val_inj, encE_injective.eq_iff]

end LabTab
end CHD
end Frontier
