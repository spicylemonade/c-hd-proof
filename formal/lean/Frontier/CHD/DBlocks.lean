import Frontier.CHD.Select

/-!
# Frontier.CHD.DBlocks — the lazy block structure `D` (Layer A model, work package L3)

Owner: agent-04.  NON-GATE.

Layer-A model of agent-09's DS' (`CHD_SEC_DS.md`): the partial-sorting structure of DMSY26
Lemma 3.4 with lazy (stale) entries and one GLOBAL live pointer per key.

* An **entry** is `(id, key, val)`; ids are unique (a global counter).
* The global map `L : κ → Option (ℕ × α)` gives the live entry `(id, val)` of every key.
  An entry `e` is **live** iff `L e.key = some (e.id, e.val)`; otherwise it is **stale** and is
  discarded when it is next scanned.
* A structure is a list of **blocks** in increasing order; block `i` owns the value interval
  `[sep_i, sep_{i+1})` (the last one `[sep_last, Bd)`), `sep_0 = ⊥`.  Entries inside a block are
  unordered.
* The **view** of a structure is the finite map `key ↦ value` of its live entries.

The balanced search tree over blocks is abstracted as the list of blocks; every tree search,
insertion or removal is charged `T` (interface point I2: a red-black tree of depth
`≤ 2 lg(#blocks + 1) + 1` realises this charge).
-/

namespace Frontier.CHD.DB

variable {κ : Type*} [DecidableEq κ] {α : Type*} [LinearOrder α]

/-- A stored entry. -/
structure Entry (κ α : Type*) where
  id : ℕ
  key : κ
  val : α
  deriving DecidableEq

/-- The global live map. -/
abbrev Live (κ α : Type*) := κ → Option (ℕ × α)

/-- `e` is live under `L`. -/
def Entry.IsLive (L : Live κ α) (e : Entry κ α) : Prop := L e.key = some (e.id, e.val)

instance (L : Live κ α) (e : Entry κ α) : Decidable (e.IsLive L) := by
  unfold Entry.IsLive; infer_instance

/-- A block: separator and unordered entry list. -/
structure Block (κ α : Type*) where
  sep : WithBot α
  ents : List (Entry κ α)

/-- live entries of an entry list -/
def liveOf (L : Live κ α) (es : List (Entry κ α)) : List (Entry κ α) :=
  es.filter (fun e => decide (e.IsLive L))

/-! ## Interval invariant of a block list -/

/-- `IntervalOK L bs lo hi`: the blocks `bs` have strictly increasing separators, the first one
equal to `lo`, and every live entry of a block lies in `[its sep, next sep)`, the last one in
`[its sep, hi)`. -/
def IntervalOK (L : Live κ α) : List (Block κ α) → WithBot α → WithBot α → Prop
  | [], _, _ => True
  | [b], lo, hi => b.sep = lo ∧ lo < hi ∧
      ∀ e ∈ b.ents, e.IsLive L → b.sep ≤ (e.val : WithBot α) ∧ (e.val : WithBot α) < hi
  | b :: b' :: bs, lo, hi => b.sep = lo ∧ lo < b'.sep ∧
      (∀ e ∈ b.ents, e.IsLive L → b.sep ≤ (e.val : WithBot α) ∧ (e.val : WithBot α) < b'.sep) ∧
      IntervalOK L (b' :: bs) b'.sep hi

/-- all live values of the block list -/
def liveVals (L : Live κ α) (bs : List (Block κ α)) : List (Entry κ α) :=
  (bs.map (fun b => liveOf L b.ents)).flatten

theorem mem_liveOf {L : Live κ α} {es : List (Entry κ α)} {e : Entry κ α} :
    e ∈ liveOf L es ↔ e ∈ es ∧ e.IsLive L := by
  unfold liveOf; rw [List.mem_filter, decide_eq_true_eq]

theorem mem_liveVals {L : Live κ α} {bs : List (Block κ α)} {e : Entry κ α} :
    e ∈ liveVals L bs ↔ (∃ b ∈ bs, e ∈ b.ents) ∧ e.IsLive L := by
  unfold liveVals
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, he⟩
    rw [List.mem_map] at hl
    obtain ⟨b, hb, rfl⟩ := hl
    rw [mem_liveOf] at he
    exact ⟨⟨b, hb, he.1⟩, he.2⟩
  · rintro ⟨⟨b, hb, he⟩, hl⟩
    exact ⟨_, List.mem_map.mpr ⟨b, hb, rfl⟩, mem_liveOf.mpr ⟨he, hl⟩⟩

/-- the first separator of a nonempty `IntervalOK` list is below `hi` -/
theorem IntervalOK.lo_lt_hi {L : Live κ α} :
    ∀ {bs : List (Block κ α)} {lo hi : WithBot α}, IntervalOK L bs lo hi → bs ≠ [] → lo < hi
  | [], _, _, _, h => absurd rfl h
  | [_], _, _, h, _ => h.2.1
  | _ :: _ :: _, _, _, h, _ => lt_trans h.2.1 (IntervalOK.lo_lt_hi h.2.2.2 (List.cons_ne_nil _ _))

/-- every live value of an `IntervalOK` list lies in `[lo, hi)` -/
theorem IntervalOK.bounds {L : Live κ α} :
    ∀ {bs : List (Block κ α)} {lo hi : WithBot α}, IntervalOK L bs lo hi →
      ∀ b ∈ bs, ∀ e ∈ b.ents, e.IsLive L → lo ≤ (e.val : WithBot α) ∧ (e.val : WithBot α) < hi
  | [], _, _, _, b, hb, _, _, _ => by simp at hb
  | [b], lo, hi, h, b', hb', e, he, hl => by
      simp only [List.mem_singleton] at hb'
      subst hb'
      obtain ⟨hs, _, hin⟩ := h
      obtain ⟨h1, h2⟩ := hin e he hl
      exact ⟨hs ▸ h1, h2⟩
  | b :: b' :: bs, lo, hi, h, c, hc, e, he, hl => by
      obtain ⟨hs, hlt, hin, hrest⟩ := h
      rcases List.mem_cons.mp hc with rfl | hc
      · obtain ⟨h1, h2⟩ := hin e he hl
        exact ⟨hs ▸ h1, lt_of_lt_of_le h2 (hrest.lo_lt_hi (List.cons_ne_nil _ _)).le⟩
      · obtain ⟨h1, h2⟩ := IntervalOK.bounds hrest c hc e he hl
        exact ⟨le_trans hlt.le h1, h2⟩

theorem IntervalOK.mono {L L' : Live κ α} (hL : ∀ e : Entry κ α, e.IsLive L' → e.IsLive L) :
    ∀ {bs : List (Block κ α)} {lo hi : WithBot α}, IntervalOK L bs lo hi → IntervalOK L' bs lo hi
  | [], _, _, _ => trivial
  | [_], _, _, h => ⟨h.1, h.2.1, fun e he hl => h.2.2 e he (hL e hl)⟩
  | _ :: _ :: _, _, _, h => ⟨h.1, h.2.1, fun e he hl => h.2.2.1 e he (hL e hl),
      IntervalOK.mono hL h.2.2.2⟩

/-- monotonicity restricted to the entries actually stored -/
theorem IntervalOK.mono' {L L' : Live κ α} :
    ∀ {bs : List (Block κ α)} {lo hi : WithBot α},
      (∀ b ∈ bs, ∀ e ∈ b.ents, e.IsLive L' → e.IsLive L) →
      IntervalOK L bs lo hi → IntervalOK L' bs lo hi
  | [], _, _, _, _ => trivial
  | [b], _, _, hL, h => ⟨h.1, h.2.1, fun e he hl =>
      h.2.2 e he (hL b (List.mem_singleton_self _) e he hl)⟩
  | b :: b' :: bs, _, _, hL, h => ⟨h.1, h.2.1,
      fun e he hl => h.2.2.1 e he (hL b List.mem_cons_self e he hl),
      IntervalOK.mono' (fun c hc e he hl => hL c (List.mem_cons_of_mem _ hc) e he hl) h.2.2.2⟩

/-! ## Structures and their views -/

/-- A `D` structure: parameter `M`, bound `Bd`, block list. -/
structure DStr (κ α : Type*) where
  M : ℕ
  Bd : α
  blocks : List (Block κ α)

/-- Well-formedness relative to the live map. -/
def WF (L : Live κ α) (D : DStr κ α) : Prop :=
  D.blocks ≠ [] ∧ IntervalOK L D.blocks ⊥ (D.Bd : WithBot α)

/-- `v` has a live entry in `D`. -/
def HasKey (L : Live κ α) (D : DStr κ α) (v : κ) : Prop :=
  ∃ e ∈ liveVals L D.blocks, e.key = v

instance (L : Live κ α) (D : DStr κ α) (v : κ) : Decidable (HasKey L D v) := by
  unfold HasKey; infer_instance

/-- The view: stored value of every key of `D`. -/
def view (L : Live κ α) (D : DStr κ α) (v : κ) : Option α :=
  if HasKey L D v then (L v).map Prod.snd else none

theorem view_eq_some {L : Live κ α} {D : DStr κ α} {v : κ} {a : α} :
    view L D v = some a ↔ ∃ e ∈ liveVals L D.blocks, e.key = v ∧ e.val = a := by
  unfold view
  constructor
  · intro h
    split_ifs at h with hk
    · obtain ⟨e, he, hkey⟩ := hk
      have hl := (mem_liveVals.mp he).2
      unfold Entry.IsLive at hl
      rw [hkey] at hl
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨e, he, hkey, h⟩
  · rintro ⟨e, he, hkey, hval⟩
    have hk : HasKey L D v := ⟨e, he, hkey⟩
    rw [ite_eq_left hk]
    have hl := (mem_liveVals.mp he).2
    unfold Entry.IsLive at hl
    rw [hkey] at hl
    rw [hl]; simp [hval]

theorem view_eq_none {L : Live κ α} {D : DStr κ α} {v : κ} :
    view L D v = none ↔ ¬ HasKey L D v := by
  unfold view
  constructor
  · intro h hk
    rw [ite_eq_left hk] at h
    obtain ⟨e, he, hkey⟩ := hk
    have hl := (mem_liveVals.mp he).2
    unfold Entry.IsLive at hl
    rw [hkey] at hl
    rw [hl] at h; simp at h
  · intro hk; rw [ite_eq_right hk]

/-- two live entries with the same key coincide in id and value -/
theorem live_key_unique {L : Live κ α} {e e' : Entry κ α} (he : e.IsLive L) (he' : e'.IsLive L)
    (hk : e.key = e'.key) : e.id = e'.id ∧ e.val = e'.val := by
  unfold Entry.IsLive at he he'
  rw [hk, he'] at he
  simp only [Option.some.injEq, Prod.mk.injEq] at he
  exact ⟨he.1.symm, he.2.symm⟩

/-! ## Pull -/

/-- Collect the live entries of front blocks until more than `M` are collected.
Returns the collected live entries, the remaining blocks, the number of removed blocks and the
number of scanned entries (live and stale). -/
def collect (L : Live κ α) (M : ℕ) :
    List (Entry κ α) → List (Block κ α) → List (Entry κ α) × List (Block κ α) × ℕ × ℕ
  | acc, [] => (acc, [], 0, 0)
  | acc, b :: bs =>
    if M < (acc ++ liveOf L b.ents).length then (acc ++ liveOf L b.ents, bs, 1, b.ents.length)
    else
      ((collect L M (acc ++ liveOf L b.ents) bs).1, (collect L M (acc ++ liveOf L b.ents) bs).2.1,
        (collect L M (acc ++ liveOf L b.ents) bs).2.2.1 + 1,
        (collect L M (acc ++ liveOf L b.ents) bs).2.2.2 + b.ents.length)

/-- structural facts about `collect` -/
theorem collect_spec (L : Live κ α) (M : ℕ) :
    ∀ (bs : List (Block κ α)) (acc : List (Entry κ α)),
      ∃ pre, bs = pre ++ (collect L M acc bs).2.1 ∧
        (collect L M acc bs).1 = acc ++ liveVals L pre ∧
        (collect L M acc bs).2.2.1 = pre.length ∧
        (collect L M acc bs).2.2.2 = (pre.map (fun b => b.ents.length)).sum ∧
        ((collect L M acc bs).2.1 = [] ∨ M < (collect L M acc bs).1.length) ∧
        (pre ≠ [] ∨ bs = [])
  | [], acc => ⟨[], by simp [collect, liveVals]⟩
  | b :: bs, acc => by
      by_cases h : M < (acc ++ liveOf L b.ents).length
      · refine ⟨[b], ?_⟩
        simp only [collect]
        rw [ite_eq_left h]
        refine ⟨rfl, by simp [liveVals], rfl, by simp, Or.inr h, Or.inl (by simp)⟩
      · obtain ⟨pre, h1, h2, h3, h4, h5, _⟩ := collect_spec L M bs (acc ++ liveOf L b.ents)
        refine ⟨b :: pre, ?_⟩
        simp only [collect]
        rw [ite_eq_right h]
        refine ⟨by rw [List.cons_append, ← h1], ?_, by rw [h3]; rfl, ?_, h5, Or.inl (by simp)⟩
        · rw [h2]; simp [liveVals, List.append_assoc]
        · rw [h4]; simp; omega

theorem liveVals_append (L : Live κ α) (bs₁ bs₂ : List (Block κ α)) :
    liveVals L (bs₁ ++ bs₂) = liveVals L bs₁ ++ liveVals L bs₂ := by
  simp [liveVals]

theorem liveVals_cons (L : Live κ α) (b : Block κ α) (bs : List (Block κ α)) :
    liveVals L (b :: bs) = liveOf L b.ents ++ liveVals L bs := by
  simp [liveVals]

/-- the separator following a block list `bs₁` inside `bs₁ ++ bs₂` -/
def nextSep (bs₂ : List (Block κ α)) (hi : WithBot α) : WithBot α :=
  match bs₂ with
  | [] => hi
  | b :: _ => b.sep

/-- splitting an `IntervalOK` list -/
theorem IntervalOK.split {L : Live κ α} :
    ∀ {bs₁ bs₂ : List (Block κ α)} {lo hi : WithBot α}, bs₁ ≠ [] →
      IntervalOK L (bs₁ ++ bs₂) lo hi →
      IntervalOK L bs₁ lo (nextSep bs₂ hi) ∧ IntervalOK L bs₂ (nextSep bs₂ hi) hi
  | [], _, _, _, h, _ => absurd rfl h
  | [b], [], lo, hi, _, h => ⟨by simpa [nextSep] using h, trivial⟩
  | [b], c :: cs, lo, hi, _, h => by
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact ⟨⟨h1, h2, h3⟩, h4⟩
  | b :: b' :: bs, bs₂, lo, hi, _, h => by
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨k1, k2⟩ := IntervalOK.split (bs₁ := b' :: bs) (bs₂ := bs₂) (List.cons_ne_nil _ _) h4
      exact ⟨⟨h1, h2, h3, k1⟩, k2⟩

/-- the separator after a nonempty prefix lies strictly above its lower bound -/
theorem IntervalOK.lo_lt_nextSep {L : Live κ α} {bs₁ bs₂ : List (Block κ α)} {lo hi : WithBot α}
    (hne : bs₁ ≠ []) (h : IntervalOK L bs₁ lo (nextSep bs₂ hi)) : lo < nextSep bs₂ hi :=
  h.lo_lt_hi hne

/-- clear the live pointers of the given keys -/
def clearKeys (L : Live κ α) (ks : List κ) : Live κ α := fun v => if v ∈ ks then none else L v

theorem isLive_clearKeys {L : Live κ α} {ks : List κ} {e : Entry κ α} :
    e.IsLive (clearKeys L ks) ↔ e.IsLive L ∧ e.key ∉ ks := by
  unfold Entry.IsLive clearKeys
  by_cases h : e.key ∈ ks <;> simp [h]

/-! The operations charge `T` per search-tree operation on the block index. -/
variable [Inhabited α] (T : ℕ)

/-- **Pull.**  Returns `(pulled keys, separator x, new live map, new structure, cost)`. -/
def pull (L : Live κ α) (D : DStr κ α) : List κ × α × Live κ α × DStr κ α × ℕ :=
  if (collect L D.M [] D.blocks).1.length ≤ D.M then
    ((collect L D.M [] D.blocks).1.map (·.key), D.Bd,
      clearKeys L ((collect L D.M [] D.blocks).1.map (·.key)),
      { D with blocks := [⟨⊥, []⟩] },
      (collect L D.M [] D.blocks).2.2.2 + 2 * (collect L D.M [] D.blocks).1.length +
        T * ((collect L D.M [] D.blocks).2.2.1 + 1) + 1)
  else
    ((((collect L D.M [] D.blocks).1.filter
        (fun e => decide (e.val < (selectC ((collect L D.M [] D.blocks).1.map (·.val)) D.M).1))).map
        (·.key)),
      (selectC ((collect L D.M [] D.blocks).1.map (·.val)) D.M).1,
      clearKeys L ((((collect L D.M [] D.blocks).1.filter
        (fun e => decide (e.val < (selectC ((collect L D.M [] D.blocks).1.map (·.val)) D.M).1))).map
        (·.key))),
      { D with blocks := ⟨⊥, (collect L D.M [] D.blocks).1.filter
        (fun e => decide ((selectC ((collect L D.M [] D.blocks).1.map (·.val)) D.M).1 ≤ e.val))⟩ ::
          (collect L D.M [] D.blocks).2.1 },
      (collect L D.M [] D.blocks).2.2.2 +
        (selectC ((collect L D.M [] D.blocks).1.map (·.val)) D.M).2 +
        4 * (collect L D.M [] D.blocks).1.length +
        T * ((collect L D.M [] D.blocks).2.2.1 + 1) + 1)

/-- Correctness of `pull` (the `PullSpec` of `Frontier.CHD.Basic`, on views), plus
well-formedness of the result and the shape of the new live map. -/
theorem pull_spec {L : Live κ α} {D : DStr κ α} (hwf : WF L D) :
    (∀ y, y ∈ (pull T L D).1 ↔ ∃ a, view L D y = some a ∧ a < (pull T L D).2.1) ∧
    (∀ y, view (pull T L D).2.2.1 (pull T L D).2.2.2.1 y =
        if y ∈ (pull T L D).1 then none else view L D y) ∧
    (pull T L D).2.1 ≤ D.Bd ∧
    WF (pull T L D).2.2.1 (pull T L D).2.2.2.1 ∧
    (pull T L D).2.2.1 = clearKeys L (pull T L D).1 ∧
    (pull T L D).2.2.2.1.M = D.M ∧ (pull T L D).2.2.2.1.Bd = D.Bd := by
  obtain ⟨hne, hint⟩ := hwf
  unfold pull
  obtain ⟨pre, hbs, hacc, -, -, hrem, hpre⟩ := collect_spec L D.M D.blocks []
  simp only [List.nil_append] at hacc
  set acc := (collect L D.M [] D.blocks).1 with hacc_def
  set rem := (collect L D.M [] D.blocks).2.1 with hrem_def
  by_cases hsmall : acc.length ≤ D.M
  · -- exhausted: every block was collected
    rw [ite_eq_left hsmall]
    dsimp only
    have hrem0 : rem = [] := by rcases hrem with h | h; exact h; omega
    rw [hrem0, List.append_nil] at hbs
    have hall : acc = liveVals L D.blocks := by rw [hacc, ← hbs]
    refine ⟨?_, ?_, le_rfl, ?_, rfl, rfl, rfl⟩
    · intro y
      simp only [List.mem_map]
      constructor
      · rintro ⟨e, he, rfl⟩
        rw [hall] at he
        refine ⟨e.val, view_eq_some.mpr ⟨e, he, rfl, rfl⟩, ?_⟩
        obtain ⟨⟨b, hb, heb⟩, hl⟩ := mem_liveVals.mp he
        exact WithBot.coe_lt_coe.mp (hint.bounds b hb e heb hl).2
      · rintro ⟨a, ha, -⟩
        obtain ⟨e, he, hk, -⟩ := view_eq_some.mp ha
        exact ⟨e, hall ▸ he, hk⟩
    · intro y
      split_ifs with hy
      · rfl
      · -- nothing is left
        have h1 : view (clearKeys L (acc.map (·.key))) ⟨D.M, D.Bd, [⟨⊥, []⟩]⟩ y = none := by
          rw [view_eq_none]
          rintro ⟨e, he, -⟩
          simp [liveVals, liveOf] at he
        rw [h1]; symm
        rw [view_eq_none]
        rintro ⟨e, he, hk⟩
        exact hy (List.mem_map.mpr ⟨e, hall ▸ he, hk⟩)
    · refine ⟨List.cons_ne_nil _ _, rfl, WithBot.bot_lt_coe _, ?_⟩
      intro e he; simp at he
  · -- a separator is selected
    rw [ite_eq_right hsmall]
    dsimp only
    have hM : D.M < acc.length := by omega
    have hpre' : pre ≠ [] := by
      rcases hpre with h | h
      · exact h
      · exfalso; rw [h] at hbs; rw [hacc] at hM
        simp only [List.nil_eq_append_iff] at hbs
        rw [hbs.1] at hM; simp [liveVals] at hM
    rw [hbs] at hint
    obtain ⟨hintP, hintR⟩ := hint.split hpre'
    set mid := nextSep rem (D.Bd : WithBot α) with hmid
    set x := (selectC (acc.map (·.val)) D.M).1 with hx
    have hkth : IsKth (acc.map (·.val)) D.M x := selectC_isKth _ (by simpa using hM)
    -- every collected value is below `mid`, every remaining one above
    have haccB : ∀ e ∈ acc, e.IsLive L ∧ (e.val : WithBot α) < mid ∧ ∃ b ∈ pre, e ∈ b.ents := by
      intro e he
      rw [hacc] at he
      obtain ⟨⟨b, hb, heb⟩, hl⟩ := mem_liveVals.mp he
      exact ⟨hl, (hintP.bounds b hb e heb hl).2, b, hb, heb⟩
    have hremB : ∀ b ∈ rem, ∀ e ∈ b.ents, e.IsLive L → mid ≤ (e.val : WithBot α) := by
      intro b hb e he hl; exact (hintR.bounds b hb e he hl).1
    have hxmid : (x : WithBot α) < mid := by
      obtain ⟨e0, he0, hex⟩ := List.mem_map.mp hkth.1
      rw [← hex]; exact (haccB e0 he0).2.1
    have hmidB : mid ≤ (D.Bd : WithBot α) := by
      rcases hr : rem with _ | ⟨b, rest⟩
      · simp [hmid, hr, nextSep]
      · have := hintR.lo_lt_hi (by rw [hr]; exact List.cons_ne_nil _ _)
        exact this.le
    have hxB : x < D.Bd := WithBot.coe_lt_coe.mp (lt_of_lt_of_le hxmid hmidB)
    set S := acc.filter (fun e => decide (e.val < x)) with hS
    set R := acc.filter (fun e => decide (x ≤ e.val)) with hR
    set ks := S.map (·.key) with hks
    -- an entry of the old structure is in `acc` or in a remaining block
    have hsplitL : ∀ e, e ∈ liveVals L D.blocks → e ∈ acc ∨ ((∃ b ∈ rem, e ∈ b.ents) ∧ e.IsLive L) := by
      intro e he
      rw [hbs, liveVals_append] at he
      rcases List.mem_append.mp he with h | h
      · exact Or.inl (hacc ▸ h)
      · exact Or.inr (mem_liveVals.mp h)
    have hS_mem : ∀ e, e ∈ S ↔ e ∈ acc ∧ e.val < x := by
      intro e; rw [hS, List.mem_filter, decide_eq_true_eq]
    have hR_mem : ∀ e, e ∈ R ↔ e ∈ acc ∧ x ≤ e.val := by
      intro e; rw [hR, List.mem_filter, decide_eq_true_eq]
    -- live entries of `acc` whose key is pulled are in `S`
    have hkey_S : ∀ e ∈ acc, e.key ∈ ks → e ∈ S := by
      intro e he hk
      obtain ⟨e', he', hkk⟩ := List.mem_map.mp hk
      have h1 := (hS_mem e').mp he'
      have hv := (live_key_unique (haccB e he).1 (haccB e' h1.1).1 hkk.symm).2
      exact (hS_mem e).mpr ⟨he, hv ▸ h1.2⟩
    refine ⟨?_, ?_, hxB.le, ?_, rfl, rfl, rfl⟩
    · -- pulled keys
      intro y
      constructor
      · intro hy
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
        have h1 := (hS_mem e).mp he
        refine ⟨e.val, view_eq_some.mpr ⟨e, ?_, rfl, rfl⟩, h1.2⟩
        rw [hbs, liveVals_append]
        exact List.mem_append_left _ (hacc ▸ h1.1)
      · rintro ⟨a, ha, hax⟩
        obtain ⟨e, he, hk, hv⟩ := view_eq_some.mp ha
        rcases hsplitL e he with h | ⟨⟨b, hb, heb⟩, hl⟩
        · exact List.mem_map.mpr ⟨e, (hS_mem e).mpr ⟨h, hv ▸ hax⟩, hk⟩
        · exfalso
          have h1 := hremB b hb e heb hl
          have h2 : (e.val : WithBot α) < mid := lt_trans (WithBot.coe_lt_coe.mpr (hv ▸ hax)) hxmid
          exact absurd h1 (not_le.mpr h2)
    · -- the rest is unchanged
      intro y
      split_ifs with hy
      · rw [view_eq_none]
        rintro ⟨e, he, hk⟩
        have hl := (mem_liveVals.mp he).2
        rw [isLive_clearKeys] at hl
        exact hl.2 (hk ▸ hy)
      · -- `y` is not pulled
        have hL' : clearKeys L ks y = L y := by simp [clearKeys, hy]
        unfold view
        rw [hL']
        have hiff : HasKey (clearKeys L ks) ⟨D.M, D.Bd, ⟨⊥, R⟩ :: rem⟩ y ↔ HasKey L D y := by
          constructor
          · rintro ⟨e, he, hk⟩
            obtain ⟨⟨b, hb, heb⟩, hl⟩ := mem_liveVals.mp he
            rw [isLive_clearKeys] at hl
            refine ⟨e, ?_, hk⟩
            rw [hbs, liveVals_append]
            rcases List.mem_cons.mp hb with rfl | hb
            · exact List.mem_append_left _ (hacc ▸ ((hR_mem e).mp heb).1)
            · exact List.mem_append_right _ (mem_liveVals.mpr ⟨⟨b, hb, heb⟩, hl.1⟩)
          · rintro ⟨e, he, hk⟩
            refine ⟨e, ?_, hk⟩
            rcases hsplitL e he with h | ⟨⟨b, hb, heb⟩, hl⟩
            · have hnotS : e ∉ S := fun hS' => hy (hk ▸ List.mem_map.mpr ⟨e, hS', rfl⟩)
              have hxe : x ≤ e.val := by
                by_contra hlt
                exact hnotS ((hS_mem e).mpr ⟨h, lt_of_not_ge hlt⟩)
              refine mem_liveVals.mpr ⟨⟨⟨⊥, R⟩, List.mem_cons_self, (hR_mem e).mpr ⟨h, hxe⟩⟩, ?_⟩
              rw [isLive_clearKeys]; exact ⟨(haccB e h).1, hk ▸ hy⟩
            · refine mem_liveVals.mpr ⟨⟨b, List.mem_cons_of_mem _ hb, heb⟩, ?_⟩
              rw [isLive_clearKeys]; exact ⟨hl, hk ▸ hy⟩
        by_cases hk : HasKey L D y
        · rw [ite_eq_left (hiff.mpr hk), ite_eq_left hk]
        · rw [ite_eq_right (fun h => hk (hiff.mp h)), ite_eq_right hk]
    · -- well-formedness of the new structure
      refine ⟨List.cons_ne_nil _ _, ?_⟩
      have hmono : ∀ e : Entry κ α, e.IsLive (clearKeys L ks) → e.IsLive L :=
        fun e h => (isLive_clearKeys.mp h).1
      have hRval : ∀ e ∈ R, (e.val : WithBot α) < mid :=
        fun e he => (haccB e ((hR_mem e).mp he).1).2.1
      rcases hr : rem with _ | ⟨b, rest⟩
      · refine ⟨rfl, WithBot.bot_lt_coe _, ?_⟩
        intro e he _
        refine ⟨bot_le, ?_⟩
        have := hRval e he
        simpa [hmid, hr, nextSep] using this
      · have hmb : mid = b.sep := by simp [hmid, hr, nextSep]
        refine ⟨rfl, ?_, ?_, ?_⟩
        · rw [← hmb]; exact lt_of_le_of_lt bot_le (lt_trans (WithBot.bot_lt_coe x) hxmid)
        · intro e he _
          exact ⟨bot_le, hmb ▸ hRval e he⟩
        · rw [hr] at hintR
          exact IntervalOK.mono hmono (hmb ▸ hintR)


/-- gluing two `IntervalOK` lists -/
theorem IntervalOK.append_cons {L : Live κ α} :
    ∀ {bs : List (Block κ α)} {b' : Block κ α} {rest : List (Block κ α)} {lo hi : WithBot α},
      IntervalOK L bs lo b'.sep → bs ≠ [] → IntervalOK L (b' :: rest) b'.sep hi →
      IntervalOK L (bs ++ b' :: rest) lo hi
  | [], _, _, _, _, _, h, _ => absurd rfl h
  | [b], b', rest, lo, hi, h1, _, h2 => ⟨h1.1, h1.2.1, h1.2.2, h2⟩
  | b :: c :: bs, b', rest, lo, hi, h1, _, h2 =>
      ⟨h1.1, h1.2.1, h1.2.2.1, IntervalOK.append_cons h1.2.2.2 (List.cons_ne_nil _ _) h2⟩

/-! ### Computable separator comparisons (no `WithBot` order instances in algorithm code) -/

/-- `s ≤ ↑a` for a separator `s` -/
def sepLe (s : WithBot α) (a : α) : Bool :=
  match s with
  | none => true
  | some x => decide (x ≤ a)

/-- `↑a < s` for a separator `s` -/
def ltSep (a : α) (s : WithBot α) : Bool :=
  match s with
  | none => false
  | some x => decide (a < x)

theorem sepLe_iff (s : WithBot α) (a : α) : sepLe s a = true ↔ s ≤ (a : WithBot α) := by
  cases s with
  | bot => simp [sepLe]
  | coe x => simp [sepLe, WithBot.coe_le_coe]

theorem ltSep_iff (a : α) (s : WithBot α) : ltSep a s = true ↔ (a : WithBot α) < s := by
  cases s with
  | bot => simp [ltSep]
  | coe x => simp [ltSep, WithBot.coe_lt_coe]

/-! ## Insert -/

/-- Normalise a block after an insertion: if it holds more than `2M+1` entries, drop its stale
entries, and if more than `M` live entries remain, split it at the median live value.
Returns the replacement blocks and the cost. -/
def fixBlock (L : Live κ α) (M : ℕ) (b : Block κ α) : List (Block κ α) × ℕ :=
  if b.ents.length ≤ 2 * M + 1 then ([b], 1)
  else if (liveOf L b.ents).length ≤ M then ([⟨b.sep, liveOf L b.ents⟩], b.ents.length + 1)
  else if ((liveOf L b.ents).filter (fun e => decide (e.val <
      (selectC ((liveOf L b.ents).map (·.val)) ((liveOf L b.ents).length / 2)).1))) = [] then
    ([⟨b.sep, liveOf L b.ents⟩], b.ents.length + 1)
  else
    ([⟨b.sep, (liveOf L b.ents).filter (fun e => decide (e.val <
        (selectC ((liveOf L b.ents).map (·.val)) ((liveOf L b.ents).length / 2)).1))⟩,
      ⟨((selectC ((liveOf L b.ents).map (·.val)) ((liveOf L b.ents).length / 2)).1 : α),
        (liveOf L b.ents).filter (fun e => decide
          ((selectC ((liveOf L b.ents).map (·.val)) ((liveOf L b.ents).length / 2)).1 ≤ e.val))⟩],
      b.ents.length + (selectC ((liveOf L b.ents).map (·.val)) ((liveOf L b.ents).length / 2)).2 +
        2 * (liveOf L b.ents).length + T + 1)

/-- Walk to the block owning `lam` (the last block with separator `≤ lam`), prepend `e` and
normalise it.  The walk itself is the search-tree descent, charged `T` by `insert`. -/
def addTo (L : Live κ α) (M : ℕ) (lam : α) (e : Entry κ α) :
    List (Block κ α) → List (Block κ α) × ℕ
  | [] => ([], 0)
  | [b] => fixBlock T L M ⟨b.sep, e :: b.ents⟩
  | b :: b' :: bs =>
    if sepLe b'.sep lam then
      (b :: (addTo L M lam e (b' :: bs)).1, (addTo L M lam e (b' :: bs)).2)
    else
      ((fixBlock T L M ⟨b.sep, e :: b.ents⟩).1 ++ b' :: bs, (fixBlock T L M ⟨b.sep, e :: b.ents⟩).2)

/-- live entries are preserved by `fixBlock` -/
theorem mem_liveVals_fixBlock {L : Live κ α} {M : ℕ} {b : Block κ α} {e : Entry κ α} :
    e ∈ liveVals L (fixBlock T L M b).1 ↔ e ∈ b.ents ∧ e.IsLive L := by
  unfold fixBlock
  split_ifs with h1 h2 h3
  · simp [liveVals, mem_liveOf]
  · simp only [liveVals, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, mem_liveOf]
    tauto
  · simp only [liveVals, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, mem_liveOf]
    tauto
  · simp only [liveVals, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.mem_append, mem_liveOf, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (⟨⟨⟨h, _⟩, _⟩, _⟩ | ⟨⟨⟨h, _⟩, _⟩, _⟩) <;> tauto
    · rintro ⟨h, hl⟩
      by_cases hlt : e.val < (selectC ((liveOf L b.ents).map (·.val)) ((liveOf L b.ents).length / 2)).1
      · exact Or.inl ⟨⟨⟨h, hl⟩, hlt⟩, hl⟩
      · exact Or.inr ⟨⟨⟨h, hl⟩, le_of_not_gt hlt⟩, hl⟩

/-- `fixBlock` keeps the interval invariant of its block -/
theorem intervalOK_fixBlock {L : Live κ α} {M : ℕ} {b : Block κ α} {hi : WithBot α}
    (hlt : b.sep < hi)
    (hb : ∀ e ∈ b.ents, e.IsLive L → b.sep ≤ (e.val : WithBot α) ∧ (e.val : WithBot α) < hi) :
    IntervalOK L (fixBlock T L M b).1 b.sep hi ∧ (fixBlock T L M b).1 ≠ [] := by
  unfold fixBlock
  split_ifs with h1 h2 h3
  · exact ⟨⟨rfl, hlt, hb⟩, List.cons_ne_nil _ _⟩
  · refine ⟨⟨rfl, hlt, fun e he hl => hb e (mem_liveOf.mp he).1 hl⟩, List.cons_ne_nil _ _⟩
  · refine ⟨⟨rfl, hlt, fun e he hl => hb e (mem_liveOf.mp he).1 hl⟩, List.cons_ne_nil _ _⟩
  · set μ := (selectC ((liveOf L b.ents).map (·.val)) ((liveOf L b.ents).length / 2)).1 with hμ
    have hμmem : μ ∈ (liveOf L b.ents).map (·.val) :=
      (selectC_isKth _ (by simp; omega)).1
    obtain ⟨eμ, heμ, heμv⟩ := List.mem_map.mp hμmem
    have hμlt : (μ : WithBot α) < hi := by
      rw [← heμv]; exact (hb eμ (mem_liveOf.mp heμ).1 (mem_liveOf.mp heμ).2).2
    obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil _ h3
    rw [List.mem_filter, decide_eq_true_eq] at he0
    have hsepμ : b.sep < (μ : WithBot α) := by
      have := hb e0 (mem_liveOf.mp he0.1).1 (mem_liveOf.mp he0.1).2
      exact lt_of_le_of_lt this.1 (WithBot.coe_lt_coe.mpr he0.2)
    refine ⟨⟨rfl, hsepμ, ?_, rfl, hμlt, ?_⟩, List.cons_ne_nil _ _⟩
    · intro e he hl
      rw [List.mem_filter, decide_eq_true_eq] at he
      exact ⟨(hb e (mem_liveOf.mp he.1).1 hl).1, WithBot.coe_lt_coe.mpr he.2⟩
    · intro e he hl
      rw [List.mem_filter, decide_eq_true_eq] at he
      exact ⟨WithBot.coe_le_coe.mpr he.2, (hb e (mem_liveOf.mp he.1).1 hl).2⟩

theorem mem_liveVals_cons' {L : Live κ α} {b : Block κ α} {bs : List (Block κ α)}
    {x : Entry κ α} : x ∈ liveVals L (b :: bs) ↔ (x ∈ b.ents ∧ x.IsLive L) ∨ x ∈ liveVals L bs := by
  rw [liveVals_cons, List.mem_append, mem_liveOf]

theorem mem_liveVals_nil {L : Live κ α} {x : Entry κ α} : x ∉ liveVals L ([] : List (Block κ α)) := by
  simp [liveVals]

theorem mem_liveVals_addTo {L : Live κ α} {M : ℕ} {lam : α} {e : Entry κ α} :
    ∀ {bs : List (Block κ α)}, bs ≠ [] → ∀ {x : Entry κ α},
      x ∈ liveVals L (addTo T L M lam e bs).1 ↔ x ∈ liveVals L bs ∨ (x = e ∧ e.IsLive L)
  | [], h, _ => absurd rfl h
  | [b], _, x => by
      simp only [addTo]
      rw [mem_liveVals_fixBlock, mem_liveVals_cons']
      simp only [List.mem_cons]
      have := mem_liveVals_nil (L := L) (x := x)
      constructor
      · rintro ⟨h | h, hl⟩
        · exact Or.inr ⟨h, h ▸ hl⟩
        · exact Or.inl (Or.inl ⟨h, hl⟩)
      · rintro ((⟨h, hl⟩ | h) | ⟨rfl, hl⟩)
        · exact ⟨Or.inr h, hl⟩
        · exact absurd h this
        · exact ⟨Or.inl rfl, hl⟩
  | b :: b' :: bs, _, x => by
      simp only [addTo]
      split_ifs with hsep
      · rw [mem_liveVals_cons', mem_liveVals_addTo (List.cons_ne_nil _ _)]
        conv_rhs => rw [mem_liveVals_cons']
        tauto
      · rw [liveVals_append, List.mem_append, mem_liveVals_fixBlock]
        conv_rhs => rw [mem_liveVals_cons']
        simp only [List.mem_cons]
        constructor
        · rintro (⟨h | h, hl⟩ | h)
          · exact Or.inr ⟨h, h ▸ hl⟩
          · exact Or.inl (Or.inl ⟨h, hl⟩)
          · exact Or.inl (Or.inr h)
        · rintro ((⟨h, hl⟩ | h) | ⟨rfl, hl⟩)
          · exact Or.inl ⟨Or.inr h, hl⟩
          · exact Or.inr h
          · exact Or.inl ⟨Or.inl rfl, hl⟩

theorem intervalOK_addTo {L : Live κ α} {M : ℕ} {lam : α} {e : Entry κ α} (hev : e.val = lam) :
    ∀ {bs : List (Block κ α)} {lo hi : WithBot α}, bs ≠ [] → IntervalOK L bs lo hi →
      lo ≤ (lam : WithBot α) → (lam : WithBot α) < hi →
      IntervalOK L (addTo T L M lam e bs).1 lo hi ∧ (addTo T L M lam e bs).1 ≠ []
  | [], _, _, h, _, _, _ => absurd rfl h
  | [b], lo, hi, _, h, hlo, hhi => by
      simp only [addTo]
      obtain ⟨hs, hlt, hb⟩ := h
      have := intervalOK_fixBlock T (M := M) (b := ⟨b.sep, e :: b.ents⟩) (hi := hi)
        (by simpa [hs] using hlt) (by
          intro x hx hl
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨by simpa [hs, hev] using hlo, by simpa [hev] using hhi⟩
          · exact hb x hx hl)
      simpa [hs] using this
  | b :: b' :: bs, lo, hi, _, h, hlo, hhi => by
      simp only [addTo]
      obtain ⟨hs, hlt, hb, hrest⟩ := h
      split_ifs with hsep
      · obtain ⟨k1, k2⟩ := intervalOK_addTo hev (bs := b' :: bs) (List.cons_ne_nil _ _) hrest
          ((sepLe_iff _ _).mp hsep) hhi
        refine ⟨?_, List.cons_ne_nil _ _⟩
        -- the head block is unchanged; the new tail starts with separator `b'.sep`
        rcases hne : (addTo T L M lam e (b' :: bs)).1 with _ | ⟨c, cs⟩
        · exact absurd hne k2
        · have hc : c.sep = b'.sep := by
            rw [hne] at k1
            rcases cs with _ | ⟨c', cs'⟩ <;> exact k1.1
          rw [hne] at k1
          exact ⟨hs, hc ▸ hlt, hc ▸ hb, hc ▸ k1⟩
      · have hlam : (lam : WithBot α) < b'.sep :=
          lt_of_not_ge (fun h => hsep ((sepLe_iff _ _).mpr h))
        obtain ⟨k1, k2⟩ := intervalOK_fixBlock T (M := M) (b := ⟨b.sep, e :: b.ents⟩) (hi := b'.sep)
          (by simpa [hs] using hlt) (by
            intro x hx hl
            rcases List.mem_cons.mp hx with rfl | hx
            · exact ⟨by simpa [hs, hev] using hlo, by simpa [hev] using hlam⟩
            · exact hb x hx hl)
        refine ⟨?_, by simp [k2]⟩
        simp only at k1
        exact IntervalOK.append_cons (hs ▸ k1) k2 hrest

/-! ### All entries (live and stale) and freshness of ids -/

/-- all entries of a block list -/
def allEnts (bs : List (Block κ α)) : List (Entry κ α) := (bs.map (·.ents)).flatten

theorem mem_allEnts {bs : List (Block κ α)} {x : Entry κ α} :
    x ∈ allEnts bs ↔ ∃ b ∈ bs, x ∈ b.ents := by
  unfold allEnts; simp [List.mem_flatten]

/-- every entry id of `D` is below `fresh` -/
def FreshOK (fresh : ℕ) (D : DStr κ α) : Prop := ∀ x ∈ allEnts D.blocks, x.id < fresh

theorem mem_allEnts_fixBlock {L : Live κ α} {M : ℕ} {b : Block κ α} {x : Entry κ α}
    (h : x ∈ allEnts (fixBlock T L M b).1) : x ∈ b.ents := by
  rw [mem_allEnts] at h
  obtain ⟨c, hc, hx⟩ := h
  unfold fixBlock at hc
  split_ifs at hc with h1 h2 h3
  · simp only [List.mem_singleton] at hc; exact hc ▸ hx
  · simp only [List.mem_singleton] at hc; rw [hc] at hx; exact (mem_liveOf.mp hx).1
  · simp only [List.mem_singleton] at hc; rw [hc] at hx; exact (mem_liveOf.mp hx).1
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact (mem_liveOf.mp (List.mem_filter.mp hx).1).1
    · exact (mem_liveOf.mp (List.mem_filter.mp hx).1).1

theorem mem_allEnts_addTo {L : Live κ α} {M : ℕ} {lam : α} {e : Entry κ α} :
    ∀ {bs : List (Block κ α)} {x : Entry κ α},
      x ∈ allEnts (addTo T L M lam e bs).1 → x ∈ allEnts bs ∨ x = e
  | [], x, h => by simp [addTo, allEnts] at h
  | [b], x, h => by
      simp only [addTo] at h
      have := mem_allEnts_fixBlock T h
      rcases List.mem_cons.mp this with rfl | hx
      · exact Or.inr rfl
      · exact Or.inl (mem_allEnts.mpr ⟨b, List.mem_singleton_self _, hx⟩)
  | b :: b' :: bs, x, h => by
      simp only [addTo] at h
      split_ifs at h with hsep
      · rw [mem_allEnts] at h
        obtain ⟨c, hc, hx⟩ := h
        rcases List.mem_cons.mp hc with rfl | hc
        · exact Or.inl (mem_allEnts.mpr ⟨c, List.mem_cons_self, hx⟩)
        · rcases mem_allEnts_addTo (bs := b' :: bs) (mem_allEnts.mpr ⟨c, hc, hx⟩) with h' | h'
          · obtain ⟨d, hd, hxd⟩ := mem_allEnts.mp h'
            exact Or.inl (mem_allEnts.mpr ⟨d, List.mem_cons_of_mem _ hd, hxd⟩)
          · exact Or.inr h'
      · rw [allEnts, List.map_append, List.flatten_append, List.mem_append] at h
        rcases h with h | h
        · have := mem_allEnts_fixBlock T (b := ⟨b.sep, e :: b.ents⟩) h
          rcases List.mem_cons.mp this with rfl | hx
          · exact Or.inr rfl
          · exact Or.inl (mem_allEnts.mpr ⟨b, List.mem_cons_self, hx⟩)
        · obtain ⟨c, hc, hx⟩ := (mem_allEnts (bs := b' :: bs)).mp h
          exact Or.inl (mem_allEnts.mpr ⟨c, List.mem_cons_of_mem _ hc, hx⟩)

/-! ### The insert operation -/

/-- `Insert` is skipped iff `v` already has a live entry of value `≤ lam`. -/
def skipIns (L : Live κ α) (v : κ) (lam : α) : Bool :=
  match L v with
  | some (_, old) => decide (old ≤ lam)
  | none => false

/-- **Insert** `(v, lam)` into `D`; `fresh` is the next free entry id.  Returns the new live
map, the new id counter, the new structure and the cost (the `T` term is the search-tree
descent to the owning block). -/
def insert (L : Live κ α) (fresh : ℕ) (D : DStr κ α) (v : κ) (lam : α) :
    Live κ α × ℕ × DStr κ α × ℕ :=
  if skipIns L v lam then (L, fresh, D, 2)
  else
    (Function.update L v (some (fresh, lam)), fresh + 1,
      { D with blocks :=
          (addTo T (Function.update L v (some (fresh, lam))) D.M lam ⟨fresh, v, lam⟩ D.blocks).1 },
      (addTo T (Function.update L v (some (fresh, lam))) D.M lam ⟨fresh, v, lam⟩ D.blocks).2 + T + 3)

/-- the value an insertion stores: `min` with the previous one -/
def insVal (old : Option α) (lam : α) : α :=
  match old with
  | none => lam
  | some a => min a lam

theorem isLive_update_of_fresh {L : Live κ α} {v : κ} {fresh : ℕ} {lam : α} {x : Entry κ α}
    (hx : x.id < fresh) :
    x.IsLive (Function.update L v (some (fresh, lam))) ↔ x.IsLive L ∧ x.key ≠ v := by
  unfold Entry.IsLive
  by_cases hk : x.key = v
  · subst hk
    simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq, ne_eq, not_true_eq_false,
      and_false, iff_false, not_and]
    intro h; omega
  · simp [Function.update_of_ne hk, hk]

/-- Correctness of `insert` on views, well-formedness, freshness and the frame property. -/
theorem insert_spec {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α}
    (hwf : WF L D) (hfr : FreshOK fresh D) (hB : lam < D.Bd)
    (hdisc : skipIns L v lam = true → HasKey L D v) :
    (∀ y, view (insert T L fresh D v lam).1 (insert T L fresh D v lam).2.2.1 y =
        if y = v then some (insVal (view L D v) lam) else view L D y) ∧
    WF (insert T L fresh D v lam).1 (insert T L fresh D v lam).2.2.1 ∧
    FreshOK (insert T L fresh D v lam).2.1 (insert T L fresh D v lam).2.2.1 ∧
    fresh ≤ (insert T L fresh D v lam).2.1 ∧
    (insert T L fresh D v lam).2.2.1.M = D.M ∧ (insert T L fresh D v lam).2.2.1.Bd = D.Bd ∧
    -- frame: any other structure with older ids keeps its view except possibly at `v`
    (∀ (D' : DStr κ α), FreshOK fresh D' → ∀ y, y ≠ v →
        view (insert T L fresh D v lam).1 D' y = view L D' y) := by
  obtain ⟨hne, hint⟩ := hwf
  unfold insert
  by_cases hskip : skipIns L v lam = true
  · rw [ite_eq_left hskip]
    dsimp only
    refine ⟨?_, ⟨hne, hint⟩, hfr, le_rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
    intro y
    split_ifs with hy
    · subst hy
      have hk := hdisc hskip
      unfold skipIns at hskip
      rcases hLv : L y with _ | ⟨i, old⟩
      · rw [hLv] at hskip; simp at hskip
      · rw [hLv] at hskip
        simp only [decide_eq_true_eq] at hskip
        have hview : view L D y = some old := by
          unfold view; rw [ite_eq_left hk, hLv]; rfl
        rw [hview]
        simp [insVal, min_eq_left hskip]
    · rfl
  · rw [ite_eq_right hskip]
    dsimp only
    set L' := Function.update L v (some (fresh, lam)) with hL'
    set e : Entry κ α := ⟨fresh, v, lam⟩ with he
    have heL : e.IsLive L' := by simp [Entry.IsLive, hL', he]
    -- live entries of the old blocks under the new map are the old live ones not keyed `v`
    have hold : ∀ x ∈ allEnts D.blocks, (x.IsLive L' ↔ x.IsLive L ∧ x.key ≠ v) :=
      fun x hx => isLive_update_of_fresh (hfr x hx)
    have hintL' : IntervalOK L' D.blocks ⊥ (D.Bd : WithBot α) :=
      IntervalOK.mono' (fun b hb x hx hl =>
        ((hold x (mem_allEnts.mpr ⟨b, hb, hx⟩)).mp hl).1) hint
    obtain ⟨k1, k2⟩ := intervalOK_addTo T (M := D.M) (e := e) (lam := lam) rfl hne hintL' bot_le
      (WithBot.coe_lt_coe.mpr hB)
    set nb := (addTo T L' D.M lam e D.blocks).1 with hnb
    -- live content of the new blocks
    have hlive : ∀ x, x ∈ liveVals L' nb ↔ (x ∈ liveVals L D.blocks ∧ x.key ≠ v) ∨ x = e := by
      intro x
      rw [hnb, mem_liveVals_addTo T hne]
      constructor
      · rintro (h | ⟨rfl, _⟩)
        · obtain ⟨⟨b, hb, hx⟩, hl⟩ := mem_liveVals.mp h
          have := (hold x (mem_allEnts.mpr ⟨b, hb, hx⟩)).mp hl
          exact Or.inl ⟨mem_liveVals.mpr ⟨⟨b, hb, hx⟩, this.1⟩, this.2⟩
        · exact Or.inr rfl
      · rintro (⟨h, hk⟩ | rfl)
        · obtain ⟨⟨b, hb, hx⟩, hl⟩ := mem_liveVals.mp h
          exact Or.inl (mem_liveVals.mpr ⟨⟨b, hb, hx⟩,
            (hold x (mem_allEnts.mpr ⟨b, hb, hx⟩)).mpr ⟨hl, hk⟩⟩)
        · exact Or.inr ⟨rfl, heL⟩
    refine ⟨?_, ⟨k2, k1⟩, ?_, by omega, rfl, rfl, ?_⟩
    · -- views
      intro y
      split_ifs with hy
      · subst hy
        have hl : view L' ⟨D.M, D.Bd, nb⟩ y = some lam :=
          view_eq_some.mpr ⟨e, (hlive e).mpr (Or.inr rfl), rfl, rfl⟩
        rw [hl]
        congr 1
        -- the stored value is `lam`, which is the `min` with any previous view value
        unfold skipIns at hskip
        rcases hLv : L y with _ | ⟨i, old⟩
        · have : view L D y = none := by
            rw [view_eq_none]; rintro ⟨x, hx, hxk⟩
            have := (mem_liveVals.mp hx).2; unfold Entry.IsLive at this
            rw [hxk, hLv] at this; simp at this
          rw [this]; rfl
        · rw [hLv] at hskip
          simp only [decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not, not_le] at hskip
          by_cases hk0 : HasKey L D y
          · have : view L D y = some old := by unfold view; rw [ite_eq_left hk0, hLv]; rfl
            rw [this]; simp [insVal, min_eq_right hskip.le]
          · have : view L D y = none := view_eq_none.mpr hk0
            rw [this]; rfl
      · -- other keys are untouched
        have hLy : L' y = L y := by simp [hL', Function.update_of_ne hy]
        have hiff : HasKey L' ⟨D.M, D.Bd, nb⟩ y ↔ HasKey L D y := by
          constructor
          · rintro ⟨x, hx, hxk⟩
            rcases (hlive x).mp hx with ⟨h, _⟩ | rfl
            · exact ⟨x, h, hxk⟩
            · exact absurd hxk.symm hy
          · rintro ⟨x, hx, hxk⟩
            exact ⟨x, (hlive x).mpr (Or.inl ⟨hx, hxk ▸ hy⟩), hxk⟩
        unfold view
        rw [hLy]
        by_cases hk : HasKey L D y
        · rw [ite_eq_left (hiff.mpr hk), ite_eq_left hk]
        · rw [ite_eq_right (fun h => hk (hiff.mp h)), ite_eq_right hk]
    · -- freshness
      intro x hx
      rcases mem_allEnts_addTo T hx with h | rfl
      · exact lt_trans (hfr x h) (Nat.lt_succ_self _)
      · exact Nat.lt_succ_self _
    · -- frame
      intro D' hfr' y hy
      have hiff : HasKey L' D' y ↔ HasKey L D' y := by
        constructor
        · rintro ⟨x, hx, hxk⟩
          obtain ⟨⟨b, hb, hxb⟩, hl⟩ := mem_liveVals.mp hx
          have := (isLive_update_of_fresh (hfr' x (mem_allEnts.mpr ⟨b, hb, hxb⟩))).mp hl
          exact ⟨x, mem_liveVals.mpr ⟨⟨b, hb, hxb⟩, this.1⟩, hxk⟩
        · rintro ⟨x, hx, hxk⟩
          obtain ⟨⟨b, hb, hxb⟩, hl⟩ := mem_liveVals.mp hx
          exact ⟨x, mem_liveVals.mpr ⟨⟨b, hb, hxb⟩,
            (isLive_update_of_fresh (hfr' x (mem_allEnts.mpr ⟨b, hb, hxb⟩))).mpr ⟨hl, hxk ▸ hy⟩⟩, hxk⟩
      have hLy : L' y = L y := by simp [hL', Function.update_of_ne hy]
      unfold view
      rw [hLy]
      by_cases hk : HasKey L D' y
      · rw [ite_eq_left (hiff.mpr hk), ite_eq_left hk]
      · rw [ite_eq_right (fun h => hk (hiff.mp h)), ite_eq_right hk]

/-! ## Delete -/

/-- **Delete** the keys `ks` (FIX-STALE deletion of settled vertices): clear their live
pointers.  Cost `|ks| + 1`. -/
def deleteKeys (L : Live κ α) (ks : List κ) : Live κ α × ℕ := (clearKeys L ks, ks.length + 1)

theorem deleteKeys_spec {L : Live κ α} {D : DStr κ α} {ks : List κ} (hwf : WF L D) :
    (∀ y, view (deleteKeys L ks).1 D y = if y ∈ ks then none else view L D y) ∧
    WF (deleteKeys L ks).1 D := by
  refine ⟨?_, ⟨hwf.1, IntervalOK.mono (fun e h => (isLive_clearKeys.mp h).1) hwf.2⟩⟩
  intro y
  simp only [deleteKeys]
  split_ifs with hy
  · rw [view_eq_none]
    rintro ⟨e, he, hk⟩
    have := (mem_liveVals.mp he).2
    rw [isLive_clearKeys] at this
    exact this.2 (hk ▸ hy)
  · have hiff : HasKey (clearKeys L ks) D y ↔ HasKey L D y := by
      constructor
      · rintro ⟨e, he, hk⟩
        obtain ⟨hm, hl⟩ := mem_liveVals.mp he
        exact ⟨e, mem_liveVals.mpr ⟨hm, (isLive_clearKeys.mp hl).1⟩, hk⟩
      · rintro ⟨e, he, hk⟩
        obtain ⟨hm, hl⟩ := mem_liveVals.mp he
        exact ⟨e, mem_liveVals.mpr ⟨hm, isLive_clearKeys.mpr ⟨hl, hk ▸ hy⟩⟩, hk⟩
    have hLy : clearKeys L ks y = L y := by simp [clearKeys, hy]
    unfold view
    rw [hLy]
    by_cases hk : HasKey L D y
    · rw [ite_eq_left (hiff.mpr hk), ite_eq_left hk]
    · rw [ite_eq_right (fun h => hk (hiff.mp h)), ite_eq_right hk]

/-! ## Merge -/

/-- Group consecutive blocks: a group is closed as soon as it holds at least `g` entries
(the last group may hold fewer).  A group keeps the separator of its first block; its entry
list is the splice of its blocks' lists (O(1) per block with linked lists). -/
def groupAux (g : ℕ) : Option (Block κ α) → List (Block κ α) → List (Block κ α)
  | none, [] => []
  | some c, [] => [c]
  | none, b :: bs => if g ≤ b.ents.length then b :: groupAux g none bs else groupAux g (some b) bs
  | some c, b :: bs =>
    if g ≤ (c.ents ++ b.ents).length then ⟨c.sep, c.ents ++ b.ents⟩ :: groupAux g none bs
    else groupAux g (some ⟨c.sep, c.ents ++ b.ents⟩) bs

/-- live entries are preserved by grouping -/
theorem mem_liveVals_groupAux {L : Live κ α} {g : ℕ} :
    ∀ {cur : Option (Block κ α)} {bs : List (Block κ α)} {x : Entry κ α},
      x ∈ liveVals L (groupAux g cur bs) ↔
        (((∃ c, cur = some c ∧ x ∈ c.ents) ∧ x.IsLive L) ∨ x ∈ liveVals L bs)
  | none, [], x => by simp [groupAux, liveVals]
  | some c, [], x => by simp [groupAux, liveVals, mem_liveOf]
  | none, b :: bs, x => by
      simp only [groupAux]
      split_ifs
      · rw [mem_liveVals_cons', mem_liveVals_groupAux, mem_liveVals_cons']; simp
      · rw [mem_liveVals_groupAux, mem_liveVals_cons']; simp
  | some c, b :: bs, x => by
      simp only [groupAux]
      split_ifs
      · rw [mem_liveVals_cons', mem_liveVals_groupAux, mem_liveVals_cons']
        simp only [List.mem_append, Option.some.injEq, exists_eq_left', reduceCtorEq, false_and,
          exists_false, false_or]
        tauto
      · rw [mem_liveVals_groupAux, mem_liveVals_cons']
        simp only [List.mem_append, Option.some.injEq, exists_eq_left']
        tauto

theorem mem_allEnts_groupAux {g : ℕ} :
    ∀ {cur : Option (Block κ α)} {bs : List (Block κ α)} {x : Entry κ α},
      x ∈ allEnts (groupAux g cur bs) ↔ ((∃ c, cur = some c ∧ x ∈ c.ents) ∨ x ∈ allEnts bs)
  | none, [], x => by simp [groupAux, allEnts]
  | some c, [], x => by simp [groupAux, allEnts]
  | none, b :: bs, x => by
      simp only [groupAux]
      split_ifs
      · simp only [allEnts, List.map_cons, List.flatten_cons, List.mem_append] at *
        rw [show x ∈ (List.map (·.ents) (groupAux g none bs)).flatten ↔ _ from mem_allEnts_groupAux]
        simp [allEnts]
      · rw [mem_allEnts_groupAux]; simp [allEnts]
  | some c, b :: bs, x => by
      simp only [groupAux]
      split_ifs
      · simp only [allEnts, List.map_cons, List.flatten_cons, List.mem_append] at *
        rw [show x ∈ (List.map (·.ents) (groupAux g none bs)).flatten ↔ _ from mem_allEnts_groupAux]
        simp [allEnts]; tauto
      · rw [mem_allEnts_groupAux]; simp [allEnts]; tauto

/-- widening the upper bound -/
theorem IntervalOK.widen {L : Live κ α} :
    ∀ {bs : List (Block κ α)} {lo hi hi' : WithBot α}, hi ≤ hi' →
      IntervalOK L bs lo hi → IntervalOK L bs lo hi'
  | [], _, _, _, _, _ => trivial
  | [_], _, _, _, hh, h => ⟨h.1, lt_of_lt_of_le h.2.1 hh,
      fun e he hl => ⟨(h.2.2 e he hl).1, lt_of_lt_of_le (h.2.2 e he hl).2 hh⟩⟩
  | _ :: _ :: _, _, _, _, hh, h => ⟨h.1, h.2.1, h.2.2.1, IntervalOK.widen hh h.2.2.2⟩

/-- merging two adjacent blocks keeps the invariant -/
theorem IntervalOK.merge2 {L : Live κ α} {c b : Block κ α} {bs : List (Block κ α)}
    {lo hi : WithBot α} (h : IntervalOK L (c :: b :: bs) lo hi) :
    IntervalOK L (⟨c.sep, c.ents ++ b.ents⟩ :: bs) lo hi := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases bs with _ | ⟨b', bs'⟩
  · obtain ⟨k1, k2, k3⟩ := h4
    refine ⟨h1, lt_trans h2 k2, ?_⟩
    intro e he hl
    rcases List.mem_append.mp he with he | he
    · exact ⟨(h3 e he hl).1, lt_trans (h3 e he hl).2 k2⟩
    · exact ⟨le_trans (h1 ▸ h2.le) (k1 ▸ (k3 e he hl).1), (k3 e he hl).2⟩
  · obtain ⟨k1, k2, k3, k4⟩ := h4
    refine ⟨h1, lt_trans h2 k2, ?_, k4⟩
    intro e he hl
    rcases List.mem_append.mp he with he | he
    · exact ⟨(h3 e he hl).1, lt_trans (h3 e he hl).2 k2⟩
    · exact ⟨le_trans (h1 ▸ h2.le) (k1 ▸ (k3 e he hl).1), (k3 e he hl).2⟩

/-- consing a block onto an equivalent tail -/
theorem IntervalOK.cons_of {L : Live κ α} {b : Block κ α} {bs bs' : List (Block κ α)}
    {lo hi : WithBot α} (h : IntervalOK L (b :: bs) lo hi)
    (h' : IntervalOK L bs' (nextSep bs hi) hi) (hsep : nextSep bs' hi = nextSep bs hi)
    (hnil : bs' = [] ↔ bs = []) : IntervalOK L (b :: bs') lo hi := by
  rcases bs with _ | ⟨c, cs⟩
  · rw [hnil.mpr rfl]; exact h
  · rcases bs' with _ | ⟨c', cs'⟩
    · exact absurd (hnil.mp rfl) (List.cons_ne_nil _ _)
    · obtain ⟨h1, h2, h3, h4⟩ := h
      simp only [nextSep] at hsep
      exact ⟨h1, hsep ▸ h2, fun e he hl => ⟨(h3 e he hl).1, hsep ▸ (h3 e he hl).2⟩, hsep ▸ h'⟩

theorem groupAux_some_ne_nil {g : ℕ} :
    ∀ {c : Block κ α} {bs : List (Block κ α)}, groupAux g (some c) bs ≠ []
  | c, [] => by simp [groupAux]
  | c, b :: bs => by
      simp only [groupAux]
      split_ifs
      · exact List.cons_ne_nil _ _
      · exact groupAux_some_ne_nil

theorem groupAux_none_nil_iff {g : ℕ} :
    ∀ {bs : List (Block κ α)}, groupAux g none bs = [] ↔ bs = []
  | [] => by simp [groupAux]
  | b :: bs => by
      simp only [groupAux]
      split_ifs
      · simp
      · simpa using groupAux_some_ne_nil

theorem nextSep_groupAux_some {g : ℕ} {hi : WithBot α} :
    ∀ {c : Block κ α} {bs : List (Block κ α)}, nextSep (groupAux g (some c) bs) hi = c.sep
  | c, [] => by simp [groupAux, nextSep]
  | c, b :: bs => by
      simp only [groupAux]
      split_ifs
      · rfl
      · exact nextSep_groupAux_some

theorem nextSep_groupAux_none {g : ℕ} {hi : WithBot α} :
    ∀ {bs : List (Block κ α)}, nextSep (groupAux g none bs) hi = nextSep bs hi
  | [] => by simp [groupAux, nextSep]
  | b :: bs => by
      simp only [groupAux]
      split_ifs
      · rfl
      · exact nextSep_groupAux_some

/-- grouping keeps the interval invariant -/
theorem intervalOK_groupAux {L : Live κ α} {g : ℕ} :
    ∀ {cur : Option (Block κ α)} {bs : List (Block κ α)} {lo hi : WithBot α},
      IntervalOK L (cur.toList ++ bs) lo hi → IntervalOK L (groupAux g cur bs) lo hi
  | none, [], _, _, h => by simpa [groupAux] using h
  | some c, [], _, _, h => by simpa [groupAux] using h
  | none, b :: bs, lo, hi, h => by
      simp only [Option.toList, List.nil_append] at h
      simp only [groupAux]
      split_ifs
      · have hrest : IntervalOK L bs (nextSep bs hi) hi := by
          rcases bs with _ | ⟨c, cs⟩
          · trivial
          · exact h.2.2.2
        have ih := intervalOK_groupAux (g := g) (cur := none) (bs := bs) (by simpa using hrest)
        exact h.cons_of ih nextSep_groupAux_none groupAux_none_nil_iff
      · exact intervalOK_groupAux (g := g) (cur := some b) (by simpa using h)
  | some c, b :: bs, lo, hi, h => by
      simp only [Option.toList, List.singleton_append] at h
      have hm := h.merge2
      simp only [groupAux]
      split_ifs
      · have hrest : IntervalOK L bs (nextSep bs hi) hi := by
          rcases bs with _ | ⟨c', cs⟩
          · trivial
          · exact hm.2.2.2
        have ih := intervalOK_groupAux (g := g) (cur := none) (bs := bs) (by simpa using hrest)
        exact hm.cons_of ih nextSep_groupAux_none groupAux_none_nil_iff
      · exact intervalOK_groupAux (g := g) (cur := some ⟨c.sep, c.ents ++ b.ents⟩) (by simpa using hm)

theorem mem_liveVals_groupAux_none {L : Live κ α} {g : ℕ} {bs : List (Block κ α)}
    {x : Entry κ α} : x ∈ liveVals L (groupAux g none bs) ↔ x ∈ liveVals L bs := by
  rw [mem_liveVals_groupAux]; simp

/-- **Merge** `D'` into `D` (DS' / M-LINK): group the blocks of `D'` into groups of at least
`M/3` entries, prepend them, and re-separate the old first block of `D` at `D'.Bd` (drop it if
that interval is empty).  Cost: one step per block of `D'` (the splices) plus one search-tree
operation per group and two for re-keying the old first block. -/
def merge (D D' : DStr κ α) : DStr κ α × ℕ :=
  match D.blocks with
  | [] => (D, 1)
  | f :: rest =>
    ({ D with blocks := groupAux (D.M / 3) none D'.blocks ++
        (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
          then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) },
     D'.blocks.length + T * ((groupAux (D.M / 3) none D'.blocks).length + 2) + 2)

/-- Correctness of `merge`: the new view is the union of the two views (which have disjoint
keys when their entry ids are disjoint), and the result is well formed. -/
theorem merge_spec {L : Live κ α} {D D' : DStr κ α} (hwf : WF L D) (hwf' : WF L D')
    (hMP1 : ∀ e ∈ liveVals L D.blocks, D'.Bd ≤ e.val)
    (hMP2 : ∀ b ∈ D.blocks.tail, (D'.Bd : WithBot α) < b.sep) (hMP0 : D'.Bd ≤ D.Bd) :
    (∀ y, HasKey L (merge T D D').1 y ↔ HasKey L D' y ∨ HasKey L D y) ∧
    (∀ y, view L (merge T D D').1 y = if HasKey L D' y then view L D' y else view L D y) ∧
    WF L (merge T D D').1 ∧ (merge T D D').1.M = D.M ∧ (merge T D D').1.Bd = D.Bd := by
  obtain ⟨hne, hint⟩ := hwf
  obtain ⟨hne', hint'⟩ := hwf'
  rcases hD : D.blocks with _ | ⟨f, rest⟩
  · exact absurd hD hne
  rw [hD] at hint hMP2
  have hmD : merge T D D' = ({ D with blocks := groupAux (D.M / 3) none D'.blocks ++
        (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
          then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) },
      D'.blocks.length + T * ((groupAux (D.M / 3) none D'.blocks).length + 2) + 2) := by
    unfold merge; rw [hD]
  rw [hmD]
  dsimp only
  set gs := groupAux (D.M / 3) none D'.blocks with hgs
  -- the live entries of `f` lie in `[D'.Bd, nextSep rest)`
  have hf : ∀ e ∈ f.ents, e.IsLive L →
      (D'.Bd : WithBot α) ≤ e.val ∧ (e.val : WithBot α) < nextSep rest (D.Bd : WithBot α) := by
    intro e he hl
    have h1 := hMP1 e (by rw [hD]; exact mem_liveVals.mpr ⟨⟨f, List.mem_cons_self, he⟩, hl⟩)
    refine ⟨WithBot.coe_le_coe.mpr h1, ?_⟩
    have := (hint.split (bs₁ := [f]) (bs₂ := rest) (List.cons_ne_nil _ _)).1
    exact (this.bounds f (List.mem_singleton_self _) e he hl).2
  have hrest : IntervalOK L rest (nextSep rest (D.Bd : WithBot α)) D.Bd :=
    (hint.split (bs₁ := [f]) (bs₂ := rest) (List.cons_ne_nil _ _)).2
  have hgsI : IntervalOK L gs ⊥ D'.Bd :=
    intervalOK_groupAux (cur := none) (by simpa using hint')
  have hgsne : gs ≠ [] := by rw [hgs]; exact fun h => hne' (groupAux_none_nil_iff.mp h)
  -- live content
  have hlive : ∀ x, x ∈ liveVals L (gs ++ (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
      then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest)) ↔
      x ∈ liveVals L D'.blocks ∨ x ∈ liveVals L D.blocks := by
    intro x
    rw [liveVals_append, List.mem_append, hgs, mem_liveVals_groupAux_none, hD]
    split_ifs with hc'
    · rw [mem_liveVals_cons', mem_liveVals_cons']
    · have hc : ¬ (D'.Bd : WithBot α) < nextSep rest (D.Bd : WithBot α) :=
        fun h => hc' ((ltSep_iff _ _).mpr h)
      rw [mem_liveVals_cons']
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | (⟨hx, hl⟩ | h))
        · exact Or.inl h
        · exact absurd (lt_of_le_of_lt (hf x hx hl).1 (hf x hx hl).2) hc
        · exact Or.inr h
  have hkey : ∀ y, HasKey L ⟨D.M, D.Bd, gs ++ (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
      then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest)⟩ y ↔ HasKey L D' y ∨ HasKey L D y := by
    intro y
    constructor
    · rintro ⟨x, hx, hk⟩
      rcases (hlive x).mp hx with h | h
      · exact Or.inl ⟨x, h, hk⟩
      · exact Or.inr ⟨x, h, hk⟩
    · rintro (⟨x, hx, hk⟩ | ⟨x, hx, hk⟩)
      · exact ⟨x, (hlive x).mpr (Or.inl hx), hk⟩
      · exact ⟨x, (hlive x).mpr (Or.inr hx), hk⟩
  refine ⟨hkey, ?_, ⟨by simp [hgsne], ?_⟩, rfl, rfl⟩
  · intro y
    by_cases h1 : HasKey L D' y
    · rw [ite_eq_left h1]
      unfold view
      rw [ite_eq_left ((hkey y).mpr (Or.inl h1)), ite_eq_left h1]
    · rw [ite_eq_right h1]
      unfold view
      by_cases h2 : HasKey L D y
      · rw [ite_eq_left ((hkey y).mpr (Or.inr h2)), ite_eq_left h2]
      · rw [ite_eq_right (fun h => ((hkey y).mp h).elim h1 h2), ite_eq_right h2]
  · -- interval invariant of the merged list
    split_ifs with hc'
    · have hc : (D'.Bd : WithBot α) < nextSep rest (D.Bd : WithBot α) := (ltSep_iff _ _).mp hc'
      have hf' : IntervalOK L (⟨(D'.Bd : WithBot α), f.ents⟩ :: rest) D'.Bd D.Bd := by
        rcases rest with _ | ⟨r, rs⟩
        · exact ⟨rfl, by simpa [nextSep] using hc, fun e he hl => by
            simpa [nextSep] using hf e he hl⟩
        · exact ⟨rfl, hc, fun e he hl => hf e he hl, hrest⟩
      exact IntervalOK.append_cons hgsI hgsne hf'
    · have hc : ¬ (D'.Bd : WithBot α) < nextSep rest (D.Bd : WithBot α) :=
        fun h => hc' ((ltSep_iff _ _).mpr h)
      rcases rest with _ | ⟨r, rs⟩
      · simp only [List.append_nil]
        exact hgsI.widen (WithBot.coe_le_coe.mpr hMP0)
      · exact absurd (hMP2 r List.mem_cons_self) (by simpa [nextSep] using hc)

/-! ## Sizes, distinctness and the pull size bound -/

/-- every block holds at most `2M + 1` entries -/
def BlockSizeOK (D : DStr κ α) : Prop := ∀ b ∈ D.blocks, b.ents.length ≤ 2 * D.M + 1

/-- entry ids of `D` are pairwise distinct -/
def IdsNodup (D : DStr κ α) : Prop := ((allEnts D.blocks).map (·.id)).Nodup

/-- values of live entries determine their keys (for walk labels: the end vertex) -/
def KeyInj (L : Live κ α) (kof : α → κ) : Prop := ∀ v i a, L v = some (i, a) → kof a = v

theorem collect_length_le (L : Live κ α) (M c : ℕ) :
    ∀ (bs : List (Block κ α)) (acc : List (Entry κ α)), acc.length ≤ M →
      (∀ b ∈ bs, b.ents.length ≤ c) → (collect L M acc bs).1.length ≤ M + c
  | [], acc, h, _ => by simp [collect]; omega
  | b :: bs, acc, h, hc => by
      simp only [collect]
      have hb : (liveOf L b.ents).length ≤ c :=
        le_trans (List.length_filter_le _ _) (hc b List.mem_cons_self)
      split_ifs with h1
      · simp only [List.length_append] at h1 ⊢; omega
      · exact collect_length_le L M c bs _ (by omega) (fun b' hb' => hc b' (List.mem_cons_of_mem _ hb'))

/-- live entries of a structure with distinct ids have distinct values -/
theorem nodup_vals_of_live {L : Live κ α} {kof : α → κ} (hK : KeyInj L kof) :
    ∀ {es : List (Entry κ α)}, (es.map (·.id)).Nodup → (∀ e ∈ es, e.IsLive L) →
      (es.map (·.val)).Nodup
  | [], _, _ => List.nodup_nil
  | e :: es, hn, hl => by
      rw [List.map_cons, List.nodup_cons] at hn ⊢
      refine ⟨?_, nodup_vals_of_live hK hn.2 (fun x hx => hl x (List.mem_cons_of_mem _ hx))⟩
      intro hmem
      obtain ⟨e', he', hv⟩ := List.mem_map.mp hmem
      have h1 := hl e List.mem_cons_self
      have h2 := hl e' (List.mem_cons_of_mem _ he')
      have hk1 := hK _ _ _ h1
      have hk2 := hK _ _ _ h2
      have hkey : e.key = e'.key := by rw [← hk1, ← hk2, hv]
      have := (live_key_unique h1 h2 hkey).1
      exact hn.1 (List.mem_map.mpr ⟨e', he', this.symm⟩)



theorem liveVals_sublist_allEnts (L : Live κ α) :
    ∀ bs : List (Block κ α), (liveVals L bs).Sublist (allEnts bs)
  | [] => by simp [liveVals, allEnts]
  | b :: bs => by
      simp only [liveVals, allEnts, List.map_cons, List.flatten_cons]
      exact List.Sublist.append List.filter_sublist (liveVals_sublist_allEnts L bs)

theorem cntLe_eq_cntLt_add_one {l : List α} {x : α} (hn : l.Nodup) (hx : x ∈ l) :
    cntLe l x = cntLt l x + 1 := by
  unfold cntLe cntLt
  induction l with
  | nil => simp at hx
  | cons a as ih =>
    rw [List.nodup_cons] at hn
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hx with rfl | h
    · have e1 : as.countP (fun y => decide (y ≤ x)) = as.countP (fun y => decide (y < x)) := by
        apply List.countP_congr
        intro y hy
        have hyx : y ≠ x := fun h => hn.1 (h ▸ hy)
        simp only [decide_eq_true_eq]
        exact ⟨fun h => lt_of_le_of_ne h hyx, le_of_lt⟩
      simp [e1]
    · have ih' := ih hn.2 h
      by_cases hax : a < x
      · simp [hax, hax.le]; omega
      · have hax' : ¬ a ≤ x := by
          intro hle
          rcases hle.lt_or_eq with h' | h'
          · exact hax h'
          · exact hn.1 (h' ▸ h)
        simp [hax, hax']; omega

/-- Size of a pull and the facts later `merge` calls need: every remaining live value and every
non-first separator lies above the returned separator. -/
theorem pull_post {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) :
    (pull T L D).1.length ≤ D.M ∧
    ((pull T L D).2.1 = D.Bd ∨ (pull T L D).1.length = D.M) ∧
    ((∃ y, HasKey L D y) → (pull T L D).1 ≠ []) ∧
    (∀ e ∈ liveVals (pull T L D).2.2.1 (pull T L D).2.2.2.1.blocks, (pull T L D).2.1 ≤ e.val) ∧
    (∀ b ∈ (pull T L D).2.2.2.1.blocks.tail, ((pull T L D).2.1 : WithBot α) < b.sep) := by
  obtain ⟨hne, hint⟩ := hwf
  unfold pull
  obtain ⟨pre, hbs, hacc, -, -, hrem, hpre⟩ := collect_spec L D.M D.blocks []
  simp only [List.nil_append] at hacc
  set acc := (collect L D.M [] D.blocks).1 with hacc_def
  set rem := (collect L D.M [] D.blocks).2.1 with hrem_def
  by_cases hsmall : acc.length ≤ D.M
  · rw [ite_eq_left hsmall]
    dsimp only
    have hrem0 : rem = [] := by rcases hrem with h | h; exact h; omega
    rw [hrem0, List.append_nil] at hbs
    have hall : acc = liveVals L D.blocks := by rw [hacc, ← hbs]
    refine ⟨by simpa using hsmall, Or.inl rfl, ?_, ?_, by simp⟩
    · rintro ⟨y, e, he, _⟩
      rw [← hall] at he
      simp only [ne_eq, List.map_eq_nil_iff]
      exact List.ne_nil_of_mem he
    · intro e he; simp [liveVals, liveOf] at he
  · rw [ite_eq_right hsmall]
    dsimp only
    have hM' : D.M < acc.length := by omega
    have hpre' : pre ≠ [] := by
      rcases hpre with h | h
      · exact h
      · exfalso; rw [h] at hbs; rw [hacc] at hM'
        simp only [List.nil_eq_append_iff] at hbs
        rw [hbs.1] at hM'; simp [liveVals] at hM'
    rw [hbs] at hint
    obtain ⟨hintP, hintR⟩ := hint.split hpre'
    set mid := nextSep rem (D.Bd : WithBot α) with hmid
    set x := (selectC (acc.map (·.val)) D.M).1 with hx
    have hkth : IsKth (acc.map (·.val)) D.M x := selectC_isKth _ (by simpa using hM')
    have haccB : ∀ e ∈ acc, e.IsLive L ∧ (e.val : WithBot α) < mid := by
      intro e he
      rw [hacc] at he
      obtain ⟨⟨b, hb, heb⟩, hl⟩ := mem_liveVals.mp he
      exact ⟨hl, (hintP.bounds b hb e heb hl).2⟩
    have hxmid : (x : WithBot α) < mid := by
      obtain ⟨e0, he0, hex⟩ := List.mem_map.mp hkth.1
      rw [← hex]; exact (haccB e0 he0).2
    -- ids of `acc` are distinct, hence so are its values
    have hacc_nodup : (acc.map (·.id)).Nodup := by
      rw [hacc]
      have hsplit : (allEnts D.blocks).map (·.id) =
          (allEnts pre).map (·.id) ++ (allEnts rem).map (·.id) := by
        rw [hbs]; simp [allEnts]
      have hid' := hid
      unfold IdsNodup at hid'
      rw [hsplit] at hid'
      have h2 : ((allEnts pre).map (·.id)).Nodup := (List.nodup_append.mp hid').1
      have hsub : (liveVals L pre).Sublist (allEnts pre) := liveVals_sublist_allEnts L pre
      exact (hsub.map _).nodup h2
    have hvals : (acc.map (·.val)).Nodup :=
      nodup_vals_of_live hK hacc_nodup (fun e he => (haccB e he).1)
    -- exactly `M` values are below `x`
    have hcnt : (acc.filter (fun e => decide (e.val < x))).length = D.M := by
      have h1 := hkth.2.1
      have h2 := hkth.2.2
      have hle := cntLe_eq_cntLt_add_one hvals hkth.1
      have : (acc.filter (fun e => decide (e.val < x))).length = cntLt (acc.map (·.val)) x := by
        unfold cntLt; rw [← List.countP_eq_length_filter, List.countP_map]; rfl
      omega
    refine ⟨by simp [hcnt], Or.inr (by simp [hcnt]), fun _ => ?_, ?_, ?_⟩
    · intro h
      have : (acc.filter (fun e => decide (e.val < x))).length = 0 := by
        simpa using congrArg List.length h
      omega
    · intro e he
      obtain ⟨⟨b, hb, heb⟩, hl⟩ := mem_liveVals.mp he
      rw [isLive_clearKeys] at hl
      rcases List.mem_cons.mp hb with rfl | hb
      · exact (List.mem_filter.mp heb).2 |> fun h => by simpa using h
      · have := (hintR.bounds b hb e heb hl.1).1
        exact (WithBot.coe_le_coe.mp (le_trans hxmid.le this))
    · intro b hb
      simp only [List.tail_cons] at hb
      rcases hr : rem with _ | ⟨r, rs⟩
      · rw [hr] at hb; simp at hb
      · rw [hr] at hb hintR hmid
        have hmr : mid = r.sep := by simp [hmid, nextSep]
        rcases List.mem_cons.mp hb with rfl | hb
        · rw [← hmr]; exact hxmid
        · -- later separators are larger still
          have hsorted : ∀ c ∈ rs, r.sep < c.sep := by
            intro c hc
            have key : ∀ {bs : List (Block κ α)} {lo hi : WithBot α}, IntervalOK L bs lo hi →
                ∀ c ∈ bs.tail, lo < c.sep := by
              intro bs
              induction bs with
              | nil => intro _ _ _ c hc; simp at hc
              | cons b0 bs0 ih =>
                intro lo hi h c hc
                rcases bs0 with _ | ⟨b1, bs1⟩
                · simp at hc
                · obtain ⟨h1, h2, _, h4⟩ := h
                  simp only [List.tail_cons] at hc
                  rcases List.mem_cons.mp hc with rfl | hc
                  · exact h2
                  · exact lt_trans h2 (ih h4 c hc)
            have := key hintR c (by simpa using hc)
            rw [hmr] at this; exact this
          exact lt_trans hxmid (hmr ▸ hsorted b hb)

/-! ## Frame over time and the lazy/literal equivalence (O6, B1 S5 / CHD_SEC_DS §4) -/

/-- A change of the live map from `L₀` to `L₁` is **fresh above `f₀`** if every key whose live
pointer changed now points nowhere or to an entry id `≥ f₀`.  Every `insert` (with id counter
`≥ f₀`), `pull`, `deleteKeys` and `merge` performed on OTHER structures produces such changes. -/
def FreshChange (f₀ : ℕ) (L₀ L₁ : Live κ α) : Prop :=
  ∀ y, L₁ y = L₀ y ∨ L₁ y = none ∨ ∃ i a, f₀ ≤ i ∧ L₁ y = some (i, a)

/-- **Frame over time**: a structure whose ids are below `f₀` keeps its view at every untouched
key and loses every touched key. -/
theorem view_of_freshChange {f₀ : ℕ} {L₀ L₁ : Live κ α} {D : DStr κ α} (hfr : FreshOK f₀ D)
    (hch : FreshChange f₀ L₀ L₁) (y : κ) :
    view L₁ D y = if L₁ y = L₀ y then view L₀ D y else none := by
  split_ifs with hy
  · have hiff : HasKey L₁ D y ↔ HasKey L₀ D y := by
      constructor
      · rintro ⟨e, he, hk⟩
        obtain ⟨hm, hl⟩ := mem_liveVals.mp he
        refine ⟨e, mem_liveVals.mpr ⟨hm, ?_⟩, hk⟩
        unfold Entry.IsLive at hl ⊢; rw [hk] at hl ⊢; rw [← hy]; exact hl
      · rintro ⟨e, he, hk⟩
        obtain ⟨hm, hl⟩ := mem_liveVals.mp he
        refine ⟨e, mem_liveVals.mpr ⟨hm, ?_⟩, hk⟩
        unfold Entry.IsLive at hl ⊢; rw [hk] at hl ⊢; rw [hy]; exact hl
    unfold view
    rw [hy]
    by_cases hk : HasKey L₀ D y
    · rw [ite_eq_left (hiff.mpr hk), ite_eq_left hk]
    · rw [ite_eq_right (fun h => hk (hiff.mp h)), ite_eq_right hk]
  · rw [view_eq_none]
    rintro ⟨e, he, hk⟩
    obtain ⟨⟨b, hb, heb⟩, hl⟩ := mem_liveVals.mp he
    have hid := hfr e (mem_allEnts.mpr ⟨b, hb, heb⟩)
    unfold Entry.IsLive at hl
    rw [hk] at hl
    rcases hch y with h | h | ⟨i, a, hi, h⟩
    · exact hy h
    · rw [h] at hl; simp at hl
    · rw [h] at hl
      simp only [Option.some.injEq, Prod.mk.injEq] at hl
      omega

/-- **Lazy/literal equivalence at a merge** (the abstract content of CHD_SEC_DS §4).
`V₀` is the literal view of the parent structure `D` when the child call started (then equal to
its lazy view under `L₀`); `W'` is the literal (= lazy) view of the returned child structure `D'`;
`Z` is the set of keys deleted from `D` right after the merge (FIX-STALE, BM.15/BM.29).
If every key touched during the child call and not in `Z` is present in `W'` with a value `≤` its
old value, then after `merge` and deletion of `Z`, the lazy view equals the literal
`keep-smaller` merge followed by deletion of `Z`. -/
theorem lazy_merge_eq_literal {f₀ : ℕ} {L₀ L₁ : Live κ α} {D D' : DStr κ α} {Z : List κ}
    {V₀ W' : κ → Option α} (hfr : FreshOK f₀ D) (hch : FreshChange f₀ L₀ L₁)
    (hV₀ : ∀ y, view L₀ D y = V₀ y) (hW' : ∀ y, view L₁ D' y = W' y)
    (hmerge : ∀ y, view L₁ (merge T D D').1 y =
      if HasKey L₁ D' y then view L₁ D' y else view L₁ D y)
    (htouch : ∀ y, L₁ y ≠ L₀ y → y ∉ Z →
      ∃ a, W' y = some a ∧ ∀ b, V₀ y = some b → a ≤ b)
    (y : κ) (hy : y ∉ Z) :
    view L₁ (merge T D D').1 y =
      match V₀ y, W' y with
      | none, w => w
      | v, none => v
      | some a, some b => some (min a b) := by
  rw [hmerge y]
  have hDy := view_of_freshChange hfr hch y
  by_cases hk : HasKey L₁ D' y
  · rw [ite_eq_left hk, hW']
    by_cases ht : L₁ y = L₀ y
    · -- untouched: then `y` is also a key of `D'`?  its live entry is in `D'` and was already live
      -- at the start, so it is `D`'s entry only if `D` and `D'` share it; the literal merge
      -- keeps the smaller value, which is the unique stored one
      rcases hW : W' y with _ | b
      · exfalso
        exact (view_eq_none.mp (by rw [hW', hW])) hk
      · rcases hV : V₀ y with _ | a
        · rfl
        · -- both views hold `y` with the SAME live value
          have h1 : view L₁ D y = some a := by rw [hDy, if_pos ht, hV₀, hV]
          have h2 : view L₁ D' y = some b := by rw [hW', hW]
          have ha := view_eq_some.mp h1
          have hb := view_eq_some.mp h2
          obtain ⟨e, he, hek, hev⟩ := ha
          obtain ⟨e', he', hek', hev'⟩ := hb
          have := (live_key_unique (mem_liveVals.mp he).2 (mem_liveVals.mp he').2
            (hek.trans hek'.symm)).2
          rw [← hev, ← hev', this]; simp
    · obtain ⟨a, ha, hle⟩ := htouch y ht hy
      rw [ha]
      rcases hV : V₀ y with _ | b
      · rfl
      · simp [min_eq_right (hle b hV)]
  · rw [ite_eq_right hk]
    have hW : W' y = none := by rw [← hW']; exact view_eq_none.mpr hk
    rw [hW, hDy]
    by_cases ht : L₁ y = L₀ y
    · rw [if_pos ht, hV₀]
      rcases V₀ y <;> rfl
    · exfalso
      obtain ⟨a, ha, _⟩ := htouch y ht hy
      rw [hW] at ha; simp at ha

/-! ## Potential and amortized costs -/

/-- number of stale entries of a block list -/
def staleCnt (L : Live κ α) (bs : List (Block κ α)) : ℕ :=
  (allEnts bs).countP (fun e => !decide (e.IsLive L))

/-- total excess of block sizes over `M` -/
def excess (M : ℕ) (bs : List (Block κ α)) : ℕ := (bs.map (fun b => b.ents.length - M)).sum

/-- the potential of a structure: stale entries pay for their discard, blocks pay for their
removal from the search tree, oversized blocks pay for their split -/
def pot (L : Live κ α) (D : DStr κ α) : ℕ :=
  2 * staleCnt L D.blocks + 2 * T * D.blocks.length + 420 * excess D.M D.blocks

theorem liveVals_eq_filter (L : Live κ α) (bs : List (Block κ α)) :
    liveVals L bs = (allEnts bs).filter (fun e => decide (e.IsLive L)) := by
  induction bs with
  | nil => simp [liveVals, allEnts]
  | cons b bs ih =>
    rw [liveVals_cons, ih]
    simp [allEnts, List.filter_append, liveOf]

theorem length_liveVals (L : Live κ α) (bs : List (Block κ α)) :
    (liveVals L bs).length = (allEnts bs).countP (fun e => decide (e.IsLive L)) := by
  rw [liveVals_eq_filter, List.countP_eq_length_filter]

theorem length_allEnts (L : Live κ α) (bs : List (Block κ α)) :
    (allEnts bs).length = (liveVals L bs).length + staleCnt L bs := by
  rw [length_liveVals, staleCnt]
  have := List.length_eq_countP_add_countP (l := allEnts bs) (fun e : Entry κ α => e.IsLive L)
  rw [this]
  congr 1
  apply List.countP_congr
  intro x _
  simp

theorem staleCnt_append (L : Live κ α) (bs₁ bs₂ : List (Block κ α)) :
    staleCnt L (bs₁ ++ bs₂) = staleCnt L bs₁ + staleCnt L bs₂ := by
  simp [staleCnt, allEnts, List.countP_append]

theorem staleCnt_cons (L : Live κ α) (b : Block κ α) (bs : List (Block κ α)) :
    staleCnt L (b :: bs) = b.ents.countP (fun e => !decide (e.IsLive L)) + staleCnt L bs := by
  simp [staleCnt, allEnts, List.countP_append]

theorem excess_append (M : ℕ) (bs₁ bs₂ : List (Block κ α)) :
    excess M (bs₁ ++ bs₂) = excess M bs₁ + excess M bs₂ := by
  simp [excess]

theorem excess_cons (M : ℕ) (b : Block κ α) (bs : List (Block κ α)) :
    excess M (b :: bs) = (b.ents.length - M) + excess M bs := by
  simp [excess]

theorem sum_length_allEnts (bs : List (Block κ α)) :
    (bs.map (fun b => b.ents.length)).sum = (allEnts bs).length := by
  simp [allEnts, List.length_flatten, Function.comp_def]

/-- **Amortized cost of `pull`**: `cost + Φ(after) ≤ Φ(before) + 735 M + 3 T + 526`. -/
theorem pull_amortized {L : Live κ α} {D : DStr κ α} {kof : α → κ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) (hsz : BlockSizeOK D) :
    (pull T L D).2.2.2.2 + pot T (pull T L D).2.2.1 (pull T L D).2.2.2.1 ≤
      pot T L D + (735 * D.M + 3 * T + 526) := by
  have hpost := pull_post T hwf hK hid hM
  obtain ⟨hne, hint⟩ := hwf
  unfold pull at hpost ⊢
  obtain ⟨pre, hbs, hacc, hk, hsc, hrem, hpre⟩ := collect_spec L D.M D.blocks []
  simp only [List.nil_append] at hacc
  set acc := (collect L D.M [] D.blocks).1 with hacc_def
  set rem := (collect L D.M [] D.blocks).2.1 with hrem_def
  have hacc_le : acc.length ≤ D.M + (2 * D.M + 1) :=
    collect_length_le L D.M (2 * D.M + 1) D.blocks [] (by simp) hsz
  have hsc' : (collect L D.M [] D.blocks).2.2.2 = acc.length + staleCnt L pre := by
    rw [hsc, sum_length_allEnts, length_allEnts L pre, ← hacc]
  have hpotD : pot T L D = 2 * (staleCnt L pre + staleCnt L rem) +
      2 * T * (pre.length + rem.length) + 420 * (excess D.M pre + excess D.M rem) := by
    unfold pot; rw [hbs, staleCnt_append, excess_append, List.length_append]
  by_cases hsmall : acc.length ≤ D.M
  · rw [ite_eq_left hsmall] at hpost ⊢
    dsimp only at hpost ⊢
    have hrem0 : rem = [] := by rcases hrem with h | h; exact h; omega
    have hpot' : pot T (clearKeys L (acc.map (·.key))) ⟨D.M, D.Bd, [⟨⊥, []⟩]⟩ = 2 * T := by
      simp [pot, staleCnt, allEnts, excess]
    rw [hpot', hsc', hk]
    have hs0 : staleCnt L ([] : List (Block κ α)) = 0 := by simp [staleCnt, allEnts]
    have he0 : excess D.M ([] : List (Block κ α)) = 0 := by simp [excess]
    rw [hrem0, hs0, he0] at hpotD
    simp only [List.length_nil, add_zero] at hpotD
    have h1 : T * (pre.length + 1) = T * pre.length + T := by ring
    have h2 : 2 * T * pre.length = 2 * (T * pre.length) := by ring
    rw [h1]; rw [h2] at hpotD
    set tp := T * pre.length
    omega
  · rw [ite_eq_right hsmall] at hpost ⊢
    dsimp only at hpost ⊢
    obtain ⟨hlen, hxB, -, -, -⟩ := hpost
    set x := (selectC (acc.map (·.val)) D.M).1 with hx
    set S := acc.filter (fun e => decide (e.val < x)) with hS
    set R := acc.filter (fun e => decide (x ≤ e.val)) with hR
    set ks := S.map (·.key) with hks
    have hM' : D.M < acc.length := by omega
    have hsel := selectC_cost (acc.map (·.val)) (k := D.M) (by simpa using hM')
    simp only [List.length_map] at hsel
    -- sizes
    have hSR : S.length + R.length = acc.length := by
      rw [hS, hR, ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      have := List.length_eq_countP_add_countP (l := acc) (fun e : Entry κ α => e.val < x)
      rw [this]; congr 1; apply List.countP_congr; intro e _; simp
    have hxneq : x ≠ D.Bd := by
      -- the separator is a live value, hence strictly below `Bd`
      have hkth : IsKth (acc.map (·.val)) D.M x := selectC_isKth _ (by simpa using hM')
      obtain ⟨e0, he0, hex⟩ := List.mem_map.mp hkth.1
      rw [hacc] at he0
      obtain ⟨⟨b, hb, heb⟩, hl⟩ := mem_liveVals.mp he0
      have := (hint.bounds b (by rw [hbs]; exact List.mem_append_left _ hb) e0 heb hl).2
      intro h; rw [hex, h] at this
      exact absurd this (lt_irrefl _)
    have hSlen : S.length = D.M := by
      rcases hxB with h | h
      · exact absurd h hxneq
      · simpa [hks] using h
    -- potential after
    have hRlive : ∀ e ∈ R, e.IsLive (clearKeys L ks) := by
      intro e he
      have he' := (List.mem_filter.mp he)
      rw [hacc] at he'
      have hl := (mem_liveVals.mp he'.1).2
      rw [isLive_clearKeys]
      refine ⟨hl, fun hk' => ?_⟩
      obtain ⟨e', he's, hkk⟩ := List.mem_map.mp hk'
      have h1 := List.mem_filter.mp he's
      rw [hacc] at h1
      have hl' := (mem_liveVals.mp h1.1).2
      have := (live_key_unique hl hl' hkk.symm).2
      have hxe : x ≤ e.val := by simpa using he'.2
      have hex : e'.val < x := by simpa using h1.2
      rw [this] at hxe
      exact absurd hex (not_lt.mpr hxe)
    have hstaleR : staleCnt (clearKeys L ks) [⟨⊥, R⟩] = 0 := by
      simp only [staleCnt, allEnts, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.append_nil]
      rw [List.countP_eq_zero]
      intro e he; simp [hRlive e he]
    have hstaleRem : staleCnt (clearKeys L ks) rem ≤ staleCnt L rem := by
      unfold staleCnt
      apply List.countP_mono_left
      intro e he h
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h ⊢
      intro hl
      apply h
      rw [isLive_clearKeys]
      refine ⟨hl, fun hk' => ?_⟩
      obtain ⟨e', he's, hkk⟩ := List.mem_map.mp hk'
      have h1 := List.mem_filter.mp he's
      rw [hacc] at h1
      obtain ⟨⟨b', hb', heb'⟩, hl'⟩ := mem_liveVals.mp h1.1
      have hide := (live_key_unique hl hl' hkk.symm).1
      -- `e` lies in `rem`, `e'` in `pre`: their ids must differ
      have hnd := hid
      unfold IdsNodup at hnd
      rw [hbs] at hnd
      simp only [allEnts, List.map_append, List.flatten_append] at hnd
      have hnd' := List.nodup_append.mp hnd
      exact hnd'.2.2 _ (List.mem_map.mpr ⟨e', (show e' ∈ allEnts pre from
        mem_allEnts.mpr ⟨b', hb', heb'⟩), rfl⟩) _ (List.mem_map.mpr ⟨e, he, rfl⟩) hide.symm
    have hpot' : pot T (clearKeys L ks) ⟨D.M, D.Bd, ⟨⊥, R⟩ :: rem⟩ ≤
        2 * staleCnt L rem + 2 * T * (1 + rem.length) +
          420 * ((R.length - D.M) + excess D.M rem) := by
      unfold pot
      simp only
      rw [show (⟨⊥, R⟩ :: rem : List (Block κ α)) = [⟨⊥, R⟩] ++ rem from rfl, staleCnt_append,
        excess_append, hstaleR]
      simp only [List.length_append, List.length_singleton, excess, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, zero_add]
      have : 1 + rem.length = rem.length + 1 := by omega
      rw [this]
      omega
    rw [hsc', hk]
    have e1 : T * (pre.length + 1) = T * pre.length + T := by ring
    have e2 : 2 * T * (1 + rem.length) = 2 * T + 2 * (T * rem.length) := by ring
    have e3 : 2 * T * (pre.length + rem.length) = 2 * (T * pre.length) + 2 * (T * rem.length) := by
      ring
    rw [e1]; rw [e2] at hpot'; rw [e3] at hpotD
    set a := T * pre.length
    set b := T * rem.length
    omega

/-- block-list potential (the part of `pot` that depends only on the blocks) -/
def bpot (L : Live κ α) (M : ℕ) (bs : List (Block κ α)) : ℕ :=
  2 * staleCnt L bs + 2 * T * bs.length + 420 * excess M bs

theorem pot_eq_bpot (L : Live κ α) (D : DStr κ α) : pot T L D = bpot T L D.M D.blocks := rfl

theorem bpot_append (L : Live κ α) (M : ℕ) (bs₁ bs₂ : List (Block κ α)) :
    bpot T L M (bs₁ ++ bs₂) = bpot T L M bs₁ + bpot T L M bs₂ := by
  unfold bpot; rw [staleCnt_append, excess_append, List.length_append]; ring

theorem bpot_cons (L : Live κ α) (M : ℕ) (b : Block κ α) (bs : List (Block κ α)) :
    bpot T L M (b :: bs) = bpot T L M [b] + bpot T L M bs := by
  rw [show b :: bs = [b] ++ bs from rfl, bpot_append]

theorem bpot_single (L : Live κ α) (M : ℕ) (b : Block κ α) :
    bpot T L M [b] = 2 * b.ents.countP (fun e => !decide (e.IsLive L)) + 2 * T +
      420 * (b.ents.length - M) := by
  simp [bpot, staleCnt, allEnts, excess]

/-- the halves of a median split of distinct values -/
theorem split_sizes {es : List (Entry κ α)} (hd : (es.map (·.val)).Nodup) (hlen : 0 < es.length) :
    (es.filter (fun e => decide (e.val <
        (selectC (es.map (·.val)) (es.length / 2)).1))).length = es.length / 2 := by
  have hk : es.length / 2 < (es.map (·.val)).length := by simp; omega
  have hkth := selectC_isKth _ hk
  have hle := cntLe_eq_cntLt_add_one hd hkth.1
  have h1 := hkth.2.1
  have h2 := hkth.2.2
  have : (es.filter (fun e => decide (e.val <
      (selectC (es.map (·.val)) (es.length / 2)).1))).length =
      cntLt (es.map (·.val)) (selectC (es.map (·.val)) (es.length / 2)).1 := by
    unfold cntLt; rw [← List.countP_eq_length_filter, List.countP_map]; rfl
  omega

/-- **Amortized cost of normalising a block** that holds at most `2M+2` entries whose live
values are distinct. -/
theorem fixBlock_amortized {L : Live κ α} {M : ℕ} {b : Block κ α} (hM : 1 ≤ M)
    (hsz : b.ents.length ≤ 2 * M + 2) (hd : ((liveOf L b.ents).map (·.val)).Nodup) :
    (fixBlock T L M b).2 + bpot T L M (fixBlock T L M b).1 ≤ bpot T L M [b] + 3 * T + 210 := by
  rw [bpot_single]
  have hst : b.ents.length = (liveOf L b.ents).length +
      b.ents.countP (fun e => !decide (e.IsLive L)) := by
    have := List.length_eq_countP_add_countP (l := b.ents) (fun e : Entry κ α => e.IsLive L)
    rw [this]; unfold liveOf; rw [List.countP_eq_length_filter]; congr 1
    apply List.countP_congr; intro x _; simp
  unfold fixBlock
  split_ifs with h1 h2 h3
  · -- no normalisation
    simp only [bpot_single]; omega
  · -- compaction: at most `M` live entries remain
    simp only [bpot_single]
    have hz : (liveOf L b.ents).countP (fun e => !decide (e.IsLive L)) = 0 := by
      rw [List.countP_eq_zero]; intro e he; simp [(mem_liveOf.mp he).2]
    simp only [hz]
    have : (liveOf L b.ents).length - M = 0 := by omega
    rw [this]
    omega
  · -- impossible for distinct values: the lower half is nonempty
    exfalso
    have hpos : 0 < (liveOf L b.ents).length := by omega
    have := split_sizes hd hpos
    rw [h3] at this
    simp at this
    omega
  · -- median split
    rw [bpot_cons, bpot_single, bpot_single]
    set le := liveOf L b.ents with hle
    have hpos : 0 < le.length := by omega
    have hlo := split_sizes hd hpos
    set μ := (selectC (le.map (·.val)) (le.length / 2)).1 with hμ
    have hsel := selectC_cost (le.map (·.val)) (k := le.length / 2) (by simp; omega)
    simp only [List.length_map] at hsel
    have hsum : (le.filter (fun e => decide (e.val < μ))).length +
        (le.filter (fun e => decide (μ ≤ e.val))).length = le.length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      have := List.length_eq_countP_add_countP (l := le) (fun e : Entry κ α => e.val < μ)
      rw [this]; congr 1; apply List.countP_congr; intro e _; simp
    have hz1 : (le.filter (fun e => decide (e.val < μ))).countP (fun e => !decide (e.IsLive L)) = 0 := by
      rw [List.countP_eq_zero]; intro e he
      simp [(mem_liveOf.mp (List.mem_filter.mp he).1).2]
    have hz2 : (le.filter (fun e => decide (μ ≤ e.val))).countP (fun e => !decide (e.IsLive L)) = 0 := by
      rw [List.countP_eq_zero]; intro e he
      simp [(mem_liveOf.mp (List.mem_filter.mp he).1).2]
    simp only [hz1, hz2]
    have hsel' : (selectC (le.map (·.val)) (le.length / 2)).2 ≤ 100 * le.length := hsel
    omega

/-- updating one key's live pointer to a fresh id creates at most one stale entry among
entries with distinct older ids -/
theorem staleCnt_update_le {L : Live κ α} {v : κ} {fresh : ℕ} {lam : α} {es : List (Entry κ α)}
    (hfr : ∀ x ∈ es, x.id < fresh) (hnd : (es.map (·.id)).Nodup) :
    es.countP (fun e => !decide (e.IsLive (Function.update L v (some (fresh, lam))))) ≤
      es.countP (fun e => !decide (e.IsLive L)) + 1 := by
  induction es with
  | nil => simp
  | cons a as ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have ih' := ih (fun x hx => hfr x (List.mem_cons_of_mem _ hx)) hnd.2
    have ha := isLive_update_of_fresh (L := L) (v := v) (lam := lam) (hfr a List.mem_cons_self)
    simp only [List.countP_cons]
    by_cases hl : a.IsLive L
    · by_cases hk : a.key = v
      · -- `a` is the old live entry of `v`: no other entry of `as` is live with key `v`
        have hnone : ∀ x ∈ as, x.IsLive L → x.key ≠ v := by
          intro x hx hxl hxk
          have := (live_key_unique hl hxl (hk.trans hxk.symm)).1
          exact hnd.1 (List.mem_map.mpr ⟨x, hx, this.symm⟩)
        have heq : as.countP (fun e => !decide (e.IsLive (Function.update L v (some (fresh, lam))))) =
            as.countP (fun e => !decide (e.IsLive L)) := by
          apply List.countP_congr
          intro x hx
          have hx' := isLive_update_of_fresh (L := L) (v := v) (lam := lam)
            (hfr x (List.mem_cons_of_mem _ hx))
          by_cases hxl : x.IsLive L
          · have h1 : x.IsLive (Function.update L v (some (fresh, lam))) :=
              hx'.mpr ⟨hxl, hnone x hx hxl⟩
            simp [hxl, h1]
          · have h1 : ¬ x.IsLive (Function.update L v (some (fresh, lam))) :=
              fun h => hxl (hx'.mp h).1
            simp [hxl, h1]
        rw [heq]
        have : ¬ a.IsLive (Function.update L v (some (fresh, lam))) := fun h => (ha.mp h).2 hk
        simp [hl, this]
      · have : a.IsLive (Function.update L v (some (fresh, lam))) := ha.mpr ⟨hl, hk⟩
        simp only [hl, this, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        omega
    · have : ¬ a.IsLive (Function.update L v (some (fresh, lam))) := fun h => hl (ha.mp h).1
      simp only [hl, this, decide_false, Bool.not_false, ↓reduceIte]
      omega

/-- **Amortized cost of `addTo`**: the owning block receives the entry and is normalised. -/
theorem addTo_amortized {L : Live κ α} {M : ℕ} {lam : α} {e : Entry κ α} (hM : 1 ≤ M)
    (he : e.IsLive L) :
    ∀ {bs : List (Block κ α)}, bs ≠ [] → (∀ b ∈ bs, b.ents.length ≤ 2 * M + 1) →
      (∀ b ∈ bs, ((liveOf L (e :: b.ents)).map (·.val)).Nodup) →
      (addTo T L M lam e bs).2 + bpot T L M (addTo T L M lam e bs).1 ≤
        bpot T L M bs + 3 * T + 630
  | [], h, _, _ => absurd rfl h
  | [b], _, hsz, hd => by
      simp only [addTo]
      have hsz' : (e :: b.ents).length ≤ 2 * M + 2 := by
        simp; have := hsz b (List.mem_singleton_self _); omega
      have := fixBlock_amortized T (b := ⟨b.sep, e :: b.ents⟩) hM hsz' (hd b (List.mem_singleton_self _))
      rw [bpot_single] at this ⊢
      simp only [List.countP_cons, List.length_cons, he, decide_true, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, add_zero] at this
      omega
  | b :: b' :: bs, _, hsz, hd => by
      simp only [addTo]
      split_ifs with hsep
      · have ih := addTo_amortized (lam := lam) hM he (List.cons_ne_nil b' bs)
          (fun c hc => hsz c (List.mem_cons_of_mem _ hc))
          (fun c hc => hd c (List.mem_cons_of_mem _ hc))
        rw [bpot_cons T L M b (addTo T L M lam e (b' :: bs)).1, bpot_cons T L M b (b' :: bs)]
        omega
      · have hsz' : (e :: b.ents).length ≤ 2 * M + 2 := by
          simp; have := hsz b List.mem_cons_self; omega
        have := fixBlock_amortized T (b := ⟨b.sep, e :: b.ents⟩) hM hsz' (hd b List.mem_cons_self)
        rw [bpot_append, bpot_cons T L M b (b' :: bs)]
        rw [bpot_single T L M ⟨b.sep, e :: b.ents⟩] at this
        rw [bpot_single T L M b]
        simp only [List.countP_cons, List.length_cons, he, decide_true, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte, add_zero] at this
        omega

theorem keyInj_update {L : Live κ α} {kof : α → κ} {v : κ} {fresh : ℕ} {lam : α}
    (hK : KeyInj L kof) (hkv : kof lam = v) :
    KeyInj (Function.update L v (some (fresh, lam))) kof := by
  intro y i a h
  by_cases hy : y = v
  · subst hy; simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact hkv
  · rw [Function.update_of_ne hy] at h; exact hK y i a h

/-- **Amortized cost of `insert`**: `cost + Φ(after) ≤ Φ(before) + 4T + 635`.  (The at most one
entry that becomes stale in ANOTHER structure raises that structure's potential by `2`.) -/
theorem insert_amortized {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α}
    {kof : α → κ} (hwf : WF L D) (hfr : FreshOK fresh D) (hid : IdsNodup D)
    (hK : KeyInj L kof) (hkv : kof lam = v) (hsz : BlockSizeOK D) (hM : 1 ≤ D.M) :
    (insert T L fresh D v lam).2.2.2 +
        pot T (insert T L fresh D v lam).1 (insert T L fresh D v lam).2.2.1 ≤
      pot T L D + (4 * T + 635) := by
  unfold insert
  by_cases hskip : skipIns L v lam = true
  · rw [ite_eq_left hskip]; dsimp only; omega
  · rw [ite_eq_right hskip]
    dsimp only
    set L' := Function.update L v (some (fresh, lam)) with hL'
    set e : Entry κ α := ⟨fresh, v, lam⟩ with he
    have heL : e.IsLive L' := by simp [Entry.IsLive, hL', he]
    have hK' : KeyInj L' kof := keyInj_update hK hkv
    have hdist : ∀ b ∈ D.blocks, ((liveOf L' (e :: b.ents)).map (·.val)).Nodup := by
      intro b hb
      have hids : ((e :: b.ents).map (·.id)).Nodup := by
        rw [List.map_cons, List.nodup_cons]
        have hsub : (b.ents.map (·.id)).Sublist ((allEnts D.blocks).map (·.id)) := by
          apply List.Sublist.map
          unfold allEnts
          exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨b, hb, rfl⟩)
        refine ⟨?_, hsub.nodup hid⟩
        intro hmem
        obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmem
        have := hfr x (mem_allEnts.mpr ⟨b, hb, hx⟩)
        simp only [he] at hxid; omega
      have hsub2 : ((liveOf L' (e :: b.ents)).map (·.id)).Sublist ((e :: b.ents).map (·.id)) :=
        List.Sublist.map _ List.filter_sublist
      exact nodup_vals_of_live hK' (hsub2.nodup hids) (fun x hx => (mem_liveOf.mp hx).2)
    have hA := addTo_amortized T (L := L') (M := D.M) (lam := lam) (e := e) hM heL hwf.1 hsz hdist
    have hst : staleCnt L' D.blocks ≤ staleCnt L D.blocks + 1 := by
      unfold staleCnt
      exact staleCnt_update_le (fun x hx => hfr x hx) hid
    have hb : bpot T L' D.M D.blocks ≤ bpot T L D.M D.blocks + 2 := by
      unfold bpot; omega
    rw [pot_eq_bpot]
    simp only at hA ⊢
    rw [pot_eq_bpot]
    omega

/-! ### Grouping: sizes and counts -/

theorem groupAux_block_le {g c : ℕ} :
    ∀ {cur : Option (Block κ α)} {bs : List (Block κ α)},
      (∀ b ∈ bs, b.ents.length ≤ c) → (∀ c0, cur = some c0 → c0.ents.length < g) →
      ∀ b ∈ groupAux g cur bs, b.ents.length ≤ g + c
  | none, [], _, _, b, hb => by simp [groupAux] at hb
  | some c0, [], _, hcur, b, hb => by
      simp only [groupAux, List.mem_singleton] at hb; subst hb
      have := hcur _ rfl; omega
  | none, b0 :: bs, hbs, _, b, hb => by
      simp only [groupAux] at hb
      split_ifs at hb with h
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact le_trans (hbs _ List.mem_cons_self) (Nat.le_add_left _ _)
        · exact groupAux_block_le (cur := none) (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb'))
            (by simp) b hb
      · exact groupAux_block_le (cur := some b0) (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb'))
          (by intro c0 h0; simp only [Option.some.injEq] at h0; subst h0; omega) b hb
  | some c0, b0 :: bs, hbs, hcur, b, hb => by
      simp only [groupAux] at hb
      have hc0 := hcur c0 rfl
      have hb0 := hbs b0 List.mem_cons_self
      split_ifs at hb with h
      · rcases List.mem_cons.mp hb with rfl | hb
        · simp only [List.length_append]; omega
        · exact groupAux_block_le (cur := none) (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb'))
            (by simp) b hb
      · exact groupAux_block_le (cur := some ⟨c0.sep, c0.ents ++ b0.ents⟩)
          (fun b' hb' => hbs b' (List.mem_cons_of_mem _ hb'))
          (by intro c1 h1; simp only [Option.some.injEq] at h1; subst h1; simp at h ⊢; omega) b hb

/-- at most `E/g + 1` groups are formed from `E` entries -/
theorem groupAux_count {g : ℕ} (hg : 1 ≤ g) :
    ∀ {cur : Option (Block κ α)} {bs : List (Block κ α)},
      (∀ c0, cur = some c0 → c0.ents.length < g) →
      g * (groupAux g cur bs).length ≤
        (allEnts bs).length + (match cur with | none => 0 | some c0 => c0.ents.length) + g
  | none, [], _ => by simp [groupAux]
  | some c0, [], _ => by simp [groupAux]
  | none, b0 :: bs, _ => by
      simp only [groupAux]
      split_ifs with h
      · have ih := groupAux_count hg (cur := none) (bs := bs) (by simp)
        simp only [List.length_cons, allEnts, List.map_cons, List.flatten_cons,
          List.length_append] at ih ⊢
        rw [Nat.mul_succ]; omega
      · have ih := groupAux_count hg (cur := some b0) (bs := bs)
          (by intro c0 h0; simp only [Option.some.injEq] at h0; subst h0; omega)
        simp only [allEnts, List.map_cons, List.flatten_cons, List.length_append] at ih ⊢
        omega
  | some c0, b0 :: bs, hcur => by
      simp only [groupAux]
      split_ifs with h
      · have ih := groupAux_count hg (cur := none) (bs := bs) (by simp)
        simp only [List.length_cons, allEnts, List.map_cons, List.flatten_cons,
          List.length_append] at ih h ⊢
        rw [Nat.mul_succ]; omega
      · have ih := groupAux_count hg (cur := some ⟨c0.sep, c0.ents ++ b0.ents⟩) (bs := bs)
          (by intro c1 h1; simp only [Option.some.injEq] at h1; subst h1; simp at h ⊢; omega)
        simp only [allEnts, List.map_cons, List.flatten_cons, List.length_append] at ih h ⊢
        omega

/-- grouping keeps every entry (so stale counts are unchanged) -/
theorem staleCnt_groupAux {L : Live κ α} {g : ℕ} :
    ∀ {cur : Option (Block κ α)} {bs : List (Block κ α)},
      staleCnt L (groupAux g cur bs) =
        (match cur with | none => 0 | some c0 => c0.ents.countP (fun e => !decide (e.IsLive L))) +
          staleCnt L bs
  | none, [] => by simp [groupAux, staleCnt, allEnts]
  | some c0, [] => by simp [groupAux, staleCnt, allEnts]
  | none, b0 :: bs => by
      simp only [groupAux]
      split_ifs
      · rw [staleCnt_cons, staleCnt_groupAux, staleCnt_cons]; simp
      · rw [staleCnt_groupAux, staleCnt_cons]; simp
  | some c0, b0 :: bs => by
      simp only [groupAux]
      split_ifs
      · rw [staleCnt_cons, staleCnt_groupAux, staleCnt_cons]; simp [List.countP_append]; ring
      · rw [staleCnt_groupAux, staleCnt_cons]; simp [List.countP_append]; ring

/-- **Amortized cost of `merge`**: `cost + Φ(merged) ≤ Φ(D) + Φ(D') + (3T + 420)·#groups + 2T + 2`
where the number of groups is at most `E(D')/(M/3) + 1` (`groupAux_count`). -/
theorem merge_amortized {L : Live κ α} {D D' : DStr κ α} (hne : D.blocks ≠ []) (hT : 1 ≤ T)
    (hsz' : BlockSizeOK D') (hMM : D.M / 3 + (2 * D'.M + 1) ≤ D.M + 1) :
    (merge T D D').2 + pot T L (merge T D D').1 ≤
      pot T L D + pot T L D' +
        (3 * T + 420) * (groupAux (D.M / 3) none D'.blocks).length + 2 * T + 2 := by
  rcases hD : D.blocks with _ | ⟨f, rest⟩
  · exact absurd hD hne
  have hmD : merge T D D' = ({ D with blocks := groupAux (D.M / 3) none D'.blocks ++
        (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
          then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) },
      D'.blocks.length + T * ((groupAux (D.M / 3) none D'.blocks).length + 2) + 2) := by
    unfold merge; rw [hD]
  rw [hmD]
  dsimp only
  set gs := groupAux (D.M / 3) none D'.blocks with hgs
  -- potential of the groups
  have hstale : staleCnt L gs = staleCnt L D'.blocks := by
    rw [hgs, staleCnt_groupAux]; simp
  have hexc : excess D.M gs ≤ gs.length := by
    have hbl := groupAux_block_le (g := D.M / 3) (c := 2 * D'.M + 1) (cur := none)
      (bs := D'.blocks) hsz' (by simp)
    rw [← hgs] at hbl
    unfold excess
    have : ∀ b ∈ gs, b.ents.length - D.M ≤ 1 := fun b hb => by have := hbl b hb; omega
    have h2 := sum_map_le_mul_sum gs (fun b => b.ents.length - D.M) (fun _ => 1) 1
      (fun x hx => by simpa using this x hx)
    simpa using h2
  have hgs_pot : bpot T L D.M gs ≤ 2 * staleCnt L D'.blocks + 2 * T * gs.length + 420 * gs.length := by
    unfold bpot; rw [hstale]; omega
  -- potential of the tail
  have htail : bpot T L D.M (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
      then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) ≤ pot T L D := by
    rw [pot_eq_bpot, hD]
    split_ifs
    · rw [bpot_cons, bpot_cons T L D.M f rest, bpot_single, bpot_single]
    · rw [bpot_cons T L D.M f rest]; omega
  have hD' : 2 * staleCnt L D'.blocks + D'.blocks.length ≤ pot T L D' := by
    unfold pot
    have : D'.blocks.length ≤ T * D'.blocks.length := Nat.le_mul_of_pos_left _ hT
    nlinarith
  rw [pot_eq_bpot]
  simp only
  rw [bpot_append]
  have e1 : T * (gs.length + 2) = T * gs.length + 2 * T := by ring
  have e2 : (3 * T + 420) * gs.length = 3 * (T * gs.length) + 420 * gs.length := by ring
  have e3 : 2 * T * gs.length = 2 * (T * gs.length) := by ring
  rw [e1, e2]; rw [e3] at hgs_pot
  set a := T * gs.length
  omega

/-- **Amortized cost of `deleteKeys`**: `cost + Φ(after) ≤ Φ(before) + 3|ks| + 1` for a structure
whose live entries have distinct ids (each deleted key makes at most one entry stale). -/
theorem deleteKeys_amortized {L : Live κ α} {D : DStr κ α} {ks : List κ} (hid : IdsNodup D) :
    (deleteKeys L ks).2 + pot T (deleteKeys L ks).1 D ≤ pot T L D + 3 * ks.length + 1 := by
  simp only [deleteKeys]
  -- entries becoming stale are live entries with a deleted key: at most one per key
  have key : ∀ (ks : List κ), staleCnt (clearKeys L ks) D.blocks ≤ staleCnt L D.blocks + ks.length := by
    intro ks
    induction ks with
    | nil =>
      unfold staleCnt; apply le_of_eq; congr 1
    | cons k ks ih =>
      have hclr : clearKeys L (k :: ks) = clearKeys (clearKeys L ks) [k] := by
        funext y; by_cases hy : y = k <;> simp [clearKeys, hy]
      rw [hclr]
      have step : staleCnt (clearKeys (clearKeys L ks) [k]) D.blocks ≤
          staleCnt (clearKeys L ks) D.blocks + 1 := by
        unfold staleCnt
        have hnd := hid
        unfold IdsNodup at hnd
        generalize hes : allEnts D.blocks = es at hnd ⊢
        clear hes
        induction es with
        | nil => simp
        | cons a as ih2 =>
          rw [List.map_cons, List.nodup_cons] at hnd
          have ih2' := ih2 hnd.2
          simp only [List.countP_cons]
          by_cases hl : a.IsLive (clearKeys L ks)
          · by_cases hk : a.key = k
            · have hnone : ∀ x ∈ as, x.IsLive (clearKeys L ks) → x.key ≠ k := by
                intro x hx hxl hxk
                have := (live_key_unique hl hxl (hk.trans hxk.symm)).1
                exact hnd.1 (List.mem_map.mpr ⟨x, hx, this.symm⟩)
              have heq : as.countP (fun e => !decide (e.IsLive (clearKeys (clearKeys L ks) [k]))) =
                  as.countP (fun e => !decide (e.IsLive (clearKeys L ks))) := by
                apply List.countP_congr
                intro x hx
                by_cases hxl : x.IsLive (clearKeys L ks)
                · have : x.IsLive (clearKeys (clearKeys L ks) [k]) :=
                    isLive_clearKeys.mpr ⟨hxl, by simpa using hnone x hx hxl⟩
                  simp [hxl, this]
                · have : ¬ x.IsLive (clearKeys (clearKeys L ks) [k]) :=
                    fun h => hxl (isLive_clearKeys.mp h).1
                  simp [hxl, this]
              rw [heq]
              have : ¬ a.IsLive (clearKeys (clearKeys L ks) [k]) := fun h =>
                (isLive_clearKeys.mp h).2 (by simp [hk])
              simp [hl, this]
            · have : a.IsLive (clearKeys (clearKeys L ks) [k]) :=
                isLive_clearKeys.mpr ⟨hl, by simpa using hk⟩
              simp only [hl, this, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              omega
          · have : ¬ a.IsLive (clearKeys (clearKeys L ks) [k]) := fun h => hl (isLive_clearKeys.mp h).1
            simp only [hl, this, decide_false, Bool.not_false, ↓reduceIte]
            omega
      simp only [List.length_cons]
      omega
  have := key ks
  unfold pot
  omega

/-! ## Preservation of the auxiliary invariants (fresh ids, distinct ids, block sizes) -/

section SubpermHelpers
variable {β γ : Type*}

theorem subperm_map' (f : β → γ) {l₁ l₂ : List β} (h : l₁.Subperm l₂) :
    (l₁.map f).Subperm (l₂.map f) := by
  obtain ⟨l, hp, hs⟩ := h
  exact ⟨l.map f, hp.map f, hs.map f⟩

theorem subperm_nodup' {l₁ l₂ : List β} (h : l₁.Subperm l₂) (hn : l₂.Nodup) : l₁.Nodup := by
  obtain ⟨l, hp, hs⟩ := h
  exact hp.nodup_iff.mp (hs.nodup hn)

theorem subperm_append' {l₁ l₂ r₁ r₂ : List β} (h₁ : l₁.Subperm l₂) (h₂ : r₁.Subperm r₂) :
    (l₁ ++ r₁).Subperm (l₂ ++ r₂) := by
  obtain ⟨l, hl, hls⟩ := h₁
  obtain ⟨r, hr, hrs⟩ := h₂
  exact ⟨l ++ r, hl.append hr, hls.append hrs⟩

theorem subperm_refl' (l : List β) : l.Subperm l := ⟨l, List.Perm.refl _, List.Sublist.refl _⟩

end SubpermHelpers

theorem allEnts_fixBlock_subperm {L : Live κ α} {M : ℕ} {b : Block κ α} :
    (allEnts (fixBlock T L M b).1).Subperm b.ents := by
  unfold fixBlock
  split_ifs with h1 h2 h3
  · simp only [allEnts, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    exact subperm_refl' _
  · simp only [allEnts, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    exact (List.filter_sublist).subperm
  · simp only [allEnts, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    exact (List.filter_sublist).subperm
  · simp only [allEnts, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    set le := liveOf L b.ents
    set μ := (selectC (le.map (·.val)) (le.length / 2)).1
    have hperm : (le.filter (fun e => decide (e.val < μ)) ++ le.filter (fun e => decide (μ ≤ e.val))).Perm le := by
      have := List.filter_append_perm (fun e : Entry κ α => decide (e.val < μ)) le
      refine List.Perm.trans ?_ this
      apply List.Perm.append_left
      apply List.Perm.of_eq
      apply List.filter_congr
      intro x _
      by_cases h : x.val < μ
      · simp [h, not_le.mpr h]
      · simp [h, not_lt.mp h]
    exact hperm.subperm.trans (List.filter_sublist).subperm

theorem allEnts_addTo_subperm {L : Live κ α} {M : ℕ} {lam : α} {e : Entry κ α} :
    ∀ {bs : List (Block κ α)}, (allEnts (addTo T L M lam e bs).1).Subperm (e :: allEnts bs)
  | [] => by simp [addTo, allEnts]
  | [b] => by
      simp only [addTo]
      have := allEnts_fixBlock_subperm T (L := L) (M := M) (b := ⟨b.sep, e :: b.ents⟩)
      simpa [allEnts] using this
  | b :: b' :: bs => by
      simp only [addTo]
      split_ifs
      · have ih := allEnts_addTo_subperm (L := L) (M := M) (lam := lam) (e := e) (bs := b' :: bs)
        simp only [allEnts, List.map_cons, List.flatten_cons] at ih ⊢
        -- `b.ents ++ X <+~ e :: b.ents ++ Y` from `X <+~ e :: Y`
        have := subperm_append' (subperm_refl' b.ents) ih
        refine this.trans ?_
        exact (List.perm_middle).subperm
      · have hf := allEnts_fixBlock_subperm T (L := L) (M := M) (b := ⟨b.sep, e :: b.ents⟩)
        simp only [allEnts, List.map_append, List.flatten_append, List.map_cons,
          List.flatten_cons] at hf ⊢
        have := subperm_append' hf (subperm_refl' ((b'.ents ++ (List.map (fun x => x.ents) bs).flatten)))
        simpa using this

theorem insert_idsNodup {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α}
    (hfr : FreshOK fresh D) (hid : IdsNodup D) :
    IdsNodup (insert T L fresh D v lam).2.2.1 := by
  unfold insert
  split_ifs
  · exact hid
  · unfold IdsNodup
    simp only
    have hsp := allEnts_addTo_subperm T (L := Function.update L v (some (fresh, lam))) (M := D.M)
      (lam := lam) (e := ⟨fresh, v, lam⟩) (bs := D.blocks)
    have hnd : ((⟨fresh, v, lam⟩ :: allEnts D.blocks : List (Entry κ α)).map (·.id)).Nodup := by
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, hid⟩
      intro hm
      obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hm
      have := hfr x hx
      simp only at hxid; omega
    exact subperm_nodup' (subperm_map' _ hsp) hnd

/-- blocks produced by `fixBlock` from a block with distinct live values have at most `2M+1`
entries -/
theorem fixBlock_size {L : Live κ α} {M : ℕ} {b : Block κ α} (hM : 1 ≤ M)
    (hsz : b.ents.length ≤ 2 * M + 2) (hd : ((liveOf L b.ents).map (·.val)).Nodup) :
    ∀ c ∈ (fixBlock T L M b).1, c.ents.length ≤ 2 * M + 1 := by
  unfold fixBlock
  split_ifs with h1 h2 h3
  · simp only [List.mem_singleton]; rintro c rfl; exact h1
  · simp only [List.mem_singleton]; rintro c rfl; simp; omega
  · exfalso
    have hpos : 0 < (liveOf L b.ents).length := by omega
    have := split_sizes hd hpos
    rw [h3] at this; simp at this; omega
  · have hpos : 0 < (liveOf L b.ents).length := by omega
    have hlo := split_sizes hd hpos
    set le := liveOf L b.ents with hle
    set μ := (selectC (le.map (·.val)) (le.length / 2)).1
    have hsum : (le.filter (fun e => decide (e.val < μ))).length +
        (le.filter (fun e => decide (μ ≤ e.val))).length = le.length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      have := List.length_eq_countP_add_countP (l := le) (fun e : Entry κ α => e.val < μ)
      rw [this]; congr 1; apply List.countP_congr; intro e _; simp
    have hle' : le.length ≤ b.ents.length := List.length_filter_le _ _
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rintro c (rfl | rfl) <;> simp only <;> omega

theorem addTo_size {L : Live κ α} {M : ℕ} {lam : α} {e : Entry κ α} (hM : 1 ≤ M) :
    ∀ {bs : List (Block κ α)}, (∀ b ∈ bs, b.ents.length ≤ 2 * M + 1) →
      (∀ b ∈ bs, ((liveOf L (e :: b.ents)).map (·.val)).Nodup) →
      ∀ c ∈ (addTo T L M lam e bs).1, c.ents.length ≤ 2 * M + 1
  | [], _, _ => by simp [addTo]
  | [b], hsz, hd => by
      simp only [addTo]
      exact fixBlock_size T (b := ⟨b.sep, e :: b.ents⟩) hM
        (by simp; have := hsz b (List.mem_singleton_self _); omega) (hd b (List.mem_singleton_self _))
  | b :: b' :: bs, hsz, hd => by
      simp only [addTo]
      split_ifs
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hsz _ List.mem_cons_self
        · exact addTo_size hM (fun c hc => hsz c (List.mem_cons_of_mem _ hc))
            (fun c hc => hd c (List.mem_cons_of_mem _ hc)) c hc
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact fixBlock_size T (b := ⟨b.sep, e :: b.ents⟩) hM
            (by simp; have := hsz b List.mem_cons_self; omega) (hd b List.mem_cons_self) c hc
        · exact hsz c (List.mem_cons_of_mem _ hc)

/-- the auxiliary invariants after `insert` -/
theorem insert_aux {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α} {kof : α → κ}
    (hfr : FreshOK fresh D) (hid : IdsNodup D) (hK : KeyInj L kof) (hkv : kof lam = v)
    (hsz : BlockSizeOK D) (hM : 1 ≤ D.M) :
    IdsNodup (insert T L fresh D v lam).2.2.1 ∧ BlockSizeOK (insert T L fresh D v lam).2.2.1 ∧
      KeyInj (insert T L fresh D v lam).1 kof := by
  refine ⟨insert_idsNodup T hfr hid, ?_, ?_⟩
  · unfold insert
    split_ifs
    · exact hsz
    · unfold BlockSizeOK
      simp only
      set L' := Function.update L v (some (fresh, lam))
      have hK' : KeyInj L' kof := keyInj_update hK hkv
      apply addTo_size T hM hsz
      intro b hb
      have hids : (((⟨fresh, v, lam⟩ : Entry κ α) :: b.ents).map (·.id)).Nodup := by
        rw [List.map_cons, List.nodup_cons]
        have hsub : (b.ents.map (·.id)).Sublist ((allEnts D.blocks).map (·.id)) := by
          apply List.Sublist.map
          unfold allEnts
          exact List.sublist_flatten_of_mem (List.mem_map.mpr ⟨b, hb, rfl⟩)
        refine ⟨?_, hsub.nodup hid⟩
        intro hmem
        obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hmem
        have := hfr x (mem_allEnts.mpr ⟨b, hb, hx⟩)
        simp only at hxid; omega
      have hsub2 : ((liveOf L' ((⟨fresh, v, lam⟩ : Entry κ α) :: b.ents)).map (·.id)).Sublist
          ((((⟨fresh, v, lam⟩ : Entry κ α)) :: b.ents).map (·.id)) :=
        List.Sublist.map _ List.filter_sublist
      exact nodup_vals_of_live hK' (hsub2.nodup hids) (fun x hx => (mem_liveOf.mp hx).2)
  · unfold insert
    split_ifs
    · exact hK
    · exact keyInj_update hK hkv

/-- the auxiliary invariants after `pull` (for every other structure the live map only loses
keys, so `KeyInj` is kept as well) -/
theorem pull_aux {L : Live κ α} {D : DStr κ α} {kof : α → κ} {fresh : ℕ} (hwf : WF L D)
    (hK : KeyInj L kof) (hid : IdsNodup D) (hM : 1 ≤ D.M) (hsz : BlockSizeOK D)
    (hfr : FreshOK fresh D) :
    IdsNodup (pull T L D).2.2.2.1 ∧ BlockSizeOK (pull T L D).2.2.2.1 ∧
      FreshOK fresh (pull T L D).2.2.2.1 ∧ KeyInj (pull T L D).2.2.1 kof := by
  have hpost := pull_post T hwf hK hid hM
  unfold pull at hpost ⊢
  obtain ⟨pre, hbs, hacc, -, -, hrem, hpre⟩ := collect_spec L D.M D.blocks []
  simp only [List.nil_append] at hacc
  set acc := (collect L D.M [] D.blocks).1 with hacc_def
  set rem := (collect L D.M [] D.blocks).2.1 with hrem_def
  have hKc : ∀ ks : List κ, KeyInj (clearKeys L ks) kof := by
    intro ks y i a h
    unfold clearKeys at h
    split_ifs at h
    exact hK y i a h
  have hacc_le : acc.length ≤ D.M + (2 * D.M + 1) :=
    collect_length_le L D.M (2 * D.M + 1) D.blocks [] (by simp) hsz
  by_cases hsmall : acc.length ≤ D.M
  · rw [ite_eq_left hsmall] at hpost ⊢
    dsimp only
    refine ⟨by simp [IdsNodup, allEnts], ?_, ?_, hKc _⟩
    · intro b hb; simp at hb; rw [hb]; simp
    · intro x hx; simp [allEnts] at hx
  · rw [ite_eq_right hsmall] at hpost ⊢
    dsimp only at hpost ⊢
    have hM' : D.M < acc.length := by omega
    set x := (selectC (acc.map (·.val)) D.M).1 with hx
    have hkth : IsKth (acc.map (·.val)) D.M x := selectC_isKth _ (by simpa using hM')
    have hacc_nodup : (acc.map (·.id)).Nodup := by
      rw [hacc]
      have hsplit : (allEnts D.blocks).map (·.id) =
          (allEnts pre).map (·.id) ++ (allEnts rem).map (·.id) := by
        rw [hbs]; simp [allEnts]
      have hid' := hid
      unfold IdsNodup at hid'
      rw [hsplit] at hid'
      have h2 : ((allEnts pre).map (·.id)).Nodup := (List.nodup_append.mp hid').1
      exact ((liveVals_sublist_allEnts L pre).map _).nodup h2
    have hvals : (acc.map (·.val)).Nodup := by
      refine nodup_vals_of_live hK hacc_nodup (fun e he => ?_)
      rw [hacc] at he
      exact (mem_liveVals.mp he).2
    have hcnt : (acc.filter (fun e => decide (e.val < x))).length = D.M := by
      have h1 := hkth.2.1
      have h2 := hkth.2.2
      have hle := cntLe_eq_cntLt_add_one hvals hkth.1
      have : (acc.filter (fun e => decide (e.val < x))).length = cntLt (acc.map (·.val)) x := by
        unfold cntLt; rw [← List.countP_eq_length_filter, List.countP_map]; rfl
      omega
    -- the new entries are a sub-permutation of the old ones
    have hsp : (allEnts (⟨⊥, acc.filter (fun e => decide (x ≤ e.val))⟩ :: rem)).Sublist
        (allEnts D.blocks) := by
      rw [hbs]
      simp only [allEnts, List.map_cons, List.flatten_cons, List.map_append, List.flatten_append]
      apply List.Sublist.append _ (List.Sublist.refl _)
      rw [hacc]
      exact List.filter_sublist.trans (liveVals_sublist_allEnts L pre)
    refine ⟨(hsp.map _).nodup hid, ?_, fun y hy => hfr y (hsp.subset hy), hKc _⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only
      have hSR : (acc.filter (fun e => decide (e.val < x))).length +
          (acc.filter (fun e => decide (x ≤ e.val))).length = acc.length := by
        rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
        have := List.length_eq_countP_add_countP (l := acc) (fun e : Entry κ α => e.val < x)
        rw [this]; congr 1; apply List.countP_congr; intro e _; simp
      omega
    · exact hsz b (by rw [hbs]; exact List.mem_append_right _ hb)

/-- the auxiliary invariants after `merge` (the two structures' ids must be disjoint) -/
theorem merge_aux {D D' : DStr κ α} {fresh : ℕ} (hne : D.blocks ≠ []) (hid : IdsNodup D)
    (hid' : IdsNodup D') (hdisj : ∀ x ∈ allEnts D.blocks, ∀ y ∈ allEnts D'.blocks, x.id ≠ y.id)
    (hsz : BlockSizeOK D) (hsz' : BlockSizeOK D') (hMM : D.M / 3 + (2 * D'.M + 1) ≤ D.M + 1)
    (hfr : FreshOK fresh D) (hfr' : FreshOK fresh D') :
    IdsNodup (merge T D D').1 ∧ BlockSizeOK (merge T D D').1 ∧ FreshOK fresh (merge T D D').1 := by
  rcases hD : D.blocks with _ | ⟨f, rest⟩
  · exact absurd hD hne
  have hmD : (merge T D D').1 = { D with blocks := groupAux (D.M / 3) none D'.blocks ++
        (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
          then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) } := by
    unfold merge; rw [hD]
  rw [hmD]
  set gs := groupAux (D.M / 3) none D'.blocks with hgs
  have hgsE : ∀ x, x ∈ allEnts gs ↔ x ∈ allEnts D'.blocks := by
    intro x; rw [hgs, mem_allEnts_groupAux]; simp
  -- ids of the groups form a permutation of those of `D'`
  have hgsperm : (allEnts gs).Perm (allEnts D'.blocks) := by
    have key : ∀ (cur : Option (Block κ α)) (bs : List (Block κ α)),
        (allEnts (groupAux (D.M / 3) cur bs)).Perm
          ((match cur with | none => [] | some c0 => c0.ents) ++ allEnts bs) := by
      intro cur bs
      induction bs generalizing cur with
      | nil => cases cur <;> simp [groupAux, allEnts]
      | cons b0 bs ih =>
        cases cur with
        | none =>
          simp only [groupAux]
          split_ifs
          · have := ih none
            simp only [allEnts, List.map_cons, List.flatten_cons] at this ⊢
            simpa using List.Perm.append_left b0.ents this
          · have := ih (some b0)
            simpa [allEnts] using this
        | some c0 =>
          simp only [groupAux]
          split_ifs
          · have := ih none
            simp only [allEnts, List.map_cons, List.flatten_cons] at this ⊢
            simpa [List.append_assoc] using List.Perm.append_left (c0.ents ++ b0.ents) this
          · have := ih (some ⟨c0.sep, c0.ents ++ b0.ents⟩)
            simpa [allEnts, List.append_assoc] using this
    simpa using key none D'.blocks
  have htailE : ∀ x, x ∈ allEnts (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
      then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest) → x ∈ allEnts D.blocks := by
    intro x hx
    rw [hD]
    split_ifs at hx
    · simpa [allEnts] using hx
    · simp only [allEnts, List.map_cons, List.flatten_cons, List.mem_append] at hx ⊢
      exact Or.inr hx
  refine ⟨?_, ?_, ?_⟩
  · unfold IdsNodup
    simp only
    rw [allEnts, List.map_append, List.flatten_append, List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact (hgsperm.map _).nodup_iff.mpr hid'
    · -- the tail is `D.blocks` up to the re-keyed or dropped first block
      have hsub : ((if ltSep D'.Bd (nextSep rest (D.Bd : WithBot α))
          then ⟨(D'.Bd : WithBot α), f.ents⟩ :: rest else rest).map (·.ents)).flatten.Sublist
          (allEnts D.blocks) := by
        rw [hD]
        split_ifs
        · simp [allEnts]
        · simp only [allEnts, List.map_cons, List.flatten_cons]
          exact List.sublist_append_right _ _
      exact (hsub.map _).nodup hid
    · intro a ha b hb hab
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
      have hx' := (hgsE x).mp hx
      have hy' := htailE y hy
      exact hdisj y hy' x hx' hab.symm
  · intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · have := groupAux_block_le (g := D.M / 3) (c := 2 * D'.M + 1) (cur := none)
        (bs := D'.blocks) hsz' (by simp) b hb
      simp only; omega
    · have hbD : b ∈ D.blocks ∨ b.ents = f.ents := by
        rw [hD]
        split_ifs at hb
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact Or.inr rfl
          · exact Or.inl (List.mem_cons_of_mem _ hb)
        · exact Or.inl (List.mem_cons_of_mem _ hb)
      rcases hbD with hbD | hbD
      · exact hsz b hbD
      · rw [hbD]; exact hsz f (by rw [hD]; exact List.mem_cons_self)
  · intro x hx
    rw [allEnts, List.map_append, List.flatten_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hfr' x ((hgsE x).mp hx)
    · exact hfr x (htailE x hx)

/-! ## Families of structures sharing one live map (the BMSSP recursion stack)

In BMSSP there is one structure per active call; all of them share the global live map `L` and
the id counter.  The family potential is the sum of the `pot`s.  The lemmas below bound the change
of the stale count of the OTHER structures, whose blocks are concatenated into `os`; together with
the per-structure lemmas above every operation has amortized cost `O(T + M)` w.r.t. the family
potential:

* `insert` into `D`: `≤ 4T + 637` (`insert_amortized` + `staleCnt_insert_others`);
* `pull` from `D`: `≤ 735 M + 3T + 526` (`pull_amortized`; others unchanged, `staleCnt_pull_others`);
* `deleteKeys ks`: `≤ 3 |ks| + 1` (`staleCnt_clearKeys_le` on the whole family);
* `merge D D'`: `≤ (3T + 420) · #groups + 2T + 2` (`merge_amortized`; `L` unchanged);
* a new structure costs `O(1)` and brings potential `2T` (`pot_new`). -/

/-- a new, empty structure has potential `2T` -/
theorem pot_new (L : Live κ α) (M : ℕ) (Bd : α) :
    pot T L ⟨M, Bd, [⟨⊥, []⟩]⟩ = 2 * T := by
  simp [pot, staleCnt, excess, allEnts]

/-- the stale count of any block list grows by at most `|ks|` when the keys `ks` are cleared -/
theorem staleCnt_clearKeys_le {L : Live κ α} {ks : List κ} {os : List (Block κ α)}
    (hnd : ((allEnts os).map (·.id)).Nodup) :
    staleCnt (clearKeys L ks) os ≤ staleCnt L os + ks.length := by
  have h := deleteKeys_amortized 0 (L := L) (D := ⟨0, default, os⟩) (ks := ks) hnd
  simp only [deleteKeys, pot] at h
  omega

/-- an insert makes at most one entry of the other structures stale -/
theorem staleCnt_insert_others {L : Live κ α} {fresh : ℕ} {D : DStr κ α} {v : κ} {lam : α}
    {os : List (Block κ α)} (hfr : ∀ x ∈ allEnts os, x.id < fresh)
    (hnd : ((allEnts os).map (·.id)).Nodup) :
    staleCnt (insert T L fresh D v lam).1 os ≤ staleCnt L os + 1 := by
  unfold insert
  split_ifs
  · dsimp only; omega
  · exact staleCnt_update_le hfr hnd

/-- clearing keys that are live in `D` does not change the stale count of structures whose ids
are disjoint from those of `D` -/
theorem staleCnt_clearKeys_others {L : Live κ α} {D : DStr κ α} {ks : List κ}
    {os : List (Block κ α)} (hks : ∀ y ∈ ks, HasKey L D y)
    (hdisj : ∀ x ∈ allEnts D.blocks, ∀ z ∈ allEnts os, x.id ≠ z.id) :
    staleCnt (clearKeys L ks) os = staleCnt L os := by
  unfold staleCnt
  apply List.countP_congr
  intro z hz
  have hiff : z.IsLive (clearKeys L ks) ↔ z.IsLive L := by
    rw [isLive_clearKeys]
    refine ⟨fun h => h.1, fun hl => ⟨hl, fun hzk => ?_⟩⟩
    obtain ⟨e, he, hek⟩ := hks _ hzk
    obtain ⟨⟨b, hb, heb⟩, hel⟩ := mem_liveVals.mp he
    exact hdisj e (mem_allEnts.mpr ⟨b, hb, heb⟩) z hz (live_key_unique hel hl hek).1
  simp [hiff]

/-- a pull does not change the stale count of the other structures -/
theorem staleCnt_pull_others {L : Live κ α} {D : DStr κ α} {os : List (Block κ α)}
    (hwf : WF L D) (hdisj : ∀ x ∈ allEnts D.blocks, ∀ z ∈ allEnts os, x.id ≠ z.id) :
    staleCnt (pull T L D).2.2.1 os = staleCnt L os := by
  obtain ⟨hmem, -, -, -, hL, -, -⟩ := pull_spec T hwf
  rw [hL]
  apply staleCnt_clearKeys_others _ hdisj
  intro y hy
  obtain ⟨a, ha, -⟩ := (hmem y).mp hy
  obtain ⟨e, he, hk, -⟩ := view_eq_some.mp ha
  exact ⟨e, he, hk⟩

/-- keys cleared elsewhere keep every other structure well formed -/
theorem wf_clearKeys {L : Live κ α} {D : DStr κ α} {ks : List κ} (hwf : WF L D) :
    WF (clearKeys L ks) D :=
  ⟨hwf.1, IntervalOK.mono (fun _ h => (isLive_clearKeys.mp h).1) hwf.2⟩

/-- an insert elsewhere keeps every other structure (with older ids) well formed -/
theorem wf_insert_others {L : Live κ α} {fresh : ℕ} {D D₂ : DStr κ α} {v : κ} {lam : α}
    (hwf : WF L D₂) (hfr : FreshOK fresh D₂) :
    WF (insert T L fresh D v lam).1 D₂ := by
  unfold insert
  split_ifs
  · exact hwf
  · refine ⟨hwf.1, IntervalOK.mono' (fun b hb e he hl => ?_) hwf.2⟩
    exact ((isLive_update_of_fresh (hfr e (mem_allEnts.mpr ⟨b, hb, he⟩))).mp hl).1

/-- a pull elsewhere keeps every other structure well formed -/
theorem wf_pull_others {L : Live κ α} {D D₂ : DStr κ α} (hwf : WF L D) (hwf₂ : WF L D₂) :
    WF (pull T L D).2.2.1 D₂ := by
  rw [(pull_spec T hwf).2.2.2.2.1]
  exact wf_clearKeys hwf₂

/-- `KeyInj` survives clearing keys -/
theorem keyInj_clearKeys {L : Live κ α} {kof : α → κ} {ks : List κ} (hK : KeyInj L kof) :
    KeyInj (clearKeys L ks) kof := by
  intro y i a h
  unfold clearKeys at h
  split_ifs at h
  exact hK y i a h

end Frontier.CHD.DB
