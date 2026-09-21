import Frontier.CostModel

/-!
# Frontier.LowerBound — Gate F infrastructure (owner: agent-06)

**NON-GATE.**  Nothing in this file is a superlinear lower bound, and nothing here meets Gate F.
It is built on agent-08's `CATree` / `CAProg` / `GateF` (Frontier/CostModel.lean), which is Cai's
topology-specialised comparison–addition class (arXiv 2609.04825v1, §2.2) in decision-tree form.

Contents.
* (V1) **Non-vacuity of `CAProg.Solves`.**  For EVERY topology and source there is an explicit
  comparison–addition tree (Bellman–Ford: `T.n` passes over all edges, one charged addition and at most
  one charged three-way comparison per relaxation) that solves exact labeled SSSP on every nonnegative
  weighting, with charged cost at most `2 * T.n * T.m`.  Without this, `GateF`'s hypothesis
  `∀ P, P.Solves s → …` could be vacuously satisfiable because of a modelling bug, and `GateF` would
  be trivially "provable".  `exists_solving_prog` records the consequence.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace LowerBound

open CATree

variable (T : Topology)

/-! ## The Bellman–Ford comparison–addition tree -/

/-- Relaxation of a schedule of edges as a comparison–addition tree.  `lab v` is the register that
holds the tentative label of `v` (`none` = `⊤`), and `wr e` the register holding the weight of `e`.
Relaxing `e = (u,v)` with `lab u = some ru` creates the register `r_ru + w_e` (one addition) and, if
`v` already has a label, compares it with that label (one comparison), keeping the smaller. -/
def relaxTree : List (Fin T.m) → (k : ℕ) → (Fin T.n → Option (Fin k)) → (Fin T.m → Fin k) →
    CATree T.n k
  | [], _, lab, _ => .leaf lab
  | e :: rest, k, lab, wr =>
    match lab (T.src e) with
    | none => relaxTree rest k lab wr
    | some ru =>
      .add ru (wr e) <|
        match lab (T.dst e) with
        | none => relaxTree rest (k + 1)
            (Function.update (fun v => (lab v).map Fin.castSucc) (T.dst e) (some (Fin.last k)))
            (fun f => Fin.castSucc (wr f))
        | some rv => .cmp (Fin.last k) (Fin.castSucc rv)
            (relaxTree rest (k + 1)
              (Function.update (fun v => (lab v).map Fin.castSucc) (T.dst e) (some (Fin.last k)))
              (fun f => Fin.castSucc (wr f)))
            (relaxTree rest (k + 1) (fun v => (lab v).map Fin.castSucc) (fun f => Fin.castSucc (wr f)))
            (relaxTree rest (k + 1) (fun v => (lab v).map Fin.castSucc) (fun f => Fin.castSucc (wr f)))

/-- One relaxation step on `ℝ≥0∞` labels. -/
noncomputable def relaxE (w : Fin T.m → ℝ≥0) (D : Fin T.n → ℝ≥0∞) (e : Fin T.m) :
    Fin T.n → ℝ≥0∞ :=
  Function.update D (T.dst e) (min (D (T.dst e)) (D (T.src e) + w e))

/-- Register file `r` and label map `lab` represent the `ℝ≥0∞` labels `D`. -/
def Rep {k : ℕ} (r : Fin k → ℝ) (lab : Fin T.n → Option (Fin k)) (D : Fin T.n → ℝ≥0∞) : Prop :=
  ∀ v, (lab v = none → D v = ⊤) ∧ ∀ i, lab v = some i → 0 ≤ r i ∧ D v = ENNReal.ofReal (r i)

theorem toOptReal_top : toOptReal (⊤ : ℝ≥0∞) = none := by simp [toOptReal]

theorem toOptReal_ofReal {x : ℝ} (hx : 0 ≤ x) : toOptReal (ENNReal.ofReal x) = some x := by
  simp [toOptReal, ENNReal.toReal_ofReal hx]

theorem Rep.castSucc {k : ℕ} {r : Fin k → ℝ} {lab : Fin T.n → Option (Fin k)} {D : Fin T.n → ℝ≥0∞}
    (h : Rep T r lab D) (c : ℝ) :
    Rep T (Fin.snoc r c) (fun v => (lab v).map Fin.castSucc) D := by
  intro v
  refine ⟨fun hv => (h v).1 (by simpa using hv), fun i hi => ?_⟩
  cases hl : lab v with
  | none => simp [hl] at hi
  | some j =>
    simp only [hl, Option.map_some, Option.some.injEq] at hi
    subst hi
    simpa [Fin.snoc_castSucc] using (h v).2 j hl

theorem Rep.update {k : ℕ} {r : Fin k → ℝ} {lab : Fin T.n → Option (Fin k)} {D : Fin T.n → ℝ≥0∞}
    (h : Rep T r lab D) (x : Fin T.n) {c : ℝ} (hc : 0 ≤ c) :
    Rep T (Fin.snoc r c)
      (Function.update (fun v => (lab v).map Fin.castSucc) x (some (Fin.last k)))
      (Function.update D x (ENNReal.ofReal c)) := by
  intro v
  by_cases hv : v = x
  · subst hv
    refine ⟨fun h' => by simp at h', fun i hi => ?_⟩
    simp only [Function.update_self, Option.some.injEq] at hi
    subst hi
    simp [Fin.snoc_last, hc]
  · have h2 := (Rep.castSucc T h c) v
    simpa [Function.update_of_ne hv] using h2

theorem relaxE_of_top (w : Fin T.m → ℝ≥0) (D : Fin T.n → ℝ≥0∞) (e : Fin T.m)
    (h : D (T.src e) = ⊤) : relaxE T w D e = D := by
  simp [relaxE, h]

/-- Simulation: the tree computes exactly the `ℝ≥0∞` Bellman–Ford labels. -/
theorem labels_relaxTree (w : Fin T.m → ℝ≥0) :
    ∀ (sched : List (Fin T.m)) (k : ℕ) (lab : Fin T.n → Option (Fin k)) (wr : Fin T.m → Fin k)
      (r : Fin k → ℝ) (D : Fin T.n → ℝ≥0∞),
      Rep T r lab D → (∀ e, r (wr e) = w e) →
      (relaxTree T sched k lab wr).labels r = fun v => toOptReal (sched.foldl (relaxE T w) D v)
  | [], k, lab, wr, r, D, hrep, _ => by
    funext v
    simp only [relaxTree, CATree.labels, List.foldl_nil]
    cases hl : lab v with
    | none => simp [(hrep v).1 hl, toOptReal_top]
    | some i =>
      obtain ⟨h0, hD⟩ := (hrep v).2 i hl
      simp [hD, toOptReal_ofReal h0]
  | e :: rest, k, lab, wr, r, D, hrep, hwr => by
    simp only [List.foldl_cons]
    cases hs : lab (T.src e) with
    | none =>
      have hD : D (T.src e) = ⊤ := (hrep _).1 hs
      rw [relaxE_of_top T w D e hD]
      simp only [relaxTree, hs]
      exact labels_relaxTree w rest k lab wr r D hrep hwr
    | some ru =>
      obtain ⟨hru0, hDu⟩ := (hrep _).2 ru hs
      set c : ℝ := r ru + r (wr e) with hc
      have hc0 : 0 ≤ c := by rw [hc, hwr e]; exact add_nonneg hru0 (NNReal.coe_nonneg (w e))
      have hsum : D (T.src e) + (w e : ℝ≥0∞) = ENNReal.ofReal c := by
        rw [hDu, hc, hwr e, ENNReal.ofReal_add hru0 (NNReal.coe_nonneg (w e)), ENNReal.ofReal_coe_nnreal]
      have hwr' : ∀ f, (Fin.snoc r c : Fin (k + 1) → ℝ) (Fin.castSucc (wr f)) = w f := by
        intro f; simp [Fin.snoc_castSucc, hwr f]
      cases hd : lab (T.dst e) with
      | none =>
        have hDv : D (T.dst e) = ⊤ := (hrep _).1 hd
        have hrel : relaxE T w D e = Function.update D (T.dst e) (ENNReal.ofReal c) := by
          simp [relaxE, hDv, hsum]
        rw [hrel]
        simp only [relaxTree, hs, hd, CATree.labels]
        exact labels_relaxTree w rest (k + 1) _ _ (Fin.snoc r c) _
          (Rep.update T hrep (T.dst e) hc0) hwr'
      | some rv =>
        obtain ⟨hrv0, hDv⟩ := (hrep _).2 rv hd
        simp only [relaxTree, hs, hd, CATree.labels]
        have hlast : (Fin.snoc r c : Fin (k + 1) → ℝ) (Fin.last k) = c := by simp [Fin.snoc_last]
        have hold : (Fin.snoc r c : Fin (k + 1) → ℝ) (Fin.castSucc rv) = r rv := by
          simp [Fin.snoc_castSucc]
        rw [hlast, hold]
        by_cases hlt : c < r rv
        · rw [if_pos hlt]
          have hrel : relaxE T w D e = Function.update D (T.dst e) (ENNReal.ofReal c) := by
            simp only [relaxE, hsum, hDv]
            rw [min_eq_right (ENNReal.ofReal_le_ofReal hlt.le)]
          rw [hrel]
          exact labels_relaxTree w rest (k + 1) _ _ (Fin.snoc r c) _
            (Rep.update T hrep (T.dst e) hc0) hwr'
        · rw [if_neg hlt]
          have hge : r rv ≤ c := le_of_not_gt hlt
          have hrel : relaxE T w D e = D := by
            simp only [relaxE, hsum, hDv]
            rw [min_eq_left (ENNReal.ofReal_le_ofReal hge), ← hDv]
            exact Function.update_eq_self _ _
          rw [hrel]
          split_ifs
          · exact labels_relaxTree w rest (k + 1) _ _ (Fin.snoc r c) _ (Rep.castSucc T hrep c) hwr'
          · exact labels_relaxTree w rest (k + 1) _ _ (Fin.snoc r c) _ (Rep.castSucc T hrep c) hwr'

/-- Charged cost of the relaxation tree: at most two operations per scheduled edge. -/
theorem cost_relaxTree_le :
    ∀ (sched : List (Fin T.m)) (k : ℕ) (lab : Fin T.n → Option (Fin k)) (wr : Fin T.m → Fin k)
      (r : Fin k → ℝ), (relaxTree T sched k lab wr).cost r ≤ 2 * sched.length
  | [], k, lab, wr, r => by simp [relaxTree, CATree.cost]
  | e :: rest, k, lab, wr, r => by
    cases hs : lab (T.src e) with
    | none =>
      simp only [relaxTree, hs, List.length_cons]
      have := cost_relaxTree_le rest k lab wr r
      omega
    | some ru =>
      cases hd : lab (T.dst e) with
      | none =>
        simp only [relaxTree, hs, hd, CATree.cost, List.length_cons]
        have := cost_relaxTree_le rest (k + 1)
          (Function.update (fun v => (lab v).map Fin.castSucc) (T.dst e) (some (Fin.last k)))
          (fun f => Fin.castSucc (wr f)) (Fin.snoc r (r ru + r (wr e)))
        omega
      | some rv =>
        simp only [relaxTree, hs, hd, CATree.cost, List.length_cons]
        have h1 := cost_relaxTree_le rest (k + 1)
          (Function.update (fun v => (lab v).map Fin.castSucc) (T.dst e) (some (Fin.last k)))
          (fun f => Fin.castSucc (wr f)) (Fin.snoc r (r ru + r (wr e)))
        have h2 := cost_relaxTree_le rest (k + 1) (fun v => (lab v).map Fin.castSucc)
          (fun f => Fin.castSucc (wr f)) (Fin.snoc r (r ru + r (wr e)))
        split_ifs <;> omega

/-! ## Bellman–Ford correctness on `ℝ≥0∞` labels (generic graph) -/

section BF

variable (G : Graph)

/-- One relaxation step on `ℝ≥0∞` labels of a weighted graph. -/
noncomputable def relaxG (D : Fin G.n → ℝ≥0∞) (e : Fin G.m) : Fin G.n → ℝ≥0∞ :=
  Function.update D (G.dst e) (min (D (G.dst e)) (D (G.src e) + G.w e))

/-- `i` passes over all edges. -/
def bfSchedG : ℕ → List (Fin G.m)
  | 0 => []
  | i + 1 => bfSchedG i ++ List.finRange G.m

variable {G}

theorem relaxG_le (D : Fin G.n → ℝ≥0∞) (e : Fin G.m) (v : Fin G.n) : relaxG G D e v ≤ D v := by
  unfold relaxG
  by_cases hv : v = G.dst e
  · subst hv; simp
  · rw [Function.update_of_ne hv]

theorem foldl_relaxG_le :
    ∀ (l : List (Fin G.m)) (D : Fin G.n → ℝ≥0∞) (v : Fin G.n), l.foldl (relaxG G) D v ≤ D v
  | [], _, _ => le_rfl
  | e :: l, D, v => (foldl_relaxG_le l _ v).trans (relaxG_le D e v)

theorem relaxG_dst_le (D : Fin G.n → ℝ≥0∞) (e : Fin G.m) :
    relaxG G D e (G.dst e) ≤ D (G.src e) + G.w e := by
  simp [relaxG]

/-- Soundness is preserved: labels never drop below the true distance. -/
theorem sound_foldlG (s : Fin G.n) :
    ∀ (l : List (Fin G.m)) (D : Fin G.n → ℝ≥0∞),
      (∀ v, G.dist s v ≤ D v) → ∀ v, G.dist s v ≤ l.foldl (relaxG G) D v
  | [], _, hD, v => hD v
  | e :: l, D, hD, v => by
    refine sound_foldlG s l _ (fun x => ?_) v
    unfold relaxG
    by_cases hx : x = G.dst e
    · subst hx
      rw [Function.update_self]
      refine le_min (hD _) ?_
      calc G.dist s (G.dst e) ≤ G.dist s (G.src e) + G.w e := Graph.dist_edge s e
        _ ≤ D (G.src e) + G.w e := add_le_add (hD _) le_rfl
    · rw [Function.update_of_ne hx]; exact hD x

/-- One pass over all edges extends completeness by one hop. -/
theorem pass_completeG (s : Fin G.n) (i : ℕ) (D : Fin G.n → ℝ≥0∞)
    (hD : ∀ v p, G.IsWalk s v p → p.length ≤ i → D v ≤ G.len p) :
    ∀ v p, G.IsWalk s v p → p.length ≤ i + 1 →
      (List.finRange G.m).foldl (relaxG G) D v ≤ G.len p := by
  intro v p hp hlen
  rcases Nat.lt_or_ge p.length (i + 1) with hlt | hge
  · exact (foldl_relaxG_le _ D v).trans (hD v p hp (by omega))
  · have hne : p ≠ [] := by
      intro h; subst h; simp at hge
    obtain ⟨p', e, rfl⟩ := (List.eq_nil_or_concat p).resolve_left hne
    rw [List.concat_eq_append] at hp hlen ⊢
    rw [Graph.IsWalk.concat_iff] at hp
    obtain ⟨hp', rfl⟩ := hp
    have hlen' : p'.length ≤ i := by simp at hlen; omega
    have hsrc : D (G.src e) ≤ G.len p' := hD _ p' hp' hlen'
    obtain ⟨l1, l2, hsplit⟩ := List.append_of_mem (List.mem_finRange e)
    rw [hsplit, List.foldl_append, List.foldl_cons]
    calc (l2.foldl (relaxG G) (relaxG G (l1.foldl (relaxG G) D) e)) (G.dst e)
        ≤ relaxG G (l1.foldl (relaxG G) D) e (G.dst e) := foldl_relaxG_le _ _ _
      _ ≤ (l1.foldl (relaxG G) D) (G.src e) + G.w e := relaxG_dst_le _ e
      _ ≤ D (G.src e) + G.w e := add_le_add (foldl_relaxG_le _ D _) le_rfl
      _ ≤ G.len p' + G.w e := add_le_add hsrc le_rfl
      _ = G.len (p' ++ [e]) := by simp [Graph.len_append]

/-- Initial labels: `0` at the source, `⊤` elsewhere. -/
noncomputable def initG (s : Fin G.n) : Fin G.n → ℝ≥0∞ := fun v => if v = s then 0 else ⊤

theorem bf_completeG (s : Fin G.n) :
    ∀ i v p, G.IsWalk s v p → p.length ≤ i →
      (bfSchedG G i).foldl (relaxG G) (initG s) v ≤ G.len p
  | 0, v, p, hp, hlen => by
    have : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [Graph.isWalk_nil_iff] at hp
    subst hp
    simp [bfSchedG, initG]
  | i + 1, v, p, hp, hlen => by
    rw [bfSchedG, List.foldl_append]
    exact pass_completeG s i _ (fun v' p' hp' hl' => bf_completeG s i v' p' hp' hl') v p hp hlen

theorem bfG_eq_dist (s : Fin G.n) (v : Fin G.n) :
    (bfSchedG G G.n).foldl (relaxG G) (initG s) v = G.dist s v := by
  apply le_antisymm
  · by_cases hr : G.Reachable s v
    · obtain ⟨p, hp, heq, -, hlen⟩ := Graph.exists_shortest_path hr
      rw [← heq]
      exact bf_completeG s G.n v p hp (le_of_lt hlen)
    · rw [(Graph.dist_eq_top_iff).mpr hr]; exact le_top
  · refine sound_foldlG s _ _ (fun x => ?_) v
    by_cases hx : x = s
    · subst hx; simp [initG]
    · simp [initG, hx]

theorem length_bfSchedG : ∀ i, (bfSchedG G i).length = i * G.m
  | 0 => by simp [bfSchedG]
  | i + 1 => by simp [bfSchedG, length_bfSchedG i, Nat.succ_mul]

end BF

/-! ## The program and its correctness -/

variable {T}

/-- Initial label map: the source holds the zero register (index `T.m`). -/
def initLab (s : Fin T.n) : Fin T.n → Option (Fin (T.m + 1 + ([] : List ℝ).length)) :=
  fun v => if v = s then some ⟨T.m, by simp⟩ else none

/-- Weight registers are the first `T.m` registers. -/
def initWr : Fin T.m → Fin (T.m + 1 + ([] : List ℝ).length) :=
  fun e => ⟨e, by simp only [List.length_nil, Nat.add_zero]; omega⟩

/-- The Bellman–Ford schedule for topology `T`: `T.n` passes over all edges. -/
def bfSched (T : Topology) : List (Fin T.m) := bfSchedG (T.withW fun _ => 0) T.n

/-- The Bellman–Ford comparison–addition program (no literals). -/
def bfProg (s : Fin T.n) : CAProg T :=
  ⟨[], relaxTree T (bfSched T) _ (initLab s) initWr⟩

theorem bfProg_rep (s : Fin T.n) (w : Fin T.m → ℝ≥0) :
    Rep T ((bfProg s).initRegs w) (initLab s)
      (initG (G := T.withW w) s) := by
  intro v
  by_cases hv : v = s
  · subst hv
    refine ⟨fun h => by simp [initLab] at h, fun i hi => ?_⟩
    simp only [initLab, if_true] at hi
    have hi' := Option.some.inj hi
    subst hi'
    simp only [CAProg.initRegs, bfProg, initG]
    refine ⟨by simp, ?_⟩
    show (if v = v then (0 : ℝ≥0∞) else ⊤) = _
    simp
  · refine ⟨fun _ => ?_, fun i hi => ?_⟩
    · show (if v = s then (0 : ℝ≥0∞) else ⊤) = ⊤
      exact if_neg hv
    · simp [initLab, hv] at hi

theorem bfProg_wr (s : Fin T.n) (w : Fin T.m → ℝ≥0) (e : Fin T.m) :
    (bfProg s).initRegs w (initWr e) = w e := by
  simp [CAProg.initRegs, bfProg, initWr]

/-- `relaxE` is `relaxG` on the weighted graph. -/
theorem relaxE_eq (w : Fin T.m → ℝ≥0) : relaxE T w = relaxG (T.withW w) := rfl

theorem bfSched_eq (w : Fin T.m → ℝ≥0) : bfSched T = bfSchedG (T.withW w) T.n := by
  unfold bfSched
  induction T.n with
  | zero => rfl
  | succ i ih => simp only [bfSchedG, ih]; rfl

/-- **(V1) Non-vacuity.**  Every topology and source admit a correct comparison–addition program. -/
theorem bfProg_solves (s : Fin T.n) : (bfProg s).Solves s := by
  intro w v
  have h := labels_relaxTree T w (bfSched T) _ (initLab s) initWr ((bfProg s).initRegs w)
    (initG (G := T.withW w) s) (bfProg_rep s w) (bfProg_wr s w)
  change (relaxTree T (bfSched T) _ (initLab s) initWr).labels ((bfProg s).initRegs w) v = _
  rw [h]
  show toOptReal ((bfSched T).foldl (relaxE T w) (initG (G := T.withW w) s) v) = _
  rw [relaxE_eq, bfSched_eq w]
  exact congrArg toOptReal (bfG_eq_dist (G := T.withW w) s v)

/-- Its charged cost is at most `2 n m` on every weighting. -/
theorem bfProg_cost_le (s : Fin T.n) (w : Fin T.m → ℝ≥0) :
    (bfProg s).cost w ≤ 2 * (T.n * T.m) := by
  have h := cost_relaxTree_le T (bfSched T) _ (initLab s) initWr ((bfProg s).initRegs w)
  have hl : (bfSched T).length = T.n * T.m := length_bfSchedG (G := T.withW fun _ => 0) T.n
  rw [hl] at h
  exact h

/-- Correct programs exist on every topology, so the universally quantified hypothesis in `GateF` is
never vacuous. -/
theorem exists_solving_prog (s : Fin T.n) :
    ∃ P : CAProg T, P.Solves s ∧ ∀ w, P.cost w ≤ 2 * (T.n * T.m) :=
  ⟨bfProg s, bfProg_solves s, bfProg_cost_le s⟩


/-! ## (V2) Every charged addition creates exactly one register: a linear floor

`exists_final` is the basic accounting fact for every lower-bound argument in this model: along the
execution on a register file `r`, the leaf is reached with a register file `r'` that EXTENDS `r` by at most
`cost` new registers, and every output value is held in `r'`.  Hence the number of distinct output values
that are not initial register values is at most the charged cost (`card_new_values_le`). -/

theorem exists_final {n : ℕ} : ∀ {k : ℕ} (t : CATree n k) (r : Fin k → ℝ),
    ∃ (k' : ℕ) (r' : Fin k' → ℝ) (hk : k ≤ k'), k' ≤ k + t.cost r ∧
      (∀ i : Fin k, r' (Fin.castLE hk i) = r i) ∧
      ∀ v x, t.labels r v = some x → ∃ j, r' j = x := by
  intro k t
  induction t with
  | leaf out =>
    intro r
    refine ⟨_, r, le_rfl, by simp [CATree.cost], fun i => by simp, fun v x h => ?_⟩
    simp only [CATree.labels] at h
    cases hv : out v with
    | none => simp [hv] at h
    | some j => exact ⟨j, by simpa [hv] using h⟩
  | add i j t ih =>
    intro r
    obtain ⟨k', r', hk, hlen, hext, hout⟩ := ih (Fin.snoc r (r i + r j))
    refine ⟨k', r', by omega, ?_, fun a => ?_, fun v x h => hout v x (by simpa [CATree.labels] using h)⟩
    · simp only [CATree.cost]; omega
    · have := hext (Fin.castSucc a)
      simp only [Fin.snoc_castSucc] at this
      rw [← this]; congr 1
  | cmp i j t₁ t₂ t₃ ih₁ ih₂ ih₃ =>
    intro r
    by_cases h1 : r i < r j
    · obtain ⟨k', r', hk, hlen, hext, hout⟩ := ih₁ r
      refine ⟨k', r', hk, ?_, hext, fun v x h => hout v x (by simpa [CATree.labels, h1] using h)⟩
      simp only [CATree.cost, if_pos h1]; omega
    · by_cases h2 : r i = r j
      · obtain ⟨k', r', hk, hlen, hext, hout⟩ := ih₂ r
        refine ⟨k', r', hk, ?_, hext, fun v x h => hout v x (by simpa [CATree.labels, h1, h2] using h)⟩
        simp only [CATree.cost, if_neg h1, if_pos h2]; omega
      · obtain ⟨k', r', hk, hlen, hext, hout⟩ := ih₃ r
        refine ⟨k', r', hk, ?_, hext, fun v x h => hout v x (by simpa [CATree.labels, h1, h2] using h)⟩
        simp only [CATree.cost, if_neg h1, if_neg h2]; omega

/-- Distinct output values that are not initial register values each need their own charged addition. -/
theorem card_new_values_le {n k : ℕ} (t : CATree n k) (r : Fin k → ℝ) (S : Finset ℝ)
    (hS : ∀ x ∈ S, (∃ v, t.labels r v = some x) ∧ ∀ i, r i ≠ x) : S.card ≤ t.cost r := by
  obtain ⟨k', r', hk, hlen, hext, hout⟩ := exists_final t r
  classical
  rcases S.eq_empty_or_nonempty with hSe | ⟨x0, hx0⟩
  · simp [hSe]
  have hne : Nonempty (Fin k') := ⟨(hout _ x0 (hS x0 hx0).1.choose_spec).choose⟩
  choose! J hJ using fun x (hx : x ∈ S) => hout _ x (hS x hx).1.choose_spec
  have hJk : ∀ x ∈ S, k ≤ (J x : ℕ) := by
    intro x hx
    by_contra hlt
    push_neg at hlt
    have h := hext ⟨J x, hlt⟩
    have heq : Fin.castLE hk ⟨(J x : ℕ), hlt⟩ = J x := Fin.ext rfl
    rw [heq, hJ x hx] at h
    exact (hS x hx).2 _ h.symm
  have hinj : Set.InjOn J S := by
    intro x hx y hy hxy
    rw [← hJ x hx, ← hJ y hy, hxy]
  have hmaps : ∀ x ∈ S, J x ∈ (Finset.univ.filter fun j : Fin k' => k ≤ (j : ℕ)) := by
    intro x hx; simp [hJk x hx]
  have hcard := Finset.card_le_card_of_injOn J hmaps hinj
  have hfilter : (Finset.univ.filter fun j : Fin k' => k ≤ (j : ℕ)).card = k' - k := by
    have : (Finset.univ.filter fun j : Fin k' => k ≤ (j : ℕ)) =
        (Finset.univ.filter fun j : Fin k' => ¬ (j : ℕ) < k) := by
      ext j; simp
    rw [this, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin, Fin.card_filter_val_lt, Nat.min_eq_right hk]
  omega

/-! ### The directed path family -/

/-- The directed path `0 → 1 → ⋯ → n` (`n + 1` vertices, `n` edges; edge `i` goes from `i` to `i+1`). -/
def pathTopo (n : ℕ) : Topology := ⟨n + 1, n, fun i => i.castSucc, fun i => i.succ⟩

/-- Its source vertex `0`. -/
def pathSrc (n : ℕ) : Fin (pathTopo n).n := ⟨0, Nat.succ_pos n⟩

/-- The path with every weight equal to `c`, as a graph. -/
def pathG (n : ℕ) (c : ℝ≥0) : Graph := ⟨n + 1, n, fun i => i.castSucc, fun i => i.succ, fun _ => c⟩

theorem pathG_walk_val {n : ℕ} {c : ℝ≥0} {u v : Fin (pathG n c).n} {p : List (Fin (pathG n c).m)}
    (h : (pathG n c).IsWalk u v p) : (v : ℕ) = u + p.length := by
  induction h with
  | nil u => simp
  | @cons e v' p' hwalk ih =>
    have hs : ((pathG n c).src e : ℕ) = e := rfl
    have hd : ((pathG n c).dst e : ℕ) = e + 1 := rfl
    rw [hd] at ih
    rw [hs, List.length_cons]
    omega

theorem pathG_len {n : ℕ} (c : ℝ≥0) (p : List (Fin (pathG n c).m)) :
    (pathG n c).len p = p.length * c := by
  induction p with
  | nil => simp [Graph.len]
  | cons e p ih =>
    rw [Graph.len_cons, ih]
    have : (pathG n c).w e = c := rfl
    rw [this, List.length_cons]
    push_cast
    ring

theorem pathG_n (n : ℕ) (c : ℝ≥0) : (pathG n c).n = n + 1 := rfl
theorem pathG_m (n : ℕ) (c : ℝ≥0) : (pathG n c).m = n := rfl

/-- The explicit walk `0 → 1 → ⋯ → j`. -/
def pathWalk (n : ℕ) (c : ℝ≥0) : (j : ℕ) → j ≤ n → List (Fin (pathG n c).m)
  | 0, _ => []
  | j + 1, h => pathWalk n c j (by omega) ++ [⟨j, by rw [pathG_m]; omega⟩]

theorem pathWalk_isWalk {n : ℕ} (c : ℝ≥0) :
    ∀ (j : ℕ) (h : j ≤ n),
      (pathG n c).IsWalk ⟨0, by rw [pathG_n]; omega⟩ ⟨j, by rw [pathG_n]; omega⟩ (pathWalk n c j h)
  | 0, _ => Graph.IsWalk.nil _
  | j + 1, h => by
    rw [pathWalk, Graph.IsWalk.concat_iff]
    exact ⟨pathWalk_isWalk c j (by omega), rfl⟩

theorem length_pathWalk (n : ℕ) (c : ℝ≥0) : ∀ (j : ℕ) (h : j ≤ n), (pathWalk n c j h).length = j
  | 0, _ => rfl
  | j + 1, h => by simp [pathWalk, length_pathWalk n c j]

theorem pathG_dist {n : ℕ} (c : ℝ≥0) (v : Fin (pathG n c).n) :
    (pathG n c).dist ⟨0, by rw [pathG_n]; omega⟩ v = ((v : ℕ) * c : ℝ≥0) := by
  apply le_antisymm
  · have hvn : (v : ℕ) ≤ n := by have h : (v : ℕ) < n + 1 := v.2; omega
    have hw := pathWalk_isWalk c v hvn
    refine (Graph.dist_le_len hw).trans ?_
    rw [pathG_len, length_pathWalk]
  · refine le_iInf₂ fun p hp => ?_
    have h := pathG_walk_val hp
    rw [pathG_len, h]
    simp

/-- **(V2) Linear floor.**  On the directed path with `n + 1` vertices and `n` edges (all reachable), every
correct comparison–addition program performs at least `n - 1` charged additions on some weighting.  So the
cost function of `GateF` is not trivial; `GateF` must beat this linear floor by an unbounded factor. -/
theorem path_floor (n : ℕ) (P : CAProg (pathTopo n)) (hP : P.Solves (pathSrc n)) :
    ∃ w, n - 1 ≤ P.cost w := by
  -- a common weight larger than every literal in absolute value
  set L : ℝ := (P.lits.map fun x => |x|).sum with hL
  have hL0 : 0 ≤ L := List.sum_nonneg (by simp)
  have hlit : ∀ x ∈ P.lits, |x| ≤ L := by
    intro x hx
    rw [hL]
    exact List.single_le_sum (fun y hy => by simp at hy; obtain ⟨z, -, rfl⟩ := hy; exact abs_nonneg z)
      _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
  let c : ℝ≥0 := ⟨L + 1, by linarith⟩
  have hc : (c : ℝ) = L + 1 := rfl
  refine ⟨fun _ => c, ?_⟩
  -- the output values `j * c`, `2 ≤ j ≤ n`
  let S : Finset ℝ := (Finset.Icc 2 n).image fun j : ℕ => (j : ℝ) * c
  have hScard : S.card = n - 1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have hc0 : (c : ℝ) ≠ 0 := by rw [hc]; linarith
      exact_mod_cast mul_right_cancel₀ hc0 hab
  rw [← hScard]
  apply card_new_values_le
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_Icc] at hj
  have hjn : j < (pathTopo n).n := by show j < n + 1; omega
  refine ⟨⟨⟨j, hjn⟩, ?_⟩, fun i => ?_⟩
  · have h1 := hP (fun _ => c) ⟨j, hjn⟩
    have h2 : ((pathTopo n).withW fun _ => c).dist (pathSrc n) ⟨j, hjn⟩ = ((j : ℕ) * c : ℝ≥0) :=
      pathG_dist c ⟨j, hjn⟩
    change P.tree.labels (P.initRegs fun _ => c) ⟨j, hjn⟩ = _
    rw [h1]
    exact (congrArg toOptReal h2).trans (by rw [toOptReal, if_neg ENNReal.coe_ne_top]; simp)
  · -- no initial register holds `j * c`
    have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj.1
    have hcpos : (0 : ℝ) < c := by rw [hc]; linarith
    have hbig : (c : ℝ) < (j : ℝ) * c := by nlinarith
    simp only [CAProg.initRegs]
    split_ifs with h1 h2 h3
    · intro heq
      have : (c : ℝ) = (j : ℝ) * c := heq
      linarith
    · intro heq
      have : (0 : ℝ) = (j : ℝ) * c := heq
      nlinarith
    · intro heq
      have hmem := List.get_mem P.lits ⟨(i : ℕ) - ((pathTopo n).m + 1), h2⟩
      have hle := hlit _ hmem
      rw [heq] at hle
      have : (j : ℝ) * c ≤ L := (le_abs_self _).trans hle
      linarith
    · intro heq
      have : (0 : ℝ) = (j : ℝ) * c := heq
      nlinarith

end LowerBound
end Frontier
