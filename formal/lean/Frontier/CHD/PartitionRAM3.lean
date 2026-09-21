import Frontier.CHD.PartitionRAM

/-!
# Frontier.CHD.PartitionRAM3 — Layer B for MakePivots (owner agent-03)

**NON-GATE.** The MakePivots scan over the stored pieces (records `g < np`, tails chained through `pt.nx`),
producing the pivot groups as COMPACT segments `pt.GV[pt.GO[j], pt.GO[j] + pt.GL[j])`, `j < pt.ng`, with the
assignment bitmap `pt.as` (`1` = assigned).  Membership in `S` and `Q` is read from the word bitmaps `fp.inS` and
`fp.inQ`.  Refines `Partition.makePivots S Q pieces`.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V}

/-- Test-and-add the vertex in register `pt.x`: if it is in `S \ Q` and unassigned, assign it and append it to
the output segment. -/
def testAdd : Stmt :=
  .seq (.wset "pt.tS" (.load "fp.inS" (.var "pt.x"))) <|
  .seq (.wset "pt.tQ" (.load "fp.inQ" (.var "pt.x"))) <|
  .seq (.wset "pt.tA" (.load "pt.as" (.var "pt.x"))) <|
  .ite (.eq (.var "pt.tS") (.lit 1))
    (.ite (.eq (.var "pt.tQ") (.lit 0))
      (.ite (.eq (.var "pt.tA") (.lit 0))
        (.seq (.wstore "pt.as" (.var "pt.x") (.lit 1)) <|
         .seq (.wstore "pt.GV" (.var "pt.gv") (.var "pt.x"))
              (.wset "pt.gv" (.add (.var "pt.gv") (.lit 1))))
        .skip)
      .skip)
    .skip

/-- The tail walk of one piece: `pt.c` members remain, the next one is `pt.x`. -/
def tailBody : Stmt :=
  .seq testAdd <|
  .seq (.wset "pt.x" (.load "pt.nx" (.var "pt.x")))
       (.wset "pt.c" (.sub (.var "pt.c") (.lit 1)))

def tailLoop : Stmt := .while (.lt (.lit 0) (.var "pt.c")) tailBody

/-- One piece `g = pt.g`: its top, then its tail; close the group if it is nonempty. -/
def pieceBody : Stmt :=
  .seq (.wset "pt.gs" (.var "pt.gv")) <|
  .seq (.wset "pt.x" (.load "pt.PT" (.var "pt.g"))) <|
  .seq testAdd <|
  .seq (.wset "pt.x" (.load "pt.PF" (.var "pt.g"))) <|
  .seq (.wset "pt.c" (.load "pt.PN" (.var "pt.g"))) <|
  .seq tailLoop <|
  .seq (.ite (.lt (.var "pt.gs") (.var "pt.gv"))
          (.seq (.wstore "pt.GO" (.var "pt.ng") (.var "pt.gs")) <|
           .seq (.wstore "pt.GL" (.var "pt.ng") (.sub (.var "pt.gv") (.var "pt.gs")))
                (.wset "pt.ng" (.add (.var "pt.ng") (.lit 1))))
          .skip)
       (.wset "pt.g" (.add (.var "pt.g") (.lit 1)))

/-- MakePivots over the records `pt.g, …, pt.np - 1`. -/
def mpLoop : Stmt := .while (.lt (.var "pt.g") (.var "pt.np")) pieceBody

section TestAdd

variable {st : State V} {x gv : ℕ}

/-- `testAdd` on a vertex of `S \ Q` not yet assigned: assign and append. -/
theorem testAdd_yes (hx : st.w "pt.x" = x) (hgv : st.w "pt.gv" = gv)
    (hS : st.wa "fp.inS" x = 1) (hQ : st.wa "fp.inQ" x = 0) (hA : st.wa "pt.as" x = 0)
    (hxl : x < st.wlen "fp.inS" ∧ x < st.wlen "fp.inQ" ∧ x < st.wlen "pt.as") (hgvl : gv < st.wlen "pt.GV")
    (hcap : gv + 1 < st.cap) :
    Runs ops testAdd st (fun st' =>
      st'.wa "pt.as" x = 1 ∧ st'.wa "pt.GV" gv = x ∧ st'.w "pt.gv" = gv + 1 ∧
      (∀ j, j ≠ x → st'.wa "pt.as" j = st.wa "pt.as" j) ∧
      (∀ j, j ≠ gv → st'.wa "pt.GV" j = st.wa "pt.GV" j) ∧
      (∀ arr j, arr ≠ "pt.as" → arr ≠ "pt.GV" → st'.wa arr j = st.wa arr j) ∧
      (∀ y, y ≠ "pt.tS" → y ≠ "pt.tQ" → y ≠ "pt.tA" → y ≠ "pt.gv" → st'.w y = st.w y) ∧
      st'.wlen = st.wlen ∧ st'.cap = st.cap ∧ st'.cost ≤ st.cost + 12) := by
  obtain ⟨h1, h2, h3⟩ := hxl
  apply wp_sound
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt (by omega)
  have hfitg : fit st.cap (gv + 1) = some (gv + 1) := fit_of_lt hcap
  simp only [testAdd, wp, evalW_load', evalW_add', evalW_var, evalW_lit', evalW_eq', State.setW_w, State.charge_w,
    State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen, State.setW_cap,
    State.storeW_w, State.storeW_wa, State.storeW_wlen, State.storeW_cap, State.charge_cost, State.setW_cost,
    State.storeW_cost, hx, hgv, hS, hQ, hA, h1, h2, h3, hgvl, hfit0, hfit1, hfitg, Option.bind_some, String.reduceEq,
    ite_true, ite_false, ne_eq, one_ne_zero, not_false_eq_true, true_implies, true_and, and_true, false_and,
    and_false, not_true_eq_false, false_implies, eq_self_iff_true]
  and_intros
  all_goals first
    | omega
    | rfl
    | (intro y y1 y2 y3 y4; simp [y1, y2, y3, y4])
    | (intro arr j h1' h2'; simp [h1', h2'])
    | (intro j hj; simp [hj])

/-- `testAdd` on a vertex that is not added: only the scratch registers change. -/
theorem testAdd_no (hx : st.w "pt.x" = x) (hxl : x < st.wlen "fp.inS" ∧ x < st.wlen "fp.inQ" ∧ x < st.wlen "pt.as")
    (hcap : 1 < st.cap) (hno : ¬ (st.wa "fp.inS" x = 1 ∧ st.wa "fp.inQ" x = 0 ∧ st.wa "pt.as" x = 0)) :
    Runs ops testAdd st (fun st' => st'.wa = st.wa ∧
      (∀ y, y ≠ "pt.tS" → y ≠ "pt.tQ" → y ≠ "pt.tA" → st'.w y = st.w y) ∧
      st'.wlen = st.wlen ∧ st'.cap = st.cap ∧ st'.cost ≤ st.cost + 12) := by
  obtain ⟨h1, h2, h3⟩ := hxl
  apply wp_sound
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt (by omega)
  by_cases hS : st.wa "fp.inS" x = 1
  · by_cases hQ : st.wa "fp.inQ" x = 0
    · have hA : st.wa "pt.as" x ≠ 0 := fun hA => hno ⟨hS, hQ, hA⟩
      have hA' : (st.wa "pt.as" x = 0) = False := by simp [hA]
      simp only [testAdd, wp, evalW_load', evalW_var, evalW_lit', evalW_eq', State.setW_w, State.charge_w,
        State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen, State.setW_cap,
        State.charge_cost, State.setW_cost, hx, hS, hQ, hA', h1, h2, h3, hfit0, hfit1, Option.bind_some,
        String.reduceEq, ite_true, ite_false, ne_eq, one_ne_zero, not_false_eq_true, true_implies, true_and,
        and_true, false_and, and_false, not_true_eq_false, false_implies, eq_self_iff_true]
      and_intros
      all_goals first
        | omega
        | rfl
        | (intro y y1 y2 y3; simp [y1, y2, y3])
    · have hQ' : (st.wa "fp.inQ" x = 0) = False := by simp [hQ]
      simp only [testAdd, wp, evalW_load', evalW_var, evalW_lit', evalW_eq', State.setW_w, State.charge_w,
        State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen, State.setW_cap,
        State.charge_cost, State.setW_cost, hx, hS, hQ', h1, h2, h3, hfit0, hfit1, Option.bind_some,
        String.reduceEq, ite_true, ite_false, ne_eq, one_ne_zero, not_false_eq_true, true_implies, true_and,
        and_true, false_and, and_false, not_true_eq_false, false_implies, eq_self_iff_true]
      and_intros
      all_goals first
        | omega
        | rfl
        | (intro y y1 y2 y3; simp [y1, y2, y3])
  · have hS' : (st.wa "fp.inS" x = 1) = False := by simp [hS]
    simp only [testAdd, wp, evalW_load', evalW_var, evalW_lit', evalW_eq', State.setW_w, State.charge_w,
      State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen, State.setW_cap,
      State.charge_cost, State.setW_cost, hx, hS', h1, h2, h3, hfit0, hfit1, Option.bind_some,
      String.reduceEq, ite_true, ite_false, ne_eq, one_ne_zero, not_false_eq_true, true_implies, true_and,
      and_true, false_and, and_false, not_true_eq_false, false_implies, eq_self_iff_true]
    and_intros
    all_goals first
      | omega
      | rfl
      | (intro y y1 y2 y3; simp [y1, y2, y3])

end TestAdd

/-! ## Representations -/

/-- The word array `arr` is the 0/1 indicator of `A` below `N`. -/
def BitRep (st : State V) (arr : String) (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ x < N, st.wa arr x = if x ∈ A then 1 else 0

/-- The list `L` is stored contiguously in `arr` from position `b`. -/
def SegAt (st : State V) (arr : String) (b : ℕ) (L : List ℕ) : Prop :=
  ∀ i (h : i < L.length), st.wa arr (b + i) = L[i]

theorem SegAt.snoc {st st' : State V} {arr : String} {b : ℕ} {L : List ℕ} {x : ℕ} (h : SegAt st arr b L)
    (hx : st'.wa arr (b + L.length) = x) (hfr : ∀ i < L.length, st'.wa arr (b + i) = st.wa arr (b + i)) :
    SegAt st' arr b (L ++ [x]) := by
  intro i hi
  rw [List.length_append, List.length_singleton] at hi
  by_cases hil : i < L.length
  · rw [List.getElem_append_left hil, hfr i hil]; exact h i hil
  · have : i = L.length := by omega
    subst this
    rw [List.getElem_append_right (by omega)]
    simpa using hx

/-- The piece-scan predicate: in `S \ Q` and not yet assigned. -/
def mpP (S Q A : Finset ℕ) (x : ℕ) : Prop := x ∈ S ∧ x ∉ Q ∧ x ∉ A

instance (S Q A : Finset ℕ) : DecidablePred (mpP S Q A) := fun x => by unfold mpP; infer_instance

theorem LL.get {st : State V} {arr : String} :
    ∀ {L : List ℕ}, LL st arr L → ∀ i (h : i + 1 < L.length), st.wa arr (L[i]'(by omega)) = L[i + 1]
  | [], _, i, h => by simp at h
  | [_], _, i, h => by simp at h
  | x :: y :: t, ⟨h1, h2⟩, i, h => by
    cases i with
    | zero => simpa using h1
    | succ i =>
      have := LL.get h2 i (by simp at h ⊢; omega)
      simpa using this

theorem filter_take_succ {L : List ℕ} {m : ℕ} (hm : m < L.length) (P : ℕ → Prop) [DecidablePred P] (top : ℕ) :
    (top :: L.take (m + 1)).filter P = (top :: L.take m).filter P ++ (if P L[m] then [L[m]] else []) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm]
  simp only [Option.toList_some, ← List.cons_append, List.filter_append, List.filter_singleton]
  split_ifs with hP <;> simp [hP]


/-! ## The tail walk of one piece -/

/-- Invariant of the tail walk with `c` members left (`m = |T| - c` processed after the top). -/
def TLI (st0 : State V) (S Q A : Finset ℕ) (N gs top : ℕ) (T : List ℕ) (c0 c : ℕ) (st : State V) : Prop :=
  c ≤ T.length ∧ st.w "pt.c" = c ∧ (0 < c → T[T.length - c]? = some (st.w "pt.x")) ∧
  SegAt st "pt.GV" gs ((top :: T.take (T.length - c)).filter (mpP S Q A)) ∧
  st.w "pt.gv" = gs + ((top :: T.take (T.length - c)).filter (mpP S Q A)).length ∧
  BitRep st "pt.as" (A ∪ ((top :: T.take (T.length - c)).filter (mpP S Q A)).toFinset) N ∧
  (∀ j < gs, st.wa "pt.GV" j = st0.wa "pt.GV" j) ∧
  (∀ arr j, arr ≠ "pt.as" → arr ≠ "pt.GV" → st.wa arr j = st0.wa arr j) ∧
  (∀ y, y ≠ "pt.x" → y ≠ "pt.c" → y ≠ "pt.gv" → y ≠ "pt.tS" → y ≠ "pt.tQ" → y ≠ "pt.tA" →
    st.w y = st0.w y) ∧
  st.wlen = st0.wlen ∧ st.cap = st0.cap ∧ st.cost + 16 * c ≤ c0

theorem tailLoop_spec {st0 : State V} {S Q A : Finset ℕ} {N gs top : ℕ} {T : List ℕ} {c0 : ℕ}
    (hnd : (top :: T).Nodup) (hLL : LL st0 "pt.nx" T)
    (hSb : BitRep st0 "fp.inS" S N) (hQb : BitRep st0 "fp.inQ" Q N)
    (hN : ∀ x ∈ top :: T, x < N)
    (hNl : N ≤ st0.wlen "fp.inS" ∧ N ≤ st0.wlen "fp.inQ" ∧ N ≤ st0.wlen "pt.as" ∧ N ≤ st0.wlen "pt.nx")
    (hGV : gs + T.length + 1 ≤ st0.wlen "pt.GV") (hcap : gs + T.length + 2 < st0.cap) :
    ∀ c st, TLI st0 S Q A N gs top T c0 c st → Runs ops tailLoop st (fun st' =>
      SegAt st' "pt.GV" gs ((top :: T).filter (mpP S Q A)) ∧
      st'.w "pt.gv" = gs + ((top :: T).filter (mpP S Q A)).length ∧
      BitRep st' "pt.as" (A ∪ ((top :: T).filter (mpP S Q A)).toFinset) N ∧
      (∀ j < gs, st'.wa "pt.GV" j = st0.wa "pt.GV" j) ∧
      (∀ arr j, arr ≠ "pt.as" → arr ≠ "pt.GV" → st'.wa arr j = st0.wa arr j) ∧
      (∀ y, y ≠ "pt.x" → y ≠ "pt.c" → y ≠ "pt.gv" → y ≠ "pt.tS" → y ≠ "pt.tQ" → y ≠ "pt.tA" →
        st'.w y = st0.w y) ∧
      st'.wlen = st0.wlen ∧ st'.cap = st0.cap ∧ st'.cost ≤ c0 + 1) := by
  apply runs_while_nat
  intro c st hTL
  obtain ⟨hcle, hrc, hrx, hseg, hgv, has, hGVold, harr, hreg, hlen, hcapst, hcost⟩ := hTL
  have hcap1 : 1 < st.cap := by rw [hcapst]; omega
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  refine ⟨if 0 < c then 1 else 0, ?_, ?_, ?_⟩
  · simp only [evalW_lt', evalW_lit', evalW_var, hrc, hfit0, Option.bind_some]
    split_ifs <;> simp [hfit0, hfit1]
  · intro hx
    have hc0 : 0 < c := by by_contra h; simp [h] at hx
    set m := T.length - c with hm
    have hmT : m < T.length := by omega
    have hxT : st.w "pt.x" = T[m] := by
      have := hrx hc0; rw [List.getElem?_eq_getElem hmT] at this; exact (Option.some.inj this).symm
    set x := T[m] with hx_def
    have hxF : x ∈ top :: T := List.mem_cons_of_mem _ (List.getElem_mem hmT)
    have hxN := hN x hxF
    set pre := (top :: T.take m).filter (mpP S Q A) with hpre
    -- `x` has not been seen in this piece
    have hxpre : x ∉ pre := by
      intro h
      have hmem : x ∈ top :: T.take m := List.mem_of_mem_filter h
      have hnd' : (top :: T.take m ++ [x]).Nodup := by
        have : top :: T.take (m + 1) = top :: T.take m ++ [x] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hmT]; rfl
        rw [← this]
        exact hnd.sublist (List.Sublist.cons₂ _ (List.take_sublist _ _))
      exact (List.nodup_append.mp hnd').2.2 x hmem x (List.mem_singleton_self _) rfl
    have hNl' : x < st.wlen "fp.inS" ∧ x < st.wlen "fp.inQ" ∧ x < st.wlen "pt.as" := by
      rw [hlen]; obtain ⟨n1, n2, n3, -⟩ := hNl; exact ⟨by omega, by omega, by omega⟩
    have hSx : st.wa "fp.inS" x = if x ∈ S then 1 else 0 := by
      rw [harr _ _ (by decide) (by decide)]; exact hSb x hxN
    have hQx : st.wa "fp.inQ" x = if x ∈ Q then 1 else 0 := by
      rw [harr _ _ (by decide) (by decide)]; exact hQb x hxN
    have hAx : st.wa "pt.as" x = if x ∈ A then 1 else 0 := by
      rw [has x hxN]; simp [Finset.mem_union, List.mem_toFinset, hxpre]
    -- the next vertex
    have hnx : ∀ st' : State V, st'.wa "pt.nx" = st0.wa "pt.nx" → ∀ hlt : m + 1 < T.length,
        st'.wa "pt.nx" x = T[m + 1] := by
      intro st' h hlt; rw [h]; exact LL.get hLL m hlt
    have hnxl : x < st.wlen "pt.nx" := by rw [hlen]; exact lt_of_lt_of_le hxN hNl.2.2.2
    have hfilt : (top :: T.take (m + 1)).filter (mpP S Q A) = pre ++ (if mpP S Q A x then [x] else []) := by
      rw [hpre, hx_def]; exact filter_take_succ hmT (mpP S Q A) top
    have hm1 : T.length - (c - 1) = m + 1 := by omega
    have hpl : pre.length ≤ m + 1 := by
      have h : pre.length ≤ (top :: T.take m).length := List.length_filter_le _ _
      simp only [List.length_cons, List.length_take] at h
      omega
    by_cases hP : mpP S Q A x
    · -- add `x`
      have hP' := hP
      obtain ⟨hxS, hxQ, hxA⟩ := hP
      have hgvl : st.w "pt.gv" < st.wlen "pt.GV" := by
        rw [hgv, hlen]; omega
      have hcapg : st.w "pt.gv" + 1 < st.cap := by rw [hgv, hcapst]; omega
      apply runs_seq
      refine Runs.mono (testAdd_yes (ops := ops) (st := st.charge 1) (x := x) (gv := st.w "pt.gv")
        (by simpa using hxT) rfl (by simp [hSx, hxS]) (by simp [hQx, hxQ]) (by simp [hAx, hxA]) hNl'
        (by simpa using hgvl) (by simpa using hcapg)) ?_
      rintro st1 ⟨h1as, h1GV, h1gv, h1asf, h1GVf, h1arr, h1reg, h1len, h1cap, h1cost⟩
      apply runs_seq
      have hfitx : evalW st1 (.load "pt.nx" (.var "pt.x")) = some (st1.wa "pt.nx" x) := by
        have : st1.w "pt.x" = x := by
          rw [h1reg "pt.x" (by decide) (by decide) (by decide) (by decide)]; simpa using hxT
        simp [this, h1len, hnxl]
      refine runs_wset hfitx ?_
      have hfitc : fit st1.cap 1 = some 1 := by rw [h1cap]; simpa using hfit1
      have hc1 : st1.w "pt.c" = c := by
        rw [h1reg "pt.c" (by decide) (by decide) (by decide) (by decide)]; simpa using hrc
      refine runs_wset (a := c - 1) (by simp [hc1, hfitc]) ?_
      refine ⟨c - 1, by omega, ?_⟩
      refine ⟨by omega, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro hc1
        rw [hm1]
        have hlt : m + 1 < T.length := by omega
        rw [List.getElem?_eq_getElem hlt]
        simp only [State.charge_w, State.setW_w, String.reduceEq, if_false, if_true]
        rw [h1arr "pt.nx" _ (by decide) (by decide)]
        simp only [State.charge_wa]
        rw [harr "pt.nx" _ (by decide) (by decide)]
        exact congrArg some (hnx st0 rfl hlt).symm
      · rw [hm1, hfilt, if_pos hP']
        refine SegAt.snoc hseg ?_ ?_
        · simp only [State.charge_wa, State.setW_wa]; rw [← hgv]; exact h1GV
        · intro i hi
          simp only [State.charge_wa, State.setW_wa]
          exact h1GVf (gs + i) (by rw [hgv]; omega)
      · simp only [State.charge_w, State.setW_w, String.reduceEq, if_false]
        rw [h1gv, hgv, hm1, hfilt, if_pos hP', List.length_append]
        simp only [List.length_singleton]
        omega
      · intro y hy
        simp only [State.charge_wa, State.setW_wa]
        rw [hm1, hfilt, if_pos hP']
        by_cases hyx : y = x
        · subst hyx; rw [h1as]; simp
        · rw [h1asf y hyx]
          simp only [State.charge_wa]
          rw [has y hy]
          simp [Finset.mem_union, List.mem_toFinset, List.mem_append, hyx]
      · intro j hj
        simp only [State.charge_wa, State.setW_wa]
        rw [h1GVf j (by rw [hgv]; omega)]; exact hGVold j hj
      · intro arr j h1' h2'
        simp only [State.charge_wa, State.setW_wa]
        rw [h1arr arr j h1' h2']; exact harr arr j h1' h2'
      · intro y y1 y2 y3 y4 y5 y6
        simp only [State.charge_w, State.setW_w, if_neg y1, if_neg y2]
        rw [h1reg y y4 y5 y6 y3]; exact hreg y y1 y2 y3 y4 y5 y6
      · simp [h1len, hlen]
      · simp [h1cap, hcapst]
      · simp only [State.charge_cost, State.setW_cost]
        have : st1.cost ≤ st.cost + 1 + 12 := by simpa using h1cost
        omega
    · -- skip `x`
      have hno : ¬ ((st.charge 1).wa "fp.inS" x = 1 ∧ (st.charge 1).wa "fp.inQ" x = 0 ∧
          (st.charge 1).wa "pt.as" x = 0) := by
        rintro ⟨h1, h2, h3⟩
        apply hP
        simp only [State.charge_wa] at h1 h2 h3
        rw [hSx] at h1; rw [hQx] at h2; rw [hAx] at h3
        refine ⟨?_, ?_, ?_⟩
        · by_contra h; simp [h] at h1
        · intro h; simp [h] at h2
        · intro h; simp [h] at h3
      apply runs_seq
      refine Runs.mono (testAdd_no (ops := ops) (st := st.charge 1) (x := x) (by simpa using hxT) hNl'
        (by simpa using hcap1) hno) ?_
      rintro st1 ⟨h1wa, h1reg, h1len, h1cap, h1cost⟩
      apply runs_seq
      have hfitx : evalW st1 (.load "pt.nx" (.var "pt.x")) = some (st1.wa "pt.nx" x) := by
        have : st1.w "pt.x" = x := by
          rw [h1reg "pt.x" (by decide) (by decide) (by decide)]; simpa using hxT
        simp [this, h1len, hnxl]
      refine runs_wset hfitx ?_
      have hfitc : fit st1.cap 1 = some 1 := by rw [h1cap]; simpa using hfit1
      have hc1 : st1.w "pt.c" = c := by
        rw [h1reg "pt.c" (by decide) (by decide) (by decide)]; simpa using hrc
      refine runs_wset (a := c - 1) (by simp [hc1, hfitc]) ?_
      refine ⟨c - 1, by omega, ?_⟩
      refine ⟨by omega, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro hc1
        rw [hm1]
        have hlt : m + 1 < T.length := by omega
        rw [List.getElem?_eq_getElem hlt]
        simp only [State.charge_w, State.setW_w, String.reduceEq, if_false, if_true]
        rw [h1wa]; simp only [State.charge_wa]
        rw [harr "pt.nx" _ (by decide) (by decide)]
        exact congrArg some (hnx st0 rfl hlt).symm
      · rw [hm1, hfilt, if_neg hP, List.append_nil]
        intro i hi; simp only [State.charge_wa, State.setW_wa]; rw [h1wa]; exact hseg i hi
      · simp only [State.charge_w, State.setW_w, String.reduceEq, if_false]
        rw [h1reg "pt.gv" (by decide) (by decide) (by decide), hm1, hfilt, if_neg hP, List.append_nil]
        simpa using hgv
      · intro y hy
        simp only [State.charge_wa, State.setW_wa]
        rw [hm1, hfilt, if_neg hP, List.append_nil, h1wa]
        exact has y hy
      · intro j hj
        simp only [State.charge_wa, State.setW_wa]; rw [h1wa]; exact hGVold j hj
      · intro arr j h1' h2'
        simp only [State.charge_wa, State.setW_wa]; rw [h1wa]; exact harr arr j h1' h2'
      · intro y y1 y2 y3 y4 y5 y6
        simp only [State.charge_w, State.setW_w, if_neg y1, if_neg y2]
        rw [h1reg y y4 y5 y6]; exact hreg y y1 y2 y3 y4 y5 y6
      · simp [h1len, hlen]
      · simp [h1cap, hcapst]
      · simp only [State.charge_cost, State.setW_cost]
        have : st1.cost ≤ st.cost + 1 + 12 := by simpa using h1cost
        omega
  · intro hx
    have hc0 : c = 0 := by by_contra h; simp [Nat.pos_of_ne_zero h] at hx
    subst hc0
    simp only [Nat.sub_zero, List.take_length] at hseg hgv has
    exact ⟨hseg, by simpa using hgv, fun x hx => by simpa using has x hx, hGVold, harr, hreg, hlen, hcapst,
      by simp; omega⟩


/-! ## One piece of MakePivots -/

/-- The groups `Gs` are stored as compact consecutive segments of `pt.GV`. -/
def GrpOut (st : State V) (Gs : List (List ℕ)) : Prop :=
  st.w "pt.ng" = Gs.length ∧ st.w "pt.gv" = (Gs.map List.length).sum ∧
  ∀ j (h : j < Gs.length), st.wa "pt.GO" j = ((Gs.take j).map List.length).sum ∧
    st.wa "pt.GL" j = Gs[j].length ∧ SegAt st "pt.GV" (((Gs.take j).map List.length).sum) Gs[j]

/-- For a duplicate-free piece, MakePivots' step appends exactly the filtered piece (if nonempty). -/
theorem mpStep_nodup (S Q : Finset ℕ) (acc : List (List ℕ) × Finset ℕ) {F : List ℕ} (hnd : F.Nodup) :
    mpStep S Q acc F =
      if F.filter (mpP S Q acc.2) = [] then acc
      else (acc.1 ++ [F.filter (mpP S Q acc.2)], acc.2 ∪ (F.filter (mpP S Q acc.2)).toFinset) := by
  have hf : F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2)) = F.filter (mpP S Q acc.2) := by
    apply List.filter_congr; intro x _
    unfold mpP
    by_cases h1 : x ∈ S <;> by_cases h2 : x ∈ Q <;> by_cases h3 : x ∈ acc.2 <;> simp [h1, h2, h3]
  unfold mpStep
  simp only
  rw [hf, List.Nodup.dedup (hnd.filter _)]

/-- Registers written by MakePivots. -/
def mpRegs : List String := ["pt.gs", "pt.x", "pt.c", "pt.gv", "pt.tS", "pt.tQ", "pt.tA", "pt.ng", "pt.g"]

theorem pieceBody_spec {st : State V} {S Q : Finset ℕ} {N g : ℕ} {F : List ℕ}
    {acc : List (List ℕ) × Finset ℕ}
    (hPR : PieceRep st g F) (hnd : F.Nodup) (hN : ∀ x ∈ F, x < N)
    (hrg : st.w "pt.g" = g)
    (hgl : g < st.wlen "pt.PT" ∧ g < st.wlen "pt.PF" ∧ g < st.wlen "pt.PN")
    (hG : GrpOut st acc.1) (hA : BitRep st "pt.as" acc.2 N)
    (hSb : BitRep st "fp.inS" S N) (hQb : BitRep st "fp.inQ" Q N)
    (hNl : N ≤ st.wlen "fp.inS" ∧ N ≤ st.wlen "fp.inQ" ∧ N ≤ st.wlen "pt.as" ∧ N ≤ st.wlen "pt.nx")
    (hGV : (acc.1.map List.length).sum + F.length ≤ st.wlen "pt.GV")
    (hGOL : acc.1.length < st.wlen "pt.GO" ∧ acc.1.length < st.wlen "pt.GL")
    (hcap : (acc.1.map List.length).sum + F.length + 2 < st.cap ∧ acc.1.length + 1 < st.cap ∧ g + 1 < st.cap) :
    Runs ops pieceBody st (fun st' =>
      GrpOut st' (mpStep S Q acc F).1 ∧ BitRep st' "pt.as" (mpStep S Q acc F).2 N ∧ st'.w "pt.g" = g + 1 ∧
      (∀ arr j, arr ≠ "pt.as" → arr ≠ "pt.GV" → arr ≠ "pt.GO" → arr ≠ "pt.GL" → st'.wa arr j = st.wa arr j) ∧
      (∀ y, y ∉ mpRegs → st'.w y = st.w y) ∧ st'.wlen = st.wlen ∧ st'.cap = st.cap ∧
      st'.cost ≤ st.cost + 16 * F.length + 40) := by
  classical
  obtain ⟨hG1, hG2, hG3⟩ := hG
  obtain ⟨hc1, hc2, hc3⟩ := hcap
  obtain ⟨top, T, rfl⟩ : ∃ top T, F = top :: T := by
    cases F with
    | nil => exact absurd rfl hPR.ne
    | cons a t => exact ⟨a, t, rfl⟩
  have htop : st.wa "pt.PT" g = top := hPR.top
  have hPN : st.wa "pt.PN" g = T.length := hPR.pn
  set gs := (acc.1.map List.length).sum with hgs
  set P := mpP S Q acc.2 with hPdef
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt (by omega)
  have hcapx : 1 < st.cap := by omega
  -- gs := gv ; x := PT[g]
  apply runs_seq
  refine runs_wset (a := gs) (by simp [hG2]) ?_
  apply runs_seq
  refine runs_wset (a := top) (by simp [hrg, hgl.1, htop]) ?_
  set st1 := (((st.setW "pt.gs" gs).charge 1).setW "pt.x" top).charge 1 with hst1
  have h1w : ∀ y, y ≠ "pt.gs" → y ≠ "pt.x" → st1.w y = st.w y := by intro y a b; simp [hst1, a, b]
  have h1wa : st1.wa = st.wa := rfl
  have h1len : st1.wlen = st.wlen := rfl
  have h1cap : st1.cap = st.cap := rfl
  have htopN := hN top List.mem_cons_self
  have hNl1 : top < st1.wlen "fp.inS" ∧ top < st1.wlen "fp.inQ" ∧ top < st1.wlen "pt.as" := by
    rw [h1len]; exact ⟨by omega, by omega, by omega⟩
  -- the top
  have htopA : st1.wa "pt.as" top = if top ∈ acc.2 then 1 else 0 := by rw [h1wa]; exact hA top htopN
  apply runs_seq
  have hmid : ∀ st2 : State V,
      SegAt st2 "pt.GV" gs ([top].filter P) → st2.w "pt.gv" = gs + ([top].filter P).length →
      BitRep st2 "pt.as" (acc.2 ∪ ([top].filter P).toFinset) N →
      (∀ j < gs, st2.wa "pt.GV" j = st.wa "pt.GV" j) →
      (∀ arr j, arr ≠ "pt.as" → arr ≠ "pt.GV" → st2.wa arr j = st.wa arr j) →
      (∀ y, y ≠ "pt.tS" → y ≠ "pt.tQ" → y ≠ "pt.tA" → y ≠ "pt.gv" → st2.w y = st1.w y) →
      st2.wlen = st.wlen → st2.cap = st.cap → st2.cost ≤ st.cost + 2 + 12 →
      Runs ops (.seq (.wset "pt.x" (.load "pt.PF" (.var "pt.g"))) <|
        .seq (.wset "pt.c" (.load "pt.PN" (.var "pt.g"))) <|
        .seq tailLoop <|
        .seq (.ite (.lt (.var "pt.gs") (.var "pt.gv"))
          (.seq (.wstore "pt.GO" (.var "pt.ng") (.var "pt.gs")) <|
           .seq (.wstore "pt.GL" (.var "pt.ng") (.sub (.var "pt.gv") (.var "pt.gs")))
                (.wset "pt.ng" (.add (.var "pt.ng") (.lit 1))))
          .skip)
        (.wset "pt.g" (.add (.var "pt.g") (.lit 1)))) st2 (fun st' =>
        GrpOut st' (mpStep S Q acc (top :: T)).1 ∧ BitRep st' "pt.as" (mpStep S Q acc (top :: T)).2 N ∧
        st'.w "pt.g" = g + 1 ∧
        (∀ arr j, arr ≠ "pt.as" → arr ≠ "pt.GV" → arr ≠ "pt.GO" → arr ≠ "pt.GL" → st'.wa arr j = st.wa arr j) ∧
        (∀ y, y ∉ mpRegs → st'.w y = st.w y) ∧ st'.wlen = st.wlen ∧ st'.cap = st.cap ∧
        st'.cost ≤ st.cost + 16 * (top :: T).length + 40) := by
    intro st2 h2seg h2gv h2as h2GVo h2arr h2reg h2len h2cap h2cost
    have hfit1' : fit st2.cap 1 = some 1 := by rw [h2cap]; exact hfit1
    have h2g : st2.w "pt.g" = g := by
      rw [h2reg _ (by decide) (by decide) (by decide) (by decide), h1w _ (by decide) (by decide)]; exact hrg
    have hPF : st2.wa "pt.PF" g = st.wa "pt.PF" g := h2arr _ _ (by decide) (by decide)
    have hPN2 : st2.wa "pt.PN" g = T.length := by rw [h2arr _ _ (by decide) (by decide)]; exact hPN
    -- x := PF[g] ; c := PN[g]
    apply runs_seq
    refine runs_wset (a := st2.wa "pt.PF" g) (by simp [h2g, h2len, hgl.2.1]) ?_
    apply runs_seq
    refine runs_wset (a := T.length) (by simp [h2g, h2len, hgl.2.2, hPN2]) ?_
    set st3 := (((st2.setW "pt.x" (st2.wa "pt.PF" g)).charge 1).setW "pt.c" T.length).charge 1 with hst3
    have h3wa : st3.wa = st2.wa := rfl
    -- the tail walk
    have hLL3 : LL st3 "pt.nx" T := by
      have := hPR.ll
      simp only [List.tail_cons] at this
      refine LL.frame this (fun j _ => ?_)
      rw [h3wa, h2arr _ _ (by decide) (by decide)]
    apply runs_seq
    refine Runs.mono (tailLoop_spec (ops := ops) (st0 := st3) (S := S) (Q := Q) (A := acc.2) (N := N)
      (gs := gs) (top := top) (T := T) (c0 := st3.cost + 16 * T.length) hnd hLL3
      (fun x hx => by rw [h3wa, h2arr _ _ (by decide) (by decide)]; exact hSb x hx)
      (fun x hx => by rw [h3wa, h2arr _ _ (by decide) (by decide)]; exact hQb x hx)
      hN (by simp only [hst3, State.charge_wlen, State.setW_wlen]; rw [h2len]; exact hNl)
      (by simp only [hst3, State.charge_wlen, State.setW_wlen]; rw [h2len]; simp at hGV; omega)
      (by simp only [hst3, State.charge_cap, State.setW_cap]; rw [h2cap]; simp at hc1; omega)
      T.length st3 ?_) ?_
    · refine ⟨le_rfl, by simp [hst3], ?_, ?_, ?_, ?_, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl,
        rfl, rfl, le_rfl⟩
      · intro hT0
        simp only [Nat.sub_self]
        have hTne : T ≠ [] := List.ne_nil_of_length_pos hT0
        rw [List.getElem?_eq_getElem hT0]
        simp only [hst3, State.charge_w, State.setW_w, String.reduceEq, if_false, if_true]
        rw [hPF, hPR.pf (by simpa using hTne)]
        cases T with
        | nil => exact absurd rfl hTne
        | cons a t => rfl
      · simp only [Nat.sub_self, List.take_zero]
        intro i hi; rw [h3wa]; exact h2seg i hi
      · simp only [Nat.sub_self, List.take_zero, hst3, State.charge_w, State.setW_w, String.reduceEq, if_false]
        exact h2gv
      · simp only [Nat.sub_self, List.take_zero]
        intro y hy; rw [h3wa]; exact h2as y hy
    rintro st4 ⟨h4seg, h4gv, h4as, h4GVo, h4arr, h4reg, h4len, h4cap, h4cost⟩
    set cur := (top :: T).filter P with hcur
    have h4gs : st4.w "pt.gs" = gs := by
      rw [h4reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp only [hst3, State.charge_w, State.setW_w, String.reduceEq, if_false]
      rw [h2reg _ (by decide) (by decide) (by decide) (by decide)]; simp [hst1]
    have h4ng : st4.w "pt.ng" = acc.1.length := by
      rw [h4reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp only [hst3, State.charge_w, State.setW_w, String.reduceEq, if_false]
      rw [h2reg _ (by decide) (by decide) (by decide) (by decide), h1w _ (by decide) (by decide)]; exact hG1
    have h4g : st4.w "pt.g" = g := by
      rw [h4reg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp only [hst3, State.charge_w, State.setW_w, String.reduceEq, if_false]
      exact h2g
    have h4cap' : st4.cap = st.cap := by rw [h4cap]; simp [hst3, h2cap]
    have h4len' : st4.wlen = st.wlen := by rw [h4len]; simp [hst3, h2len]
    have h4GV : ∀ j < gs, st4.wa "pt.GV" j = st.wa "pt.GV" j := fun j hj => by
      rw [h4GVo j hj, h3wa, h2GVo j hj]
    have h4arr' : ∀ arr j, arr ≠ "pt.as" → arr ≠ "pt.GV" → st4.wa arr j = st.wa arr j := fun arr j a b => by
      rw [h4arr arr j a b, h3wa, h2arr arr j a b]
    -- old segments live below `gs`
    have hold : ∀ j (h : j < acc.1.length), ((acc.1.take j).map List.length).sum + acc.1[j].length ≤ gs := by
      intro j h
      rw [hgs]
      have e := List.sum_take_succ (acc.1.map List.length) j (by simpa using h)
      simp only [List.getElem_map] at e
      rw [← List.map_take, ← List.map_take] at e
      have hsub := List.take_sublist (j + 1) acc.1
      have := (hsub.map List.length).sum_le_sum (fun _ _ => Nat.zero_le _)
      omega
    have hmp := mpStep_nodup S Q acc hnd
    have hfitg : fit st4.cap (g + 1) = some (g + 1) := fit_of_lt (by rw [h4cap']; omega)
    have hfit1 : fit st4.cap 1 = some 1 := fit_of_lt (by rw [h4cap']; omega)
    have hfit0 : fit st4.cap 0 = some 0 := fit_of_lt (by rw [h4cap']; omega)
    -- the regs frame from `st` to `st4` outside the MakePivots registers
    have h4w : ∀ y, y ∉ mpRegs → st4.w y = st.w y := by
      intro y hy
      simp only [mpRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9⟩ := hy
      rw [h4reg y y2 y3 y4 y5 y6 y7]
      simp only [hst3, State.charge_w, State.setW_w, if_neg y2, if_neg y3]
      rw [h2reg y y5 y6 y7 y4, h1w y y1 y2]
    by_cases hc0 : cur = []
    · -- empty group: nothing recorded
      rw [if_pos hc0] at hmp
      apply runs_seq
      refine runs_ite_false (by simp [h4gs, h4gv, hc0, hfit0]) (runs_skip ?_)
      refine runs_wset (a := g + 1) (by simp [h4g, hfitg, hfit1]) ?_
      rw [hmp]
      refine ⟨⟨?_, ?_, ?_⟩, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [State.charge_w, State.setW_w, String.reduceEq, if_false]; exact h4ng
      · simp only [State.charge_w, State.setW_w, String.reduceEq, if_false]; rw [h4gv, hc0]; simp [hgs]
      · intro j h
        obtain ⟨a1, a2, a3⟩ := hG3 j h
        simp only [State.charge_wa, State.setW_wa]
        refine ⟨by rw [h4arr' _ _ (by decide) (by decide)]; exact a1,
          by rw [h4arr' _ _ (by decide) (by decide)]; exact a2, ?_⟩
        intro i hi
        simp only [State.charge_wa, State.setW_wa]
        rw [h4GV (((acc.1.take j).map List.length).sum + i) (by have := hold j h; omega)]; exact a3 i hi
      · intro y hy; simp only [State.charge_wa, State.setW_wa]; rw [h4as y hy, hc0]; simp
      · intro arr j a b c d; simp only [State.charge_wa, State.setW_wa]; exact h4arr' arr j a b
      · intro y hy
        have hyg : y ≠ "pt.g" := by intro h; apply hy; simp [mpRegs, h]
        simp only [State.charge_w, State.setW_w, if_neg hyg]
        exact h4w y hy
      · simp [h4len']
      · simp [h4cap']
      · simp only [State.charge_cost, State.setW_cost]
        have : st3.cost = st2.cost + 2 := by simp [hst3]
        simp only [List.length_cons] at h4cost ⊢
        omega
    · -- nonempty group: record it
      have hlt : gs < gs + cur.length := by
        have := List.length_pos_of_ne_nil hc0; omega
      rw [if_neg hc0] at hmp
      have hGOl : acc.1.length < st4.wlen "pt.GO" := by rw [h4len']; exact hGOL.1
      have hGLl : acc.1.length < st4.wlen "pt.GL" := by rw [h4len']; exact hGOL.2
      have hfitng : fit st4.cap (acc.1.length + 1) = some (acc.1.length + 1) :=
        fit_of_lt (by rw [h4cap']; omega)
      apply runs_seq
      refine runs_ite_true (x := 1) (by simp [h4gs, h4gv, hlt, hfit1]) one_ne_zero ?_
      apply runs_seq
      refine runs_wstore (j := acc.1.length) (a := gs) (by simp [h4ng]) (by simp [h4gs]) (by simpa using hGOl) ?_
      apply runs_seq
      refine runs_wstore (j := acc.1.length) (a := cur.length) (by simp [h4ng]) (by simp [h4gv, h4gs])
        (by simpa using hGLl) ?_
      refine runs_wset (a := acc.1.length + 1) (by simp [h4ng, hfit1, hfitng]) ?_
      refine runs_wset (a := g + 1) (by simp [h4g, hfitg, hfit1]) ?_
      rw [hmp]
      have hlen1 : (acc.1 ++ [cur]).length = acc.1.length + 1 := by simp
      refine ⟨⟨?_, ?_, ?_⟩, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [State.charge_w, State.setW_w, State.storeW_w, String.reduceEq, if_false, if_true]
        exact hlen1.symm
      · simp only [State.charge_w, State.setW_w, State.storeW_w, String.reduceEq, if_false]
        rw [h4gv]; simp [hgs, hcur, hPdef]
      · intro j h
        rw [hlen1] at h
        simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
        by_cases hj : j < acc.1.length
        · obtain ⟨a1, a2, a3⟩ := hG3 j hj
          have hne : j ≠ acc.1.length := by omega
          rw [List.take_append_of_le_length (by omega), List.getElem_append_left hj]
          refine ⟨?_, ?_, ?_⟩
          · simp only [String.reduceEq, false_and, if_false, hne, and_false, true_and]
            rw [h4arr' _ _ (by decide) (by decide)]; exact a1
          · simp only [String.reduceEq, false_and, if_false, hne, and_false, true_and]
            rw [h4arr' _ _ (by decide) (by decide)]; exact a2
          · intro i hi
            simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
            rw [h4GV (((acc.1.take j).map List.length).sum + i) (by have := hold j hj; omega)]; exact a3 i hi
        · have hj' : j = acc.1.length := by omega
          subst hj'
          rw [List.take_left, List.getElem_append_right (by simp)]
          simp only [Nat.sub_self, List.getElem_cons_zero, String.reduceEq, false_and, if_false, and_self,
            if_true, true_and]
          refine ⟨by rw [← hgs], rfl, ?_⟩
          intro i hi
          simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
          rw [← hgs]; exact h4seg i hi
      · intro y hy
        simp only [State.charge_wa, State.setW_wa, State.storeW_wa, String.reduceEq, false_and, if_false]
        exact h4as y hy
      · intro arr j a b c d
        simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
        rw [if_neg (by rintro ⟨h, -⟩; exact d h), if_neg (by rintro ⟨h, -⟩; exact c h)]
        exact h4arr' arr j a b
      · intro y hy
        have hyg : y ≠ "pt.g" := by intro h; apply hy; simp [mpRegs, h]
        have hyn : y ≠ "pt.ng" := by intro h; apply hy; simp [mpRegs, h]
        simp only [State.charge_w, State.setW_w, State.storeW_w, if_neg hyg, if_neg hyn]
        exact h4w y hy
      · simp [h4len']
      · simp [h4cap']
      · simp only [State.charge_cost, State.setW_cost, State.storeW_cost]
        have : st3.cost = st2.cost + 2 := by simp [hst3]
        simp only [List.length_cons] at h4cost ⊢
        omega
  by_cases hPt : P top
  · obtain ⟨hS, hQ, hAt⟩ := hPt
    refine Runs.mono (testAdd_yes (ops := ops) (st := st1) (x := top) (gv := gs) (by simp [hst1])
      (by rw [h1w _ (by decide) (by decide)]; exact hG2)
      (by rw [h1wa, hSb top htopN]; simp [hS]) (by rw [h1wa, hQb top htopN]; simp [hQ])
      (by rw [htopA]; simp [hAt]) hNl1 (by rw [h1len]; simp at hGV; omega) (by rw [h1cap]; simp at hc1; omega)) ?_
    rintro st2 ⟨h2as, h2GV, h2gv, h2asf, h2GVf, h2arr, h2reg, h2len, h2cap, h2cost⟩
    have hPt' : P top := ⟨hS, hQ, hAt⟩
    refine hmid st2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [List.filter_singleton, decide_eq_true hPt', cond_true]
      intro i hi; simp at hi; subst hi; simpa using h2GV
    · rw [h2gv]; simp only [List.filter_singleton, decide_eq_true hPt', cond_true]; simp
    · intro y hy
      simp only [List.filter_singleton, decide_eq_true hPt', cond_true]
      by_cases hyt : y = top
      · subst hyt; rw [h2as]; simp
      · rw [h2asf y hyt, h1wa, hA y hy]; simp [hyt]
    · intro j hj; rw [h2GVf j (by omega), h1wa]
    · intro arr j a b; rw [h2arr arr j a b, h1wa]
    · intro y a b c d; exact h2reg y a b c d
    · rw [h2len, h1len]
    · rw [h2cap, h1cap]
    · have : st1.cost = st.cost + 2 := by simp [hst1]
      omega
  · have hno : ¬ (st1.wa "fp.inS" top = 1 ∧ st1.wa "fp.inQ" top = 0 ∧ st1.wa "pt.as" top = 0) := by
      rintro ⟨h1, h2, h3⟩
      apply hPt
      rw [h1wa, hSb top htopN] at h1; rw [h1wa, hQb top htopN] at h2; rw [htopA] at h3
      refine ⟨?_, ?_, ?_⟩
      · by_contra h; simp [h] at h1
      · intro h; simp [h] at h2
      · intro h; simp [h] at h3
    refine Runs.mono (testAdd_no (ops := ops) (st := st1) (x := top) (by simp [hst1]) hNl1
      (by rw [h1cap]; exact hcapx) hno) ?_
    rintro st2 ⟨h2wa, h2reg, h2len, h2cap, h2cost⟩
    refine hmid st2 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [List.filter_singleton, decide_eq_false hPt, cond_false]; intro i hi; simp at hi
    · rw [h2reg "pt.gv" (by decide) (by decide) (by decide), h1w "pt.gv" (by decide) (by decide)]
      simp only [List.filter_singleton, decide_eq_false hPt, cond_false]; simpa using hG2
    · simp only [List.filter_singleton, decide_eq_false hPt, cond_false]; intro y hy; rw [h2wa, h1wa, hA y hy]; simp
    · intro j _; rw [h2wa, h1wa]
    · intro arr j _ _; rw [h2wa, h1wa]
    · intro y a b c _; exact h2reg y a b c
    · rw [h2len, h1len]
    · rw [h2cap, h1cap]
    · have : st1.cost = st.cost + 2 := by simp [hst1]
      omega


/-! ## The MakePivots loop over all pieces -/

theorem GrpOut.charge {st : State V} {Gs : List (List ℕ)} (h : GrpOut st Gs) (k : ℕ) : GrpOut (st.charge k) Gs := h

/-- Invariant of the MakePivots loop after `g` pieces. -/
def MPI (st0 : State V) (S Q : Finset ℕ) (N : ℕ) (pcs : List (List ℕ)) (c0 : ℕ) (n : ℕ) (st : State V) : Prop :=
  n ≤ pcs.length ∧ st.w "pt.g" = pcs.length - n ∧
  GrpOut st ((pcs.take (pcs.length - n)).foldl (mpStep S Q) ([], ∅)).1 ∧
  BitRep st "pt.as" ((pcs.take (pcs.length - n)).foldl (mpStep S Q) ([], ∅)).2 N ∧
  (∀ arr j, arr ≠ "pt.as" → arr ≠ "pt.GV" → arr ≠ "pt.GO" → arr ≠ "pt.GL" → st.wa arr j = st0.wa arr j) ∧
  (∀ y, y ∉ mpRegs → st.w y = st0.w y) ∧ st.wlen = st0.wlen ∧ st.cap = st0.cap ∧
  st.cost + ((pcs.drop (pcs.length - n)).map (fun F => 16 * F.length + 42)).sum ≤ c0

/-- The accumulated groups' total length is at most the pieces' total length. -/
theorem mp_total_le (S Q : Finset ℕ) (pcs : List (List ℕ)) :
    (((pcs.foldl (mpStep S Q) ([], ∅)).1).map List.length).sum ≤ (pcs.map List.length).sum := by
  induction pcs using List.reverseRecOn with
  | nil => simp
  | append_singleton pcs F ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := pcs.foldl (mpStep S Q) ([], ∅)
    unfold mpStep
    simp only
    split_ifs
    · simp [List.map_append, List.sum_append]; omega
    · simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have : (F.filter (fun x => decide (x ∈ S ∧ x ∉ Q ∧ x ∉ acc.2))).dedup.length ≤ F.length :=
        (List.dedup_sublist _).length_le.trans (List.length_filter_le _ _)
      omega

/-- The number of groups is at most the number of pieces. -/
theorem mp_count_le (S Q : Finset ℕ) (pcs : List (List ℕ)) :
    ((pcs.foldl (mpStep S Q) ([], ∅)).1).length ≤ pcs.length := (mpInv_fold S Q pcs).count

theorem mpLoop_spec {st0 : State V} {S Q : Finset ℕ} {N : ℕ} {pcs : List (List ℕ)} {c0 : ℕ}
    (hPR : PiecesRep st0 0 pcs) (hnd : ∀ F ∈ pcs, F.Nodup) (hN : ∀ F ∈ pcs, ∀ x ∈ F, x < N)
    (hnp : st0.w "pt.np" = pcs.length)
    (hpl : pcs.length ≤ st0.wlen "pt.PT" ∧ pcs.length ≤ st0.wlen "pt.PF" ∧ pcs.length ≤ st0.wlen "pt.PN")
    (hSb : BitRep st0 "fp.inS" S N) (hQb : BitRep st0 "fp.inQ" Q N)
    (hNl : N ≤ st0.wlen "fp.inS" ∧ N ≤ st0.wlen "fp.inQ" ∧ N ≤ st0.wlen "pt.as" ∧ N ≤ st0.wlen "pt.nx")
    (hGV : (pcs.map List.length).sum ≤ st0.wlen "pt.GV")
    (hGOL : pcs.length ≤ st0.wlen "pt.GO" ∧ pcs.length ≤ st0.wlen "pt.GL")
    (hcap : (pcs.map List.length).sum + 2 < st0.cap ∧ pcs.length + 1 < st0.cap) :
    ∀ n st, MPI st0 S Q N pcs c0 n st → Runs ops mpLoop st (fun st' =>
      GrpOut st' (makePivots S Q pcs) ∧ BitRep st' "pt.as" ((pcs.foldl (mpStep S Q) ([], ∅)).2) N ∧
      (∀ arr j, arr ≠ "pt.as" → arr ≠ "pt.GV" → arr ≠ "pt.GO" → arr ≠ "pt.GL" → st'.wa arr j = st0.wa arr j) ∧
      (∀ y, y ∉ mpRegs → st'.w y = st0.w y) ∧ st'.wlen = st0.wlen ∧ st'.cap = st0.cap ∧ st'.cost ≤ c0 + 1) := by
  apply runs_while_nat
  intro n st hMP
  obtain ⟨hnle, hrg, hG, hA, harr, hreg, hlen, hcapst, hcost⟩ := hMP
  have hcap1 : 1 < st.cap := by rw [hcapst]; omega
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  have hnp' : st.w "pt.np" = pcs.length := by rw [hreg _ (by simp [mpRegs])]; exact hnp
  refine ⟨if pcs.length - n < pcs.length then 1 else 0, ?_, ?_, ?_⟩
  · simp only [evalW_lt', evalW_var, hrg, hnp', Option.bind_some]
    split_ifs <;> simp [hfit1, fit_of_lt (show 0 < st.cap by omega)]
  · intro hx
    have hn0 : 0 < n := by
      by_contra h; have : n = 0 := by omega
      subst this; simp at hx
    set g := pcs.length - n with hg
    have hgl : g < pcs.length := by omega
    set F := pcs[g] with hF
    have hFmem : F ∈ pcs := List.getElem_mem hgl
    set acc := (pcs.take g).foldl (mpStep S Q) ([], ∅) with hacc
    have hPRg : PieceRep (st.charge 1) g F := by
      have := hPR g hgl
      simp only [Nat.zero_add] at this
      refine PieceRep.frame this ?_ ?_ ?_ ?_ ?_
      · exact harr _ _ (by decide) (by decide) (by decide) (by decide)
      · exact harr _ _ (by decide) (by decide) (by decide) (by decide)
      · exact harr _ _ (by decide) (by decide) (by decide) (by decide)
      · exact harr _ _ (by decide) (by decide) (by decide) (by decide)
      · intro j _; exact harr _ _ (by decide) (by decide) (by decide) (by decide)
    have htot : (acc.1.map List.length).sum ≤ ((pcs.take g).map List.length).sum := mp_total_le S Q (pcs.take g)
    have hcnt : acc.1.length ≤ (pcs.take g).length := mp_count_le S Q (pcs.take g)
    have hsum_split : ((pcs.take g).map List.length).sum + F.length ≤ (pcs.map List.length).sum := by
      have h1 : pcs = pcs.take g ++ F :: pcs.drop (g + 1) := by
        rw [hF, ← List.drop_eq_getElem_cons hgl, List.take_append_drop]
      have h2 : (pcs.map List.length).sum = ((pcs.take g).map List.length).sum +
          (F.length + ((pcs.drop (g + 1)).map List.length).sum) := by
        conv_lhs => rw [h1]
        simp [List.sum_append]
      omega
    have htakel : (pcs.take g).length = g := by simp; omega
    refine Runs.mono (pieceBody_spec (ops := ops) (st := st.charge 1) (S := S) (Q := Q) (N := N) (g := g)
      (F := F) (acc := acc) hPRg (hnd F hFmem) (hN F hFmem) (by simpa using hrg)
      (by simp only [State.charge_wlen]; rw [hlen]; exact ⟨by omega, by omega, by omega⟩) hG hA
      (fun x hx => by simp only [State.charge_wa]; rw [harr _ _ (by decide) (by decide) (by decide) (by decide)]
                      exact hSb x hx)
      (fun x hx => by simp only [State.charge_wa]; rw [harr _ _ (by decide) (by decide) (by decide) (by decide)]
                      exact hQb x hx)
      (by simp only [State.charge_wlen]; rw [hlen]; exact hNl)
      (by simp only [State.charge_wlen]; rw [hlen]; omega)
      (by simp only [State.charge_wlen]; rw [hlen]; exact ⟨by omega, by omega⟩)
      (by simp only [State.charge_cap]; rw [hcapst]; exact ⟨by omega, by omega, by omega⟩)) ?_
    rintro st' ⟨h1G, h1A, h1g, h1arr, h1reg, h1len, h1cap, h1cost⟩
    have htk : pcs.length - (n - 1) = g + 1 := by omega
    have hfold : (pcs.take (g + 1)).foldl (mpStep S Q) ([], ∅) = mpStep S Q acc F := by
      rw [List.take_add_one, List.getElem?_eq_getElem hgl]
      simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    refine ⟨n - 1, by omega, by omega, by rw [h1g, htk], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [htk, hfold]; exact h1G
    · rw [htk, hfold]; exact h1A
    · intro arr j a b c d; rw [h1arr arr j a b c d]; exact harr arr j a b c d
    · intro y hy; rw [h1reg y hy]; exact hreg y hy
    · simp [h1len, hlen]
    · simp [h1cap, hcapst]
    · rw [htk]
      have hdrop : pcs.drop g = F :: pcs.drop (g + 1) := by rw [hF]; exact List.drop_eq_getElem_cons hgl
      rw [hdrop] at hcost
      simp only [List.map_cons, List.sum_cons] at hcost
      have : st'.cost ≤ st.cost + 1 + 16 * F.length + 40 := by simpa using h1cost
      omega
  · intro hx
    have hn0 : n = 0 := by
      by_contra h; have : pcs.length - n < pcs.length := by omega
      simp [this] at hx
    subst hn0
    simp only [Nat.sub_zero, List.take_length] at hG hA
    refine ⟨GrpOut.charge hG 1, hA, harr, hreg, hlen, hcapst, ?_⟩
    · simp only [Nat.sub_zero, List.drop_length, List.map_nil, List.sum_nil, Nat.add_zero] at hcost
      simp; omega

end Frontier.CHD.PartitionRAM
