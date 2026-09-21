import Frontier.CHD.PartitionRAM

/-!
# Frontier.CHD.PartitionRAM2 — Layer B for the tree partition, part 2 (owner agent-03)

**NON-GATE.** The per-tree initialisation loop (`an[w] := 0` over the tree segment) and the per-tree block
(initialisation, Algorithm 5, root merge), refining `Partition.pieces` for one tree.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V}

/-! ## The initialisation loop -/

/-- One step: `i := i - 1; an[TV[b + i]] := 0`. -/
def initBody : Stmt :=
  .seq (.wset "pt.i" (.sub (.var "pt.i") (.lit 1)))
    (.wstore "pt.an" (.load "fp.TV" (.add (.var "pt.b") (.var "pt.i"))) (.lit 0))

/-- Clear the accumulator counts of the tree segment `fp.TV[b, b + i)`, from the top. -/
def initLoop : Stmt := .while (.lt (.lit 0) (.var "pt.i")) initBody

/-- Invariant of the initialisation loop at `pt.i = i`: positions `[i, len)` are cleared. -/
def IL (st0 : State V) (b : ℕ) (ord : List ℕ) (c0 : ℕ) (i : ℕ) (st : State V) : Prop :=
  i ≤ ord.length ∧ st.w "pt.i" = i ∧
  (∀ j (hj : j < ord.length), i ≤ j → st.wa "pt.an" ord[j] = 0) ∧
  (∀ j, j ∉ ord → st.wa "pt.an" j = st0.wa "pt.an" j) ∧
  (∀ arr j, arr ≠ "pt.an" → st.wa arr j = st0.wa arr j) ∧
  (∀ x, x ≠ "pt.i" → st.w x = st0.w x) ∧ st.wlen = st0.wlen ∧ st.cap = st0.cap ∧
  st.cost + 4 * i ≤ c0

theorem initLoop_spec {st0 : State V} {b : ℕ} {ord : List ℕ} (hnd : ord.Nodup) (hne : ord ≠ [])
    (hseg : ∀ j (h : j < ord.length), st0.wa "fp.TV" (b + j) = ord[j])
    (htv : b + ord.length ≤ st0.wlen "fp.TV") (hvl : ∀ x ∈ ord, x < st0.wlen "pt.an")
    (hcap : b + ord.length < st0.cap) (hb : st0.w "pt.b" = b) {c0 : ℕ} :
    ∀ i st, IL st0 b ord c0 i st → Runs ops initLoop st (fun st' =>
      (∀ w ∈ ord, st'.wa "pt.an" w = 0) ∧
      (∀ j, j ∉ ord → st'.wa "pt.an" j = st0.wa "pt.an" j) ∧
      (∀ arr j, arr ≠ "pt.an" → st'.wa arr j = st0.wa arr j) ∧
      (∀ x, x ≠ "pt.i" → st'.w x = st0.w x) ∧ st'.w "pt.i" = 0 ∧ st'.wlen = st0.wlen ∧
      st'.cap = st0.cap ∧ st'.cost ≤ c0 + 1) := by
  apply runs_while_nat
  intro i st hIL
  obtain ⟨hile, hri, hclr, han, harr, hreg, hlen, hcapst, hcost⟩ := hIL
  have hlen1 : 1 ≤ ord.length := List.length_pos_of_ne_nil hne
  have hcap1 : 1 < st.cap := by rw [hcapst]; omega
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  refine ⟨if 0 < i then 1 else 0, ?_, ?_, ?_⟩
  · simp only [evalW_lt', evalW_lit', evalW_var, hri, hfit0, Option.bind_some]
    split_ifs <;> simp [hfit0, hfit1]
  · intro hx
    have hi0 : 0 < i := by by_contra h; simp [h] at hx
    have hj : i - 1 < ord.length := by omega
    have hbj : b + (i - 1) < st.cap := by rw [hcapst]; omega
    have hfitb : fit st.cap (b + (i - 1)) = some (b + (i - 1)) := fit_of_lt hbj
    have hbreg : st.w "pt.b" = b := by rw [hreg _ (by decide)]; exact hb
    have htvj : st.wa "fp.TV" (b + (i - 1)) = ord[i - 1] := by rw [harr _ _ (by decide)]; exact hseg _ hj
    have htvl : b + (i - 1) < st.wlen "fp.TV" := by rw [hlen]; omega
    have hanl : ord[i - 1] < st.wlen "pt.an" := by rw [hlen]; exact hvl _ (List.getElem_mem hj)
    apply wp_sound
    simp only [initBody, wp, evalW_load', evalW_add', evalW_sub', evalW_var, evalW_lit', State.setW_w,
      State.charge_w, State.charge_wa, State.charge_wlen, State.charge_cap, State.setW_wa, State.setW_wlen,
      State.setW_cap, State.charge_cost, State.setW_cost, hri, hfit1, hfit0, Option.bind_some, if_pos rfl,
      hbreg, String.reduceEq, if_false, hfitb, htvl, if_true, htvj, hanl, true_and]
    refine ⟨i - 1, by omega, by omega, by simp, ?_, ?_, ?_, ?_, by simp [hlen], by simp [hcapst], ?_⟩
    · intro j hj' hij
      by_cases hjj : j = i - 1
      · subst hjj; simp
      · have hne : ord[j] ≠ ord[i - 1] := by
          intro heq
          exact hjj ((List.Nodup.getElem_inj_iff hnd).mp heq)
        simpa [hne] using hclr j hj' (by omega)
    · intro j hjo
      have hne : j ≠ ord[i - 1] := fun h => hjo (h ▸ List.getElem_mem hj)
      simpa [hne] using han j hjo
    · intro arr j harr'
      simpa [harr'] using harr arr j harr'
    · intro x hx'
      simpa [hx'] using hreg x hx'
    · (try simp only [State.storeW_cost, State.charge_cost, State.setW_cost]); omega
  · intro hx
    have hi0 : i = 0 := by by_contra h; simp [Nat.pos_of_ne_zero h] at hx
    subst hi0
    refine ⟨fun w hw => ?_, han, harr, hreg, hri, hlen, hcapst, by simp; omega⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    exact hclr j hj (Nat.zero_le _)

/-! ## One tree: initialisation, Algorithm 5, root merge -/

/-- The per-tree block (`pt.b`, `pt.len` set by the caller). -/
def treeBlk : Stmt :=
  .seq (.wset "pt.np0" (.var "pt.np")) <|
  .seq (.wset "pt.i" (.var "pt.len")) <|
  .seq initLoop <|
  .seq (.wset "pt.i" (.sub (.var "pt.len") (.lit 1))) <|
  .seq loopA' finBlk

/-- Registers written by the per-tree block. -/
def treeRegs : List String := ["pt.v", "pt.p", "pt.ap", "pt.av", "pt.np", "pt.i", "pt.np0", "pt.r", "pt.g"]

/-- Frame of the per-tree block. -/
structure TFrame (st st' : State V) (np0 : ℕ) (ord : List ℕ) : Prop where
  loc : ∀ j, j ∉ ord → st'.wa "pt.nx" j = st.wa "pt.nx" j ∧ st'.wa "pt.an" j = st.wa "pt.an" j ∧
      st'.wa "pt.af" j = st.wa "pt.af" j ∧ st'.wa "pt.al" j = st.wa "pt.al" j
  old : ∀ arr g, (arr = "pt.PT" ∨ arr = "pt.PF" ∨ arr = "pt.PL" ∨ arr = "pt.PN") → g < np0 →
      st'.wa arr g = st.wa arr g
  arr : ∀ arr j, arr ∉ ptArrs → st'.wa arr j = st.wa arr j
  reg : ∀ x, x ∉ treeRegs → st'.w x = st.w x
  wlen : st'.wlen = st.wlen
  cap : st'.cap = st.cap

/-- **One tree**: the RAM stores exactly `Partition.pieces` of the tree at records `np0, …`. -/
theorem treeBlk_spec {st : State V} {k b np0 root : ℕ} {ord : List ℕ} (hk : 2 ≤ k)
    (hpf : ParentFirst (st.wa "fp.par") root ord)
    (hseg : ∀ j (h : j < ord.length), st.wa "fp.TV" (b + j) = ord[j])
    (htv : b + ord.length ≤ st.wlen "fp.TV")
    (hvl : ∀ x ∈ ord, x < st.wlen "fp.par" ∧ x < st.wlen "pt.an" ∧ x < st.wlen "pt.af" ∧
      x < st.wlen "pt.al" ∧ x < st.wlen "pt.nx")
    (hpl : np0 + ord.length ≤ st.wlen "pt.PT" ∧ np0 + ord.length ≤ st.wlen "pt.PF" ∧
      np0 + ord.length ≤ st.wlen "pt.PL" ∧ np0 + ord.length ≤ st.wlen "pt.PN")
    (hcap : b + ord.length < st.cap ∧ 2 * k < st.cap ∧ np0 + ord.length + 1 < st.cap)
    (hb : st.w "pt.b" = b) (hlen : st.w "pt.len" = ord.length) (hkm : st.w "pt.km1" = k - 1)
    (hnp : st.w "pt.np" = np0) :
    Runs ops treeBlk st (fun st' =>
      PiecesRep st' np0 (pieces k (st.wa "fp.par") ord.tail.reverse root) ∧
      st'.w "pt.np" = np0 + (pieces k (st.wa "fp.par") ord.tail.reverse root).length ∧
      TFrame st st' np0 ord ∧ st'.cost ≤ st.cost + 34 * ord.length + 30) := by
  have hne : ord ≠ [] := by
    rintro rfl; obtain ⟨-, hh, -⟩ := hpf; simp at hh
  have hnd : ord.Nodup := hpf.1
  have hlen1 : 1 ≤ ord.length := List.length_pos_of_ne_nil hne
  obtain ⟨hc1, hc2, hc3⟩ := hcap
  have hcap1 : 1 < st.cap := by omega
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  -- step 1: np0 := np ; step 2: i := len
  apply runs_seq
  refine runs_wset (a := np0) (by simp [hnp]) ?_
  apply runs_seq
  refine runs_wset (a := ord.length) (by simp [hlen]) ?_
  set st2 := (((st.setW "pt.np0" np0).charge 1).setW "pt.i" ord.length).charge 1 with hst2
  have h2wa : st2.wa = st.wa := rfl
  have h2len : st2.wlen = st.wlen := rfl
  have h2cap : st2.cap = st.cap := rfl
  have h2w : ∀ x, x ≠ "pt.i" → x ≠ "pt.np0" → st2.w x = st.w x := by
    intro x h1 h2; simp [hst2, h1, h2]
  -- step 3: the initialisation loop
  apply runs_seq
  refine Runs.mono (initLoop_spec (ops := ops) (st0 := st2) (b := b) (ord := ord) hnd hne
    (by rw [h2wa]; exact hseg) (by rw [h2len]; exact htv) (fun x hx => by rw [h2len]; exact (hvl x hx).2.1)
    (by rw [h2cap]; exact hc1) (by rw [h2w _ (by decide) (by decide)]; exact hb)
    (c0 := st2.cost + 4 * ord.length) ord.length st2
    ⟨le_rfl, by simp [hst2], fun j hj hij => absurd hij (by omega), fun _ _ => rfl, fun _ _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, le_rfl⟩) ?_
  rintro st3 ⟨h3an, h3anf, h3arr, h3reg, h3i, h3len, h3cap, h3cost⟩
  -- step 4: i := len - 1
  have hfit1' : fit st3.cap 1 = some 1 := by rw [h3cap, h2cap]; exact hfit1
  have h3lenr : st3.w "pt.len" = ord.length := by
    rw [h3reg _ (by decide), h2w _ (by decide) (by decide)]; exact hlen
  apply runs_seq
  refine runs_wset (a := ord.length - 1) (by simp [h3lenr, hfit1']) ?_
  set st4 := (st3.setW "pt.i" (ord.length - 1)).charge 1 with hst4
  have h4wa : ∀ arr j, arr ≠ "pt.an" → st4.wa arr j = st.wa arr j := fun arr j h => h3arr arr j h
  have h4par : st4.wa "fp.par" = st.wa "fp.par" := funext fun j => h4wa _ j (by decide)
  have h4len : st4.wlen = st.wlen := h3len
  have h4cap : st4.cap = st.cap := h3cap
  have h4w : ∀ x, x ≠ "pt.i" → x ≠ "pt.np0" → st4.w x = st.w x := by
    intro x h1 h2
    simp only [hst4, State.charge_w, State.setW_w, if_neg h1]
    rw [h3reg x h1, h2w x h1 h2]
  -- step 5: Algorithm 5
  have hC : TCtx st4 k b np0 root ord :=
    { hs := hk, pf := by rw [h4par]; exact hpf,
      seg := fun j hj => by rw [h4wa _ _ (by decide)]; exact hseg j hj,
      tvlen := by rw [h4len]; exact htv,
      vlen := fun x hx => by rw [h4len]; exact hvl x hx,
      plen := by rw [h4len]; exact hpl,
      cap := by rw [h4cap]; exact ⟨hc1, hc2, hc3⟩,
      rb := by rw [h4w _ (by decide) (by decide)]; exact hb,
      rk := by rw [h4w _ (by decide) (by decide)]; exact hkm }
  have hrestlen : ord.tail.reverse.length = ord.length - 1 := by simp
  have hLI : LI st4 k b np0 root ord (st4.cost + 30 * (ord.length - 1)) (ord.length - 1) st4 := by
    refine ⟨le_rfl, by simp [hst4], ?_, LFrame.refl _ _ _, le_rfl⟩
    have h0 : ord.length - 1 - (ord.length - 1) = 0 := by omega
    rw [h0, List.drop_zero, List.take_zero, List.foldl_nil]
    refine ⟨fun w hw => ?_, ?_, fun g hg => absurd hg (by simp [init])⟩
    · have hwo : w ∈ ord := (mem_ord_iff_of_parentFirst hpf w).mpr hw
      refine ⟨?_, fun h => absurd rfl h, fun h => absurd rfl h, trivial⟩
      simp only [init, List.tail_cons, List.length_nil]
      exact h3an w hwo
    · simp only [init, List.length_nil, Nat.add_zero]
      rw [h4w _ (by decide) (by decide)]; exact hnp
  apply runs_seq
  refine Runs.mono (loopA_spec (ops := ops) hC _ _ hLI) ?_
  rintro st5 ⟨h5R, h5F, h5i, h5cost⟩
  -- step 6: the root merge
  have ht := treeOrder_of_parentFirst hC.pf
  have hroot : st5.wa "fp.TV" b = root := by
    rw [h5F.arr _ _ (by decide), h4wa _ _ (by decide)]
    have := hseg 0 hlen1
    obtain ⟨-, hh, -⟩ := hpf
    cases hord : ord with
    | nil => exact absurd hord hne
    | cons a t =>
      simp only [hord, List.head?_cons, Option.some.injEq] at hh
      simp only [hord, List.getElem_cons_zero, Nat.add_zero] at this
      rw [this, hh]
  refine Runs.mono (fin_step (ops := ops) hk ht h5R
    (by rw [h5F.reg _ (by decide), h4w _ (by decide) (by decide)]; exact hb)
    (by rw [h5F.wlen, h4len]; omega) hroot
    (by rw [h5F.reg _ (by decide), hst4]; simp [h3reg _ (by decide : "pt.np0" ≠ "pt.i"), hst2])
    (fun x hx => by
      have hxo : x ∈ ord := (mem_ord_iff_of_parentFirst hpf x).mpr hx
      rw [h5F.wlen, h4len]; exact (hvl x hxo).2)
    (by rw [h5F.wlen, h4len, hrestlen]; obtain ⟨p1, p2, p3, p4⟩ := hpl; omega)
    (by rw [h5F.cap, h4cap, hrestlen]; omega)) ?_
  rintro st6 ⟨h6P, h6np, h6F, h6cost⟩
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := h6F
  rw [h4par] at h6P h6np
  refine ⟨h6P, h6np, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    have hj' : j ∉ ord.tail.reverse ++ [root] := fun h => hj ((mem_ord_iff_of_parentFirst hpf j).mpr h)
    obtain ⟨a1, a2, a3, a4⟩ := h5F.loc j hj
    refine ⟨by rw [f1 j hj', a1]; exact h4wa _ _ (by decide), ?_, ?_, ?_⟩
    · rw [f3 _ _ (by decide), a2]; show st3.wa "pt.an" j = _; rw [h3anf j hj]; rfl
    · rw [f3 _ _ (by decide), a3]; exact h4wa _ _ (by decide)
    · rw [f3 _ _ (by decide), a4]; exact h4wa _ _ (by decide)
  · intro arr g harr hg
    rw [f2 arr g harr hg, h5F.old arr g harr hg]
    rcases harr with rfl | rfl | rfl | rfl <;> exact h4wa _ _ (by decide)
  · intro arr j harr
    have harr' : arr ∉ ["pt.nx", "pt.PT", "pt.PF", "pt.PL", "pt.PN"] := by
      intro h; apply harr; simp only [ptArrs, List.mem_cons] at h ⊢; tauto
    have han : arr ≠ "pt.an" := by intro h; apply harr; simp [ptArrs, h]
    rw [f3 arr j harr', h5F.arr arr j harr]; exact h4wa arr j han
  · intro x hx
    simp only [treeRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9⟩ := hx
    rw [f4 x x8 x9 x5, h5F.reg x (by simp [loopRegs]; tauto), h4w x x6 x7]
  · rw [f5, h5F.wlen, h4len]
  · rw [f6, h5F.cap, h4cap]
  · have e1 : st2.cost = st.cost + 2 := by simp [hst2]
    have e4 : st4.cost = st3.cost + 1 := by simp [hst4]
    omega

/-! ## Parent-function congruence (the RAM has one global parent array) -/

section Congr

variable {α : Type*} [DecidableEq α]

theorem run_congr (s : ℕ) {par par' : α → α} :
    ∀ (rest : List α) (st : PState α), (∀ v ∈ rest, par v = par' v) →
      rest.foldl (step s par) st = rest.foldl (step s par') st
  | [], _, _ => rfl
  | v :: rest, st, h => by
    simp only [List.foldl_cons]
    have hv : step s par st v = step s par' st v := by simp only [step, h v List.mem_cons_self]
    rw [hv]
    exact run_congr s rest _ (fun w hw => h w (List.mem_cons_of_mem _ hw))

theorem pieces_congr (s : ℕ) {par par' : α → α} {rest : List α} (root : α)
    (h : ∀ v ∈ rest, par v = par' v) : pieces s par rest root = pieces s par' rest root := by
  have hr : run s par rest = run s par' rest := run_congr s rest init h
  unfold pieces
  rw [hr]

theorem parentFirst_congr {par par' : α → α} {root : α} {ord : List α} (hpf : ParentFirst par root ord)
    (h : ∀ v ∈ ord.tail, par v = par' v) : ParentFirst par' root ord := by
  obtain ⟨hnd, hhead, hpar⟩ := hpf
  refine ⟨hnd, hhead, fun pre post v hord hpre => ?_⟩
  have hvt : v ∈ ord.tail := by
    cases pre with
    | nil => exact absurd rfl hpre
    | cons a pre' => rw [hord]; simp
  rw [← h v hvt]
  exact hpar pre post v hord hpre

end Congr

/-- A tree has at most `|ord|` pieces. -/
theorem pieces_length_le {k : ℕ} (hk : 2 ≤ k) {par : ℕ → ℕ} {root : ℕ} {rest : List ℕ}
    (ht : TreeOrder par rest root) : (pieces k par rest root).length ≤ rest.length + 1 := by
  have hI := inv_run hk ht
  have hgl := groups_length_le hk hI
  unfold pieces
  cases hlast : (run k par rest).groups.getLast? with
  | none => simp
  | some G =>
    simp only [List.length_append, List.length_singleton, List.length_dropLast]
    omega

/-! ## The forest loop -/

/-- One tree of the forest: load its segment, run the per-tree block, advance. -/
def forestBody : Stmt :=
  .seq (.wset "pt.b" (.load "fp.toff" (.var "pt.t"))) <|
  .seq (.wset "pt.len" (.load "fp.tlen" (.var "pt.t"))) <|
  .seq treeBlk (.wset "pt.t" (.add (.var "pt.t") (.lit 1)))

/-- The PT forest loop over the trees `t = pt.t, …, fp.nt - 1`. -/
def forestLoop : Stmt := .while (.lt (.var "pt.t") (.var "fp.nt")) forestBody

/-- Registers written by the forest loop. -/
def forestRegs : List String := treeRegs ++ ["pt.t", "pt.b", "pt.len"]

/-- The RAM layout of a FindPivots forest (agent-09's B-L2 output). -/
structure ForestAt (st : State V) (trees : List (TreeRec ℕ)) : Prop where
  nt : st.w "fp.nt" = trees.length
  offl : trees.length ≤ st.wlen "fp.toff" ∧ trees.length ≤ st.wlen "fp.tlen"
  seg : ∀ t (ht : t < trees.length), st.wa "fp.toff" t + trees[t].ord.length ≤ st.wlen "fp.TV" ∧
    st.wa "fp.tlen" t = trees[t].ord.length ∧
    ∀ j (hj : j < trees[t].ord.length), st.wa "fp.TV" (st.wa "fp.toff" t + j) = trees[t].ord[j]
  par : ∀ T ∈ trees, ∀ v ∈ T.ord.tail, st.wa "fp.par" v = T.par v
  pf : ∀ T ∈ trees, ParentFirst T.par T.root T.ord
  disj : trees.Pairwise (fun a b => ∀ w ∈ a.ord, w ∉ b.ord)

/-- Invariant of the forest loop after the first `t` trees. -/
def FI (st0 : State V) (k : ℕ) (trees : List (TreeRec ℕ)) (c0 : ℕ) (n : ℕ) (st : State V) : Prop :=
  n ≤ trees.length ∧ st.w "pt.t" = trees.length - n ∧
  PiecesRep st 0 (forestPieces k (trees.take (trees.length - n))) ∧
  st.w "pt.np" = (forestPieces k (trees.take (trees.length - n))).length ∧
  (∀ j, (∀ T ∈ trees.take (trees.length - n), j ∉ T.ord) →
    st.wa "pt.nx" j = st0.wa "pt.nx" j ∧ st.wa "pt.an" j = st0.wa "pt.an" j ∧
    st.wa "pt.af" j = st0.wa "pt.af" j ∧ st.wa "pt.al" j = st0.wa "pt.al" j) ∧
  (∀ arr j, arr ∉ ptArrs → st.wa arr j = st0.wa arr j) ∧
  (∀ x, x ∉ forestRegs → st.w x = st0.w x) ∧ st.wlen = st0.wlen ∧ st.cap = st0.cap ∧
  st.cost + ((trees.drop (trees.length - n)).map (fun T => 40 * T.ord.length + 40)).sum ≤ c0

theorem forestPieces_length_le {k : ℕ} (hk : 2 ≤ k) :
    ∀ trees : List (TreeRec ℕ), (∀ T ∈ trees, ParentFirst T.par T.root T.ord) →
      (forestPieces k trees).length ≤ (trees.map (fun T => T.ord.length)).sum
  | [], _ => by simp [forestPieces]
  | T :: ts, h => by
    have hT := h T List.mem_cons_self
    have ih := forestPieces_length_le hk ts (fun U hU => h U (List.mem_cons_of_mem _ hU))
    have h1 := pieces_length_le hk (treeOrder_of_parentFirst hT)
    have h2 := length_ord_of_parentFirst hT
    simp only [forestPieces, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    omega

theorem forestPieces_take_succ (k : ℕ) (trees : List (TreeRec ℕ)) {t : ℕ} (ht : t < trees.length) :
    forestPieces k (trees.take (t + 1)) =
      forestPieces k (trees.take t) ++ pieces k trees[t].par trees[t].ord.tail.reverse trees[t].root := by
  unfold forestPieces
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.flatMap_append,
    List.flatMap_singleton]

theorem pieces_tail_mem_ord {k : ℕ} (hk : 2 ≤ k) {T : TreeRec ℕ} (hT : ParentFirst T.par T.root T.ord) :
    ∀ F ∈ pieces k T.par T.ord.tail.reverse T.root, ∀ x ∈ F.tail, x ∈ T.ord := by
  intro F hF x hx
  have hperm := pieces_tails_perm hk (treeOrder_of_parentFirst hT)
  have : x ∈ T.ord.tail.reverse := hperm.subset (List.mem_flatMap.mpr ⟨F, hF, hx⟩)
  exact List.mem_of_mem_tail (List.mem_reverse.mp this)

theorem forestPieces_tail_mem {k : ℕ} (hk : 2 ≤ k) :
    ∀ trees : List (TreeRec ℕ), (∀ T ∈ trees, ParentFirst T.par T.root T.ord) →
      ∀ F ∈ forestPieces k trees, ∀ x ∈ F.tail, ∃ T ∈ trees, x ∈ T.ord := by
  intro trees hpf F hF x hx
  obtain ⟨T, hT, hFT⟩ := List.mem_flatMap.mp hF
  exact ⟨T, hT, pieces_tail_mem_ord hk (hpf T hT) F hFT x hx⟩

theorem PiecesRep.frame_wa {st st' : State V} {np0 : ℕ} {L : List (List ℕ)} (h : PiecesRep st np0 L)
    (hwa : st'.wa = st.wa) : PiecesRep st' np0 L :=
  fun g hg => PieceRep.frame (h g hg) (by rw [hwa]) (by rw [hwa]) (by rw [hwa]) (by rw [hwa])
    (fun j _ => by rw [hwa])

theorem trees_length_le_sum {trees : List (TreeRec ℕ)} (hpf : ∀ T ∈ trees, ParentFirst T.par T.root T.ord) :
    trees.length ≤ (trees.map (fun T => T.ord.length)).sum := by
  induction trees with
  | nil => simp
  | cons T ts ih =>
    have hT := hpf T List.mem_cons_self
    have h1 := length_ord_of_parentFirst hT
    have := ih (fun U hU => hpf U (List.mem_cons_of_mem _ hU))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- **The forest loop**: after all trees, the RAM stores exactly `forestPieces k trees` at records `0, 1, …`. -/
theorem forestLoop_spec {st0 : State V} {k : ℕ} {trees : List (TreeRec ℕ)} (hk : 2 ≤ k)
    (hF : ForestAt st0 trees)
    (hbnd : ∀ T ∈ trees, ∀ x ∈ T.ord, x < st0.wlen "fp.par" ∧ x < st0.wlen "pt.an" ∧ x < st0.wlen "pt.af" ∧
      x < st0.wlen "pt.al" ∧ x < st0.wlen "pt.nx")
    (hPl : (trees.map (fun T => T.ord.length)).sum ≤ st0.wlen "pt.PT" ∧
      (trees.map (fun T => T.ord.length)).sum ≤ st0.wlen "pt.PF" ∧
      (trees.map (fun T => T.ord.length)).sum ≤ st0.wlen "pt.PL" ∧
      (trees.map (fun T => T.ord.length)).sum ≤ st0.wlen "pt.PN")
    (hcapT : ∀ t (ht : t < trees.length), st0.wa "fp.toff" t + trees[t].ord.length < st0.cap)
    (hcapK : 2 * k < st0.cap) (hcapS : (trees.map (fun T => T.ord.length)).sum + 1 < st0.cap)
    (hkm : st0.w "pt.km1" = k - 1) {c0 : ℕ} :
    ∀ n st, FI st0 k trees c0 n st → Runs ops forestLoop st (fun st' =>
      PiecesRep st' 0 (forestPieces k trees) ∧ st'.w "pt.np" = (forestPieces k trees).length ∧
      (∀ j, (∀ T ∈ trees, j ∉ T.ord) →
        st'.wa "pt.nx" j = st0.wa "pt.nx" j ∧ st'.wa "pt.an" j = st0.wa "pt.an" j ∧
        st'.wa "pt.af" j = st0.wa "pt.af" j ∧ st'.wa "pt.al" j = st0.wa "pt.al" j) ∧
      (∀ arr j, arr ∉ ptArrs → st'.wa arr j = st0.wa arr j) ∧
      (∀ x, x ∉ forestRegs → st'.w x = st0.w x) ∧ st'.wlen = st0.wlen ∧ st'.cap = st0.cap ∧
      st'.cost ≤ c0 + 1) := by
  have hpfT := hF.pf
  apply runs_while_nat
  intro n st hFI
  obtain ⟨hnle, hrt, hPR, hnp, hloc, harr, hreg, hlen, hcapst, hcost⟩ := hFI
  have hcap1 : 1 < st.cap := by rw [hcapst]; omega
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  have hnt : st.w "fp.nt" = trees.length := by rw [hreg _ (by simp [forestRegs, treeRegs])]; exact hF.nt
  refine ⟨if trees.length - n < trees.length then 1 else 0, ?_, ?_, ?_⟩
  · simp only [evalW_lt', evalW_var, hrt, hnt, Option.bind_some]
    split_ifs <;> simp [hfit1, fit_of_lt (show 0 < st.cap by omega)]
  · intro hx
    have hn0 : 0 < n := by
      by_contra h; have : n = 0 := by omega
      subst this; simp at hx
    set t := trees.length - n with ht_def
    have htl : t < trees.length := by omega
    set T := trees[t] with hT_def
    have hTmem : T ∈ trees := List.getElem_mem htl
    obtain ⟨hseg1, hseg2, hseg3⟩ := hF.seg t htl
    have hpfT' := hpfT T hTmem
    have hlenT := length_ord_of_parentFirst hpfT'
    -- sizes
    set A := forestPieces k (trees.take t) with hA
    have hAle : A.length ≤ ((trees.take t).map (fun T => T.ord.length)).sum :=
      forestPieces_length_le hk _ (fun U hU => hpfT U (List.mem_of_mem_take hU))
    have hsum_split : ((trees.take t).map (fun T => T.ord.length)).sum + T.ord.length ≤
        (trees.map (fun T => T.ord.length)).sum := by
      have h1 : trees = trees.take t ++ T :: trees.drop (t + 1) := by
        rw [hT_def, ← List.drop_eq_getElem_cons htl, List.take_append_drop]
      have h2 : (trees.map (fun T => T.ord.length)).sum = ((trees.take t).map (fun T => T.ord.length)).sum +
          (T.ord.length + ((trees.drop (t + 1)).map (fun T => T.ord.length)).sum) := by
        conv_lhs => rw [h1]
        simp [List.sum_append]
      omega
    have htrees := trees_length_le_sum hpfT
    -- the body starts from `st.charge 1`
    set st1 := st.charge 1 with hst1
    have htoffl : t < st1.wlen "fp.toff" := by
      simp only [hst1, State.charge_wlen]; rw [hlen]; have := hF.offl.1; omega
    have htlenl : t < st1.wlen "fp.tlen" := by
      simp only [hst1, State.charge_wlen]; rw [hlen]; have := hF.offl.2; omega
    have htoff : st1.wa "fp.toff" t = st0.wa "fp.toff" t := harr _ _ (by decide)
    have htlen : st1.wa "fp.tlen" t = T.ord.length := by
      show st.wa "fp.tlen" t = _; rw [harr _ _ (by decide)]; exact hseg2
    have hrt1 : st1.w "pt.t" = t := hrt
    apply runs_seq
    refine runs_wset (a := st0.wa "fp.toff" t) (by simp [hrt1, htoffl, htoff]) ?_
    apply runs_seq
    refine runs_wset (a := T.ord.length) (by simp [hrt1, htlenl, htlen]) ?_
    set b0 := st0.wa "fp.toff" t with hb0
    set st2 := (((st1.setW "pt.b" b0).charge 1).setW "pt.len" T.ord.length).charge 1 with hst2
    have h2wa : st2.wa = st.wa := rfl
    have h2len : st2.wlen = st0.wlen := hlen
    have h2cap : st2.cap = st0.cap := hcapst
    have h2w : ∀ x, x ≠ "pt.b" → x ≠ "pt.len" → st2.w x = st.w x := by
      intro x h1 h2; simp [hst2, hst1, h1, h2]
    have h2par : ∀ v ∈ T.ord.tail, st2.wa "fp.par" v = T.par v := by
      intro v hv; rw [h2wa, harr _ _ (by decide)]; exact hF.par T hTmem v hv
    have hpf2 : ParentFirst (st2.wa "fp.par") T.root T.ord :=
      parentFirst_congr hpfT' (fun v hv => (h2par v hv).symm)
    apply runs_seq
    refine Runs.mono (treeBlk_spec (ops := ops) (st := st2) (k := k) (b := b0) (np0 := A.length)
      (root := T.root) (ord := T.ord) hk hpf2
      (fun j hj => by rw [h2wa, harr _ _ (by decide)]; exact hseg3 j hj)
      (by rw [h2len]; exact hseg1)
      (fun x hx => by rw [h2len]; exact hbnd T hTmem x hx)
      (by
        rw [h2len]; obtain ⟨p1, p2, p3, p4⟩ := hPl
        have := hAle; have := hsum_split
        exact ⟨by omega, by omega, by omega, by omega⟩)
      (by
        rw [h2cap]
        have := hAle; have := hsum_split; have := hcapS
        exact ⟨hcapT t htl, hcapK, by omega⟩)
      (by simp [hst2, hst1])
      (by simp [hst2, hst1])
      (by rw [h2w _ (by decide) (by decide), hreg _ (by simp [forestRegs, treeRegs])]; exact hkm)
      (by rw [h2w _ (by decide) (by decide)]; exact hnp)) ?_
    rintro st3 ⟨h3P, h3np, h3F, h3cost⟩
    have hfit3 : fit st3.cap (t + 1) = some (t + 1) := fit_of_lt (by rw [h3F.cap, h2cap]; omega)
    have h3t : st3.w "pt.t" = t := by
      rw [h3F.reg _ (by simp [treeRegs]), h2w _ (by decide) (by decide)]; exact hrt
    refine runs_wset (a := t + 1) (by simp [h3t, fit_of_lt (show 1 < st3.cap by rw [h3F.cap, h2cap]; omega),
      hfit3]) ?_
    set st4 := (st3.setW "pt.t" (t + 1)).charge 1 with hst4
    have h4wa : st4.wa = st3.wa := rfl
    have hpc : pieces k (st2.wa "fp.par") T.ord.tail.reverse T.root = pieces k T.par T.ord.tail.reverse T.root :=
      pieces_congr k T.root (fun v hv => h2par v (List.mem_reverse.mp hv))
    rw [hpc] at h3P h3np
    have htn : trees.length - (n - 1) = t + 1 := by omega
    refine ⟨n - 1, by omega, by omega, by simp [hst4, htn], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- the records
      rw [htn, forestPieces_take_succ k trees htl, ← hA, ← hT_def]
      intro g hg
      rw [List.length_append] at hg
      by_cases hgA : g < A.length
      · rw [List.getElem_append_left hgA]
        have hold := hPR g (by simpa [ht_def] using hgA)
        simp only [Nat.zero_add] at hold ⊢
        refine PieceRep.frame hold ?_ ?_ ?_ ?_ ?_
        · rw [h4wa, h3F.old _ _ (Or.inl rfl) hgA]; rfl
        · rw [h4wa, h3F.old _ _ (Or.inr (Or.inr (Or.inr rfl))) hgA]; rfl
        · rw [h4wa, h3F.old _ _ (Or.inr (Or.inl rfl)) hgA]; rfl
        · rw [h4wa, h3F.old _ _ (Or.inr (Or.inr (Or.inl rfl))) hgA]; rfl
        · intro j hj
          have hjt : j ∈ (A[g]'hgA).tail := List.dropLast_subset _ hj
          obtain ⟨T', hT', hjT'⟩ := forestPieces_tail_mem hk (trees.take t)
            (fun U hU => hpfT U (List.mem_of_mem_take hU)) _ (List.getElem_mem hgA) j hjt
          have hjT : j ∉ T.ord := by
            intro hjT
            obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT'
            have hlt : i < t := by
              have := hi; simp only [List.length_take] at this; omega
            have hpw := List.pairwise_iff_getElem.mp hF.disj i t (by simp at hi; omega) htl hlt
            simp only [List.getElem_take] at hjT'
            exact hpw _ hjT' hjT
          rw [h4wa, (h3F.loc j hjT).1]; rfl
      · have hg' : g - A.length < (pieces k T.par T.ord.tail.reverse T.root).length := by omega
        rw [List.getElem_append_right (by omega)]
        have := h3P (g - A.length) hg'
        have heq : A.length + (g - A.length) = g := by omega
        simp only [Nat.zero_add]
        rw [heq] at this
        exact PieceRep.frame this rfl rfl rfl rfl (fun _ _ => rfl)
    · rw [htn, forestPieces_take_succ k trees htl, ← hA, ← hT_def, List.length_append]
      simp only [hst4, State.charge_w, State.setW_w, String.reduceEq, if_false]
      exact h3np
    · intro j hj
      rw [htn] at hj
      have hjT : j ∉ T.ord := fun h => hj T (List.mem_iff_getElem.mpr ⟨t, by simp; omega, by simp [hT_def]⟩) h
      have hjold : ∀ T' ∈ trees.take (trees.length - n), j ∉ T'.ord := fun T' hT' => hj T' (by
        rw [List.take_add_one]; exact List.mem_append_left _ hT')
      obtain ⟨a1, a2, a3, a4⟩ := h3F.loc j hjT
      obtain ⟨b1, b2, b3, b4⟩ := hloc j hjold
      exact ⟨by rw [h4wa, a1, h2wa, b1], by rw [h4wa, a2, h2wa, b2], by rw [h4wa, a3, h2wa, b3],
        by rw [h4wa, a4, h2wa, b4]⟩
    · intro arr j harr'
      rw [h4wa, h3F.arr arr j harr', h2wa, harr arr j harr']
    · intro x hx
      simp only [forestRegs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
      simp only [hst4, State.charge_w, State.setW_w, if_neg hx2]
      rw [h3F.reg x hx1, h2w x hx3 hx4, hreg x (by simp [forestRegs, hx1, hx2, hx3, hx4])]
    · simp only [hst4, State.charge_wlen, State.setW_wlen]; rw [h3F.wlen, h2len]
    · simp only [hst4, State.charge_cap, State.setW_cap]; rw [h3F.cap, h2cap]
    · rw [htn]
      have hdrop : trees.drop t = T :: trees.drop (t + 1) := by rw [hT_def]; exact List.drop_eq_getElem_cons htl
      rw [hdrop] at hcost
      simp only [List.map_cons, List.sum_cons] at hcost
      have e4 : st4.cost = st3.cost + 1 := by simp [hst4]
      have e2 : st2.cost = st.cost + 1 + 2 := by simp [hst2, hst1]
      omega
  · intro hx
    have hn0 : n = 0 := by
      by_contra h; have : trees.length - n < trees.length := by omega
      simp [this] at hx
    subst hn0
    simp only [Nat.sub_zero, List.take_length] at hPR hnp hloc
    refine ⟨hPR.frame_wa rfl, by simpa using hnp, fun j hj => by simpa using hloc j hj, harr, hreg, hlen,
      hcapst, ?_⟩
    simp only [Nat.sub_zero, List.drop_length, List.map_nil, List.sum_nil, Nat.add_zero] at hcost
    simp; omega

end Frontier.CHD.PartitionRAM
