import Frontier.CHD.TreeRAM7
import Frontier.CHD.PartitionMap
import Frontier.CHD.PartitionRAM5

/-!
# Frontier.CHD.TreeRAM8 — (T3) compaction of the forest into the PT layout (owner agent-03)

**NON-GATE** (Layer B).  `compactProg` walks the chains of the tree layer (`tr.hd`, `tr.nx`, `tr.ln`) and writes
the tree orders contiguously: tree `t` at `fp.TV[fp.toff[t] ..]`, length `fp.tlen[t]`, `fp.nt` trees — the
`ForestAt` layout read by the PT program (`ptProg_spec`).  `compactProg_spec` (lists of words) and
`compact_forestAt` (from `FR0` over `Fin N`: `ForestAt` of the relabelled forest `trees.map natTree`), cost
`O(Σ|T| + #trees)`.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

variable {V : Type} {ops : VOps V}

/-- Registers of the compaction. -/
def ctRegs : List String := ["ct.t", "ct.o", "ct.i", "ct.l", "ct.w"]

/-- Copy one chain vertex. -/
def cpBody : Stmt :=
  .seq (.wstore "fp.TV" (.var "ct.o") (.var "ct.w")) <|
  .seq (.wset "ct.o" (.add (.var "ct.o") (.lit 1))) <|
  .seq (.wset "ct.w" (.load "tr.nx" (.var "ct.w")))
       (.wset "ct.i" (.add (.var "ct.i") (.lit 1)))

def cpLoop : Stmt := .while (.lt (.var "ct.i") (.var "ct.l")) cpBody

/-- Copy tree `ct.t`. -/
def ctBody : Stmt :=
  .seq (.wstore "fp.toff" (.var "ct.t") (.var "ct.o")) <|
  .seq (.wset "ct.l" (.load "tr.ln" (.var "ct.t"))) <|
  .seq (.wstore "fp.tlen" (.var "ct.t") (.var "ct.l")) <|
  .seq (.wset "ct.w" (.load "tr.hd" (.var "ct.t"))) <|
  .seq (.wset "ct.i" (.lit 0)) <|
  .seq cpLoop
       (.wset "ct.t" (.add (.var "ct.t") (.lit 1)))

def ctLoop : Stmt := .while (.lt (.var "ct.t") (.var "tr.nt")) ctBody

/-- (T3) The compaction. -/
def compactProg : Stmt :=
  .seq (.wset "ct.t" (.lit 0)) <| .seq (.wset "ct.o" (.lit 0)) <| .seq ctLoop (.wset "fp.nt" (.var "tr.nt"))

/-! ## The chain copy -/

/-- Invariant of the chain copy with `n` vertices left. -/
def CPI (st0 : State V) (O : List ℕ) (o0 c0 n : ℕ) (st : State V) : Prop :=
  n ≤ O.length ∧ st.w "ct.i" = O.length - n ∧ st.w "ct.o" = o0 + (O.length - n) ∧ st.w "ct.l" = O.length ∧
  (∀ i (h : i < O.length), i = O.length - n → st.w "ct.w" = O[i]) ∧
  SegAt st "fp.TV" o0 (O.take (O.length - n)) ∧
  (∀ j, (j < o0 ∨ o0 + (O.length - n) ≤ j) → st.wa "fp.TV" j = st0.wa "fp.TV" j) ∧
  (∀ a j, a ≠ "fp.TV" → st.wa a j = st0.wa a j) ∧
  (∀ y, y ≠ "ct.i" → y ≠ "ct.o" → y ≠ "ct.w" → st.w y = st0.w y) ∧
  st.wlen = st0.wlen ∧ st.cap = st0.cap ∧ st.cost + 5 * n ≤ c0

theorem cpLoop_spec {st0 : State V} {O : List ℕ} {o0 c0 : ℕ}
    (hll : LL st0 "tr.nx" O) (hOl : ∀ x ∈ O, x < st0.wlen "tr.nx") (hTV : o0 + O.length ≤ st0.wlen "fp.TV")
    (hcap : o0 + O.length + 1 < st0.cap) :
    ∀ n st, CPI st0 O o0 c0 n st → Runs ops cpLoop st (fun st' => CPI st0 O o0 (c0 + 1) 0 st') := by
  apply runs_while_nat
  rintro n st ⟨hnle, hi, ho, hl, hw, hseg, hfr, harr, hreg, hlen, hcapst, hcost⟩
  have hcap1 : 1 < st.cap := by rw [hcapst]; omega
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  refine ⟨if O.length - n < O.length then 1 else 0, ?_, ?_, ?_⟩
  · simp only [evalW_lt', evalW_var, hi, hl, Option.bind_some]
    split_ifs <;> simp [hfit0, hfit1]
  · intro hx
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      subst this; simp at hx
    obtain ⟨i, hidef⟩ : ∃ i, i = O.length - n := ⟨_, rfl⟩
    rw [← hidef] at hi ho hseg hfr
    have hil : i < O.length := by omega
    have hwi := hw i hil hidef
    have hOi : O[i] < st.wlen "tr.nx" := by rw [hlen]; exact hOl _ (List.getElem_mem hil)
    have hTVi : o0 + i < st.wlen "fp.TV" := by rw [hlen]; omega
    have hfito : fit st.cap (o0 + i + 1) = some (o0 + i + 1) := fit_of_lt (by rw [hcapst]; omega)
    have hfiti : fit st.cap (i + 1) = some (i + 1) := fit_of_lt (by rw [hcapst]; omega)
    have hnxi : st.wa "tr.nx" O[i] = st0.wa "tr.nx" O[i] := harr _ _ (by decide)
    apply runs_seq
    refine runs_wstore (j := o0 + i) (a := O[i]) (by simp [ho]) (by simp [hwi]) hTVi ?_
    apply runs_seq
    refine runs_wset (a := o0 + i + 1) (by simp [ho, hfit1, hfito]) ?_
    apply runs_seq
    refine runs_wset (a := st.wa "tr.nx" O[i]) (by simp [hwi, hOi]) ?_
    refine runs_wset (a := i + 1) (by simp [hi, hfit1, hfiti]) ?_
    have hjj : O.length - (n - 1) = i + 1 := by omega
    refine ⟨n - 1, by omega, by omega, by simp; omega, by simp; omega, by simp [hl], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · intro i' hi' hi'def
      obtain rfl : i' = i + 1 := by omega
      simp only [State.charge_w, State.setW_w, State.storeW_w]
      simp only [show ("ct.w" : String) = "ct.i" ↔ False by decide, if_false, if_true]
      rw [hnxi]
      exact LL.get hll i hi'
    · rw [hjj, List.take_add_one, List.getElem?_eq_getElem hil, Option.toList_some]
      refine SegAt.snoc hseg ?_ (fun j hj => ?_)
      · have : (O.take i).length = i := by simp; omega
        rw [this]; simp
      · have : (O.take i).length = i := by simp; omega
        rw [this] at hj
        simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
        rw [if_neg (by omega)]
    · intro j hj
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
      rw [if_neg (by omega)]
      exact hfr j (by omega)
    · intro a j ha
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
      rw [if_neg (by rintro ⟨h, -⟩; exact ha h)]
      exact harr a j ha
    · intro y h1 h2 h3
      simp only [State.charge_w, State.setW_w, State.storeW_w, if_neg h1, if_neg h2, if_neg h3]
      exact hreg y h1 h2 h3
    · simp [hlen]
    · simp [hcapst]
    · simp only [State.charge_cost, State.setW_cost, State.storeW_cost]
      omega
  · intro hx
    have hn : n = 0 := by
      by_contra h
      have : O.length - n < O.length := by omega
      simp [this] at hx
    subst hn
    exact ⟨hnle, hi, ho, hl, hw, hseg, hfr, harr, hreg, hlen, hcapst, by simp; omega⟩

/-! ## The tree loop -/

/-- Offset of tree `t` in the compact layout. -/
def offs (Os : List (List ℕ)) (t : ℕ) : ℕ := ((Os.take t).map List.length).sum

theorem offs_succ (Os : List (List ℕ)) {t : ℕ} (ht : t < Os.length) : offs Os (t + 1) = offs Os t + Os[t].length := by
  unfold offs
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.map_append, List.sum_append]
  simp

theorem offs_le_succ (Os : List (List ℕ)) (m : ℕ) : offs Os m ≤ offs Os (m + 1) := by
  unfold offs
  rw [List.take_add_one, List.map_append, List.sum_append]
  omega

theorem offs_le_add (Os : List (List ℕ)) (t : ℕ) : ∀ d, offs Os t ≤ offs Os (t + d)
  | 0 => le_refl _
  | d + 1 => (offs_le_add Os t d).trans (by rw [← Nat.add_assoc]; exact offs_le_succ Os (t + d))

theorem offs_mono (Os : List (List ℕ)) {t t' : ℕ} (ht : t < Os.length) (htt : t < t') :
    offs Os t + Os[t].length ≤ offs Os t' := by
  rw [← offs_succ Os ht]
  obtain ⟨d, rfl⟩ : ∃ d, t' = t + 1 + d := ⟨t' - (t + 1), by omega⟩
  exact offs_le_add Os (t + 1) d

theorem offs_le (Os : List (List ℕ)) (t : ℕ) : offs Os t ≤ (Os.map List.length).sum := by
  unfold offs
  conv_rhs => rw [← List.take_append_drop t Os]
  rw [List.map_append, List.sum_append]
  omega

/-- Invariant of the tree loop with `n` trees left. -/
def CTI (st0 : State V) (Os : List (List ℕ)) (c0 n : ℕ) (st : State V) : Prop :=
  n ≤ Os.length ∧ st.w "ct.t" = Os.length - n ∧ st.w "ct.o" = offs Os (Os.length - n) ∧
  (∀ t (h : t < Os.length), t < Os.length - n →
    st.wa "fp.toff" t = offs Os t ∧ st.wa "fp.tlen" t = Os[t].length ∧ SegAt st "fp.TV" (offs Os t) Os[t]) ∧
  (∀ a j, a ≠ "fp.TV" → a ≠ "fp.toff" → a ≠ "fp.tlen" → st.wa a j = st0.wa a j) ∧
  (∀ y, y ∉ ctRegs → st.w y = st0.w y) ∧ st.wlen = st0.wlen ∧ st.cap = st0.cap ∧
  st.cost + ((Os.drop (Os.length - n)).map (fun O => 5 * O.length + 9)).sum ≤ c0

theorem sum_drop_succ (Os : List (List ℕ)) {t : ℕ} (ht : t < Os.length) (g : List ℕ → ℕ) :
    ((Os.drop t).map g).sum = g Os[t] + ((Os.drop (t + 1)).map g).sum := by
  rw [List.drop_eq_getElem_cons ht, List.map_cons, List.sum_cons]

theorem ctLoop_spec {st0 : State V} {Os : List (List ℕ)} {c0 : ℕ}
    (hnt : st0.w "tr.nt" = Os.length)
    (hhd : ∀ t (h : t < Os.length), Os[t].head? = some (st0.wa "tr.hd" t))
    (hln : ∀ t (h : t < Os.length), st0.wa "tr.ln" t = Os[t].length)
    (hll : ∀ t (h : t < Os.length), LL st0 "tr.nx" Os[t])
    (hOl : ∀ t (h : t < Os.length), ∀ x ∈ Os[t], x < st0.wlen "tr.nx")
    (hTV : (Os.map List.length).sum ≤ st0.wlen "fp.TV")
    (htl : Os.length ≤ st0.wlen "fp.toff" ∧ Os.length ≤ st0.wlen "fp.tlen" ∧ Os.length ≤ st0.wlen "tr.hd" ∧
      Os.length ≤ st0.wlen "tr.ln")
    (hcap : (Os.map List.length).sum + Os.length + 2 < st0.cap) :
    ∀ n st, CTI st0 Os c0 n st → Runs ops ctLoop st (fun st' => CTI st0 Os (c0 + 1) 0 st') := by
  obtain ⟨l1, l2, l3, l4⟩ := htl
  apply runs_while_nat
  rintro n st ⟨hnle, ht, ho, hdone, harr, hreg, hlen, hcapst, hcost⟩
  have hcap1 : 1 < st.cap := by rw [hcapst]; omega
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hnt' : st.w "tr.nt" = Os.length := by rw [hreg _ (by decide)]; exact hnt
  refine ⟨if Os.length - n < Os.length then 1 else 0, ?_, ?_, ?_⟩
  · simp only [evalW_lt', evalW_var, ht, hnt', Option.bind_some]
    split_ifs <;> simp [hfit0, hfit1]
  · intro hx
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      subst this; simp at hx
    obtain ⟨t, htdef⟩ : ∃ t, t = Os.length - n := ⟨_, rfl⟩
    rw [← htdef] at ht ho hdone hcost
    have htl : t < Os.length := by omega
    obtain ⟨O, hO⟩ : ∃ O, O = Os[t] := ⟨_, rfl⟩
    have hOhd := hhd t htl
    rw [← hO] at hOhd
    obtain ⟨w0, O', rfl⟩ : ∃ w0 O', O = w0 :: O' := by
      cases O with
      | nil => simp at hOhd
      | cons a l => exact ⟨a, l, rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at hOhd
    have hlnt : st.wa "tr.ln" t = (w0 :: O').length := by
      rw [harr _ _ (by decide) (by decide) (by decide), hln t htl, ← hO]
    have hhdt : st.wa "tr.hd" t = w0 := by rw [harr _ _ (by decide) (by decide) (by decide), ← hOhd]
    have hoff1 : offs Os (t + 1) = offs Os t + (w0 :: O').length := by rw [offs_succ Os htl, ← hO]
    have hoffS : offs Os (t + 1) ≤ (Os.map List.length).sum := offs_le Os (t + 1)
    have hfitt : fit st.cap (t + 1) = some (t + 1) := fit_of_lt (by rw [hcapst]; omega)
    -- toff, l, tlen, w, i
    apply runs_seq
    refine runs_wstore (j := t) (a := offs Os t) (by simp [ht]) (by simp [ho])
      (by show t < st.wlen "fp.toff"; rw [hlen]; omega) ?_
    apply runs_seq
    refine runs_wset (a := (w0 :: O').length) (by simp [ht, show t < st.wlen "tr.ln" by rw [hlen]; omega, hlnt]) ?_
    apply runs_seq
    refine runs_wstore (j := t) (a := (w0 :: O').length) (by simp [ht]) (by simp) (by simp; rw [hlen]; omega) ?_
    apply runs_seq
    refine runs_wset (a := w0) (by simp [ht, show t < st.wlen "tr.hd" by rw [hlen]; omega, hhdt]) ?_
    apply runs_seq
    refine runs_wset (a := 0) (by simp [hfit0]) ?_
    generalize hs5 : ((((((((((st.charge 1).storeW "fp.toff" t (offs Os t)).charge 1).setW "ct.l"
      (w0 :: O').length).charge 1).storeW "fp.tlen" t (w0 :: O').length).charge 1).setW "ct.w" w0).charge
      1).setW "ct.i" 0).charge 1 = s5
    have h5wa : ∀ a j, s5.wa a j = if a = "fp.tlen" ∧ j = t then (w0 :: O').length else
        if a = "fp.toff" ∧ j = t then offs Os t else st.wa a j := by
      intro a j; rw [← hs5]; simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
    have h5w : ∀ y, s5.w y = if y = "ct.i" then 0 else if y = "ct.w" then w0 else if y = "ct.l" then
        (w0 :: O').length else st.w y := by
      intro y; rw [← hs5]; simp only [State.charge_w, State.setW_w, State.storeW_w]
    have h5len : s5.wlen = st.wlen := by rw [← hs5]; rfl
    have h5cap : s5.cap = st.cap := by rw [← hs5]; rfl
    have h5cost : s5.cost = st.cost + 6 := by rw [← hs5]; simp
    have h5nx : s5.wa "tr.nx" = st0.wa "tr.nx" := by
      funext j; rw [h5wa]; simp only [show ("tr.nx" : String) = "fp.tlen" ↔ False by decide,
        show ("tr.nx" : String) = "fp.toff" ↔ False by decide, false_and, if_false]
      exact harr _ _ (by decide) (by decide) (by decide)
    have hllt : LL s5 "tr.nx" (w0 :: O') := by
      have := hll t htl; rw [← hO] at this
      exact LL.frame this (fun j _ => by rw [h5nx])
    have hOlt : ∀ x ∈ w0 :: O', x < s5.wlen "tr.nx" := by
      intro x hx; rw [h5len, hlen]; exact hOl t htl x (by rw [← hO]; exact hx)
    have hCP0 : CPI s5 (w0 :: O') (offs Os t) (s5.cost + 5 * (w0 :: O').length) (w0 :: O').length s5 := by
      refine ⟨le_refl _, by rw [h5w]; simp, by rw [h5w]; simp [ho], by rw [h5w]; simp, ?_, ?_, fun _ _ => rfl,
        fun _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, le_refl _⟩
      · intro i hi hidef
        have hi0 : i = 0 := by simp at hidef; omega
        subst hi0
        rw [h5w]; simp
      · intro i hi; simp at hi
    apply runs_seq
    refine Runs.mono (cpLoop_spec (ops := ops) (st0 := s5) hllt hOlt
      (by rw [h5len, hlen]; omega) (by rw [h5cap, hcapst]; omega) _ s5 hCP0) ?_
    rintro s6 ⟨-, -, h6o, -, -, h6seg, h6fr, h6arr, h6reg, h6len, h6cap, h6cost⟩
    simp only [Nat.sub_zero, List.take_length] at h6o h6seg h6fr
    refine runs_wset (a := t + 1) (by simp [h6reg "ct.t" (by decide) (by decide) (by decide), h5w, ht, h6cap,
      h5cap, hfit1, hfitt]) ?_
    have hjj : Os.length - (n - 1) = t + 1 := by omega
    refine ⟨n - 1, by omega, by omega, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.charge_w, State.setW_w, show ("ct.o" : String) = "ct.t" ↔ False by decide, if_false]
      rw [h6o, hjj, hoff1]
    · intro t' ht' ht'lt
      rw [hjj] at ht'lt
      simp only [State.charge_wa, State.setW_wa]
      by_cases htt : t' = t
      · subst htt
        refine ⟨?_, ?_, ?_⟩
        · rw [h6arr _ _ (by decide), h5wa]; simp
        · rw [h6arr _ _ (by decide), h5wa, ← hO]; simp
        · rw [← hO]; exact h6seg
      · have ht't : t' < t := by omega
        obtain ⟨a1, a2, a3⟩ := hdone t' ht' ht't
        refine ⟨?_, ?_, ?_⟩
        · rw [h6arr _ _ (by decide), h5wa]; simp [htt, a1]
        · rw [h6arr _ _ (by decide), h5wa]; simp [htt, a2]
        · intro i hi
          have hmono := offs_mono Os ht' ht't
          show s6.wa "fp.TV" (offs Os t' + i) = _
          rw [h6fr (offs Os t' + i) (Or.inl (by omega)), h5wa]
          simp only [show ("fp.TV" : String) = "fp.tlen" ↔ False by decide,
            show ("fp.TV" : String) = "fp.toff" ↔ False by decide, false_and, if_false]
          exact a3 i hi
    · intro a j h1 h2 h3
      simp only [State.charge_wa, State.setW_wa]
      rw [h6arr _ _ h1, h5wa, if_neg (by rintro ⟨h, -⟩; exact h3 h), if_neg (by rintro ⟨h, -⟩; exact h2 h)]
      exact harr a j h1 h2 h3
    · intro y hy
      have e1 : y ≠ "ct.t" := fun h => hy (by simp [ctRegs, h])
      have e2 : y ≠ "ct.o" := fun h => hy (by simp [ctRegs, h])
      have e3 : y ≠ "ct.i" := fun h => hy (by simp [ctRegs, h])
      have e4 : y ≠ "ct.l" := fun h => hy (by simp [ctRegs, h])
      have e5 : y ≠ "ct.w" := fun h => hy (by simp [ctRegs, h])
      simp only [State.charge_w, State.setW_w, if_neg e1]
      rw [h6reg y e3 e2 e5, h5w, if_neg e3, if_neg e5, if_neg e4]
      exact hreg y hy
    · simp [h6len, h5len, hlen]
    · simp [h6cap, h5cap, hcapst]
    · rw [hjj]
      have hsd := sum_drop_succ Os htl (fun O => 5 * O.length + 9)
      rw [← hO] at hsd
      simp only [State.charge_cost, State.setW_cost]
      simp only [List.length_cons] at hsd h6cost ⊢
      omega
  · intro hx
    have hn : n = 0 := by
      by_contra h
      have : Os.length - n < Os.length := by omega
      simp [this] at hx
    subst hn
    refine ⟨hnle, ht, ho, hdone, harr, hreg, hlen, hcapst, ?_⟩
    simp only [Nat.sub_zero, List.drop_length, List.map_nil, List.sum_nil, Nat.add_zero, State.charge_cost]
      at hcost ⊢
    omega

/-- **(T3) The compaction** (lists of words): tree `t` of `Os` at `fp.TV[offs t ..]`. -/
theorem compactProg_spec {st0 : State V} {Os : List (List ℕ)}
    (hnt : st0.w "tr.nt" = Os.length)
    (hhd : ∀ t (h : t < Os.length), Os[t].head? = some (st0.wa "tr.hd" t))
    (hln : ∀ t (h : t < Os.length), st0.wa "tr.ln" t = Os[t].length)
    (hll : ∀ t (h : t < Os.length), LL st0 "tr.nx" Os[t])
    (hOl : ∀ t (h : t < Os.length), ∀ x ∈ Os[t], x < st0.wlen "tr.nx")
    (hTV : (Os.map List.length).sum ≤ st0.wlen "fp.TV")
    (htl : Os.length ≤ st0.wlen "fp.toff" ∧ Os.length ≤ st0.wlen "fp.tlen" ∧ Os.length ≤ st0.wlen "tr.hd" ∧
      Os.length ≤ st0.wlen "tr.ln")
    (hcap : (Os.map List.length).sum + Os.length + 2 < st0.cap) :
    Runs ops compactProg st0 (fun st' => st'.w "fp.nt" = Os.length ∧
      st'.w "ct.o" = (Os.map List.length).sum ∧
      (∀ t (h : t < Os.length), st'.wa "fp.toff" t = offs Os t ∧ st'.wa "fp.tlen" t = Os[t].length ∧
        SegAt st' "fp.TV" (offs Os t) Os[t]) ∧
      (∀ a j, a ≠ "fp.TV" → a ≠ "fp.toff" → a ≠ "fp.tlen" → st'.wa a j = st0.wa a j) ∧
      (∀ y, y ≠ "fp.nt" → y ∉ ctRegs → st'.w y = st0.w y) ∧ st'.wlen = st0.wlen ∧ st'.cap = st0.cap ∧
      st'.cost ≤ st0.cost + ((Os.map (fun O => 5 * O.length + 9))).sum + 4) := by
  have hfit0 : fit st0.cap 0 = some 0 := fit_of_lt (by omega)
  apply runs_seq
  refine runs_wset (a := 0) (by simp [hfit0]) ?_
  apply runs_seq
  refine runs_wset (a := 0) (by simp [hfit0]) ?_
  generalize hs2 : (((st0.setW "ct.t" 0).charge 1).setW "ct.o" 0).charge 1 = s2
  have h2wa : s2.wa = st0.wa := by rw [← hs2]; rfl
  have h2len : s2.wlen = st0.wlen := by rw [← hs2]; rfl
  have h2cap : s2.cap = st0.cap := by rw [← hs2]; rfl
  have h2cost : s2.cost = st0.cost + 2 := by rw [← hs2]; simp
  have h2w : ∀ y, y ∉ ctRegs → s2.w y = st0.w y := by
    intro y hy
    have e1 : y ≠ "ct.t" := fun h => hy (by simp [ctRegs, h])
    have e2 : y ≠ "ct.o" := fun h => hy (by simp [ctRegs, h])
    rw [← hs2]; simp [e1, e2]
  have hCT0 : CTI s2 Os (s2.cost + ((Os.map (fun O => 5 * O.length + 9))).sum) Os.length s2 := by
    refine ⟨le_refl _, by rw [← hs2]; simp, by rw [← hs2]; simp [offs], fun t _ h => absurd h (by omega),
      fun _ _ _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, by simp⟩
  apply runs_seq
  refine Runs.mono (ctLoop_spec (ops := ops) (st0 := s2) (by rw [h2w _ (by decide)]; exact hnt)
    (fun t h => by rw [h2wa]; exact hhd t h) (fun t h => by rw [h2wa]; exact hln t h)
    (fun t h => LL.frame (hll t h) (fun j _ => by rw [h2wa])) (fun t h x hx => by rw [h2len]; exact hOl t h x hx)
    (by rw [h2len]; exact hTV) (by rw [h2len]; exact htl) (by rw [h2cap]; exact hcap) _ s2 hCT0) ?_
  rintro s3 ⟨-, -, h3o, h3done, h3arr, h3reg, h3len, h3cap, h3cost⟩
  have hnt3 : s3.w "tr.nt" = Os.length := by rw [h3reg _ (by decide), h2w _ (by decide)]; exact hnt
  refine runs_wset (a := Os.length) (by simp [hnt3]) ?_
  refine ⟨by simp, ?_, fun t h => ?_, fun a j h1 h2 h3 => ?_, fun y hy1 hy2 => ?_, by simp [h3len, h2len],
    by simp [h3cap, h2cap], ?_⟩
  · simp only [State.charge_w, State.setW_w, show ("ct.o" : String) = "fp.nt" ↔ False by decide, if_false]
    rw [h3o, Nat.sub_zero]; simp [offs]
  · obtain ⟨a1, a2, a3⟩ := h3done t h (by omega)
    exact ⟨by simpa using a1, by simpa using a2, fun i hi => by simpa using a3 i hi⟩
  · simp only [State.charge_wa, State.setW_wa]; rw [h3arr a j h1 h2 h3, h2wa]
  · simp only [State.charge_w, State.setW_w, if_neg hy1]; rw [h3reg y hy2, h2w y hy2]
  · simp only [State.charge_cost, State.setW_cost]
    simp only [Nat.sub_zero, List.drop_length, List.map_nil, List.sum_nil, Nat.add_zero] at h3cost
    omega

/-! ## From the tree layer over `Fin N` -/

/-- Parent function on words. -/
def natPar {N : ℕ} (p : Fin N → Fin N) (n : ℕ) : ℕ := if h : n < N then (p ⟨n, h⟩).val else 0

theorem natPar_val {N : ℕ} (p : Fin N → Fin N) (a : Fin N) : natPar p a.val = (p a).val := by
  simp [natPar, a.2]

/-- A tree over `Fin N` as a tree of words. -/
def natTree {N : ℕ} (T : TreeRec (Fin N)) : TreeRec ℕ := relabel Fin.val (fun T => natPar T.par) T

theorem sum_len_le {N : ℕ} {trees : List (TreeRec (Fin N))}
    (hdisj : trees.Pairwise (fun a b => ∀ w ∈ a.ord, w ∉ b.ord)) (hnd : ∀ T ∈ trees, T.ord.Nodup) :
    (trees.map (fun T => T.ord.length)).sum ≤ N := by
  have hF : (trees.flatMap (fun T => T.ord)).Nodup :=
    List.nodup_flatMap.mpr ⟨hnd, hdisj.imp (fun h w hwa hwb => h w hwa hwb)⟩
  have := hF.length_le_card
  simp only [Fintype.card_fin, List.length_flatMap] at this
  exact this

/-- **(T3) The compaction of the tree layer's forest** gives `ForestAt` of the relabelled forest. -/
theorem compact_forestAt {st0 : State V} {N : ℕ} {trees : List (TreeRec (Fin N))} (hF : FR0 st0 N trees)
    (hpf : ∀ T ∈ trees, ParentFirst T.par T.root T.ord)
    (hlen : N ≤ st0.wlen "fp.TV" ∧ N ≤ st0.wlen "fp.toff" ∧ N ≤ st0.wlen "fp.tlen") (hcap : 2 * N + 2 < st0.cap) :
    Runs ops compactProg st0 (fun st' => ForestAt st' (trees.map natTree) ∧ FR0 st' N trees ∧
      st'.w "ct.o" = (trees.map (fun T => T.ord.length)).sum ∧
      SegAt st' "fp.TV" 0 (trees.map (fun T => T.ord.map Fin.val)).flatten ∧
      (∀ t (h : t < trees.length), st'.wa "fp.toff" t + trees[t].ord.length ≤
        (trees.map (fun T => T.ord.length)).sum) ∧
      (∀ a j, a ≠ "fp.TV" → a ≠ "fp.toff" → a ≠ "fp.tlen" → st'.wa a j = st0.wa a j) ∧
      (∀ y, y ≠ "fp.nt" → y ∉ ctRegs → st'.w y = st0.w y) ∧ st'.wlen = st0.wlen ∧ st'.cap = st0.cap ∧
      st'.cost ≤ st0.cost + 14 * ((trees.map natTree).map (fun T => T.ord.length)).sum + 4) := by
  obtain ⟨lTV, ltoff, ltlen⟩ := hlen
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hF.lens
  set Os : List (List ℕ) := trees.map (fun T => T.ord.map Fin.val) with hOs
  have hOsl : Os.length = trees.length := by simp [hOs]
  have hOst : ∀ t (h : t < Os.length), Os[t] = (trees[t]'(by rw [← hOsl]; exact h)).ord.map Fin.val := by
    intro t h; simp [hOs]
  have hsum : (Os.map List.length).sum = (trees.map (fun T => T.ord.length)).sum := by
    simp [hOs, Function.comp_def]
  have hsumN := sum_len_le hF.disj hF.nodup
  have hlenN : trees.length ≤ (trees.map (fun T => T.ord.length)).sum := by
    have := length_le_flatMap_length (fun T hT => by
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hT; exact hF.ne t ht)
    simpa [List.length_flatMap] using this
  have hsumN' : ((trees.map natTree).map (fun T => T.ord.length)).sum = (trees.map (fun T => T.ord.length)).sum := by
    simp [natTree, relabel, Function.comp_def]
  refine Runs.mono (compactProg_spec (ops := ops) (st0 := st0) (Os := Os) (by rw [hOsl]; exact hF.nt)
    (fun t h => by rw [hOst t h, List.head?_map]; exact hF.hd t _)
    (fun t h => by rw [hOst t h, List.length_map]; exact hF.ln t _)
    (fun t h => by rw [hOst t h]; exact hF.ll t _)
    (fun t h x hx => by
      rw [hOst t h] at hx
      obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
      have := w.2; omega)
    (by omega) (by rw [hOsl]; omega) (by omega)) ?_
  rintro st' ⟨hnt', hct', hseg, harr, hreg, hlen', hcap', hcost⟩
  have hTV' : ∀ a ∈ frWA0, st'.wa a = st0.wa a ∧ st'.wlen a = st0.wlen a := by
    intro a ha
    have e1 : a ≠ "fp.TV" := by rintro rfl; simp [frWA0] at ha
    have e2 : a ≠ "fp.toff" := by rintro rfl; simp [frWA0] at ha
    have e3 : a ≠ "fp.tlen" := by rintro rfl; simp [frWA0] at ha
    exact ⟨funext (fun j => harr a j e1 e2 e3), by rw [hlen']⟩
  have hFR' : FR0 st' N trees := hF.frame hTV' (hreg _ (by decide) (by decide))
  refine ⟨⟨by rw [hnt']; simp [hOsl], ?_, fun t ht => ?_, fun T hT v hv => ?_, fun T hT => ?_, ?_⟩, hFR',
    by rw [hct', hsum], segAt_flatten Os 0 (fun j hj => by rw [Nat.zero_add]; exact (hseg j hj).2.2),
    fun t ht => ?_, harr, hreg, hlen', hcap', ?_⟩
  · simp only [List.length_map, hlen']; exact ⟨by omega, by omega⟩
  · have ht' : t < Os.length := by simpa [hOsl] using ht
    obtain ⟨a1, a2, a3⟩ := hseg t ht'
    have hord : (trees.map natTree)[t].ord = Os[t] := by rw [hOst t ht']; simp [natTree, relabel]
    have hoffs := offs_succ Os ht'
    have hoffle := offs_le Os (t + 1)
    refine ⟨?_, ?_, fun j hj => ?_⟩
    · rw [a1, hord, hlen']; omega
    · rw [a2, hord]
    · rw [a1]
      have hj' : j < Os[t].length := by rw [← hord]; exact hj
      rw [a3 j hj']
      simp only [hord]
  · obtain ⟨T0, hT0, rfl⟩ := List.mem_map.mp hT
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hT0
    simp only [natTree, relabel] at hv ⊢
    rw [← List.map_tail] at hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    rw [harr _ _ (by decide) (by decide) (by decide), hF.par t ht w hw, natPar_val]
  · obtain ⟨T0, hT0, rfl⟩ := List.mem_map.mp hT
    exact parentFirst_map Fin.val Fin.val_injective (natPar_val T0.par) (hpf T0 hT0)
  · rw [List.pairwise_map]
    refine hF.disj.imp (fun {a b} h w hwa hwb => ?_)
    simp only [natTree, relabel] at hwa hwb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hwa
    obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hwb
    exact h x hx (Fin.ext hyx ▸ hy)
  · have ht' : t < Os.length := by rw [hOsl]; exact ht
    have a1 := (hseg t ht').1
    have hoffs := offs_succ Os ht'
    have hoffle := offs_le Os (t + 1)
    have hlt : Os[t].length = trees[t].ord.length := by rw [hOst t ht', List.length_map]
    rw [a1, ← hlt, ← hsum]; omega
  · rw [hsumN']
    have : (Os.map (fun O => 5 * O.length + 9)).sum = 5 * (Os.map List.length).sum + 9 * Os.length := by
      rw [sum_map_affine]
    rw [this, hsum, hOsl] at hcost
    omega

end Frontier.CHD.PartitionRAM
