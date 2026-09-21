import Frontier.RAMRep
import Frontier.RAMWP
import Frontier.CHD.LabRAM
import Frontier.CHD.DRep
import Frontier.CHD.DLazy

/-!
# DList — linked-list fragments of the RAM `D` structure (B-L3, agent-04, NON-GATE)

Entry lists run through `ent.nxt` (`0` = end, `i+1` = entry `i`), as in agent-02's layout.  An
entry `i` is live iff `live[ent.key[i]] = i + 1`.

* `walkCopy`: walk the list from `dl.p`, copy the ids of LIVE entries to `sel.w[dl.w + ·]` in list
  order; `dl.c` = number copied, `dl.t` = length.
-/

open scoped NNReal

namespace Frontier.CHD.DList

open Frontier.RAM WExpr Stmt LabRAM
open Frontier.CHD.DIns (LList tlWord)

variable {ops : VOps ℝ≥0}

/-- entry `i` is live (in state `st`) -/
def liveW (st : State ℝ≥0) (i : ℕ) : Prop := st.wa "live" (st.wa "ent.key" i) = i + 1

instance (st : State ℝ≥0) (i : ℕ) : Decidable (liveW st i) := by unfold liveW; infer_instance

/-- frame: a list survives any state change that keeps `ent.nxt` on its ids and its length -/
theorem _root_.Frontier.CHD.DIns.LList.frame {st st' : State ℝ≥0} :
    ∀ {h : ℕ} {l : List ℕ}, LList st h l → st'.wlen "ent.nxt" = st.wlen "ent.nxt" →
      (∀ i ∈ l, st'.wa "ent.nxt" i = st.wa "ent.nxt" i) → LList st' h l
  | _, _, .nil, _, _ => .nil
  | _, _, .cons i l hi hl, hlen, hnx => by
      refine .cons i l (by rw [hlen]; exact hi) ?_
      rw [hnx i List.mem_cons_self]
      exact hl.frame hlen (fun j hj => hnx j (List.mem_cons_of_mem _ hj))

theorem _root_.Frontier.CHD.DIns.LList.head_eq {st : State ℝ≥0} {h : ℕ} {l : List ℕ} (hl : LList st h l) :
    h = match l with | [] => 0 | i :: _ => i + 1 := by
  cases hl <;> rfl

theorem _root_.Frontier.CHD.DIns.LList.cons_inv {st : State ℝ≥0} {h i : ℕ} {l : List ℕ} (hl : LList st h (i :: l)) :
    h = i + 1 ∧ i < st.wlen "ent.nxt" ∧ LList st (st.wa "ent.nxt" i) l := by
  cases hl with
  | cons _ _ hi hl' => exact ⟨rfl, hi, hl'⟩

theorem _root_.Frontier.CHD.DIns.LList.nil_inv {st : State ℝ≥0} {h : ℕ} (hl : LList st h []) : h = 0 := by
  cases hl; rfl

/-- ids of a list are below the length of `ent.nxt` -/
theorem _root_.Frontier.CHD.DIns.LList.lt_len {st : State ℝ≥0} : ∀ {h : ℕ} {l : List ℕ}, LList st h l →
    ∀ i ∈ l, i < st.wlen "ent.nxt"
  | _, _, .nil, i, hi => absurd hi List.not_mem_nil
  | _, _, .cons j l hj hl, i, hi => by
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hj
      · exact hl.lt_len i hi

/-! ## walkCopy -/

/-- walk the list from `dl.p`, copying live ids to `sel.w[dl.w + dl.c]` -/
def walkBody : Stmt :=
  seq (wset "dl.i" (sub (var "dl.p") (lit 1)))
  (seq (ite (eq (load "live" (load "ent.key" (var "dl.i"))) (var "dl.p"))
          (seq (wstore "sel.w" (add (var "dl.w") (var "dl.c")) (var "dl.i"))
               (wset "dl.c" (add (var "dl.c") (lit 1))))
          skip)
  (seq (wset "dl.t" (add (var "dl.t") (lit 1)))
       (wset "dl.p" (load "ent.nxt" (var "dl.i")))))

def walkCopy : Stmt :=
  seq (wset "dl.t" (lit 0)) (seq (wset "dl.c" (lit 0))
    (.while (lt (lit 0) (var "dl.p")) walkBody))

/-- registers written by `walkCopy` -/
def walkRegs : List String := ["dl.t", "dl.c", "dl.i", "dl.p"]

/-! ### one-step loop rules -/

theorem runs_while_step {c : WExpr} {b : Stmt} {q : State ℝ≥0} {Q : State ℝ≥0 → Prop} {x : ℕ}
    (hc : evalW q c = some x) (hx : x ≠ 0)
    (h : Runs ops b (q.charge 1) (fun q' => Runs ops (.while c b) q' Q)) :
    Runs ops (.while c b) q Q := by
  obtain ⟨f1, q', h1, f2, r, h2, hQ⟩ := h
  refine ⟨max f1 f2 + 1, r, ?_, hQ⟩
  rw [exec_while, hc]
  simp only [Option.bind_some, ne_eq, hx, not_false_eq_true, ite_true]
  rw [exec_mono ops h1 (le_max_left _ _)]
  exact exec_mono ops h2 (le_max_right _ _)

theorem runs_while_exit {c : WExpr} {b : Stmt} {q : State ℝ≥0} {Q : State ℝ≥0 → Prop}
    (hc : evalW q c = some 0) (hQ : Q (q.charge 1)) : Runs ops (.while c b) q Q :=
  ⟨1, q.charge 1, by rw [exec_while, hc]; simp, hQ⟩

/-- the segment `arr[base, base + |l|)` spells `l` -/
def Spells (q : State ℝ≥0) (arr : String) (base : ℕ) (l : List ℕ) : Prop :=
  ∀ r (h : r < l.length), q.wa arr (base + r) = l[r]

/-- loop invariant of `walkCopy`: prefix `pre` processed, `rest` remaining -/
structure WInv (st : State ℝ≥0) (w0 : ℕ) (pre rest : List ℕ) (q : State ℝ≥0) : Prop where
  t : q.w "dl.t" = pre.length
  c : q.w "dl.c" = (pre.filter (liveW st)).length
  w : q.w "dl.w" = w0
  list : LList q (q.w "dl.p") rest
  spell : Spells q "sel.w" w0 (pre.filter (liveW st))
  out : ∀ x, (x < w0 ∨ w0 + (pre.filter (liveW st)).length ≤ x) → q.wa "sel.w" x = st.wa "sel.w" x
  unch : Unchanged st q ["sel.w"] [] walkRegs []
  wlen : q.wlen "sel.w" = st.wlen "sel.w"

theorem liveW_of_unch {st q : State ℝ≥0} (hu : Unchanged st q ["sel.w"] [] walkRegs []) (i : ℕ) :
    (q.wa "live" (q.wa "ent.key" i) = i + 1) ↔ liveW st i := by
  have h1 := (hu.warr "live" (by simp)).1
  have h2 := (hu.warr "ent.key" (by simp)).1
  unfold liveW; rw [h1, h2]


/-- one iteration of `walkCopy`'s loop -/
theorem walk_step (st : State ℝ≥0) (w0 : ℕ) {pre rest : List ℕ} {i : ℕ} (q : State ℝ≥0)
    (hkey : ∀ i, i < st.wlen "ent.nxt" → i < st.wlen "ent.key" ∧ st.wa "ent.key" i < st.wlen "live")
    (hcap : ∀ n, n ≤ st.wlen "sel.w" → n + 1 < st.cap)
    (hI : WInv st w0 pre (i :: rest) q) (hlen : w0 + (pre ++ i :: rest).length ≤ st.wlen "sel.w") :
    wp ops walkBody (fun q' => WInv st w0 (pre ++ [i]) rest q' ∧ q'.cost ≤ q.cost + 6) q := by
  obtain ⟨ht, hc, hw, hl, hsp, hout, hu, hwl⟩ := hI
  obtain ⟨hp, hi, hl'⟩ := hl.cons_inv
  have hcapq : q.cap = st.cap := hu.cap
  have hnx : q.wlen "ent.nxt" = st.wlen "ent.nxt" := (hu.warr "ent.nxt" (by simp [walkRegs])).2
  have hnx' : q.wa "ent.nxt" = st.wa "ent.nxt" := (hu.warr "ent.nxt" (by simp)).1
  have hk1 : q.wlen "ent.key" = st.wlen "ent.key" := (hu.warr "ent.key" (by simp)).2
  have hk2 : q.wa "ent.key" = st.wa "ent.key" := (hu.warr "ent.key" (by simp)).1
  have hl1 : q.wlen "live" = st.wlen "live" := (hu.warr "live" (by simp)).2
  have hl2 : q.wa "live" = st.wa "live" := (hu.warr "live" (by simp)).1
  obtain ⟨hik, hkl⟩ := hkey i (hnx ▸ hi)
  have hfl : (pre.filter (liveW st)).length ≤ pre.length := List.length_filter_le _ _
  have hplen : (pre ++ i :: rest).length = pre.length + rest.length + 1 := by simp; omega
  have hc0 : w0 + (pre.filter (liveW st)).length + 1 < st.cap := hcap _ (by omega)
  have hc1 : pre.length + 1 < st.cap := hcap _ (by omega)
  have hsl : w0 + (pre.filter (liveW st)).length < q.wlen "sel.w" := by rw [hwl]; omega
  have h1cap : 1 < st.cap := by omega
  have h0cap : 0 < st.cap := by omega
  have hcw : w0 + (pre.filter (liveW st)).length < st.cap := by omega
  have hcc : (pre.filter (liveW st)).length + 1 < st.cap := by omega
  have hkl' : q.wa "ent.key" i < q.wlen "live" := by rw [hk2, hl1]; exact hkl
  have hi' : i < st.wlen "ent.nxt" := hnx ▸ hi
  by_cases hlv : liveW st i
  · have hbit : q.wa "live" (q.wa "ent.key" i) = i + 1 := by rw [hl2, hk2]; exact hlv
    simp only [walkBody, wp, evalW_sub', evalW_var, evalW_lit', evalW_eq', evalW_load',
      evalW_add', Option.bind_some, State.setW_w, State.charge_w, State.charge_wa,
      State.setW_wa, State.charge_wlen, State.setW_wlen, State.charge_cap, State.setW_cap,
      State.storeW_w, State.storeW_wa, State.storeW_wlen, State.storeW_cap]
    simp [hp, hw, hc, ht, hbit, hcapq, hk1, hnx, hik, hkl', fit, h1cap, hcw, hcc, hc1, hsl, hi']
    have hfa : (pre ++ [i]).filter (liveW st) = pre.filter (liveW st) ++ [i] := by
      simp [List.filter_append, hlv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · rw [hfa]; simp
    · simp [hw]
    · simp only [State.charge_w, State.setW_w, if_true]
      exact hl'.frame (by simp) (by intro j _; simp)
    · rw [hfa]
      intro r hr
      simp only [List.length_append, List.length_singleton] at hr
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and]
      by_cases hrc : r = (pre.filter (liveW st)).length
      · subst hrc; simp
      · have hr' : r < (pre.filter (liveW st)).length := by omega
        rw [if_neg (by omega)]
        rw [hsp r hr', List.getElem_append_left hr']
    · rw [hfa]
      intro x hx
      simp only [List.length_append, List.length_singleton] at hx
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and]
      rw [if_neg (by omega)]
      exact hout x (by omega)
    · simp only [unch_charge]
      rw [unch_setW (by simp [walkRegs]), unch_charge, unch_setW (by simp [walkRegs]), unch_charge,
        unch_setW (by simp [walkRegs]), unch_charge, unch_storeW (by simp), unch_charge, unch_charge,
        unch_setW (by simp [walkRegs])]
      exact hu
    · simp [hwl]
  · have hbit : q.wa "live" (q.wa "ent.key" i) ≠ i + 1 := by rw [hl2, hk2]; exact hlv
    simp only [walkBody, wp, evalW_sub', evalW_var, evalW_lit', evalW_eq', evalW_load',
      evalW_add', Option.bind_some, State.setW_w, State.charge_w, State.charge_wa,
      State.setW_wa, State.charge_wlen, State.setW_wlen, State.charge_cap, State.setW_cap,
      State.storeW_w, State.storeW_wa, State.storeW_wlen, State.storeW_cap]
    simp [hp, hw, hc, ht, hbit, hcapq, hk1, hnx, hik, hkl', fit, h1cap, h0cap, hcw, hcc, hc1, hsl, hi']
    have hfa : (pre ++ [i]).filter (liveW st) = pre.filter (liveW st) := by
      simp [List.filter_append, hlv]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · rw [hfa]; simp [hc]
    · simp [hw]
    · simp only [State.charge_w, State.setW_w, if_true]
      exact hl'.frame (by simp) (by intro j _; simp)
    · rw [hfa]
      intro r hr
      simp only [State.charge_wa, State.setW_wa]
      exact hsp r hr
    · rw [hfa]
      intro x hx
      simp only [State.charge_wa, State.setW_wa]
      exact hout x hx
    · simp only [unch_charge]
      rw [unch_setW (by simp [walkRegs]), unch_charge, unch_setW (by simp [walkRegs]), unch_charge,
        unch_charge, unch_charge, unch_setW (by simp [walkRegs])]
      exact hu
    · simp [hwl]

/-- the loop of `walkCopy`, by induction on the remaining list -/
theorem walk_loop (st : State ℝ≥0) (w0 : ℕ)
    (hkey : ∀ i, i < st.wlen "ent.nxt" → i < st.wlen "ent.key" ∧ st.wa "ent.key" i < st.wlen "live")
    (hcap : ∀ n, n ≤ st.wlen "sel.w" → n + 1 < st.cap) :
    ∀ (rest pre : List ℕ) (q : State ℝ≥0), WInv st w0 pre rest q →
      q.cost ≤ st.cost + 2 + 7 * pre.length →
      w0 + (pre ++ rest).length ≤ st.wlen "sel.w" →
      Runs ops (.while (lt (lit 0) (var "dl.p")) walkBody) q
        (fun r => WInv st w0 (pre ++ rest) [] r ∧ r.cost ≤ st.cost + 3 + 7 * (pre ++ rest).length)
  | [], pre, q, hI, hcost, hlen => by
      have hp : q.w "dl.p" = 0 := hI.list.nil_inv
      have hc1 : 1 < q.cap := by
        rw [hI.unch.cap]; exact hcap 0 (Nat.zero_le _)
      refine runs_while_exit ?_ ?_
      · simp [hp, fit, show 0 < q.cap by omega]
      · simp only [List.append_nil]
        refine ⟨⟨hI.t, hI.c, hI.w, hI.list.frame (by simp) (by simp), hI.spell, hI.out,
          ?_, hI.wlen⟩, ?_⟩
        · exact (hI.unch.trans (Unchanged.charge q 1 _ _ _ _))
        · simp only [State.charge_cost]; omega
  | i :: rest, pre, q, hI, hcost, hlen => by
      have hp : q.w "dl.p" = i + 1 := hI.list.cons_inv.1
      have hcapq : q.cap = st.cap := hI.unch.cap
      have hc1 : 1 < q.cap := by rw [hcapq]; exact lt_of_le_of_lt (by omega) (hcap 0 (Nat.zero_le _))
      refine runs_while_step (x := 1) ?_ one_ne_zero ?_
      · simp [hp, fit, hc1, show 0 < q.cap by omega]
      · have hI' : WInv st w0 pre (i :: rest) (q.charge 1) :=
          ⟨hI.t, hI.c, hI.w, hI.list.frame (by simp) (by simp), hI.spell, hI.out,
            (unch_charge 1).mpr hI.unch, hI.wlen⟩
        refine (wp_sound walkBody _ _ (walk_step st w0 (q.charge 1) hkey hcap hI' hlen)).mono ?_
        rintro q' ⟨hI2, hc2⟩
        have hlen' : w0 + ((pre ++ [i]) ++ rest).length ≤ st.wlen "sel.w" := by
          simpa using hlen
        have := walk_loop st w0 hkey hcap rest (pre ++ [i]) q' hI2
          (by simp only [State.charge_cost, List.length_append, List.length_singleton] at hc2 ⊢; omega)
          hlen'
        simpa [List.append_assoc] using this


/-- **walkCopy**: from `dl.p` = head of the list `ids` and write base `dl.w`, the live ids are
copied to `sel.w[dl.w, dl.w + c)` in list order, `dl.c = c`, `dl.t = |ids|`; only `sel.w` (in
that range) and the registers `dl.t dl.c dl.i dl.p` are written; cost `≤ 5 + 7 |ids|`. -/
theorem walkCopy_spec (st : State ℝ≥0) (ids : List ℕ) (hL : LList st (st.w "dl.p") ids)
    (hkey : ∀ i, i < st.wlen "ent.nxt" → i < st.wlen "ent.key" ∧ st.wa "ent.key" i < st.wlen "live")
    (hcap : st.wlen "sel.w" + 1 < st.cap) (hlen : st.w "dl.w" + ids.length ≤ st.wlen "sel.w") :
    Runs ops walkCopy st (fun r => WInv st (st.w "dl.w") ids [] r ∧
      r.cost ≤ st.cost + 5 + 7 * ids.length) := by
  have hcap' : ∀ n, n ≤ st.wlen "sel.w" → n + 1 < st.cap := fun n hn => by omega
  have h0 : 0 < st.cap := by omega
  apply wp_sound
  rw [walkCopy, wp_seq, wp_wset_of (a := 0) (by simp [fit, h0]), wp_seq,
    wp_wset_of (a := 0) (by simp [fit, h0])]
  set q0 := ((((st.setW "dl.t" 0).charge 1).setW "dl.c" 0).charge 1) with hq0
  have hI0 : WInv st (st.w "dl.w") [] ids q0 := by
    refine ⟨by simp [hq0], by simp [hq0], by simp [hq0], ?_, ?_, ?_, ?_, by simp [hq0]⟩
    · have : q0.w "dl.p" = st.w "dl.p" := by simp [hq0]
      rw [this]; exact hL.frame (by simp [hq0]) (by intro j _; simp [hq0])
    · intro r hr; simp at hr
    · intro x _; simp [hq0]
    · rw [hq0, unch_charge, unch_setW (by simp [walkRegs]), unch_charge,
        unch_setW (by simp [walkRegs])]
      exact Unchanged.refl _ _ _ _ _
  have := walk_loop (ops := ops) st (st.w "dl.w") hkey hcap' ids [] q0 hI0
    (by simp [hq0]) (by simpa using hlen)
  show Runs ops _ q0 _
  refine this.mono ?_
  rintro r ⟨hr1, hr2⟩
  simp only [List.nil_append] at hr1 hr2
  exact ⟨hr1, by omega⟩

/-! ## buildList: link the id segment `sel.w[dl.a, dl.a + dl.n)` into a list -/

def buildBody : Stmt :=
  seq (wset "dl.j" (sub (var "dl.j") (lit 1)))
  (seq (wset "dl.x" (load "sel.w" (add (var "dl.a") (var "dl.j"))))
  (seq (wstore "ent.nxt" (var "dl.x") (var "dl.h"))
       (wset "dl.h" (add (var "dl.x") (lit 1)))))

def buildLoop : Stmt := .while (lt (lit 0) (var "dl.j")) buildBody

def buildList : Stmt :=
  seq (wset "dl.h" (lit 0)) (seq (wset "dl.j" (var "dl.n")) buildLoop)

/-- registers written by `buildList` -/
def buildRegs : List String := ["dl.h", "dl.j", "dl.x"]

/-- loop invariant of `buildList`: the suffix `l.drop j` is linked -/
structure BInv (st : State ℝ≥0) (a : ℕ) (l : List ℕ) (j : ℕ) (q : State ℝ≥0) : Prop where
  jr : q.w "dl.j" = j
  jle : j ≤ l.length
  ar : q.w "dl.a" = a
  list : LList q (q.w "dl.h") (l.drop j)
  outside : ∀ y, y ∉ l.drop j → q.wa "ent.nxt" y = st.wa "ent.nxt" y
  unch : Unchanged st q ["ent.nxt"] [] buildRegs []
  nlen : q.wlen "ent.nxt" = st.wlen "ent.nxt"

theorem build_loop (st : State ℝ≥0) (a : ℕ) (l : List ℕ) (hsp : Spells st "sel.w" a l)
    (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < st.wlen "ent.nxt")
    (hseg : a + l.length ≤ st.wlen "sel.w") (hcap : a + l.length + 1 < st.cap)
    (hxc : ∀ x ∈ l, x + 1 < st.cap) :
    ∀ (j : ℕ) (q : State ℝ≥0), BInv st a l j q → q.cost ≤ st.cost + 2 + 5 * (l.length - j) →
      Runs ops buildLoop q (fun r => BInv st a l 0 r ∧ r.cost ≤ st.cost + 3 + 5 * l.length)
  | 0, q, hI, hc => by
      refine runs_while_exit ?_ ?_
      · have h0 : 0 < q.cap := by rw [hI.unch.cap]; omega
        simp [hI.jr, fit, h0]
      · refine ⟨⟨hI.jr, hI.jle, hI.ar, hI.list.frame (by simp) (by simp), hI.outside,
          (unch_charge 1).mpr hI.unch, hI.nlen⟩, ?_⟩
        simp only [State.charge_cost]; simp at hc; omega
  | j + 1, q, hI, hc => by
      obtain ⟨hjr, hjle, har, hl, hout, hu, hnl⟩ := hI
      have hcapq : q.cap = st.cap := hu.cap
      have hjl : j < l.length := by omega
      have hsw : q.wa "sel.w" = st.wa "sel.w" := (hu.warr "sel.w" (by simp)).1
      have hswl : q.wlen "sel.w" = st.wlen "sel.w" := (hu.warr "sel.w" (by simp)).2
      set x := l[j] with hx
      have hxm : x ∈ l := List.getElem_mem _
      have hxs : q.wa "sel.w" (a + j) = x := by rw [hsw]; exact hsp j hjl
      have hxl : x < q.wlen "ent.nxt" := by rw [hnl]; exact hlt x hxm
      have hdrop : l.drop j = x :: l.drop (j + 1) := List.drop_eq_getElem_cons hjl
      have hxnot : x ∉ l.drop (j + 1) := by
        have := hdrop ▸ (List.drop_sublist j l).nodup hnd
        exact (List.nodup_cons.mp this).1
      have h1 : 1 < q.cap := by rw [hcapq]; omega
      refine runs_while_step (x := 1) (by simp [hjr, fit, h1, show 0 < q.cap by omega]) one_ne_zero ?_
      apply wp_sound
      have hajc : a + j < q.cap := by rw [hcapq]; omega
      have hajl : a + j < q.wlen "sel.w" := by rw [hswl]; omega
      have hx1 : x + 1 < q.cap := by rw [hcapq]; exact hxc x hxm
      simp only [buildLoop, buildBody, wp, evalW_sub', evalW_var, evalW_lit', evalW_load',
        evalW_add', Option.bind_some, State.setW_w, State.charge_w, State.charge_wa,
        State.setW_wa, State.charge_wlen, State.setW_wlen, State.charge_cap, State.setW_cap,
        State.storeW_w, State.storeW_wa, State.storeW_wlen, State.storeW_cap]
      simp [hjr, har, fit, h1, show 0 < q.cap by omega, hajc, hajl, hxs, hxl, hx1]
      refine build_loop st a l hsp hnd hlt hseg hcap hxc j _ ?_ ?_
      · refine ⟨by simp, by omega, by simp [har], ?_, ?_, ?_, by simp [hnl]⟩
        · simp only [State.charge_w, State.setW_w, if_true]
          rw [hdrop]
          refine .cons x _ (by simp [hxl]) ?_
          simp only [State.charge_wa, State.setW_wa, State.storeW_wa, and_self, if_true]
          refine hl.frame (by simp) ?_
          intro y hy
          simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and]
          rw [if_neg (by intro h; rw [h] at hy; exact hxnot hy)]
        · intro y hy
          rw [hdrop] at hy
          simp only [List.mem_cons, not_or] at hy
          simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and]
          rw [if_neg hy.1]
          exact hout y hy.2
        · simp only [unch_charge]
          rw [unch_setW (by simp [buildRegs]), unch_charge, unch_storeW (by simp), unch_charge,
            unch_setW (by simp [buildRegs]), unch_charge, unch_setW (by simp [buildRegs]), unch_charge]
          exact hu
      · simp only [State.charge_cost, State.setW_cost, State.storeW_cost]
        omega

/-- **buildList**: links the id segment `l` spelled by `sel.w[dl.a, dl.a + dl.n)` (distinct ids)
into a list headed by `dl.h`; `ent.nxt` changes only at ids of `l`. -/
theorem buildList_spec (st : State ℝ≥0) (l : List ℕ) (hsp : Spells st "sel.w" (st.w "dl.a") l)
    (hn : st.w "dl.n" = l.length) (hnd : l.Nodup) (hlt : ∀ x ∈ l, x < st.wlen "ent.nxt")
    (hseg : st.w "dl.a" + l.length ≤ st.wlen "sel.w") (hcap : st.w "dl.a" + l.length + 1 < st.cap)
    (hxc : ∀ x ∈ l, x + 1 < st.cap) :
    Runs ops buildList st (fun r => LList r (r.w "dl.h") l ∧
      (∀ y, y ∉ l → r.wa "ent.nxt" y = st.wa "ent.nxt" y) ∧
      Unchanged st r ["ent.nxt"] [] buildRegs [] ∧ r.wlen "ent.nxt" = st.wlen "ent.nxt" ∧
      r.cost ≤ st.cost + 3 + 5 * l.length) := by
  have h0 : 0 < st.cap := by omega
  apply wp_sound
  rw [buildList, wp_seq, wp_wset_of (a := 0) (by simp [fit, h0]), wp_seq,
    wp_wset_of (a := l.length) (by simp [hn])]
  set q0 := ((((st.setW "dl.h" 0).charge 1).setW "dl.j" l.length).charge 1) with hq0
  have hI0 : BInv st (st.w "dl.a") l l.length q0 := by
    refine ⟨by simp [hq0], le_rfl, by simp [hq0], ?_, ?_, ?_, by simp [hq0]⟩
    · have : q0.w "dl.h" = 0 := by simp [hq0]
      rw [this, List.drop_length]; exact .nil
    · intro y _; simp [hq0]
    · rw [hq0, unch_charge, unch_setW (by simp [buildRegs]), unch_charge,
        unch_setW (by simp [buildRegs])]
      exact Unchanged.refl _ _ _ _ _
  have := build_loop (ops := ops) st (st.w "dl.a") l hsp hnd hlt hseg hcap hxc l.length q0 hI0
    (by simp [hq0])
  show Runs ops _ q0 _
  refine this.mono ?_
  rintro r ⟨hr, hc⟩
  refine ⟨?_, ?_, hr.unch, hr.nlen, hc⟩
  · have := hr.list; simpa using this
  · intro y hy; exact hr.outside y (by simpa using hy)

/-! ## concat: splice list 2 behind list 1 in `O(1)` -/

/-- the last entry of a nonempty list points to `0` -/
theorem _root_.Frontier.CHD.DIns.LList.nxt_last {st : State ℝ≥0} : ∀ {h : ℕ} {l : List ℕ}, LList st h l → l ≠ [] →
    st.wa "ent.nxt" (tlWord l - 1) = 0
  | _, _, .nil, hne => absurd rfl hne
  | _, _, .cons i [] hi hl, _ => by
      simp only [tlWord, List.getLast?_singleton, Nat.add_sub_cancel]
      exact hl.nil_inv
  | _, _, .cons i (j :: l) hi hl, _ => by
      have := hl.nxt_last (List.cons_ne_nil _ _)
      simpa [tlWord, List.getLast?_cons_cons] using this

theorem tlWord_mem {l : List ℕ} (hne : l ≠ []) : tlWord l - 1 ∈ l := by
  unfold tlWord
  rcases h : l.getLast? with _ | i
  · simp at h; exact absurd h hne
  · simp only [Nat.add_sub_cancel]; exact List.mem_of_getLast? h

/-- **append**: after pointing the last entry of `l₁` to the head of `l₂` the lists join -/
theorem _root_.Frontier.CHD.DIns.LList.append {st st' : State ℝ≥0} {h₁ h₂ : ℕ} {l₁ l₂ : List ℕ} (hl₁ : LList st h₁ l₁)
    (hl₂ : LList st h₂ l₂) (hne : l₁ ≠ []) (hnd : l₁.Nodup) (hdisj : ∀ x ∈ l₁, x ∉ l₂)
    (hlen : st'.wlen "ent.nxt" = st.wlen "ent.nxt")
    (hset : st'.wa "ent.nxt" (tlWord l₁ - 1) = h₂)
    (hkeep : ∀ y, y ≠ tlWord l₁ - 1 → st'.wa "ent.nxt" y = st.wa "ent.nxt" y) :
    LList st' h₁ (l₁ ++ l₂) := by
  induction hl₁ with
  | nil => exact absurd rfl hne
  | cons i l hi hl ih =>
    rcases l with _ | ⟨j, l'⟩
    · -- `i` is the last entry
      simp only [tlWord, List.getLast?_singleton, Nat.add_sub_cancel] at hset hkeep
      refine .cons i l₂ (by rw [hlen]; exact hi) ?_
      rw [hset]
      refine hl₂.frame hlen (fun y hy => hkeep y ?_)
      rintro rfl; exact hdisj _ List.mem_cons_self hy
    · have htl : tlWord (i :: j :: l') = tlWord (j :: l') := by
        simp [tlWord, List.getLast?_cons_cons]
      rw [htl] at hset hkeep
      have hne' : j :: l' ≠ [] := List.cons_ne_nil _ _
      have hmem := tlWord_mem hne'
      have hinot : i ∉ j :: l' := (List.nodup_cons.mp hnd).1
      have hik : st'.wa "ent.nxt" i = st.wa "ent.nxt" i := hkeep i (fun h => hinot (h ▸ hmem))
      refine .cons i _ (by rw [hlen]; exact hi) ?_
      rw [hik]
      exact ih hne' (List.nodup_cons.mp hnd).2 (fun x hx => hdisj x (List.mem_cons_of_mem _ hx))
        hset hkeep

/-! ## concat: `c ← c ++ b` on block records (`O(1)`) -/

/-- append the entries of block record `mg.b` to block record `mg.c` -/
def concatS : Stmt :=
  seq (ite (lt (lit 0) (load "blk.hd" (var "mg.b")))
         (seq (ite (eq (load "blk.hd" (var "mg.c")) (lit 0))
                (wstore "blk.hd" (var "mg.c") (load "blk.hd" (var "mg.b")))
                (wstore "ent.nxt" (sub (load "blk.tl" (var "mg.c")) (lit 1)) (load "blk.hd" (var "mg.b"))))
              (wstore "blk.tl" (var "mg.c") (load "blk.tl" (var "mg.b"))))
         skip)
  (wstore "blk.cnt" (var "mg.c") (add (load "blk.cnt" (var "mg.c")) (load "blk.cnt" (var "mg.b"))))

theorem tlWord_append_of_ne {l₁ l₂ : List ℕ} (h : l₂ ≠ []) : tlWord (l₁ ++ l₂) = tlWord l₂ := by
  unfold tlWord; rw [List.getLast?_append_of_ne_nil _ h]

theorem tlWord_append_nil (l : List ℕ) : tlWord (l ++ []) = tlWord l := by simp

theorem tlWord_pos {l : List ℕ} (h : l ≠ []) : 0 < tlWord l := by
  unfold tlWord
  rcases hl : l.getLast? with _ | i
  · simp at hl; exact absurd hl h
  · simp

theorem _root_.Frontier.CHD.DIns.LList.head_pos {st : State ℝ≥0} {h : ℕ} {l : List ℕ} (hl : LList st h l) (hne : l ≠ []) :
    0 < h := by
  rcases l with _ | ⟨i, l⟩
  · exact absurd rfl hne
  · rw [hl.cons_inv.1]; omega

theorem _root_.Frontier.CHD.DIns.LList.nil_of_zero {st : State ℝ≥0} {l : List ℕ} (hl : LList st 0 l) : l = [] := by
  rcases l with _ | ⟨i, l⟩
  · rfl
  · have := hl.cons_inv.1; omega

section Concat

open Frontier.CHD.DIns Frontier.CHD.DB

variable {G : Graph} {s : Fin G.n}

/-- entries and separators only depend on the pool/label arrays, not on `blk.hd/tl/cnt, ent.nxt` -/
theorem entRep_keep {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {i : ℕ} {v : Fin G.n} {a : WLab G s} (h : EntRep q H V i v a)
    (hu : Unchanged q r ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] [] [] []) :
    EntRep r H V i v a :=
  h.of_eq (by rw [(hu.warr _ (by simp)).1]) (by rw [(hu.varr _ (by simp)).1])
    (by rw [(hu.warr _ (by simp [entA])).1]) (by rw [(hu.warr _ (by simp [entA])).1])
    (by rw [(hu.warr _ (by simp [entA])).1]) (by rw [(hu.warr _ (by simp [entA])).1])

theorem sepRep_keep {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bid : ℕ} {sp : WithBot (WLab G s)} (h : SepRep q H V bid sp)
    (hu : Unchanged q r ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] [] [] []) :
    SepRep r H V bid sp :=
  h.of_eq (by rw [(hu.warr _ (by simp)).1]) (by rw [(hu.varr _ (by simp)).1])
    (by rw [(hu.warr _ (by simp [blkA])).1]) (by rw [(hu.warr _ (by simp [blkA])).1])
    (by rw [(hu.warr _ (by simp [blkA])).1]) (by rw [(hu.warr _ (by simp [blkA])).1])

/-- **concat**: block record `c` absorbs the entries of block record `b` -/
theorem concat_spec (q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (c b : ℕ) (cb bb : Block (Fin G.n) (WLab G s))
    (hc : BlkRep q H V c cb) (hb : BlkRep q H V b bb)
    (hnd : (cb.ents.map (·.id)).Nodup) (hdisj : ∀ x ∈ cb.ents.map (·.id), x ∉ bb.ents.map (·.id))
    (hcl : c < q.wlen "blk.hd" ∧ c < q.wlen "blk.tl" ∧ c < q.wlen "blk.cnt")
    (hbl : b < q.wlen "blk.hd" ∧ b < q.wlen "blk.tl" ∧ b < q.wlen "blk.cnt")
    (hcap : cb.ents.length + bb.ents.length < q.cap) (h1 : 1 < q.cap)
    (hmc : q.w "mg.c" = c) (hmb : q.w "mg.b" = b) :
    wp ops concatS (fun r => BlkRep r H V c ⟨cb.sep, cb.ents ++ bb.ents⟩ ∧
      (∀ y, y ≠ c → r.wa "blk.hd" y = q.wa "blk.hd" y ∧ r.wa "blk.tl" y = q.wa "blk.tl" y ∧
        r.wa "blk.cnt" y = q.wa "blk.cnt" y) ∧
      (∀ y, y ∉ cb.ents.map (·.id) → r.wa "ent.nxt" y = q.wa "ent.nxt" y) ∧
      Unchanged q r ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] [] [] [] ∧
      r.wlen "ent.nxt" = q.wlen "ent.nxt" ∧ r.cost ≤ q.cost + 8 ∧ (∀ a, r.wlen a = q.wlen a)) q := by
  obtain ⟨hcs, hcL, hcE, hcc, hct⟩ := hc
  obtain ⟨hbs, hbL, hbE, hbc, hbt⟩ := hb
  have h0 : 0 < q.cap := by omega
  by_cases hbe : bb.ents = []
  · -- nothing to splice
    have hhb : q.wa "blk.hd" b = 0 := by rw [hbe] at hbL; exact hbL.nil_inv
    have hcq : cb.ents.length < q.cap := by omega
    simp [concatS, wp, fit, h0, h1, hmb, hmc, hhb, hcl, hbl, hcc, hbc, hbe, hcq]
    have hU : Unchanged q (((q.charge 1).charge 1).storeW "blk.cnt" c cb.ents.length)
        ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] [] [] [] := by
      rw [unch_storeW (by simp), unch_charge, unch_charge]; exact Unchanged.refl _ _ _ _ _
    have hU' := (unch_charge (st' := ((q.charge 1).charge 1).storeW "blk.cnt" c cb.ents.length) 1).mpr hU
    refine ⟨⟨sepRep_keep hcs hU', ?_, fun x hx => entRep_keep (hcE x hx) hU', by simp, ?_⟩,
      fun y h1 h2 => absurd h2 h1, hU⟩
    · simp only [State.charge_wa, State.storeW_wa, show ("blk.hd" = "blk.cnt") = False by decide,
        false_and, if_false]
      exact hcL.of_eq (fun j _ => by simp) (by simp)
    · simp only [State.charge_wa, State.storeW_wa, show ("blk.tl" = "blk.cnt") = False by decide,
        false_and, if_false]
      exact hct
  · have hhb : 0 < q.wa "blk.hd" b := hbL.head_pos (by simpa using hbe)
    have hbcq : bb.ents.length < q.cap := by omega
    have hcq : cb.ents.length < q.cap := by omega
    by_cases hce : cb.ents = []
    · have hhc : q.wa "blk.hd" c = 0 := by rw [hce] at hcL; exact hcL.nil_inv
      simp [concatS, wp, fit, h0, h1, hmb, hmc, hhb, hhc, hcl, hbl, hcc, hbc, hce, hbcq]
      set r0 := (((((((q.charge 1).charge 1).storeW "blk.hd" c (q.wa "blk.hd" b)).charge 1).storeW
        "blk.tl" c (q.wa "blk.tl" b)).charge 1).storeW "blk.cnt" c bb.ents.length) with hr0
      have hU : Unchanged q r0 ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] [] [] [] := by
        rw [hr0, unch_storeW (by simp), unch_charge, unch_storeW (by simp), unch_charge,
          unch_storeW (by simp), unch_charge, unch_charge]
        exact Unchanged.refl _ _ _ _ _
      have hU' := (unch_charge (st' := r0) 1).mpr hU
      refine ⟨⟨sepRep_keep hcs hU', ?_, fun x hx => entRep_keep (hbE x hx) hU', by simp [hr0], ?_⟩,
        fun y h1 => ⟨fun h2 => absurd h2 h1, fun h2 => absurd h2 h1, fun h2 => absurd h2 h1⟩, hU⟩
      · have : (r0.charge 1).wa "blk.hd" c = q.wa "blk.hd" b := by simp [hr0]
        rw [this]
        exact hbL.of_eq (fun j _ => by simp [hr0]) (by simp [hr0])
      · have : (r0.charge 1).wa "blk.tl" c = q.wa "blk.tl" b := by simp [hr0]
        rw [this]; exact hbt
    · have hhc : q.wa "blk.hd" c ≠ 0 := Nat.pos_iff_ne_zero.mp (hcL.head_pos (by simpa using hce))
      have hcne : cb.ents.map (·.id) ≠ [] := by simpa using hce
      have hbne : bb.ents.map (·.id) ≠ [] := by simpa using hbe
      have htc : 0 < q.wa "blk.tl" c := by rw [hct]; exact tlWord_pos hcne
      have hmem := tlWord_mem hcne
      have hlast : tlWord (cb.ents.map (·.id)) - 1 < q.wlen "ent.nxt" := hcL.lt_len _ hmem
      have hsum : cb.ents.length + bb.ents.length < q.cap := hcap
      simp [concatS, wp, fit, h0, h1, hmb, hmc, hhb, hhc, hcl, hbl, hcc, hbc, hct, hlast, hsum]
      set t1 := tlWord (cb.ents.map (·.id)) - 1 with ht1
      set r0 := (((((((q.charge 1).charge 1).storeW "ent.nxt" t1 (q.wa "blk.hd" b)).charge 1).storeW
        "blk.tl" c (q.wa "blk.tl" b)).charge 1).storeW "blk.cnt" c (cb.ents.length + bb.ents.length))
        with hr0
      have hU : Unchanged q r0 ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] [] [] [] := by
        rw [hr0, unch_storeW (by simp), unch_charge, unch_storeW (by simp), unch_charge,
          unch_storeW (by simp), unch_charge, unch_charge]
        exact Unchanged.refl _ _ _ _ _
      have hU' := (unch_charge (st' := r0) 1).mpr hU
      refine ⟨⟨sepRep_keep hcs hU', ?_, ?_, by simp [hr0], ?_⟩,
        fun y h1 => ⟨fun h2 => absurd h2 h1, fun h2 => absurd h2 h1⟩, ?_, hU⟩
      · have : (r0.charge 1).wa "blk.hd" c = q.wa "blk.hd" c := by simp [hr0]
        rw [this, List.map_append]
        refine LList.append hcL hbL hcne hnd hdisj (by simp [hr0]) (by simp [hr0, ht1]) ?_
        intro y hy
        have hy' : y ≠ t1 := hy
        simp [hr0, hy']
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact entRep_keep (hcE x hx) hU'
        · exact entRep_keep (hbE x hx) hU'
      · have : (r0.charge 1).wa "blk.tl" c = q.wa "blk.tl" b := by simp [hr0]
        rw [this, hbt, List.map_append, tlWord_append_of_ne hbne]
      · intro y hy hyt
        exfalso
        obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hmem
        exact hy x hx (by rw [hxy, hyt])

end Concat

/-! ## Families of block records -/

section Recs

open Frontier.CHD.DIns Frontier.CHD.DB

variable {G : Graph} {s : Fin G.n}

/-- entry ids of a list of blocks -/
def entIds (bs : List (Block (Fin G.n) (WLab G s))) : List ℕ := bs.flatMap (fun b => b.ents.map (·.id))

/-- a family of block records: distinct record ids, each represented, all entry ids distinct -/
def RecsOK (q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (recs : List (ℕ × Block (Fin G.n) (WLab G s))) : Prop :=
  (recs.map Prod.fst).Nodup ∧ (∀ p ∈ recs, BlkRep q H V p.1 p.2) ∧ (entIds (recs.map Prod.snd)).Nodup

theorem entIds_cons (b : Block (Fin G.n) (WLab G s)) (bs : List (Block (Fin G.n) (WLab G s))) :
    entIds (b :: bs) = b.ents.map (·.id) ++ entIds bs := by simp [entIds]

theorem entIds_append (bs₁ bs₂ : List (Block (Fin G.n) (WLab G s))) :
    entIds (bs₁ ++ bs₂) = entIds bs₁ ++ entIds bs₂ := by simp [entIds]

theorem RecsOK.perm {q : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {r₁ r₂ : List (ℕ × Block (Fin G.n) (WLab G s))} (h : RecsOK q H V r₁) (hp : r₁.Perm r₂) :
    RecsOK q H V r₂ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨(hp.map _).nodup_iff.mp h1, fun p hp' => h2 p (hp.symm.subset hp'), ?_⟩
  have : (entIds (r₁.map Prod.snd)).Perm (entIds (r₂.map Prod.snd)) := by
    unfold entIds; exact (hp.map _).flatMap_right _
  exact this.nodup_iff.mp h3

end Recs

section Recs2

open Frontier.CHD.DIns Frontier.CHD.DB

variable {G : Graph} {s : Fin G.n}

/-- **concat on a family**: records `c` and `b` of a family fuse into `c` -/
theorem concat_recs (q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (c b : ℕ) (cb bb : Block (Fin G.n) (WLab G s)) (rest : List (ℕ × Block (Fin G.n) (WLab G s)))
    (hR : RecsOK q H V ((c, cb) :: (b, bb) :: rest))
    (hcl : c < q.wlen "blk.hd" ∧ c < q.wlen "blk.tl" ∧ c < q.wlen "blk.cnt")
    (hbl : b < q.wlen "blk.hd" ∧ b < q.wlen "blk.tl" ∧ b < q.wlen "blk.cnt")
    (hcap : cb.ents.length + bb.ents.length < q.cap) (h1 : 1 < q.cap)
    (hmc : q.w "mg.c" = c) (hmb : q.w "mg.b" = b) :
    wp ops concatS (fun r => RecsOK r H V ((c, ⟨cb.sep, cb.ents ++ bb.ents⟩) :: rest) ∧
      Unchanged q r ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] [] [] [] ∧
      r.wlen "ent.nxt" = q.wlen "ent.nxt" ∧ r.cost ≤ q.cost + 8 ∧ (∀ a, r.wlen a = q.wlen a)) q := by
  obtain ⟨hn, hB, he⟩ := hR
  simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
  obtain ⟨⟨hcb, hcr⟩, hbr, hrn⟩ := hn
  have hBc := hB (c, cb) List.mem_cons_self
  have hBb := hB (b, bb) (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [List.map_cons, entIds_cons] at he
  rw [List.nodup_append] at he
  obtain ⟨hcn, he2, hdisj1⟩ := he
  rw [List.nodup_append] at he2
  obtain ⟨hbn, hrn', hdisj2⟩ := he2
  have hdisj : ∀ x ∈ cb.ents.map (·.id), x ∉ bb.ents.map (·.id) := by
    intro x hx hx'; exact hdisj1 x hx x (List.mem_append_left _ hx') rfl
  have hdisjR : ∀ x ∈ cb.ents.map (·.id), x ∉ entIds (rest.map Prod.snd) := by
    intro x hx hx'; exact hdisj1 x hx x (List.mem_append_right _ hx') rfl
  refine wp_mono concatS ?_ q (concat_spec q H V c b cb bb hBc hBb hcn hdisj hcl hbl hcap h1 hmc hmb)
  rintro r ⟨hBc', hfr, hnx, hU, hnl, hc, hwl⟩
  refine ⟨⟨?_, ?_, ?_⟩, hU, hnl, hc, hwl⟩
  · simp only [List.map_cons, List.nodup_cons]; exact ⟨hcr, hrn⟩
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hBc'
    · have hpB := hB p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
      have hpc : p.1 ≠ c := fun h => hcr (h ▸ List.mem_map_of_mem hp)
      obtain ⟨h1', h2', h3', h4', h5'⟩ := hpB
      obtain ⟨fh, ft, fc⟩ := hfr p.1 hpc
      refine ⟨sepRep_keep h1' hU, ?_, fun x hx => entRep_keep (h3' x hx) hU, by rw [fc]; exact h4',
        by rw [ft]; exact h5'⟩
      rw [fh]
      refine h2'.of_eq (fun j hj => hnx j ?_) (le_of_eq hnl.symm)
      intro hjc
      apply hdisjR j hjc
      unfold entIds
      exact List.mem_flatMap.mpr ⟨p.2, List.mem_map_of_mem hp, hj⟩
  · simp only [List.map_cons, entIds_cons, List.map_append]
    rw [List.append_assoc]
    rw [List.nodup_append, List.nodup_append]
    refine ⟨hcn, ⟨hbn, hrn', hdisj2⟩, ?_⟩
    intro x hx y hy hxy
    rcases List.mem_append.mp hy with hy | hy
    · exact hdisj1 x hx y (List.mem_append_left _ hy) hxy
    · exact hdisj1 x hx y (List.mem_append_right _ hy) hxy

end Recs2

/-! ## Merge: the grouping loop (in place on the shared stack) -/

section MergeLoop

open Frontier.CHD.DIns Frontier.CHD.DB

variable {G : Graph} {s : Fin G.n}

/-- `dsl.stk[top - w] := x; w := w + 1` -/
def emitS (x : WExpr) : Stmt :=
  seq (wstore "dsl.stk" (sub (var "mg.top") (var "mg.w")) x) (wset "mg.w" (add (var "mg.w") (lit 1)))

/-- process child block `i` (list order = from the stack top down) -/
def mgBody : Stmt :=
  seq (wset "mg.b" (load "dsl.stk" (sub (var "mg.top") (var "mg.i"))))
  (seq (ite (eq (var "mg.acc") (lit 0))
          (ite (lt (load "blk.cnt" (var "mg.b")) (var "mg.g"))
             (wset "mg.acc" (add (var "mg.b") (lit 1)))
             (emitS (var "mg.b")))
          (seq (wset "mg.c" (sub (var "mg.acc") (lit 1)))
          (seq concatS
               (ite (lt (load "blk.cnt" (var "mg.c")) (var "mg.g"))
                  skip
                  (seq (emitS (var "mg.c")) (wset "mg.acc" (lit 0)))))))
       (wset "mg.i" (add (var "mg.i") (lit 1))))

def mgLoop : Stmt := .while (lt (var "mg.i") (var "mg.ck")) mgBody

/-- registers written by the grouping loop -/
def mgRegs : List String := ["mg.i", "mg.w", "mg.acc", "mg.b", "mg.c"]

/-- the unread child records `(cid j, block j)` for `j ≥ i` -/
def unread (cid : ℕ → ℕ) (cbl : List (Block (Fin G.n) (WLab G s))) (i : ℕ) :
    List (ℕ × Block (Fin G.n) (WLab G s)) :=
  ((List.range' i (cbl.length - i)).map cid).zip (cbl.drop i)

/-- loop invariant of the grouping loop -/
structure GInv (st0 q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (g top : ℕ) (cid : ℕ → ℕ) (cbl : List (Block (Fin G.n) (WLab G s)))
    (others : List (ℕ × Block (Fin G.n) (WLab G s)))
    (i : ℕ) (em : List (Block (Fin G.n) (WLab G s))) (emIds : List ℕ)
    (cur : Option (ℕ × Block (Fin G.n) (WLab G s))) : Prop where
  ireg : q.w "mg.i" = i
  ile : i ≤ cbl.length
  wreg : q.w "mg.w" = em.length
  wle : em.length + (if cur.isSome then 1 else 0) ≤ i
  accreg : q.w "mg.acc" = (match cur with | none => 0 | some p => p.1 + 1)
  geq : em ++ groupAux g (cur.map Prod.snd) (cbl.drop i) = groupAux g none cbl
  emlen : emIds.length = em.length
  emstk : ∀ j (h : j < em.length), q.wa "dsl.stk" (top - j) = emIds[j]'(emlen ▸ h)
  unrd : ∀ j, i ≤ j → j < cbl.length → q.wa "dsl.stk" (top - j) = cid j
  below : ∀ x, x + cbl.length ≤ top → q.wa "dsl.stk" x = st0.wa "dsl.stk" x
  recs : RecsOK q H V (emIds.zip em ++ cur.toList ++ unread cid cbl i ++ others)
  topr : q.w "mg.top" = top
  gr : q.w "mg.g" = g
  ckr : q.w "mg.ck" = cbl.length
  unch : Unchanged st0 q ["dsl.stk", "blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] [] mgRegs []
  lstk : q.wlen "dsl.stk" = st0.wlen "dsl.stk"
  lhd : q.wlen "blk.hd" = st0.wlen "blk.hd"
  ltl : q.wlen "blk.tl" = st0.wlen "blk.tl"
  lcnt : q.wlen "blk.cnt" = st0.wlen "blk.cnt"
  lnx : q.wlen "ent.nxt" = st0.wlen "ent.nxt"

theorem unread_cons (cid : ℕ → ℕ) (cbl : List (Block (Fin G.n) (WLab G s))) (i : ℕ)
    (hi : i < cbl.length) :
    unread cid cbl i = (cid i, cbl[i]) :: unread cid cbl (i + 1) := by
  unfold unread
  have e1 : cbl.length - i = (cbl.length - (i + 1)) + 1 := by omega
  rw [e1, List.range'_succ, List.map_cons, List.drop_eq_getElem_cons hi, List.zip_cons_cons]

theorem unread_end (cid : ℕ → ℕ) (cbl : List (Block (Fin G.n) (WLab G s))) :
    unread cid cbl cbl.length = [] := by
  simp [unread]

end MergeLoop

section MergeStep

open Frontier.CHD.DIns Frontier.CHD.DB

variable {G : Graph} {s : Fin G.n}

/-- the arrays a block record depends on -/
def bArrs : List String :=
  ["blk.bot", "blk.h", "blk.v", "blk.e", "blk.r", "blk.hd", "blk.tl", "blk.cnt", "ent.nxt",
   "ent.key", "ent.h", "ent.v", "ent.e", "ent.r"]

/-- block records only depend on the arrays `bArrs` (and the two label value arrays) -/
theorem blkRep_of_arrays {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {bid : ℕ} {b : Block (Fin G.n) (WLab G s)} (h : BlkRep q H V bid b)
    (hA : ∀ a ∈ bArrs, r.wa a = q.wa a) (hV1 : r.va "ent.len" = q.va "ent.len")
    (hV2 : r.va "blk.len" = q.va "blk.len") (hlen : r.wlen "ent.nxt" = q.wlen "ent.nxt") :
    BlkRep r H V bid b := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1.of_eq (by rw [hA _ (by simp [bArrs])]) (by rw [show blkA.l = "blk.len" from rfl, hV2])
    (by rw [hA _ (by simp [bArrs, blkA])]) (by rw [hA _ (by simp [bArrs, blkA])])
    (by rw [hA _ (by simp [bArrs, blkA])]) (by rw [hA _ (by simp [bArrs, blkA])]), ?_,
    fun x hx => (h3 x hx).of_eq (by rw [hA _ (by simp [bArrs])])
      (by rw [show entA.l = "ent.len" from rfl, hV1]) (by rw [hA _ (by simp [bArrs, entA])])
      (by rw [hA _ (by simp [bArrs, entA])]) (by rw [hA _ (by simp [bArrs, entA])])
      (by rw [hA _ (by simp [bArrs, entA])]), by rw [hA _ (by simp [bArrs])]; exact h4,
    by rw [hA _ (by simp [bArrs])]; exact h5⟩
  rw [hA _ (by simp [bArrs])]
  exact h2.of_eq (fun j _ => by rw [hA _ (by simp [bArrs])]) (le_of_eq hlen.symm)

theorem recsOK_of_arrays {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {recs : List (ℕ × Block (Fin G.n) (WLab G s))} (h : RecsOK q H V recs)
    (hA : ∀ a ∈ bArrs, r.wa a = q.wa a) (hV1 : r.va "ent.len" = q.va "ent.len")
    (hV2 : r.va "blk.len" = q.va "blk.len") (hlen : r.wlen "ent.nxt" = q.wlen "ent.nxt") :
    RecsOK r H V recs :=
  ⟨h.1, fun p hp => blkRep_of_arrays (h.2.1 p hp) hA hV1 hV2 hlen, h.2.2⟩

/-- a state change writing only `dsl.stk` and registers keeps all block records -/
theorem recsOK_of_stk {q r : State ℝ≥0} {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ}
    {recs : List (ℕ × Block (Fin G.n) (WLab G s))} (h : RecsOK q H V recs) {wr : List String}
    (hu : Unchanged q r ["dsl.stk"] [] wr []) : RecsOK r H V recs :=
  recsOK_of_arrays h (fun a ha => (hu.warr a (by
      intro h'; simp only [List.mem_singleton] at h'; subst h'; simp [bArrs] at ha)).1)
    (hu.varr _ (by simp)).1 (hu.varr _ (by simp)).1 (hu.warr _ (by simp)).2

/-- side conditions of the grouping loop (capacities; fixed along the loop) -/
structure GSide (st0 : State ℝ≥0) (top : ℕ) (cid : ℕ → ℕ) (cbl : List (Block (Fin G.n) (WLab G s)))
    : Prop where
  topstk : top < st0.wlen "dsl.stk"
  topck : cbl.length ≤ top + 1
  cidl : ∀ j < cbl.length, cid j < st0.wlen "blk.hd" ∧ cid j < st0.wlen "blk.tl" ∧
    cid j < st0.wlen "blk.cnt"
  cidc : ∀ j < cbl.length, cid j + 1 < st0.cap
  capt : top + (entIds cbl).length + 2 < st0.cap

theorem mg_stepB (st0 q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (g top : ℕ) (cid : ℕ → ℕ) (cbl : List (Block (Fin G.n) (WLab G s)))
    (others : List (ℕ × Block (Fin G.n) (WLab G s))) (i : ℕ)
    (em : List (Block (Fin G.n) (WLab G s))) (emIds : List ℕ)
    (hS : GSide st0 top cid cbl) (hI : GInv st0 q H V g top cid cbl others i em emIds none)
    (hi : i < cbl.length) (hlt : (cbl[i]).ents.length < g) :
    wp ops mgBody (fun r => GInv st0 r H V g top cid cbl others (i + 1) em emIds
      (some (cid i, cbl[i])) ∧ r.cost ≤ q.cost + 5) q := by
  have hstk := hI.unrd i le_rfl hi
  have hU := hI.unch
  have hcapq : q.cap = st0.cap := hU.cap
  have hlstk := hI.lstk
  have hlcnt := hI.lcnt
  have hrec := hI.recs
  rw [unread_cons cid cbl i hi] at hrec
  have hBb : BlkRep q H V (cid i) cbl[i] := hrec.2.1 (cid i, cbl[i]) (by simp)
  have hcnt : q.wa "blk.cnt" (cid i) = (cbl[i]).ents.length := hBb.2.2.2.1
  have hc1 : 1 < q.cap := by rw [hcapq]; have := hS.capt; omega
  have hti : top - i < q.wlen "dsl.stk" := by rw [hlstk]; have := hS.topstk; omega
  have hcl : cid i < q.wlen "blk.cnt" := by rw [hlcnt]; exact (hS.cidl i hi).2.2
  have hcc : cid i + 1 < q.cap := by rw [hcapq]; exact hS.cidc i hi
  have hi1 : i + 1 < q.cap := by rw [hcapq]; have := hS.capt; have := hS.topck; omega
  simp [mgBody, wp, fit, hc1, show 0 < q.cap by omega, hI.topr, hI.ireg, hI.accreg, hI.gr, hstk,
    hti, hcl, hcnt, hlt, hcc, hi1]
  set r := ((((((((q.setW "mg.b" (cid i)).charge 1).charge 1).charge 1).setW "mg.acc" (cid i + 1)).charge
    1).setW "mg.i" (i + 1)).charge 1) with hr
  have hUr : Unchanged q r [] [] mgRegs [] := by
    rw [hr, unch_charge, unch_setW (by simp [mgRegs]), unch_charge, unch_setW (by simp [mgRegs]),
      unch_charge, unch_charge, unch_charge, unch_setW (by simp [mgRegs])]
    exact Unchanged.refl _ _ _ _ _
  have hwa : r.wa = q.wa := by simp [hr]
  have hdrop : cbl.drop i = cbl[i] :: cbl.drop (i + 1) := List.drop_eq_getElem_cons hi
  have hwle := hI.wle
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, add_zero] at hwle
  refine ⟨by simp [hr], by omega, by simp [hr, hI.wreg], by simp; omega, by simp [hr], ?_, hI.emlen,
    fun j hj => by rw [hwa]; exact hI.emstk j hj, fun j hj hj' => by rw [hwa]; exact hI.unrd j (by omega) hj',
    fun x hx => by rw [hwa]; exact hI.below x hx, ?_, by simp [hr, hI.topr], by simp [hr, hI.gr],
    by simp [hr, hI.ckr], ?_, by simp [hr, hI.lstk], by simp [hr, hI.lhd], by simp [hr, hI.ltl],
    by simp [hr, hI.lcnt], by simp [hr, hI.lnx]⟩
  · have := hI.geq
    rw [hdrop] at this
    simp only [Option.map_none, Option.map_some] at this ⊢
    rw [← this]
    congr 1
    simp only [groupAux]
    rw [if_neg (by omega)]
  · have hl : emIds.zip em ++ (some (cid i, cbl[i])).toList ++ unread cid cbl (i + 1) ++ others =
        emIds.zip em ++ none.toList ++ (cid i, cbl[i]) :: unread cid cbl (i + 1) ++ others := by simp
    rw [hl]
    exact recsOK_of_arrays hrec (fun a _ => by rw [hwa]) (by simp [hr]) (by simp [hr]) (by simp [hr])
  · exact hU.trans (hUr.mono (by simp) (by simp) (by simp) (by simp))

theorem mg_stepA (st0 q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (g top : ℕ) (cid : ℕ → ℕ) (cbl : List (Block (Fin G.n) (WLab G s)))
    (others : List (ℕ × Block (Fin G.n) (WLab G s))) (i : ℕ)
    (em : List (Block (Fin G.n) (WLab G s))) (emIds : List ℕ)
    (hS : GSide st0 top cid cbl) (hI : GInv st0 q H V g top cid cbl others i em emIds none)
    (hi : i < cbl.length) (hge : g ≤ (cbl[i]).ents.length) :
    wp ops mgBody (fun r => GInv st0 r H V g top cid cbl others (i + 1) (em ++ [cbl[i]])
      (emIds ++ [cid i]) none ∧ r.cost ≤ q.cost + 6) q := by
  have hstk := hI.unrd i le_rfl hi
  have hU := hI.unch
  have hcapq : q.cap = st0.cap := hU.cap
  have hlstk := hI.lstk
  have hlcnt := hI.lcnt
  have hrec := hI.recs
  rw [unread_cons cid cbl i hi] at hrec
  have hBb : BlkRep q H V (cid i) cbl[i] := hrec.2.1 (cid i, cbl[i]) (by simp)
  have hcnt : q.wa "blk.cnt" (cid i) = (cbl[i]).ents.length := hBb.2.2.2.1
  have hc1 : 1 < q.cap := by rw [hcapq]; have := hS.capt; omega
  have hti : top - i < q.wlen "dsl.stk" := by rw [hlstk]; have := hS.topstk; omega
  have hcl : cid i < q.wlen "blk.cnt" := by rw [hlcnt]; exact (hS.cidl i hi).2.2
  have hi1 : i + 1 < q.cap := by rw [hcapq]; have := hS.capt; have := hS.topck; omega
  have hwle := hI.wle
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, add_zero] at hwle
  have hw1 : em.length + 1 < q.cap := by omega
  have htw : top - em.length < q.wlen "dsl.stk" := by rw [hlstk]; have := hS.topstk; omega
  have hnlt : ¬ (cbl[i]).ents.length < g := by omega
  simp [mgBody, emitS, wp, fit, hc1, show 0 < q.cap by omega, hI.topr, hI.ireg, hI.accreg, hI.gr,
    hstk, hti, hcl, hcnt, hnlt, hi1, hI.wreg, htw, hw1]
  set r := (((((((((q.setW "mg.b" (cid i)).charge 1).charge 1).charge 1).storeW "dsl.stk"
    (top - em.length) (cid i)).charge 1).setW "mg.w" (em.length + 1)).charge 1).setW "mg.i"
      (i + 1)).charge 1 with hr
  have hUr : Unchanged q r ["dsl.stk"] [] mgRegs [] := by
    rw [hr, unch_charge, unch_setW (by simp [mgRegs]), unch_charge, unch_setW (by simp [mgRegs]),
      unch_charge, unch_storeW (by simp), unch_charge, unch_charge, unch_charge,
      unch_setW (by simp [mgRegs])]
    exact Unchanged.refl _ _ _ _ _
  have hwa : ∀ x, x ≠ top - em.length → r.wa "dsl.stk" x = q.wa "dsl.stk" x := by
    intro x hx; simp [hr, hx]
  have hdrop : cbl.drop i = cbl[i] :: cbl.drop (i + 1) := List.drop_eq_getElem_cons hi
  have htop := hS.topck
  have hacc0 : q.w "mg.acc" = 0 := by simpa using hI.accreg
  refine ⟨by simp [hr], by omega, by simp [hr], by simp; omega, by simp [hr, hacc0], ?_, by simp [hI.emlen],
    ?_, ?_, ?_, ?_, by simp [hr, hI.topr], by simp [hr, hI.gr], by simp [hr, hI.ckr], ?_,
    by simp [hr, hI.lstk], by simp [hr, hI.lhd], by simp [hr, hI.ltl], by simp [hr, hI.lcnt],
    by simp [hr, hI.lnx]⟩
  · have := hI.geq
    rw [hdrop] at this
    simp only [Option.map_none] at this ⊢
    rw [← this, List.append_assoc]
    congr 1
    simp only [groupAux]
    rw [if_pos hge]; rfl
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hje : j = em.length
    · subst hje; simp [hr, hI.emlen]
    · rw [hwa _ (by omega), hI.emstk j (by omega)]
      simp [List.getElem_append_left (show j < emIds.length by rw [hI.emlen]; omega)]
  · intro j hj hj'
    rw [hwa _ (by omega)]; exact hI.unrd j (by omega) hj'
  · intro x hx
    rw [hwa _ (by omega)]; exact hI.below x hx
  · have hz : (emIds ++ [cid i]).zip (em ++ [cbl[i]]) = emIds.zip em ++ [(cid i, cbl[i])] := by
      rw [List.zip_append (by rw [hI.emlen])]; simp
    have hl : (emIds ++ [cid i]).zip (em ++ [cbl[i]]) ++ (none : Option (ℕ × Block (Fin G.n) (WLab G s))).toList
        ++ unread cid cbl (i + 1) ++ others =
        emIds.zip em ++ none.toList ++ (cid i, cbl[i]) :: unread cid cbl (i + 1) ++ others := by
      rw [hz]; simp
    rw [hl]
    exact recsOK_of_stk hrec hUr
  · exact hU.trans (hUr.mono (by simp) (by simp) (by simp) (by simp))

theorem wp_wstore_of {arr : String} {i e : WExpr} {Q : State ℝ≥0 → Prop} {st : State ℝ≥0} {j a : ℕ}
    (hi : evalW st i = some j) (he : evalW st e = some a) (hj : j < st.wlen arr) :
    wp ops (.wstore arr i e) Q st = Q ((st.storeW arr j a).charge 1) := by
  simp [wp, hi, he, hj]

theorem wp_ite_of {c : WExpr} {a b : Stmt} {Q : State ℝ≥0 → Prop} {st : State ℝ≥0} {x : ℕ}
    (hc : evalW st c = some x) :
    wp ops (.ite c a b) Q st = ((x ≠ 0 → wp ops a Q (st.charge 1)) ∧ (x = 0 → wp ops b Q (st.charge 1))) := by
  simp [wp, hc]

/-- steps C/D: the accumulator absorbs the next child block, then possibly closes -/
theorem mg_stepCD (st0 q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (g top : ℕ) (cid : ℕ → ℕ) (cbl : List (Block (Fin G.n) (WLab G s)))
    (others : List (ℕ × Block (Fin G.n) (WLab G s))) (i : ℕ)
    (em : List (Block (Fin G.n) (WLab G s))) (emIds : List ℕ) (c : ℕ) (cb : Block (Fin G.n) (WLab G s))
    (hS : GSide st0 top cid cbl) (hI : GInv st0 q H V g top cid cbl others i em emIds (some (c, cb)))
    (hi : i < cbl.length) (hcl : c < st0.wlen "blk.hd" ∧ c < st0.wlen "blk.tl" ∧ c < st0.wlen "blk.cnt")
    (hcsz : cb.ents.length + (cbl[i]).ents.length < st0.cap) :
    wp ops mgBody (fun r =>
      (g ≤ cb.ents.length + (cbl[i]).ents.length ∧
        GInv st0 r H V g top cid cbl others (i + 1) (em ++ [⟨cb.sep, cb.ents ++ (cbl[i]).ents⟩])
          (emIds ++ [c]) none ∧ r.cost ≤ q.cost + 16) ∨
      (cb.ents.length + (cbl[i]).ents.length < g ∧
        GInv st0 r H V g top cid cbl others (i + 1) em emIds
          (some (c, ⟨cb.sep, cb.ents ++ (cbl[i]).ents⟩)) ∧ r.cost ≤ q.cost + 16)) q := by
  have hstk := hI.unrd i le_rfl hi
  have hU := hI.unch
  have hcapq : q.cap = st0.cap := hU.cap
  have hrec := hI.recs
  rw [unread_cons cid cbl i hi] at hrec
  have hc1 : 1 < q.cap := by rw [hcapq]; have := hS.capt; omega
  have hti : top - i < q.wlen "dsl.stk" := by rw [hI.lstk]; have := hS.topstk; omega
  have hacc : q.w "mg.acc" = c + 1 := by simpa using hI.accreg
  have hwle := hI.wle
  simp only [Option.isSome_some, if_true] at hwle
  rw [mgBody, wp_seq, wp_wset_of (a := cid i) (by simp [hI.topr, hI.ireg, hti, hstk])]
  rw [wp_seq, wp_ite_of (x := 0) (by
    simp [hacc, fit, hc1, show 0 < q.cap by omega])]
  refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
  rw [wp_seq, wp_wset_of (a := c) (by simp [hacc, fit, hc1])]
  rw [wp_seq]
  set q2 := (((((q.setW "mg.b" (cid i)).charge 1).charge 1).setW "mg.c" c).charge 1) with hq2
  have hq2wa : q2.wa = q.wa := by simp [hq2]
  have hrec2 : RecsOK q2 H V ((c, cb) :: (cid i, cbl[i]) ::
      (emIds.zip em ++ unread cid cbl (i + 1) ++ others)) := by
    have h := recsOK_of_arrays (r := q2) hrec (fun a _ => by rw [hq2wa]) (by simp [hq2])
      (by simp [hq2]) (by simp [hq2])
    refine h.perm ?_
    simp only [Option.toList_some, List.append_assoc, List.singleton_append, List.cons_append]
    exact (List.perm_middle.trans (List.Perm.cons _ List.perm_middle))
  have hcl2 : c < q2.wlen "blk.hd" ∧ c < q2.wlen "blk.tl" ∧ c < q2.wlen "blk.cnt" := by
    simp only [hq2, State.charge_wlen, State.setW_wlen]
    rw [hI.lhd, hI.ltl, hI.lcnt]; exact hcl
  have hbl2 : cid i < q2.wlen "blk.hd" ∧ cid i < q2.wlen "blk.tl" ∧ cid i < q2.wlen "blk.cnt" := by
    simp only [hq2, State.charge_wlen, State.setW_wlen]
    rw [hI.lhd, hI.ltl, hI.lcnt]; exact hS.cidl i hi
  have hcap2 : cb.ents.length + (cbl[i]).ents.length < q2.cap := by
    simp only [hq2, State.charge_cap, State.setW_cap]; rw [hcapq]; exact hcsz
  have hc12 : 1 < q2.cap := by simp only [hq2, State.charge_cap, State.setW_cap]; exact hc1
  refine wp_mono concatS ?_ q2 (concat_recs (ops := ops) q2 H V c (cid i) cb cbl[i] _ hrec2 hcl2 hbl2
    hcap2 hc12 (by simp [hq2]) (by simp [hq2]))
  rintro r ⟨hR, hUc, hnl, hcost, hwl⟩
  have hrw : ∀ x, r.w x = q2.w x := fun x => hUc.wreg x (by simp)
  have hrstk : r.wa "dsl.stk" = q.wa "dsl.stk" := by
    rw [(hUc.warr "dsl.stk" (by simp)).1, hq2wa]
  have hBn : BlkRep r H V c ⟨cb.sep, cb.ents ++ (cbl[i]).ents⟩ := hR.2.1 _ List.mem_cons_self
  have hcntr : r.wa "blk.cnt" c = cb.ents.length + (cbl[i]).ents.length := by
    have := hBn.2.2.2.1; simpa using this
  have hcr : c < r.wlen "blk.cnt" := by rw [hwl]; exact hcl2.2.2
  have hrc : r.cap = q.cap := by rw [hUc.cap]; simp [hq2]
  have hc1r : 1 < r.cap := by rw [hrc]; exact hc1
  have hmc : r.w "mg.c" = c := by rw [hrw]; simp [hq2]
  have hmg : r.w "mg.g" = g := by rw [hrw]; simp [hq2, hI.gr]
  have hmi : r.w "mg.i" = i := by rw [hrw]; simp [hq2, hI.ireg]
  have hmw : r.w "mg.w" = em.length := by rw [hrw]; simp [hq2, hI.wreg]
  have hmt : r.w "mg.top" = top := by rw [hrw]; simp [hq2, hI.topr]
  have hi1 : i + 1 < r.cap := by rw [hrc, hcapq]; have := hS.capt; have := hS.topck; omega
  have hdrop : cbl.drop i = cbl[i] :: cbl.drop (i + 1) := List.drop_eq_getElem_cons hi
  -- the frame from `q` to `r`
  have hUqr : Unchanged q r ["blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] [] mgRegs [] := by
    have h1 : Unchanged q q2 [] [] mgRegs [] := by
      rw [hq2, unch_charge, unch_setW (by simp [mgRegs]), unch_charge, unch_charge,
        unch_setW (by simp [mgRegs])]
      exact Unchanged.refl _ _ _ _ _
    exact (h1.mono (by simp) (by simp) (by simp) (by simp)).trans
      (hUc.mono (by simp) (by simp) (by simp) (by simp))
  have hwlen : ∀ a, r.wlen a = q.wlen a := by intro a; rw [hwl]; simp [hq2]
  by_cases hlt : cb.ents.length + (cbl[i]).ents.length < g
  · -- D: keep accumulating
    rw [wp_ite_of (x := 1) (by simp [hmc, hcr, hcntr, hmg, hlt, fit, hc1r])]
    refine ⟨fun _ => ?_, fun h => absurd h one_ne_zero⟩
    rw [wp_skip, wp_wset_of (a := i + 1) (by simp [hmi, fit, hi1, hc1r])]
    right
    set r' := (((r.charge 1).charge 1).setW "mg.i" (i + 1)).charge 1 with hr'
    have hUr' : Unchanged r r' [] [] mgRegs [] := by
      rw [hr', unch_charge, unch_setW (by simp [mgRegs]), unch_charge, unch_charge]
      exact Unchanged.refl _ _ _ _ _
    have hwa' : r'.wa = r.wa := by simp [hr']
    refine ⟨hlt, ⟨by simp [hr'], by omega, by simp [hr', hmw], by simp; omega, by simp [hr', hrw, hq2, hacc],
      ?_, hI.emlen, ?_, ?_, ?_, ?_, by simp [hr', hmt], by simp [hr', hmg],
      by simp [hr', hrw, hq2, hI.ckr], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · have := hI.geq
      rw [hdrop] at this
      simp only [Option.map_some] at this ⊢
      rw [← this]
      congr 1
      simp only [groupAux, List.length_append]
      rw [if_neg (by omega)]
    · intro j hj; rw [hwa', hrstk]; exact hI.emstk j hj
    · intro j hj hj'; rw [hwa', hrstk]; exact hI.unrd j (by omega) hj'
    · intro x hx; rw [hwa', hrstk]; exact hI.below x hx
    · have h := recsOK_of_arrays (r := r') hR (fun a _ => by rw [hwa']) (by simp [hr'])
        (by simp [hr']) (by simp [hr'])
      refine h.perm ?_
      simp only [Option.toList_some, List.append_assoc, List.singleton_append]
      exact List.perm_middle.symm
    · exact hU.trans ((hUqr.trans (hUr'.mono (by simp) (by simp) (by simp) (by simp))).mono
        (by simp) (by simp) (by simp) (by simp))
    · simp [hr', hwlen, hI.lstk]
    · simp [hr', hwlen, hI.lhd]
    · simp [hr', hwlen, hI.ltl]
    · simp [hr', hwlen, hI.lcnt]
    · simp [hr', hwlen, hI.lnx]
    · simp only [hr', State.charge_cost, State.setW_cost]
      have : q2.cost = q.cost + 3 := by simp [hq2]
      omega
  · -- C: close the group
    rw [wp_ite_of (x := 0) (by simp [hmc, hcr, hcntr, hmg, hlt, fit, hc1r, show 0 < r.cap by omega])]
    refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
    have hw1 : em.length + 1 < r.cap := by rw [hrc, hcapq]; have := hS.capt; have := hS.topck; omega
    have htw : top - em.length < r.wlen "dsl.stk" := by
      rw [hwlen, hI.lstk]; have := hS.topstk; omega
    simp only [emitS, wp_seq]
    simp [wp, hmt, hmw, hmc, fit, hc1r, show 0 < r.cap by omega, htw, hw1, hmi, hi1]
    left
    set r' := (((((((((r.charge 1).storeW "dsl.stk" (top - em.length) c).charge 1).setW "mg.w"
      (em.length + 1)).charge 1).setW "mg.acc" 0).charge 1).setW "mg.i" (i + 1)).charge 1) with hr'
    have hUr' : Unchanged r r' ["dsl.stk"] [] mgRegs [] := by
      rw [hr', unch_charge, unch_setW (by simp [mgRegs]), unch_charge, unch_setW (by simp [mgRegs]),
        unch_charge, unch_setW (by simp [mgRegs]), unch_charge, unch_storeW (by simp), unch_charge]
      exact Unchanged.refl _ _ _ _ _
    have hwa' : ∀ x, x ≠ top - em.length → r'.wa "dsl.stk" x = q.wa "dsl.stk" x := by
      intro x hx; rw [← hrstk]; simp [hr', hx]
    have htop := hS.topck
    refine ⟨by omega, ⟨by simp [hr'], by omega, by simp [hr'], by simp; omega, by simp [hr'],
      ?_, by simp [hI.emlen], ?_, ?_, ?_, ?_, by simp [hr', hmt], by simp [hr', hmg],
      by simp [hr', hrw, hq2, hI.ckr], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · have := hI.geq
      rw [hdrop] at this
      simp only [Option.map_some, Option.map_none] at this ⊢
      rw [← this, List.append_assoc]
      congr 1
      simp only [groupAux, List.length_append]
      rw [if_pos (by omega)]; rfl
    · intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hje : j = em.length
      · subst hje; simp [hr', hI.emlen]
      · rw [hwa' _ (by omega), hI.emstk j (by omega)]
        simp [List.getElem_append_left (show j < emIds.length by rw [hI.emlen]; omega)]
    · intro j hj hj'
      rw [hwa' _ (by omega)]; exact hI.unrd j (by omega) hj'
    · intro x hx
      rw [hwa' _ (by omega)]; exact hI.below x hx
    · have h := recsOK_of_stk hR hUr'
      refine h.perm ?_
      have hz : (emIds ++ [c]).zip (em ++ [⟨cb.sep, cb.ents ++ (cbl[i]).ents⟩]) =
          emIds.zip em ++ [(c, ⟨cb.sep, cb.ents ++ (cbl[i]).ents⟩)] := by
        rw [List.zip_append (by rw [hI.emlen])]; simp
      rw [hz]
      simp only [Option.toList_none, List.append_nil, List.append_assoc, List.singleton_append]
      exact List.perm_middle.symm
    · exact hU.trans ((hUqr.mono (by simp) (by simp) (by simp) (by simp)).trans
        (hUr'.mono (by simp) (by simp) (by simp) (by simp)))
    · simp [hr', hwlen, hI.lstk]
    · simp [hr', hwlen, hI.lhd]
    · simp [hr', hwlen, hI.ltl]
    · simp [hr', hwlen, hI.lcnt]
    · simp [hr', hwlen, hI.lnx]
    · have : q2.cost = q.cost + 3 := by simp [hq2]
      simp [hr']
      omega

/-- entries of the accumulated group and of the next child block fit in the child's entries -/
theorem acc_size_le {g : ℕ} {cbl : List (Block (Fin G.n) (WLab G s))} {i : ℕ}
    {em : List (Block (Fin G.n) (WLab G s))} {cb : Block (Fin G.n) (WLab G s)} (hi : i < cbl.length)
    (hgeq : em ++ groupAux g (some cb) (cbl.drop i) = groupAux g none cbl) :
    cb.ents.length + (cbl[i]).ents.length ≤ (entIds cbl).length := by
  have h1 := (Frontier.CHD.DL.groupAux_allEnts_perm g (some cb) (cbl.drop i)).length_eq
  have h2 := (Frontier.CHD.DL.groupAux_allEnts_perm g none cbl).length_eq
  have h3 := congrArg (fun l => (allEnts l).length) hgeq
  rw [show allEnts (em ++ groupAux g (some cb) (cbl.drop i)) =
      allEnts em ++ allEnts (groupAux g (some cb) (cbl.drop i)) by simp [allEnts]] at h3
  simp only [List.length_append, List.nil_append] at h1 h2 h3
  have hd : allEnts (cbl.drop i) = (cbl[i]).ents ++ allEnts (cbl.drop (i + 1)) := by
    unfold allEnts
    rw [List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons]
  rw [hd, List.length_append] at h1
  have he : (entIds cbl).length = (allEnts cbl).length := by
    simp [entIds, allEnts, List.length_flatMap, List.length_flatten, Function.comp_def]
  omega

/-- **the grouping loop**: all child blocks are processed -/
theorem mg_loop (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (g top : ℕ) (cid : ℕ → ℕ) (cbl : List (Block (Fin G.n) (WLab G s)))
    (others : List (ℕ × Block (Fin G.n) (WLab G s))) (hS : GSide st0 top cid cbl) :
    ∀ (n i : ℕ) (q : State ℝ≥0) (em : List (Block (Fin G.n) (WLab G s))) (emIds : List ℕ)
      (cur : Option (ℕ × Block (Fin G.n) (WLab G s))), cbl.length - i = n →
      GInv st0 q H V g top cid cbl others i em emIds cur →
      (∀ p, cur = some p → ∃ j < cbl.length, p.1 = cid j) →
      (∀ x ∈ emIds, ∃ j < cbl.length, x = cid j) →
      Runs ops mgLoop q (fun r => ∃ em' emIds' cur', GInv st0 r H V g top cid cbl others
        cbl.length em' emIds' cur' ∧ (∀ p, cur' = some p → ∃ j < cbl.length, p.1 = cid j) ∧
        (∀ x ∈ emIds', ∃ j < cbl.length, x = cid j) ∧
        r.cost ≤ q.cost + 17 * n + 1)
  | 0, i, q, em, emIds, cur, hn, hI, hcur, hem => by
      have hi : i = cbl.length := by have := hI.ile; omega
      subst hi
      have hc1 : 1 < q.cap := by rw [hI.unch.cap]; have := hS.capt; omega
      refine runs_while_exit (by simp [hI.ireg, hI.ckr, fit, hc1, show 0 < q.cap by omega]) ?_
      refine ⟨em, emIds, cur, ?_, hcur, hem, by simp⟩
      exact ⟨by simp [hI.ireg], hI.ile, by simp [hI.wreg], hI.wle, by simp [hI.accreg], hI.geq,
        hI.emlen, fun j hj => by simp [hI.emstk j hj], fun j hj hj' => by simp [hI.unrd j hj hj'],
        fun x hx => by simp [hI.below x hx],
        recsOK_of_arrays hI.recs (fun a _ => by simp) (by simp) (by simp) (by simp),
        by simp [hI.topr], by simp [hI.gr], by simp [hI.ckr], (unch_charge 1).mpr hI.unch,
        by simp [hI.lstk], by simp [hI.lhd], by simp [hI.ltl], by simp [hI.lcnt], by simp [hI.lnx]⟩
  | n + 1, i, q, em, emIds, cur, hn, hI, hcur, hem => by
      have hi : i < cbl.length := by omega
      have hc1 : 1 < q.cap := by rw [hI.unch.cap]; have := hS.capt; omega
      refine runs_while_step (x := 1) (by simp [hI.ireg, hI.ckr, fit, hc1, hi]) one_ne_zero ?_
      have hI1 : GInv st0 (q.charge 1) H V g top cid cbl others i em emIds cur :=
        ⟨by simp [hI.ireg], hI.ile, by simp [hI.wreg], hI.wle, by simp [hI.accreg], hI.geq,
          hI.emlen, fun j hj => by simp [hI.emstk j hj], fun j hj hj' => by simp [hI.unrd j hj hj'],
          fun x hx => by simp [hI.below x hx],
          recsOK_of_arrays hI.recs (fun a _ => by simp) (by simp) (by simp) (by simp),
          by simp [hI.topr], by simp [hI.gr], by simp [hI.ckr], (unch_charge 1).mpr hI.unch,
          by simp [hI.lstk], by simp [hI.lhd], by simp [hI.ltl], by simp [hI.lcnt], by simp [hI.lnx]⟩
      rcases cur with _ | ⟨c, cb⟩
      · by_cases hge : g ≤ (cbl[i]).ents.length
        · refine (wp_sound _ _ _ (mg_stepA st0 (q.charge 1) H V g top cid cbl others i em emIds hS hI1
            hi hge)).mono ?_
          rintro r ⟨hr, hc⟩
          refine (mg_loop st0 H V g top cid cbl others hS n (i + 1) r _ _ none (by omega) hr
            (by simp) (by
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hem x hx
              · simp at hx; exact ⟨i, hi, hx⟩)).mono ?_
          rintro r' ⟨em', emIds', cur', h1, h2, h2', h3⟩
          exact ⟨em', emIds', cur', h1, h2, h2', by simp at hc; omega⟩
        · refine (wp_sound _ _ _ (mg_stepB st0 (q.charge 1) H V g top cid cbl others i em emIds hS hI1
            hi (by omega))).mono ?_
          rintro r ⟨hr, hc⟩
          refine (mg_loop st0 H V g top cid cbl others hS n (i + 1) r _ _ _ (by omega) hr
            (by intro p hp; cases hp; exact ⟨i, hi, rfl⟩) hem).mono ?_
          rintro r' ⟨em', emIds', cur', h1, h2, h2', h3⟩
          exact ⟨em', emIds', cur', h1, h2, h2', by simp at hc; omega⟩
      · obtain ⟨j, hj, hcj⟩ := hcur (c, cb) rfl
        have hcl : c < st0.wlen "blk.hd" ∧ c < st0.wlen "blk.tl" ∧ c < st0.wlen "blk.cnt" := by
          simp only at hcj; rw [hcj]; exact hS.cidl j hj
        have hsz : cb.ents.length + (cbl[i]).ents.length < st0.cap := by
          have := acc_size_le (cb := cb) hi (by simpa using hI.geq); have := hS.capt; omega
        refine (wp_sound _ _ _ (mg_stepCD st0 (q.charge 1) H V g top cid cbl others i em emIds c cb hS
          hI1 hi hcl hsz)).mono ?_
        rintro r (⟨_, hr, hc⟩ | ⟨_, hr, hc⟩)
        · refine (mg_loop st0 H V g top cid cbl others hS n (i + 1) r _ _ none (by omega) hr
            (by simp) (by
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hem x hx
              · simp at hx; exact ⟨j, hj, hx.trans hcj⟩)).mono ?_
          rintro r' ⟨em', emIds', cur', h1, h2, h2', h3⟩
          exact ⟨em', emIds', cur', h1, h2, h2', by simp at hc; omega⟩
        · refine (mg_loop st0 H V g top cid cbl others hS n (i + 1) r _ _ _ (by omega) hr
            (by intro p hp; cases hp; exact ⟨j, hj, hcj⟩) hem).mono ?_
          rintro r' ⟨em', emIds', cur', h1, h2, h2', h3⟩
          exact ⟨em', emIds', cur', h1, h2, h2', by simp at hc; omega⟩

end MergeStep

/-! ## Merge: flush the last group, shift the groups down to the parent's slice -/

section MergeFinish

open Frontier.CHD.DIns Frontier.CHD.DB

variable {G : Graph} {s : Fin G.n}

def mgFlush : Stmt :=
  ite (var "mg.acc")
    (seq (wstore "dsl.stk" (sub (var "mg.top") (var "mg.w")) (sub (var "mg.acc") (lit 1)))
         (wset "mg.w" (add (var "mg.w") (lit 1))))
    skip

/-- after the loop and the flush, the groups `gs` sit at `top, top-1, …` -/
structure GDone (st0 q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (g top : ℕ) (cbl : List (Block (Fin G.n) (WLab G s)))
    (others : List (ℕ × Block (Fin G.n) (WLab G s))) (ids : List ℕ) : Prop where
  wreg : q.w "mg.w" = (groupAux g none cbl).length
  idlen : ids.length = (groupAux g none cbl).length
  stk : ∀ j (h : j < ids.length), q.wa "dsl.stk" (top - j) = ids[j]
  below : ∀ x, x + cbl.length ≤ top → q.wa "dsl.stk" x = st0.wa "dsl.stk" x
  recs : RecsOK q H V (ids.zip (groupAux g none cbl) ++ others)
  wle : (groupAux g none cbl).length ≤ cbl.length
  topr : q.w "mg.top" = top
  unch : Unchanged st0 q ["dsl.stk", "blk.hd", "blk.tl", "blk.cnt", "ent.nxt"] [] mgRegs []
  lstk : q.wlen "dsl.stk" = st0.wlen "dsl.stk"
  lnx : q.wlen "ent.nxt" = st0.wlen "ent.nxt"

theorem mg_flush (st0 q : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (g top : ℕ) (cid : ℕ → ℕ) (cbl : List (Block (Fin G.n) (WLab G s)))
    (others : List (ℕ × Block (Fin G.n) (WLab G s))) (em : List (Block (Fin G.n) (WLab G s)))
    (emIds : List ℕ) (cur : Option (ℕ × Block (Fin G.n) (WLab G s))) (hS : GSide st0 top cid cbl)
    (hI : GInv st0 q H V g top cid cbl others cbl.length em emIds cur) :
    wp ops mgFlush (fun r => GDone st0 r H V g top cbl others (emIds ++ (cur.map Prod.fst).toList) ∧
      r.cost ≤ q.cost + 3) q := by
  have hgeq := hI.geq
  rw [List.drop_length] at hgeq
  have hc1 : 1 < q.cap := by rw [hI.unch.cap]; have := hS.capt; omega
  have hwle := hI.wle
  rcases cur with _ | ⟨c, cb⟩
  · simp only [Option.map_none] at hgeq
    have hgs : groupAux g none cbl = em := by rw [← hgeq]; simp [groupAux]
    have hacc : q.w "mg.acc" = 0 := by simpa using hI.accreg
    simp [mgFlush, wp, hacc]
    simp only [Option.isSome_none, Bool.false_eq_true, if_false, add_zero] at hwle
    refine ⟨by simp [hI.wreg, hgs], by simp [hI.emlen, hgs],
      fun j hj => by simp [hI.emstk j (by rw [← hI.emlen]; exact hj)],
      fun x hx => by simp [hI.below x hx], ?_, by rw [hgs]; omega, by simp [hI.topr],
      (unch_charge 1).mpr ((unch_charge 1).mpr hI.unch), by simp [hI.lstk], by simp [hI.lnx]⟩
    rw [hgs]
    have h := hI.recs
    rw [unread_end] at h
    exact recsOK_of_arrays (by simpa using h) (fun a _ => by simp) (by simp) (by simp) (by simp)
  · simp only [Option.map_some] at hgeq
    have hgs : groupAux g none cbl = em ++ [cb] := by rw [← hgeq]; simp [groupAux]
    have hacc : q.w "mg.acc" = c + 1 := by simpa using hI.accreg
    simp only [Option.isSome_some, if_true] at hwle
    have htw : top - em.length < q.wlen "dsl.stk" := by
      rw [hI.lstk]; have := hS.topstk; omega
    have hw1 : em.length + 1 < q.cap := by rw [hI.unch.cap]; have := hS.capt; have := hS.topck; omega
    simp [mgFlush, wp, hacc, hI.topr, hI.wreg, fit, hc1, htw, hw1]
    set r := ((((q.charge 1).storeW "dsl.stk" (top - em.length) c).charge 1).setW "mg.w"
      (em.length + 1)).charge 1 with hr
    have hUr : Unchanged q r ["dsl.stk"] [] mgRegs [] := by
      rw [hr, unch_charge, unch_setW (by simp [mgRegs]), unch_charge, unch_storeW (by simp),
        unch_charge]
      exact Unchanged.refl _ _ _ _ _
    have hwa : ∀ x, x ≠ top - em.length → r.wa "dsl.stk" x = q.wa "dsl.stk" x := by
      intro x hx; simp [hr, hx]
    have htop := hS.topck
    refine ⟨by simp [hr, hgs], by simp [hI.emlen, hgs], ?_, ?_, ?_,
      by rw [hgs]; simp; omega, by simp [hr, hI.topr],
      hI.unch.trans (hUr.mono (by simp) (by simp) (by simp) (by simp)),
      by simp [hr, hI.lstk], by simp [hr, hI.lnx]⟩
    · intro j hj
      have hel := hI.emlen
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hje : j = em.length
      · subst hje; simp [hr, hI.emlen]
      · rw [hwa _ (by omega), hI.emstk j (by omega)]
        simp [List.getElem_append_left (show j < emIds.length by omega)]
    · intro x hx
      rw [hwa _ (by omega)]; exact hI.below x hx
    · rw [hgs, List.zip_append (by rw [hI.emlen]), show [c].zip [cb] = [(c, cb)] from rfl]
      have h := recsOK_of_stk hI.recs hUr
      rw [unread_end] at h
      simpa using h

end MergeFinish

/-! ## Merge: shift the groups down onto the parent's slice -/

section Shift

def shiftBody : Stmt :=
  seq (wstore "dsl.stk" (add (var "mg.dst") (var "mg.j")) (load "dsl.stk" (add (var "mg.src") (var "mg.j"))))
      (wset "mg.j" (add (var "mg.j") (lit 1)))

def shiftLoop : Stmt := .while (lt (var "mg.j") (var "mg.w")) shiftBody

def mgShift : Stmt := seq (wset "mg.j" (lit 0)) shiftLoop

/-- invariant of the shift after `k` copies -/
structure SInv (st0 q : State ℝ≥0) (dst src w k : ℕ) : Prop where
  jr : q.w "mg.j" = k
  kle : k ≤ w
  done : ∀ j < k, q.wa "dsl.stk" (dst + j) = st0.wa "dsl.stk" (src + j)
  low : ∀ x, x < dst → q.wa "dsl.stk" x = st0.wa "dsl.stk" x
  high : ∀ x, dst + k ≤ x → q.wa "dsl.stk" x = st0.wa "dsl.stk" x
  unch : Unchanged st0 q ["dsl.stk"] [] ["mg.j"] []
  lstk : q.wlen "dsl.stk" = st0.wlen "dsl.stk"

theorem shift_loop (st0 : State ℝ≥0) (dst src w : ℕ) (hds : dst ≤ src)
    (hlen : src + w ≤ st0.wlen "dsl.stk") (hcap : src + w + 1 < st0.cap)
    (hdr : st0.w "mg.dst" = dst) (hsr : st0.w "mg.src" = src) (hwr : st0.w "mg.w" = w) :
    ∀ (n k : ℕ) (q : State ℝ≥0), w - k = n → SInv st0 q dst src w k →
      Runs ops shiftLoop q (fun r => SInv st0 r dst src w w ∧ r.cost ≤ q.cost + 3 * n + 1)
  | 0, k, q, hn, hI => by
      have hk : k = w := by have := hI.kle; omega
      subst hk
      have hc : q.cap = st0.cap := hI.unch.cap
      have hc1 : 1 < q.cap := by omega
      have hw : q.w "mg.w" = k := by rw [hI.unch.wreg _ (by simp)]; exact hwr
      refine runs_while_exit (by simp [hI.jr, hw, fit, hc1, show q.cap ≠ 0 by omega]) ?_
      exact ⟨⟨by simp [hI.jr], le_rfl, fun j hj => by simp [hI.done j hj], fun x hx => by simp [hI.low x hx],
        fun x hx => by simp [hI.high x hx], (unch_charge 1).mpr hI.unch, by simp [hI.lstk]⟩, by simp⟩
  | n + 1, k, q, hn, hI => by
      have hk : k < w := by omega
      have hc : q.cap = st0.cap := hI.unch.cap
      have hc1 : 1 < q.cap := by omega
      have hw : q.w "mg.w" = w := by rw [hI.unch.wreg _ (by simp)]; exact hwr
      have hd : q.w "mg.dst" = dst := by rw [hI.unch.wreg _ (by simp)]; exact hdr
      have hs : q.w "mg.src" = src := by rw [hI.unch.wreg _ (by simp)]; exact hsr
      refine runs_while_step (x := 1) (by simp [hI.jr, hw, fit, hc1, hk]) one_ne_zero ?_
      apply wp_sound
      have hsl : src + k < q.wlen "dsl.stk" := by rw [hI.lstk]; omega
      have hdl : dst + k < q.wlen "dsl.stk" := by rw [hI.lstk]; omega
      have hsc : src + k < q.cap := by omega
      have hdc : dst + k < q.cap := by omega
      have hk1 : k + 1 < q.cap := by omega
      have hread : q.wa "dsl.stk" (src + k) = st0.wa "dsl.stk" (src + k) := hI.high _ (by omega)
      simp [shiftBody, wp, hI.jr, hd, hs, fit, hc1, hsl, hdl, hsc, hdc, hk1, hread]
      refine (shift_loop st0 dst src w hds hlen hcap hdr hsr hwr n (k + 1) _ (by omega) ?_).mono ?_
      · refine ⟨by simp, by omega, ?_, ?_, ?_, ?_, by simp [hI.lstk]⟩
        · intro j hj
          by_cases hjk : j = k
          · subst hjk; simp
          · have hne : dst + j ≠ dst + k := by omega
            simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and]
            rw [if_neg hne]; exact hI.done j (by omega)
        · intro x hx; simp [show x ≠ dst + k by omega, hI.low x hx]
        · intro x hx; simp [show x ≠ dst + k by omega, hI.high x (by omega)]
        · rw [unch_charge, unch_setW (by simp), unch_charge, unch_storeW (by simp), unch_charge]
          exact hI.unch
      · rintro r ⟨h1, h2⟩
        exact ⟨h1, by simp at h2; omega⟩

end Shift

/-! ## The merge fragment -/

section MergeFrag

open Frontier.CHD.DIns Frontier.CHD.DB

variable {G : Graph} {s : Fin G.n}

/-- **in-place merge** of the child slice (on top of the parent slice) into the parent;
inputs `mg.pb` (parent base), `mg.pk` (parent size), `mg.ck` (child size), `mg.g` (`M/3`),
`mg.drop` (`1` iff the parent's front block is dropped), `mg.lv` (parent level). -/
def mgInit : Stmt :=
  seq (wset "mg.top" (sub (add (add (var "mg.pb") (var "mg.pk")) (var "mg.ck")) (lit 1)))
  (seq (wset "mg.i" (lit 0)) (seq (wset "mg.w" (lit 0)) (wset "mg.acc" (lit 0))))

def mgSetShift : Stmt :=
  seq (wset "mg.src" (sub (add (var "mg.top") (lit 1)) (var "mg.w")))
      (wset "mg.dst" (add (var "mg.pb") (sub (var "mg.pk") (var "mg.drop"))))

def mgSetSz : Stmt :=
  wstore "dsl.sz" (var "mg.lv") (add (sub (var "mg.pk") (var "mg.drop")) (var "mg.w"))

def mergeS : Stmt :=
  seq mgInit (seq mgLoop (seq mgFlush (seq mgSetShift (seq mgShift mgSetSz))))

/-- registers written by `mergeS` -/
def mergeRegs : List String := ["mg.top", "mg.i", "mg.w", "mg.acc", "mg.b", "mg.c", "mg.src",
  "mg.dst", "mg.j"]

end MergeFrag

section MergeSpec

open Frontier.CHD.DIns Frontier.CHD.DB

variable {G : Graph} {s : Fin G.n}

/-- the records of a structure with base `bse` and blocks `P`, in list order -/
def recsOf (st : State ℝ≥0) (bse : ℕ) (P : List (Block (Fin G.n) (WLab G s))) :
    List (ℕ × Block (Fin G.n) (WLab G s)) :=
  ((List.range P.length).map (stkId st bse P.length)).zip P

/-- the merged parent structure -/
def mergedD (DP D' : DStr (Fin G.n) (WLab G s)) (keep : Bool) (g : ℕ) : DStr (Fin G.n) (WLab G s) :=
  ⟨DP.M, DP.Bd, groupAux g none D'.blocks ++ (if keep then DP.blocks else DP.blocks.tail)⟩

theorem recsOf_eq_unread (st : State ℝ≥0) (bse : ℕ) (P : List (Block (Fin G.n) (WLab G s))) :
    recsOf st bse P = unread (stkId st bse P.length) P 0 := by
  simp [recsOf, unread, List.range_eq_range']

theorem stkId_top (st : State ℝ≥0) (pb kP kC j : ℕ) (hj : j < kC) :
    stkId st (pb + kP) kC j = st.wa "dsl.stk" (pb + kP + kC - 1 - j) := by
  unfold stkId; congr 1; omega

theorem mem_recsOf (st : State ℝ≥0) (bse : ℕ) (P : List (Block (Fin G.n) (WLab G s))) (k : ℕ)
    (hk : k < P.length) : (stkId st bse P.length k, P[k]) ∈ recsOf st bse P := by
  unfold recsOf
  rw [List.mem_iff_getElem]
  exact ⟨k, by simp [hk], by simp [List.getElem_zip]⟩

theorem mem_zip_getElem {α β : Type*} (l₁ : List α) (l₂ : List β) (i : ℕ) (h₁ : i < l₁.length)
    (h₂ : i < l₂.length) : (l₁[i], l₂[i]) ∈ l₁.zip l₂ := by
  rw [List.mem_iff_getElem]
  exact ⟨i, by simp [h₁, h₂], by simp [List.getElem_zip]⟩

/-- **Spec of the in-place merge** (grouping, flush, shift, size). -/
theorem mergeS_spec (st0 : State ℝ≥0) (H : Fin G.n → ℕ → List (Fin G.m)) (V : Fin G.n → ℕ)
    (bcap lvP lvC pb : ℕ) (DP D' : DStr (Fin G.n) (WLab G s)) (keep : Bool) (g : ℕ)
    (hPne : DP.blocks ≠ []) (hPd : DRep st0 H V bcap lvP pb DP)
    (hCd : DRep st0 H V bcap lvC (pb + DP.blocks.length) D')
    (ext : List (ℕ × Block (Fin G.n) (WLab G s)))
    (hR : RecsOK st0 H V (recsOf st0 (pb + DP.blocks.length) D'.blocks ++ (recsOf st0 pb DP.blocks ++ ext)))
    (hS : GSide st0 (pb + DP.blocks.length + D'.blocks.length - 1)
      (stkId st0 (pb + DP.blocks.length) D'.blocks.length) D'.blocks)
    (hpb : st0.w "mg.pb" = pb) (hpk : st0.w "mg.pk" = DP.blocks.length)
    (hck : st0.w "mg.ck" = D'.blocks.length) (hg : st0.w "mg.g" = g)
    (hdr : st0.w "mg.drop" = (if keep then 0 else 1)) (hlv : st0.w "mg.lv" = lvP)
    (hszl : lvP < st0.wlen "dsl.sz") :
    Runs ops mergeS st0 (fun r =>
      DRep r H V bcap lvP pb (mergedD DP D' keep g) ∧
      Unchanged st0 r ["dsl.stk", "blk.hd", "blk.tl", "blk.cnt", "ent.nxt", "dsl.sz"] []
        (mergeRegs ++ ["mg.w"]) [] ∧
      r.cost ≤ st0.cost + 17 * D'.blocks.length + 3 * (groupAux g none D'.blocks).length + 20 ∧
      (∃ ids : List ℕ, RecsOK r H V (ids.zip (groupAux g none D'.blocks) ++ (recsOf st0 pb DP.blocks ++ ext)) ∧
        recsOf r pb (mergedD DP D' keep g).blocks =
          ids.zip (groupAux g none D'.blocks) ++ (recsOf st0 pb DP.blocks).drop (if keep then 0 else 1) ∧
        ∀ x ∈ ids, ∃ j < D'.blocks.length, x = stkId st0 (pb + DP.blocks.length) D'.blocks.length j) ∧
      (∀ x, x < pb → r.wa "dsl.stk" x = st0.wa "dsl.stk" x) ∧
      (∀ l, l ≠ lvP → r.wa "dsl.sz" l = st0.wa "dsl.sz" l)) := by
  set kP := DP.blocks.length with hkP
  set kC := D'.blocks.length with hkC
  set top := pb + kP + kC - 1 with htop
  set cid := stkId st0 (pb + kP) kC with hcid
  have hkP1 : 1 ≤ kP := by
    rcases h : DP.blocks with _ | ⟨b, bs⟩
    · exact absurd h hPne
    · simp [hkP, h]
  have hcapt := hS.capt
  have htopstk := hS.topstk
  have hc0 : 0 < st0.cap := by omega
  have hc1 : 1 < st0.cap := by omega
  -- mgInit
  apply wp_sound
  rw [mergeS, wp_seq, mgInit, wp_seq, wp_wset_of (a := top) (by
    simp [hpb, hpk, hck, fit, show pb + kP < st0.cap by omega, show pb + kP + kC < st0.cap by omega,
      hc1, htop])]
  rw [wp_seq, wp_wset_of (a := 0) (by simp [fit, hc0]), wp_seq, wp_wset_of (a := 0) (by simp [fit, hc0]),
    wp_wset_of (a := 0) (by simp [fit, hc0])]
  set q1 := ((((((((st0.setW "mg.top" top).charge 1).setW "mg.i" 0).charge 1).setW "mg.w" 0).charge 1).setW
    "mg.acc" 0).charge 1) with hq1
  have hq1wa : q1.wa = st0.wa := by simp [hq1]
  have hq1va : q1.va = st0.va := by simp [hq1]
  have hq1wl : q1.wlen = st0.wlen := by simp [hq1]
  have hq1cap : q1.cap = st0.cap := by simp [hq1]
  have hS1 : GSide q1 top cid D'.blocks :=
    ⟨by rw [hq1wl]; exact hS.topstk, hS.topck, fun j hj => by rw [hq1wl]; exact hS.cidl j hj,
      fun j hj => by rw [hq1cap]; exact hS.cidc j hj, by rw [hq1cap]; exact hS.capt⟩
  have hR1 : RecsOK q1 H V (recsOf st0 (pb + kP) D'.blocks ++ (recsOf st0 pb DP.blocks ++ ext)) :=
    recsOK_of_arrays hR (fun a _ => by rw [hq1wa]) (by rw [hq1va]) (by rw [hq1va]) (by rw [hq1wl])
  have hI0 : GInv q1 q1 H V g top cid D'.blocks (recsOf st0 pb DP.blocks ++ ext) 0 [] [] none := by
    refine ⟨by simp [hq1], Nat.zero_le _, by simp [hq1], by simp, by simp [hq1], by simp, rfl,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ hj => ?_, fun x _ => rfl, ?_,
      by simp [hq1], by simp [hq1, hg], by simp [hq1, hck, hkC], Unchanged.refl _ _ _ _ _, rfl, rfl, rfl,
      rfl, rfl⟩
    · rw [hq1wa, hcid, stkId_top st0 pb kP kC j hj]
    · rw [recsOf_eq_unread] at hR1
      simpa using hR1
  rw [wp_seq]
  show Runs ops mgLoop q1 _
  refine (mg_loop (ops := ops) q1 H V g top cid D'.blocks (recsOf st0 pb DP.blocks ++ ext) hS1 kC 0 q1 [] [] none
    (by simp [hkC]) hI0 (by simp) (by simp)).mono ?_
  rintro r1 ⟨em, emIds, cur, hI1, hcur1, hem1, hc1r⟩
  rw [wp_seq]
  refine wp_mono mgFlush ?_ r1 (mg_flush (ops := ops) q1 r1 H V g top cid D'.blocks
    (recsOf st0 pb DP.blocks ++ ext) em emIds cur hS1 hI1)
  rintro r2 ⟨hD2, hc2⟩
  set gs := groupAux g none D'.blocks with hgs
  set ids := emIds ++ (cur.map Prod.fst).toList with hids
  set w := gs.length with hw
  have hw2 : r2.w "mg.w" = w := hD2.wreg
  have hwle : w ≤ kC := hD2.wle
  have hreg : ∀ x, x ∉ mgRegs → r2.w x = q1.w x := fun x hx => hD2.unch.wreg x hx
  have hr2pb : r2.w "mg.pb" = pb := by rw [hreg _ (by simp [mgRegs])]; simp [hq1, hpb]
  have hr2pk : r2.w "mg.pk" = kP := by rw [hreg _ (by simp [mgRegs])]; simp [hq1, hpk]
  have hr2dr : r2.w "mg.drop" = (if keep then 0 else 1) := by
    rw [hreg _ (by simp [mgRegs])]; simp [hq1, hdr]
  have hr2lv : r2.w "mg.lv" = lvP := by rw [hreg _ (by simp [mgRegs])]; simp [hq1, hlv]
  have hr2top : r2.w "mg.top" = top := hD2.topr
  have hr2cap : r2.cap = st0.cap := by rw [hD2.unch.cap, hq1cap]
  set drop := (if keep then 0 else 1) with hdrop
  have hdrop1 : drop ≤ 1 := by rw [hdrop]; split_ifs <;> omega
  -- mgSetShift
  rw [wp_seq, mgSetShift, wp_seq, wp_wset_of (a := top + 1 - w) (by
    simp [hr2top, hw2, fit, hr2cap, show top + 1 < st0.cap by omega, hc1])]
  rw [wp_wset_of (a := pb + (kP - drop)) (by
    simp [hr2pb, hr2pk, hr2dr, fit, hr2cap, show pb + (kP - drop) < st0.cap by omega])]
  set r3 := (((r2.setW "mg.src" (top + 1 - w)).charge 1).setW "mg.dst" (pb + (kP - drop))).charge 1
    with hr3
  -- mgShift
  rw [wp_seq, mgShift, wp_seq, wp_wset_of (a := 0) (by simp [fit, hr3, hr2cap, hc0])]
  set r3' := (r3.setW "mg.j" 0).charge 1 with hr3'
  show Runs ops shiftLoop r3' _
  have hsl : top + 1 - w + w ≤ r3'.wlen "dsl.stk" := by
    simp only [hr3', hr3, State.charge_wlen, State.setW_wlen]; rw [hD2.lstk, hq1wl]; omega
  refine (shift_loop (ops := ops) r3' (pb + (kP - drop)) (top + 1 - w) w (by omega) hsl
    (by simp [hr3', hr3, hr2cap]; omega) (by simp [hr3', hr3]) (by simp [hr3', hr3])
    (by simp [hr3', hr3, hw2]) w 0 r3' (by simp) ⟨by simp [hr3'], Nat.zero_le _,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun x _ => rfl, fun x _ => rfl,
      Unchanged.refl _ _ _ _ _, rfl⟩).mono ?_
  rintro r4 ⟨hS4, hc4⟩
  -- registers at r4
  have hreg4 : ∀ x, x ≠ "mg.j" → r4.w x = r3'.w x := fun x hx => hS4.unch.wreg x (by simpa using hx)
  have hr4lv : r4.w "mg.lv" = lvP := by rw [hreg4 _ (by simp)]; simp [hr3', hr3, hr2lv]
  have hr4pk : r4.w "mg.pk" = kP := by rw [hreg4 _ (by simp)]; simp [hr3', hr3, hr2pk]
  have hr4dr : r4.w "mg.drop" = drop := by rw [hreg4 _ (by simp)]; simp [hr3', hr3, hr2dr]
  have hr4w : r4.w "mg.w" = w := by rw [hreg4 _ (by simp)]; simp [hr3', hr3, hw2]
  have hr4cap : r4.cap = st0.cap := by rw [hS4.unch.cap]; simp [hr3', hr3, hr2cap]
  have hr4szl : r4.wlen "dsl.sz" = st0.wlen "dsl.sz" := by
    rw [(hS4.unch.warr "dsl.sz" (by simp)).2]; simp [hr3', hr3]
    rw [(hD2.unch.warr "dsl.sz" (by simp)).2, hq1wl]
  have hszv : kP - drop + w < st0.cap := by omega
  rw [mgSetSz, wp_wstore_of (j := lvP) (a := kP - drop + w) (by simp [hr4lv])
    (by simp [hr4pk, hr4dr, hr4w, fit, hr4cap, hszv, show kP - drop < st0.cap by omega])
    (by rw [hr4szl]; exact hszl)]
  set r5 := (r4.storeW "dsl.sz" lvP (kP - drop + w)).charge 1 with hr5
  have hidl : ids.length = w := hD2.idlen
  -- stack contents
  have hr5stk : r5.wa "dsl.stk" = r4.wa "dsl.stk" := by funext j; simp [hr5]
  have hr3stk : r3'.wa "dsl.stk" = r2.wa "dsl.stk" := by simp [hr3', hr3]
  have hstkG : ∀ i (hi : i < w), r5.wa "dsl.stk" (pb + (kP - drop) + (w - 1 - i)) = ids[i]'(by omega) := by
    intro i hi
    rw [hr5stk, hS4.done (w - 1 - i) (by omega), hr3stk]
    rw [show top + 1 - w + (w - 1 - i) = top - i by omega]
    exact hD2.stk i (by omega)
  have hstkP : ∀ j, j < kP - drop →
      r5.wa "dsl.stk" (pb + (kP - drop - 1 - j)) = stkId st0 pb kP (j + drop) := by
    intro j hj
    rw [hr5stk, hS4.low _ (by omega), hr3stk, hD2.below _ (by omega), hq1wa]
    unfold stkId; congr 1; omega
  -- records
  have hR5 : RecsOK r5 H V (ids.zip gs ++ (recsOf st0 pb DP.blocks ++ ext)) := by
    refine recsOK_of_arrays hD2.recs (fun a ha => ?_) ?_ ?_ ?_
    · have h45 : r5.wa a = r4.wa a := by
        have : a ≠ "dsl.sz" := by intro h; subst h; simp [bArrs] at ha
        funext j; simp [hr5, this]
      rw [h45, (hS4.unch.warr a (by intro h; simp at h; subst h; simp [bArrs] at ha)).1]
      simp [hr3', hr3]
    · simp [hr5]; rw [(hS4.unch.varr _ (by simp)).1]; simp [hr3', hr3]
    · simp [hr5]; rw [(hS4.unch.varr _ (by simp)).1]; simp [hr3', hr3]
    · simp [hr5]; rw [(hS4.unch.warr _ (by simp)).2]; simp [hr3', hr3]
  have hfst : ((ids.zip gs ++ recsOf st0 pb DP.blocks).map Prod.fst) =
      ids ++ (List.range kP).map (stkId st0 pb kP) := by
    rw [List.map_append, List.map_fst_zip (by omega)]
    simp [recsOf, List.map_fst_zip, hkP]
  have hR5' : ((ids.zip gs ++ recsOf st0 pb DP.blocks).map Prod.fst).Nodup := by
    have := hR5.1
    rw [← List.append_assoc, List.map_append] at this
    exact (List.nodup_append.mp this).1
  have hnd : (ids ++ (List.range kP).map (stkId st0 pb kP)).Nodup := hfst ▸ hR5'
  have hTeq : (if keep then DP.blocks else DP.blocks.tail) = DP.blocks.drop drop := by
    rcases hk : keep <;> simp [hdrop, hk, List.drop_one]
  have hTlen : (if keep then DP.blocks else DP.blocks.tail).length = kP - drop := by
    rcases hk : keep <;> simp [hdrop, hk, hkP]
  have hidsC : ∀ x ∈ ids, ∃ j < kC, x = cid j := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hem1 x hx
    · rcases hcur : cur with _ | ⟨c, cb⟩
      · rw [hcur] at hx; simp at hx
      · rw [hcur] at hx
        simp at hx
        obtain ⟨j, hj, hcj⟩ := hcur1 (c, cb) hcur
        exact ⟨j, hj, hx ▸ hcj⟩
  have hBeq : (mergedD DP D' keep g).blocks = gs ++ DP.blocks.drop drop := by
    simp only [mergedD]; rw [hTeq]
  have hBlen : (mergedD DP D' keep g).blocks.length = w + (kP - drop) := by
    rw [hBeq]; simp [hw, hkP]
  have hstkl : r5.wlen "dsl.stk" = st0.wlen "dsl.stk" := by
    simp only [hr5, State.charge_wlen, State.storeW_wlen]
    rw [hS4.lstk]; simp [hr3', hr3]; rw [hD2.lstk, hq1wl]
  -- the id at list position `i` of the merged structure
  have hid : ∀ i (hi : i < w + (kP - drop)), stkId r5 pb (w + (kP - drop)) i =
      if h : i < w then ids[i]'(by omega) else stkId st0 pb kP (i - w + drop) := by
    intro i hi
    split_ifs with hiw
    · unfold stkId
      rw [show pb + (w + (kP - drop) - 1 - i) = pb + (kP - drop) + (w - 1 - i) by omega]
      exact hstkG i hiw
    · unfold stkId
      rw [show pb + (w + (kP - drop) - 1 - i) = pb + (kP - drop - 1 - (i - w)) by omega]
      exact hstkP (i - w) (by omega)
  have hrecs5 : recsOf r5 pb (mergedD DP D' keep g).blocks = ids.zip gs ++ (recsOf st0 pb DP.blocks).drop drop := by
    have hidx : List.length (ids.zip gs) = w := by simp [List.length_zip, hidl, hw]
    have hl1 : (recsOf r5 pb (mergedD DP D' keep g).blocks).length = w + (kP - drop) := by
      simp [recsOf, List.length_zip, hBlen]
    have hl2 : (ids.zip gs ++ (recsOf st0 pb DP.blocks).drop drop).length = w + (kP - drop) := by
      rw [List.length_append, hidx, List.length_drop]; simp [recsOf, List.length_zip, hkP]
    apply List.ext_getElem (by rw [hl1, hl2])
    intro i h1 h2
    have hi : i < w + (kP - drop) := by rw [hl1] at h1; exact h1
    have e : stkId r5 pb (mergedD DP D' keep g).blocks.length i =
        if h : i < w then ids[i]'(by omega) else stkId st0 pb kP (i - w + drop) := by
      rw [hBlen]; exact hid i hi
    have eL : (recsOf r5 pb (mergedD DP D' keep g).blocks)[i] =
        (stkId r5 pb (mergedD DP D' keep g).blocks.length i, (mergedD DP D' keep g).blocks[i]'(by
          rw [hBlen]; exact hi)) := by
      simp [recsOf, List.getElem_zip]
    rw [eL, e]
    by_cases hiw : i < w
    · rw [dif_pos hiw]
      have eR : (ids.zip gs ++ (recsOf st0 pb DP.blocks).drop drop)[i] = (ids[i]'(by omega), gs[i]'(by omega)) := by
        rw [List.getElem_append_left (by rw [hidx]; exact hiw)]; simp [List.getElem_zip]
      rw [eR]
      congr 1
      simp only [hBeq]; rw [List.getElem_append_left]
    · rw [dif_neg hiw]
      have eR : (ids.zip gs ++ (recsOf st0 pb DP.blocks).drop drop)[i] =
          (stkId st0 pb kP (i - w + drop), DP.blocks[i - w + drop]'(by omega)) := by
        rw [List.getElem_append_right (by rw [hidx]; omega)]
        simp only [List.getElem_drop, recsOf, List.getElem_zip, List.getElem_map, List.getElem_range]
        congr 1 <;> (try congr 1) <;> simp [hidx] <;> omega
      rw [eR]
      congr 1
      simp only [hBeq]
      rw [List.getElem_append_right (by omega), List.getElem_drop]
      congr 1; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨ids, hR5, hrecs5, hidsC⟩, ?_, ?_⟩
  · simp [hr5, hBlen]; omega
  · simp [hr5, hr4szl]; exact hszl
  · rw [hBlen, hstkl]; omega
  · intro i hi
    rw [hBlen] at hi ⊢
    rw [hid i hi]
    split_ifs with hiw
    · have hB : (mergedD DP D' keep g).blocks[i]'(by rw [hBlen]; exact hi) = gs[i]'(by omega) := by
        simp only [hBeq]; rw [List.getElem_append_left]
      rw [hB]
      exact hR5.2.1 _ (List.mem_append_left _ (mem_zip_getElem ids gs i (by omega) (by omega)))
    · have hB : (mergedD DP D' keep g).blocks[i]'(by rw [hBlen]; exact hi) =
          DP.blocks[i - w + drop]'(by omega) := by
        simp only [hBeq]
        rw [List.getElem_append_right (by omega), List.getElem_drop]
        congr 1; omega
      rw [hB]
      exact hR5.2.1 _ (List.mem_append_right _ (List.mem_append_left _
        (mem_recsOf st0 pb DP.blocks _ (by omega))))
  · intro a b ha hb hab
    rw [hBlen] at ha hb hab
    rw [hid a ha, hid b hb] at hab
    split_ifs at hab with h1 h2 h2
    · exact (List.Nodup.getElem_inj_iff (List.nodup_append.mp hnd).1).mp hab
    · exfalso
      exact (List.nodup_append.mp hnd).2.2 _ (List.getElem_mem _) _
        (List.mem_map.mpr ⟨b - w + drop, List.mem_range.mpr (by omega), rfl⟩) hab
    · exfalso
      exact (List.nodup_append.mp hnd).2.2 _ (List.getElem_mem _) _
        (List.mem_map.mpr ⟨a - w + drop, List.mem_range.mpr (by omega), rfl⟩) hab.symm
    · have := hPd.inj _ _ (by omega) (by omega) hab
      omega
  · intro i hi
    rw [hBlen] at hi ⊢
    rw [hid i hi]
    split_ifs with hiw
    · obtain ⟨j, hj, hx⟩ := hidsC _ (List.getElem_mem _)
      rw [hx, hcid]
      exact hCd.bidb j hj
    · exact hPd.bidb _ (by omega)
  · have hU1 : Unchanged st0 q1 [] [] mergeRegs [] := by
      rw [hq1, unch_charge, unch_setW (by simp [mergeRegs]), unch_charge,
        unch_setW (by simp [mergeRegs]), unch_charge, unch_setW (by simp [mergeRegs]), unch_charge,
        unch_setW (by simp [mergeRegs])]
      exact Unchanged.refl _ _ _ _ _
    have hU3 : Unchanged r2 r3' [] [] mergeRegs [] := by
      rw [hr3', unch_charge, unch_setW (by simp [mergeRegs]), hr3, unch_charge,
        unch_setW (by simp [mergeRegs]), unch_charge, unch_setW (by simp [mergeRegs])]
      exact Unchanged.refl _ _ _ _ _
    have hU5 : Unchanged r4 r5 ["dsl.sz"] [] [] [] := by
      rw [hr5, unch_charge, unch_storeW (by simp)]
      exact Unchanged.refl _ _ _ _ _
    have hsub : mgRegs ⊆ mergeRegs ++ ["mg.w"] := by
      intro x hx
      simp only [mgRegs, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with h | h | h | h | h <;> subst h <;> simp [mergeRegs]
    refine (((hU1.mono (by simp) (by simp) (by simp) (by simp)).trans
      (hD2.unch.mono (by simp) (by simp) hsub (by simp))).trans
      (hU3.mono (by simp) (by simp) (by simp) (by simp))).trans ?_
    exact (hS4.unch.mono (by simp) (by simp) (by simp [mergeRegs]) (by simp)).trans
      (hU5.mono (by simp) (by simp) (by simp) (by simp))
  · have hq1c : q1.cost = st0.cost + 4 := by simp [hq1]
    have hr3c : r3'.cost = r2.cost + 3 := by simp [hr3', hr3]
    have hr5c : r5.cost = r4.cost + 1 := by simp [hr5]
    omega
  · intro x hx
    rw [hr5stk, hS4.low _ (by omega), hr3stk, hD2.below _ (by omega), hq1wa]
  · intro l hl
    have h1 : r5.wa "dsl.sz" l = r4.wa "dsl.sz" l := by simp [hr5, hl]
    rw [h1, (hS4.unch.warr "dsl.sz" (by simp)).1]
    simp only [hr3', hr3, State.charge_wa, State.setW_wa]
    rw [(hD2.unch.warr "dsl.sz" (by simp)).1, hq1wa]

/-- the merged structure of `mergeS` is exactly the Layer-A `DB.merge` result, when the caller has
re-keyed the parent's front block (`keep` = the merge test) -/
theorem mergedD_eq_merge (D D' : DStr (Fin G.n) (WLab G s)) (f : Block (Fin G.n) (WLab G s))
    (rest : List (Block (Fin G.n) (WLab G s))) (hD : D.blocks = f :: rest) :
    mergedD { D with blocks := (if ltSep D'.Bd (nextSep rest (D.Bd : WithBot (WLab G s)))
        then ⟨(D'.Bd : WithBot (WLab G s)), f.ents⟩ else f) :: rest } D'
      (ltSep D'.Bd (nextSep rest (D.Bd : WithBot (WLab G s)))) (D.M / 3) = (merge 1 D D').1 := by
  unfold mergedD merge
  rw [hD]
  split_ifs with h
  · simp [h]
  · simp [h]

end MergeSpec

end Frontier.CHD.DList
