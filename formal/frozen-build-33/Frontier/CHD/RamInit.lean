import Frontier.CHD.RamLevel
import Frontier.RAMWP
import Frontier.CHD.LabRAM

/-!
# Frontier.CHD.RamInit — BM.5–7 of the RAM spine: pivots of the level-`l` groups (owner: agent-01)

**NON-GATE** (B-L4, Layer B, agent-08's spine).  `grpMin cmp`: the member of group `j` (row `l` of
agent-08's group table, `RamLevel.GrpRep`) with the least key, by one scan with a key comparison
`cmp` (`lab.bit := [κ tt.ra < κ tt.rb]`, instantiated by agent-06's `cmpTT`).  Used by BM.7 (the
initial pivots) and by BM.23 (re-selection).
-/

namespace Frontier.CHD.RamInit

open Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel

variable {V : Type} {ops : VOps V}

/-- `x := x + 1` -/
def incr (x : String) : Stmt := wset x (add (var x) (lit 1))

/-- The registers written by `grpMin` itself. -/
def gmRegs : List String := ["sp.q", "sp.qe", "sp.b", "tt.ra", "tt.rb"]

/-- **Argmin over group `j`** (register `sp.j`) of row `lvl`: `sp.b := ` the first member with the
least key.  `b := gm[gs[j]]`; for the other members `x`: if `κ x < κ b` then `b := x`. -/
def grpMin (cmp : Stmt) : Stmt :=
  seq (wset "sp.q" (load "sp.gs" (rb (var "sp.j"))))
  (seq (wset "sp.qe" (add (var "sp.q") (load "sp.gl" (rb (var "sp.j")))))
  (seq (wset "sp.b" (load "sp.gm" (rb (var "sp.q"))))
  (seq (incr "sp.q")
       (.while (lt (var "sp.q") (var "sp.qe"))
          (seq (wset "tt.ra" (load "sp.gm" (rb (var "sp.q"))))
          (seq (wset "tt.rb" (var "sp.b"))
          (seq cmp
          (seq (ite (var "lab.bit") (wset "sp.b" (var "tt.ra")) skip)
               (incr "sp.q")))))))))

/-- **The key-comparison interface**: from a state with the key representation `KR`, `cmp` sets
`lab.bit := [κ tt.ra < κ tt.rb]` (both in `dom`), writes only the registers `CW`, costs at most
`C`, and keeps `KR`.  `KR` survives the writes of `grpMin`.  `Bud` is a cost budget. -/
structure CmpI {β : Type*} [LinearOrder β] (ops : VOps V) (cmp : Stmt) (KR : State V → Prop)
    (κ : ℕ → β) (dom : ℕ → Prop) (C Bud : ℕ) (CW CV FA FR : List String) : Prop where
  run : ∀ st, KR st → dom (st.w "tt.ra") → dom (st.w "tt.rb") → st.cost + C ≤ Bud →
    Runs ops cmp st (fun r => r.w "lab.bit" = (if κ (st.w "tt.ra") < κ (st.w "tt.rb") then 1 else 0) ∧
      Unchanged st r [] [] CW CV ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + C ∧ KR r)
  /-- `KR` survives writes to the word arrays `FA` and the word registers `FR` (forward in time) -/
  frame : ∀ st r, KR st → Unchanged st r FA [] FR [] → st.cost ≤ r.cost → KR r
  bit_mem : "lab.bit" ∈ CW
  regs : ∀ a ∈ CW, a ∉ gmRegs ∧ a ≠ "lvl" ∧ a ≠ "n" ∧ a ≠ "sp.j"

/-- A row-indexed load `arr[lvl * n + e]`. -/
theorem eval_row_load (st : State V) (arr : String) {e : WExpr} {l n i : ℕ}
    (hl : st.w "lvl" = l) (hn : st.w "n" = n) (he : evalW st e = some i)
    (hlt : l * n + i < st.wlen arr) (hcap : l * n + i < st.cap) :
    evalW st (load arr (rb e)) = some (st.wa arr (l * n + i)) := by
  have h1 : l * n < st.cap := by omega
  simp [rb, evalW_load', evalW_add', evalW_mul', hl, hn, he, fit_of_lt h1, fit_of_lt hcap, hlt]

/-- The members of group `j` of level `l`, in segment order. -/
def mlist (st : State V) (l n j : ℕ) : List ℕ :=
  (List.range (gl st l n j)).map fun q => gmem st l n (gs st l n j + q)

theorem mlist_length (st : State V) (l n j : ℕ) : (mlist st l n j).length = gl st l n j := by
  simp [mlist]

theorem mem_mlist_take {st : State V} {l n j i x : ℕ} :
    x ∈ (mlist st l n j).take i ↔ ∃ q, q < i ∧ q < gl st l n j ∧ x = gmem st l n (gs st l n j + q) := by
  simp only [mlist, ← List.map_take, List.take_range, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, by omega, by omega, rfl⟩
  · rintro ⟨q, h1, h2, rfl⟩
    exact ⟨q, by omega, rfl⟩

theorem mem_P_of_mlist {st : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (hG : GrpRep st l n p P piv) {j : ℕ} (hj : j < p) {x : ℕ} :
    x ∈ mlist st l n j ↔ x ∈ P j := by
  rw [hG.img j hj, Finset.mem_image]
  simp only [mlist, List.mem_map, List.mem_range, Finset.mem_range]

/-- **`grpMin` finds a key-minimal member of group `j`.** -/
theorem grpMin_spec {β : Type*} [LinearOrder β] {cmp : Stmt} {KR : State V → Prop} {κ : ℕ → β}
    {dom : ℕ → Prop} {C Bud : ℕ} {CW CV FA FR : List String} (hI : CmpI ops cmp KR κ dom C Bud CW CV FA FR)
    (hFR : ∀ a ∈ gmRegs ++ CW, a ∈ FR)
    (st : State V) {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ} (hG : GrpRep st l n p P piv)
    (hl : st.w "lvl" = l) (hn : st.w "n" = n) {j : ℕ} (hj : st.w "sp.j" = j) (hjp : j < p)
    (hne : 0 < gl st l n j) (hdom : ∀ x ∈ P j, dom x) (hK : KR st)
    (hcap : (l + 1) * n < st.cap) (hbud : st.cost + 4 + gl st l n j * (C + 8) ≤ Bud) :
    Runs ops (grpMin cmp) st (fun r =>
      r.w "sp.b" ∈ P j ∧ (∀ x ∈ P j, κ (r.w "sp.b") ≤ κ x) ∧ KR r ∧
      Unchanged st r [] [] (gmRegs ++ CW) CV ∧ r.wlen = st.wlen ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 4 + gl st l n j * (C + 8)) := by
  classical
  have hpn := hG.p_le
  have hseg := hG.seg j hjp
  have hn1 : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  have hlnj : l * n + j < (l + 1) * n := row_index_lt (by omega)
  set g := gl st l n j with hg
  set g0 := gs st l n j with hg0
  have hgs_len : l * n + j < st.wlen "sp.gs" := by have := hG.len_gs; omega
  have hgl_len : l * n + j < st.wlen "sp.gl" := by have := hG.len_gl; omega
  have hgm_len : ∀ q, q < g → l * n + (g0 + q) < st.wlen "sp.gm" := by
    intro q hq; have := hG.len_gm; have := row_index_lt (l := l) (show g0 + q < n by omega); omega
  have hgm_cap : ∀ q, q < g → l * n + (g0 + q) < st.cap := by
    intro q hq; have := row_index_lt (l := l) (show g0 + q < n by omega); omega
  have hmemP : ∀ q, q < g → gmem st l n (g0 + q) ∈ P j := by
    intro q hq
    rw [← mem_P_of_mlist hG hjp]
    simp only [mlist, List.mem_map, List.mem_range]
    exact ⟨q, hq, rfl⟩
  -- (1) `sp.q := gs[j]`
  have e1 : evalW st (load "sp.gs" (rb (var "sp.j"))) = some g0 :=
    eval_row_load st "sp.gs" hl hn (by simp [hj]) hgs_len (by omega)
  refine runs_seq (runs_wset e1 ?_)
  set st1 := (st.setW "sp.q" g0).charge 1 with hst1
  -- (2) `sp.qe := sp.q + gl[j]`
  have e2 : evalW st1 (add (var "sp.q") (load "sp.gl" (rb (var "sp.j")))) = some (g0 + g) := by
    have hl1 : st1.w "lvl" = l := by simp [hst1, hl]
    have hn1' : st1.w "n" = n := by simp [hst1, hn]
    have hload := eval_row_load st1 "sp.gl" (e := var "sp.j") (i := j) hl1 hn1' (by simp [hst1, hj])
      (by simpa [hst1] using hgl_len) (by simp [hst1]; omega)
    simp only [evalW_add', evalW_var, hload, Option.bind_some]
    have h1 : st1.w "sp.q" = g0 := by simp [hst1]
    have h2 : st1.wa "sp.gl" (l * n + j) = g := rfl
    have h3 : st1.cap = st.cap := rfl
    rw [h1, h2, h3]
    exact fit_of_lt (by omega)
  refine runs_seq (runs_wset e2 ?_)
  set st2 := (st1.setW "sp.qe" (g0 + g)).charge 1 with hst2
  -- (3) `sp.b := gm[sp.q]`
  have e3 : evalW st2 (load "sp.gm" (rb (var "sp.q"))) = some (gmem st l n (g0 + 0)) := by
    have := eval_row_load st2 "sp.gm" (l := l) (n := n) (i := g0 + 0) (e := var "sp.q")
      (by simp [hst2, hst1, hl]) (by simp [hst2, hst1, hn]) (by simp [hst2, hst1])
      (by simpa [hst2, hst1] using hgm_len 0 hne) (by simpa [hst2, hst1] using hgm_cap 0 hne)
    rw [this]; rfl
  refine runs_seq (runs_wset e3 ?_)
  set st3 := (st2.setW "sp.b" (gmem st l n (g0 + 0))).charge 1 with hst3
  -- (4) `sp.q := sp.q + 1`
  have e4 : evalW st3 (add (var "sp.q") (lit 1)) = some (g0 + 1) := by
    simp [hst3, hst2, hst1, fit_of_lt (show g0 + 1 < st.cap by omega),
      fit_of_lt (show 1 < st.cap by omega)]
  refine runs_seq (runs_wset e4 ?_)
  set st4 := (st3.setW "sp.q" (g0 + 1)).charge 1 with hst4
  have mq : "sp.q" ∈ gmRegs ++ CW := by simp [gmRegs]
  have mqe : "sp.qe" ∈ gmRegs ++ CW := by simp [gmRegs]
  have mb : "sp.b" ∈ gmRegs ++ CW := by simp [gmRegs]
  have mra : "tt.ra" ∈ gmRegs ++ CW := by simp [gmRegs]
  have mrb : "tt.rb" ∈ gmRegs ++ CW := by simp [gmRegs]
  have hU4' : Unchanged st st4 [] [] (gmRegs ++ CW) [] := by
    rw [hst4, unch_charge, unch_setW mq, hst3, unch_charge, unch_setW mb, hst2, unch_charge,
      unch_setW mqe, hst1, unch_charge, unch_setW mq]
    exact Unchanged.refl _ _ _ _ _
  have hU4 : Unchanged st st4 [] [] (gmRegs ++ CW) CV := hU4'.mono (by simp) (by simp) (by simp) (by simp)
  have hK4 : KR st4 := hI.frame st st4 hK (hU4'.mono (by simp) (by simp) hFR (by simp))
    (by simp [hst4, hst3, hst2, hst1] <;> omega)
  -- the loop
  refine runs_while_nat (fun m r => ∃ i, m = g - i ∧ 1 ≤ i ∧ i ≤ g ∧ r.w "sp.q" = g0 + i ∧
      r.w "sp.qe" = g0 + g ∧ r.w "sp.b" ∈ (mlist st l n j).take i ∧
      (∀ x ∈ (mlist st l n j).take i, κ (r.w "sp.b") ≤ κ x) ∧ KR r ∧
      Unchanged st r [] [] (gmRegs ++ CW) CV ∧ r.wlen = st.wlen ∧
      st.cost ≤ r.cost ∧ r.cost + (g - i) * (C + 8) + 1 ≤ st.cost + 4 + g * (C + 8)) _ ?_ (g - 1) st4 ?_
  swap
  · refine ⟨1, rfl, le_rfl, hne, by simp [hst4], by simp [hst4, hst3, hst2], ?_, ?_, hK4, hU4,
      by simp [hst4, hst3, hst2, hst1], by simp [hst4, hst3, hst2, hst1]; omega, ?_⟩
    · -- the first member
      rw [mem_mlist_take]
      exact ⟨0, by omega, hne, by simp [hst4, hst3]; rfl⟩
    · intro x hx
      rw [mem_mlist_take] at hx
      obtain ⟨q, hq, -, rfl⟩ := hx
      have : q = 0 := by omega
      subst this
      simp [hst4, hst3]
      exact le_rfl
    · simp [hst4, hst3, hst2, hst1]
      have : g * (C + 8) = (g - 1) * (C + 8) + (C + 8) := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
  rintro m r ⟨i, rfl, hi1, hig, hq, hqe, hb, hbmin, hKr, hUr, hwl, hc1, hc2⟩
  have hcapr : r.cap = st.cap := hUr.cap
  have hlr : r.w "lvl" = l := by rw [hUr.wreg "lvl" (by simp [gmRegs]; intro h; exact (hI.regs _ h).2.1 rfl)]; exact hl
  have hnr : r.w "n" = n := by rw [hUr.wreg "n" (by simp [gmRegs]; intro h; exact (hI.regs _ h).2.2.1 rfl)]; exact hn
  have hwar : r.wa = st.wa := funext fun a => (hUr.warr a (by simp)).1
  refine ⟨if g0 + i < g0 + g then 1 else 0, by
    rw [evalW_lt_of (by rw [evalW_var, hq]) (by rw [evalW_var, hqe]) (by omega)], fun hx => ?_, fun hx => ?_⟩
  · -- one more member
    have hig' : i < g := by by_contra h; rw [if_neg (by omega)] at hx; exact hx rfl
    set x := gmem st l n (g0 + i) with hx_def
    have hxP : x ∈ P j := hmemP i hig'
    -- `tt.ra := gm[sp.q]`
    have ea : evalW (r.charge 1) (load "sp.gm" (rb (var "sp.q"))) = some x := by
      have := eval_row_load (r.charge 1) "sp.gm" (l := l) (n := n) (i := g0 + i) (e := var "sp.q")
        (by simpa using hlr) (by simpa using hnr) (by simp [hq]) (by simpa [hwl] using hgm_len i hig')
        (by simpa [hcapr] using hgm_cap i hig')
      rw [this]; simp [hwar, gmem, hx_def]
    refine runs_seq (runs_wset ea ?_)
    set r1 := ((r.charge 1).setW "tt.ra" x).charge 1 with hr1
    refine runs_seq (runs_wset (a := r.w "sp.b") (by simp [hr1]) ?_)
    set r2 := (r1.setW "tt.rb" (r.w "sp.b")).charge 1 with hr2
    have hU2 : Unchanged st r2 [] [] (gmRegs ++ CW) CV := by
      rw [hr2, unch_charge, unch_setW mrb, hr1, unch_charge, unch_setW mra, unch_charge]
      exact hUr
    have hK2 : KR r2 := hI.frame r r2 hKr (Unchanged.mono (show Unchanged r r2 [] [] (gmRegs ++ CW) [] by
      rw [hr2, unch_charge, unch_setW mrb, hr1, unch_charge, unch_setW mra, unch_charge]
      exact Unchanged.refl _ _ _ _ _) (by simp) (by simp) hFR (by simp)) (by simp [hr2, hr1] <;> omega)
    have hbP : r.w "sp.b" ∈ P j := by
      rw [← mem_P_of_mlist hG hjp]; exact List.mem_of_mem_take hb
    have hra : r2.w "tt.ra" = x := by simp [hr2, hr1]
    have hrb : r2.w "tt.rb" = r.w "sp.b" := by simp [hr2]
    have hbud2 : r2.cost + C ≤ Bud := by
      have : r2.cost = r.cost + 3 := by simp [hr2, hr1]
      have : (g - i) * (C + 8) = (g - (i + 1)) * (C + 8) + (C + 8) := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
    refine runs_seq ((hI.run r2 hK2 (by rw [hra]; exact hdom x hxP) (by rw [hrb]; exact hdom _ hbP)
      hbud2).mono ?_)
    rintro r3 ⟨hbit, hU3, hc3a, hc3b, hK3⟩
    rw [hra, hrb] at hbit
    have hU23 : Unchanged st r3 [] [] (gmRegs ++ CW) CV :=
      hU2.trans (hU3.mono (by simp) (by simp) (by simp) (by simp))
    have hq3 : r3.w "sp.q" = g0 + i := by
      rw [hU3.wreg "sp.q" (fun h => ((hI.regs _ h).1 (by simp [gmRegs])))]; simp [hr2, hr1, hq]
    have hb3 : r3.w "sp.b" = r.w "sp.b" := by
      rw [hU3.wreg "sp.b" (fun h => ((hI.regs _ h).1 (by simp [gmRegs])))]; simp [hr2, hr1]
    have hra3 : r3.w "tt.ra" = x := by
      rw [hU3.wreg "tt.ra" (fun h => ((hI.regs _ h).1 (by simp [gmRegs])))]; exact hra
    have hqe3 : r3.w "sp.qe" = g0 + g := by
      rw [hU3.wreg "sp.qe" (fun h => ((hI.regs _ h).1 (by simp [gmRegs])))]; simp [hr2, hr1, hqe]
    have hcap3 : r3.cap = st.cap := hU23.cap
    have hwl3 : r3.wlen = st.wlen := by
      funext a; rw [(hU3.warr a (by simp)).2]; simp [hr2, hr1, hwl]
    -- the new running minimum
    set b' := if κ x < κ (r.w "sp.b") then x else r.w "sp.b" with hb'
    have hb'mem : b' ∈ (mlist st l n j).take (i + 1) := by
      rw [hb']
      split_ifs
      · rw [mem_mlist_take]; exact ⟨i, by omega, hig', rfl⟩
      · exact List.take_subset_take_left _ (by omega) hb
    have hb'min : ∀ y ∈ (mlist st l n j).take (i + 1), κ b' ≤ κ y := by
      intro y hy
      rw [mem_mlist_take] at hy
      obtain ⟨q, hq1, hq2, rfl⟩ := hy
      by_cases hqi : q < i
      · have := hbmin _ (by rw [mem_mlist_take]; exact ⟨q, hqi, hq2, rfl⟩)
        rw [hb']; split_ifs with hlt
        · exact le_trans (le_of_lt hlt) this
        · exact this
      · have : q = i := by omega
        subst this
        rw [hb']; split_ifs with hlt
        · exact le_rfl
        · exact not_lt.mp hlt
    -- `if lab.bit then sp.b := tt.ra`, then `sp.q := sp.q + 1`
    have hc2r : r2.cost = r.cost + 3 := by simp [hr2, hr1]
    have hstep_cost : (g - i) * (C + 8) = (g - (i + 1)) * (C + 8) + (C + 8) := by
      rw [← Nat.succ_mul]; congr 1; omega
    refine runs_seq ?_
    by_cases hlt : κ x < κ (r.w "sp.b")
    · have h1 : r3.w "lab.bit" = 1 := by rw [hbit, if_pos hlt]
      refine runs_ite_true (by simp [h1]) one_ne_zero ?_
      refine runs_wset (a := x) (by simp [hra3]) ?_
      set r4 := ((r3.charge 1).setW "sp.b" x).charge 1 with hr4
      have e5 : evalW r4 (add (var "sp.q") (lit 1)) = some (g0 + i + 1) := by
        simp [hr4, hq3, hcap3, fit_of_lt (show g0 + i + 1 < st.cap by omega),
          fit_of_lt (show 1 < st.cap by omega)]
      refine runs_wset e5 ?_
      set r5 := (r4.setW "sp.q" (g0 + i + 1)).charge 1 with hr5
      have hU35 : Unchanged r3 r5 [] [] (gmRegs ++ CW) [] := by
        rw [hr5, unch_charge, unch_setW mq, hr4, unch_charge, unch_setW mb, unch_charge]
        exact Unchanged.refl _ _ _ _ _
      have hb5 : r5.w "sp.b" = x := by simp [hr5, hr4]
      have hq5 : r5.w "sp.q" = g0 + (i + 1) := by simp [hr5]; try omega
      have hqe5 : r5.w "sp.qe" = g0 + g := by simp [hr5, hr4, hqe3]
      have hwl5 : r5.wlen = st.wlen := by simp [hr5, hr4, hwl3]
      have hc5 : r5.cost = r3.cost + 3 := by simp [hr5, hr4]
      refine ⟨g - (i + 1), by omega, i + 1, rfl, by omega, by omega, hq5, hqe5, ?_, ?_,
        hI.frame r3 r5 hK3 (hU35.mono (by simp) (by simp) hFR (by simp)) (by simp [hr5, hr4] <;> omega),
        hU23.trans (hU35.mono (by simp) (by simp) (by simp) (by simp)), hwl5, by omega, by omega⟩
      · rw [hb5]; rw [hb', if_pos hlt] at hb'mem; exact hb'mem
      · intro y hy
        have := hb'min y hy
        rw [hb', if_pos hlt] at this
        rw [hb5]; exact this
    · have h0 : r3.w "lab.bit" = 0 := by rw [hbit, if_neg hlt]
      refine runs_ite_false (by simp [h0]) ?_
      refine runs_skip ?_
      set r4 := (r3.charge 1).charge 1 with hr4
      have e5 : evalW r4 (add (var "sp.q") (lit 1)) = some (g0 + i + 1) := by
        simp [hr4, hq3, hcap3, fit_of_lt (show g0 + i + 1 < st.cap by omega),
          fit_of_lt (show 1 < st.cap by omega)]
      refine runs_wset e5 ?_
      set r5 := (r4.setW "sp.q" (g0 + i + 1)).charge 1 with hr5
      have hU35 : Unchanged r3 r5 [] [] (gmRegs ++ CW) [] := by
        rw [hr5, unch_charge, unch_setW mq, hr4, unch_charge, unch_charge]
        exact Unchanged.refl _ _ _ _ _
      have hb5 : r5.w "sp.b" = r.w "sp.b" := by simp [hr5, hr4, hb3]
      have hq5 : r5.w "sp.q" = g0 + (i + 1) := by simp [hr5]; try omega
      have hqe5 : r5.w "sp.qe" = g0 + g := by simp [hr5, hr4, hqe3]
      have hwl5 : r5.wlen = st.wlen := by simp [hr5, hr4, hwl3]
      have hc5 : r5.cost = r3.cost + 3 := by simp [hr5, hr4]
      refine ⟨g - (i + 1), by omega, i + 1, rfl, by omega, by omega, hq5, hqe5, ?_, ?_,
        hI.frame r3 r5 hK3 (hU35.mono (by simp) (by simp) hFR (by simp)) (by simp [hr5, hr4] <;> omega),
        hU23.trans (hU35.mono (by simp) (by simp) (by simp) (by simp)), hwl5, by omega, by omega⟩
      · rw [hb5]; rw [hb', if_neg hlt] at hb'mem; exact hb'mem
      · intro y hy
        have := hb'min y hy
        rw [hb', if_neg hlt] at this
        rw [hb5]; exact this
  · -- the scan is complete
    have hig' : i = g := by by_contra h; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    have htake : (mlist st l n j).take i = mlist st l n j :=
      List.take_of_length_le (by rw [mlist_length]; omega)
    rw [htake] at hb hbmin
    refine ⟨?_, ?_, hI.frame r _ hKr (by rw [unch_charge]; exact Unchanged.refl _ _ _ _ _) (by simp),
      by rw [unch_charge]; exact hUr, by simp [hwl], by simp; omega, by simp; omega⟩
    · simp only [State.charge_w]; exact (mem_P_of_mlist hG hjp).mp hb
    · intro y hy
      simp only [State.charge_w]
      exact hbmin y ((mem_P_of_mlist hG hjp).mpr hy)


/-! ## BM.7: the pivots of all groups -/

/-- `GrpRep` depends only on the group arrays; the pivots are read from `sp.gp`. -/
theorem GrpRep.of_arrays' {st st' : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv piv' : ℕ → ℕ}
    (h : GrpRep st l n p P piv)
    (hwa : ∀ a ∈ ["sp.gm", "sp.gs", "sp.gl", "sp.gpos", "sp.g"], st'.wa a = st.wa a)
    (hwl : ∀ a ∈ grpArrs, st'.wlen a = st.wlen a)
    (hpv : ∀ j < p, st'.wa "sp.gp" (l * n + j) = piv' j) : GrpRep st' l n p P piv' := by
  have e1 := hwa "sp.gm" (by simp); have e2 := hwa "sp.gs" (by simp)
  have e3 := hwa "sp.gl" (by simp); have e5 := hwa "sp.gpos" (by simp)
  have e6 := hwa "sp.g" (by simp)
  have gs' : ∀ j, gs st' l n j = gs st l n j := fun j => by simp only [gs, e2]
  have gl' : ∀ j, gl st' l n j = gl st l n j := fun j => by simp only [gl, e3]
  have gm' : ∀ q, gmem st' l n q = gmem st l n q := fun q => by simp only [gmem, e1]
  refine ⟨by rw [hwl _ (by simp [grpArrs])]; exact h.len_gm, by rw [hwl _ (by simp [grpArrs])]; exact h.len_gs,
    by rw [hwl _ (by simp [grpArrs])]; exact h.len_gl, by rw [hwl _ (by simp [grpArrs])]; exact h.len_gp,
    by rw [hwl _ (by simp [grpArrs])]; exact h.len_gpos, by rw [hwl _ (by simp [grpArrs])]; exact h.len_g,
    h.p_le, fun j hj => by rw [gs', gl']; exact h.seg j hj,
    fun j hj q hq => by rw [gl'] at hq; rw [gs', gm']; exact h.mem_lt j hj q hq,
    fun j hj q hq => by rw [gl'] at hq; rw [gs', gm', e5]; exact h.pos j hj q hq,
    fun j hj q hq => by rw [gl'] at hq; rw [gs', gm', e6]; exact h.memb j hj q hq,
    fun j hj => by rw [h.img j hj, gl']; apply Finset.image_congr; intro q _; simp only [gs', gm'],
    fun x hx => by
      rw [e6]
      rcases h.nomemb x hx with h0 | ⟨j, hj, hg, hxP⟩
      · exact Or.inl h0
      · exact Or.inr ⟨j, hj, hg, hxP⟩,
    hpv, fun j hj j' hj' hne => by rw [gs', gl', gs', gl']; exact h.disj j hj j' hj' hne⟩

theorem GrpRep.charge' {st : State V} {l n p : ℕ} {P : ℕ → Finset ℕ} {piv : ℕ → ℕ}
    (h : GrpRep st l n p P piv) (k : ℕ) : GrpRep (st.charge k) l n p P piv :=
  GrpRep.of_arrays' h (fun a _ => rfl) (fun a _ => rfl) (fun j hj => h.pivs j hj)

/-- **BM.7**: for every group `j < sp.np[lvl]`, `sp.gp[lvl, j] := grpMin`. -/
def pivProg (cmp : Stmt) : Stmt :=
  seq (wset "sp.j" (lit 0))
  (.while (lt (var "sp.j") (load "sp.np" (var "lvl")))
    (seq (grpMin cmp)
    (seq (wstore "sp.gp" (rb (var "sp.j")) (var "sp.b"))
         (incr "sp.j"))))

/-- The registers written by `pivProg` itself. -/
def pvRegs : List String := "sp.j" :: gmRegs

/-- **BM.7 is correct**: every group gets a key-minimal member as its pivot; only the pivot row
`sp.gp[l·n, l·n + p)` and registers are written. -/
theorem pivProg_spec {β : Type*} [LinearOrder β] {cmp : Stmt} {KR : State V → Prop} {κ : ℕ → β}
    {dom : ℕ → Prop} {C Bud : ℕ} {CW CV FA FR : List String}
    (hI : CmpI ops cmp KR κ dom C Bud CW CV FA FR) (hFR : ∀ a ∈ pvRegs ++ CW, a ∈ FR)
    (hFA : "sp.gp" ∈ FA) (st : State V) {l n p : ℕ} {P : ℕ → Finset ℕ} {piv0 : ℕ → ℕ}
    (hG : GrpRep st l n p P piv0) (hl : st.w "lvl" = l) (hn : st.w "n" = n)
    (hnp : st.wa "sp.np" l = p) (hnpl : l < st.wlen "sp.np")
    (hne : ∀ j < p, 0 < gl st l n j) (hdom : ∀ j < p, ∀ x ∈ P j, dom x) (hK : KR st)
    (hcap : (l + 1) * n < st.cap) (hcap1 : 1 < st.cap)
    (hbud : st.cost + 2 + p * 7 + (∑ j ∈ Finset.range p, gl st l n j) * (C + 8) ≤ Bud) :
    Runs ops (pivProg cmp) st (fun r => GrpRep r l n p P (fun j => r.wa "sp.gp" (l * n + j)) ∧
      (∀ j < p, r.wa "sp.gp" (l * n + j) ∈ P j ∧
        ∀ x ∈ P j, κ (r.wa "sp.gp" (l * n + j)) ≤ κ x) ∧
      KR r ∧ Unchanged st r ["sp.gp"] [] (pvRegs ++ CW) CV ∧
      (∀ i, (i < l * n ∨ l * n + p ≤ i) → r.wa "sp.gp" i = st.wa "sp.gp" i) ∧ r.wlen = st.wlen ∧
      st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 2 + p * 7 + (∑ j ∈ Finset.range p, gl st l n j) * (C + 8)) := by
  classical
  have hpn := hG.p_le
  have hn1 : n ≤ (l + 1) * n := Nat.le_mul_of_pos_left n (by omega)
  have mj : "sp.j" ∈ pvRegs ++ CW := by simp [pvRegs]
  have hgmFR : ∀ a ∈ gmRegs ++ CW, a ∈ FR := fun a ha => hFR a (by
    simp only [pvRegs, List.cons_append, List.mem_cons]; exact Or.inr ha)
  have hsumle : ∀ j, j ≤ p → ∑ q ∈ Finset.range j, gl st l n q ≤ ∑ q ∈ Finset.range p, gl st l n q :=
    fun j hj => Finset.sum_le_sum_of_subset (Finset.range_mono hj)
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by omega)) ?_)
  set st1 := (st.setW "sp.j" 0).charge 1 with hst1
  have hU1' : Unchanged st st1 ["sp.gp"] [] (pvRegs ++ CW) [] := by
    rw [hst1, unch_charge, unch_setW mj]; exact Unchanged.refl _ _ _ _ _
  have hU1 : Unchanged st st1 ["sp.gp"] [] (pvRegs ++ CW) CV :=
    hU1'.mono (by simp) (by simp) (by simp) (by simp)
  refine runs_while_nat (fun m r => ∃ j, m = p - j ∧ j ≤ p ∧ r.w "sp.j" = j ∧
      GrpRep r l n p P (fun j' => r.wa "sp.gp" (l * n + j')) ∧
      (∀ j' < j, r.wa "sp.gp" (l * n + j') ∈ P j' ∧
        ∀ x ∈ P j', κ (r.wa "sp.gp" (l * n + j')) ≤ κ x) ∧
      KR r ∧ Unchanged st r ["sp.gp"] [] (pvRegs ++ CW) CV ∧ r.wlen = st.wlen ∧
      (∀ i, (i < l * n ∨ l * n + j ≤ i) → r.wa "sp.gp" i = st.wa "sp.gp" i) ∧
      st.cost ≤ r.cost ∧
      r.cost ≤ st.cost + 1 + j * 7 + (∑ q ∈ Finset.range j, gl st l n q) * (C + 8)) _ ?_ p st1 ?_
  swap
  · refine ⟨0, by simp, by omega, by simp [hst1], ?_, fun j' hj' => absurd hj' (by omega),
      hI.frame st st1 hK (hU1'.mono (by simp [hFA]) (by simp) hFR (by simp)) (by simp [hst1] <;> omega), hU1, by simp [hst1],
      fun i _ => by simp [hst1], by simp [hst1], by simp [hst1]⟩
    exact GrpRep.of_arrays' hG (fun a _ => by simp [hst1]) (fun a _ => by simp [hst1])
      (fun j _ => by simp [hst1])
  rintro m r ⟨j, rfl, hjp, hjr, hGr, hpiv, hKr, hUr, hwlr, hgp, hc1, hc2⟩
  have hcapr : r.cap = st.cap := hUr.cap
  have hlr : r.w "lvl" = l := by
    rw [hUr.wreg "lvl" (by simp [pvRegs, gmRegs]; intro h; exact (hI.regs _ h).2.1 rfl)]; exact hl
  have hnr : r.w "n" = n := by
    rw [hUr.wreg "n" (by simp [pvRegs, gmRegs]; intro h; exact (hI.regs _ h).2.2.1 rfl)]; exact hn
  have hwaNp : r.wa "sp.np" = st.wa "sp.np" := (hUr.warr "sp.np" (by simp)).1
  have hwaGl : r.wa "sp.gl" = st.wa "sp.gl" := (hUr.warr "sp.gl" (by simp)).1
  have hgl : ∀ q, gl r l n q = gl st l n q := fun q => by simp only [gl, hwaGl]
  have hnpl' : l < r.wlen "sp.np" := by rw [hwlr]; exact hnpl
  have eT : evalW r (lt (var "sp.j") (load "sp.np" (var "lvl"))) = some (if j < p then 1 else 0) := by
    rw [evalW_lt_of (by rw [evalW_var, hjr]) (x := j) (y := p) (by
      simp [hlr, hnpl', hwaNp, hnp]) (by rw [hcapr]; omega)]
  refine ⟨if j < p then 1 else 0, eT, fun hx => ?_, fun hx => ?_⟩
  · have hjp' : j < p := by by_contra h; rw [if_neg h] at hx; exact hx rfl
    have hsj := hsumle (j + 1) (by omega)
    rw [Finset.sum_range_succ] at hsj
    have hm1 := Nat.mul_le_mul_right (C + 8) hsj
    rw [Nat.add_mul] at hm1
    have hbud' : (r.charge 1).cost + 4 + gl (r.charge 1) l n j * (C + 8) ≤ Bud := by
      simp only [State.charge_cost]
      rw [show gl (r.charge 1) l n j = gl st l n j from hgl j]
      omega
    refine runs_seq ((grpMin_spec hI hgmFR (r.charge 1) (GrpRep.charge' hGr 1) (by simpa using hlr) (by simpa using hnr)
      (by simpa using hjr) hjp' (by rw [show gl (r.charge 1) l n j = gl st l n j from hgl j]; exact hne j hjp')
      (hdom j hjp') (hI.frame r _ hKr (by rw [unch_charge]; exact Unchanged.refl _ _ _ _ _) (by simp))
      (by simpa [hcapr] using hcap) hbud').mono ?_)
    rintro r2 ⟨hb2P, hb2min, hK2, hU2, hwl2, hc2a, hc2b⟩
    have hwa2 : r2.wa = r.wa := funext fun a => (hU2.warr a (by simp)).1
    have hc2a' : r.cost + 1 ≤ r2.cost := by simpa using hc2a
    have hc2b' : r2.cost ≤ r.cost + 1 + 4 + gl st l n j * (C + 8) := by
      have := hc2b
      rw [show gl (r.charge 1) l n j = gl st l n j from hgl j] at this
      simpa using this
    have mgp : "sp.gp" ∈ ["sp.gp"] := List.mem_singleton_self _
    have hsub2 : ∀ a ∈ gmRegs ++ CW, a ∈ pvRegs ++ CW := by
      intro a ha; simp only [pvRegs, List.cons_append, List.mem_cons]; exact Or.inr ha
    have hU2' : Unchanged r r2 ["sp.gp"] [] (pvRegs ++ CW) CV :=
      (Unchanged.charge r 1 _ _ _ _).trans (hU2.mono (by simp) (by simp) hsub2 (by simp))
    have hj2 : r2.w "sp.j" = j := by
      rw [hU2.wreg "sp.j" (by simp [gmRegs]; intro h; exact (hI.regs _ h).2.2.2 rfl)]; simpa using hjr
    have hl2 : r2.w "lvl" = l := by
      rw [hU2.wreg "lvl" (by simp [gmRegs]; intro h; exact (hI.regs _ h).2.1 rfl)]; simpa using hlr
    have hn2 : r2.w "n" = n := by
      rw [hU2.wreg "n" (by simp [gmRegs]; intro h; exact (hI.regs _ h).2.2.1 rfl)]; simpa using hnr
    have hcap2 : r2.cap = st.cap := by rw [hU2.cap]; simpa using hcapr
    -- `sp.gp[lvl * n + sp.j] := sp.b`
    have hidx : l * n + j < r2.wlen "sp.gp" := by
      rw [hwl2]; have := hG.len_gp; simp only [State.charge_wlen, hwlr]
      have := row_index_lt (l := l) (show j < n by omega); omega
    have eI : evalW r2 (rb (var "sp.j")) = some (l * n + j) := by
      simp [rb, hl2, hn2, hj2, fit_of_lt (show l * n < r2.cap by rw [hcap2]; have := row_index_lt (l := l) (show j < n by omega); omega),
        fit_of_lt (show l * n + j < r2.cap by rw [hcap2]; have := row_index_lt (l := l) (show j < n by omega); omega)]
    refine runs_seq (runs_wstore eI (by simp : evalW r2 (var "sp.b") = some (r2.w "sp.b")) hidx ?_)
    set r3 := (r2.storeW "sp.gp" (l * n + j) (r2.w "sp.b")).charge 1 with hr3
    have e5 : evalW r3 (add (var "sp.j") (lit 1)) = some (j + 1) := by
      simp [hr3, hj2, hcap2, fit_of_lt (show j + 1 < st.cap by
        have := row_index_lt (l := l) (show j < n by omega); omega), fit_of_lt (show 1 < st.cap by omega)]
    refine runs_wset e5 ?_
    set r4 := (r3.setW "sp.j" (j + 1)).charge 1 with hr4
    have hwa4 : ∀ a i, r4.wa a i = if a = "sp.gp" ∧ i = l * n + j then r2.w "sp.b" else r.wa a i := by
      intro a i; simp [hr4, hr3, hwa2]
    have hU24 : Unchanged r2 r4 ["sp.gp"] [] (pvRegs ++ CW) [] := by
      rw [hr4, unch_charge, unch_setW mj, hr3, unch_charge, unch_storeW mgp]
      exact Unchanged.refl _ _ _ _ _
    have hUr4 : Unchanged r r4 ["sp.gp"] [] (pvRegs ++ CW) CV :=
      hU2'.trans (hU24.mono (by simp) (by simp) (by simp) (by simp))
    have hU4 : Unchanged st r4 ["sp.gp"] [] (pvRegs ++ CW) CV := hUr.trans hUr4
    refine ⟨p - (j + 1), by omega, j + 1, rfl, by omega, by simp [hr4], ?_, ?_, ?_, hU4, ?_, ?_,
      ?_, ?_⟩
    · refine GrpRep.of_arrays' hGr (fun a ha => ?_) (fun a _ => ?_) (fun j' _ => rfl)
      · funext i
        have hne' : a ≠ "sp.gp" := by simp at ha; rcases ha with h | h | h | h | h <;> simp [h]
        rw [hwa4]; simp [hne']
      · simp [hr4, hr3, hwl2]
    · intro j' hj'
      by_cases hjj : j' = j
      · subst hjj
        rw [hwa4]; simp only [and_true, if_true]
        exact ⟨hb2P, hb2min⟩
      · have hne' : l * n + j' ≠ l * n + j := by omega
        rw [hwa4]; simp only [hne', and_false, if_false]
        exact hpiv j' (by omega)
    · exact hI.frame r2 r4 hK2 (hU24.mono (by simp [hFA]) (by simp) hFR (by simp))
        (by simp [hr4, hr3] <;> omega)
    · simp [hr4, hr3, hwl2, hwlr]
    · intro i hi
      rw [hwa4]
      have hne' : i ≠ l * n + j := by omega
      simp only [hne', and_false, if_false]
      exact hgp i (by omega)
    · simp [hr4, hr3]; omega
    · have hsum_succ : (∑ q ∈ Finset.range (j + 1), gl st l n q) =
          (∑ q ∈ Finset.range j, gl st l n q) + gl st l n j := Finset.sum_range_succ _ _
      simp only [hr4, hr3, State.charge_cost, State.setW_cost, State.storeW_cost]
      rw [hsum_succ, Nat.add_mul (∑ q ∈ Finset.range j, gl st l n q) (gl st l n j) (C + 8)]
      omega
  · -- all groups done
    have hjp' : j = p := by by_contra h; rw [if_pos (by omega)] at hx; exact one_ne_zero hx
    subst hjp'
    refine ⟨GrpRep.charge' hGr 1, hpiv, hI.frame r _ hKr (by rw [unch_charge]; exact Unchanged.refl _ _ _ _ _) (by simp),
      by rw [unch_charge]; exact hUr, hgp, by simp [hwlr], by simp; omega, by simp; omega⟩

end Frontier.CHD.RamInit
