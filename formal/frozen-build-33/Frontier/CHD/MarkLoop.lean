import Frontier.CHD.PartitionRAM3

/-!
# Frontier.CHD.MarkLoop — marking a stored list into a word bitmap (owner agent-03)

**NON-GATE** (Layer B).  `markLoop arrL arrB val` writes `arrB[arrL[j]] := val` for `j ∈ [mk.j, mk.e)`.
`markLoop_spec`: from a list `L` stored contiguously at `arrL[b, b + |L|)`, the bitmap ends with `val` at the members of
`L` and is unchanged elsewhere; only `arrB` and the registers `mk.j`, `mk.x` change; cost `4|L| + 1`.
Used for the membership bitmaps of FindPivots-HD (`fp.inS`, `fp.inQ`: set with `1`, cleared with `0`).
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM

variable {V : Type} {ops : VOps V}

/-- One marking step. -/
def markBody (arrL arrB : String) (val : ℕ) : Stmt :=
  .seq (.wset "mk.x" (.load arrL (.var "mk.j"))) <|
  .seq (.wstore arrB (.var "mk.x") (.lit val))
       (.wset "mk.j" (.add (.var "mk.j") (.lit 1)))

/-- The marking loop over `arrL[mk.j, mk.e)`. -/
def markLoop (arrL arrB : String) (val : ℕ) : Stmt :=
  .while (.lt (.var "mk.j") (.var "mk.e")) (markBody arrL arrB val)

/-- Invariant with `n` elements left. -/
def MKI (st0 : State V) (arrL arrB : String) (val : ℕ) (b : ℕ) (L : List ℕ) (c0 n : ℕ) (st : State V) : Prop :=
  n ≤ L.length ∧ st.w "mk.j" = b + (L.length - n) ∧
  (∀ x, st.wa arrB x = if x ∈ L.take (L.length - n) then val else st0.wa arrB x) ∧
  (∀ arr j, arr ≠ arrB → st.wa arr j = st0.wa arr j) ∧
  (∀ y, y ≠ "mk.x" → y ≠ "mk.j" → st.w y = st0.w y) ∧ st.wlen = st0.wlen ∧ st.cap = st0.cap ∧
  st.cost + 4 * n ≤ c0

theorem markLoop_spec {st0 : State V} {arrL arrB : String} {val b : ℕ} {L : List ℕ} {c0 : ℕ}
    (hLB : arrL ≠ arrB) (hseg : SegAt st0 arrL b L) (he : st0.w "mk.e" = b + L.length)
    (hLl : b + L.length ≤ st0.wlen arrL) (hBl : ∀ x ∈ L, x < st0.wlen arrB)
    (hcap : b + L.length + 1 < st0.cap) (hval : val < st0.cap) :
    ∀ n st, MKI st0 arrL arrB val b L c0 n st → Runs ops (markLoop arrL arrB val) st (fun st' =>
      (∀ x, st'.wa arrB x = if x ∈ L then val else st0.wa arrB x) ∧
      (∀ arr j, arr ≠ arrB → st'.wa arr j = st0.wa arr j) ∧
      (∀ y, y ≠ "mk.x" → y ≠ "mk.j" → st'.w y = st0.w y) ∧ st'.wlen = st0.wlen ∧ st'.cap = st0.cap ∧
      st'.cost ≤ c0 + 1) := by
  apply runs_while_nat
  intro n st hMK
  obtain ⟨hnle, hrj, hB, harr, hreg, hlen, hcapst, hcost⟩ := hMK
  have hcap1 : 1 < st.cap := by rw [hcapst]; omega
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hfitv : fit st.cap val = some val := fit_of_lt (by rw [hcapst]; exact hval)
  have he' : st.w "mk.e" = b + L.length := by rw [hreg _ (by decide) (by decide)]; exact he
  refine ⟨if b + (L.length - n) < b + L.length then 1 else 0, ?_, ?_, ?_⟩
  · simp only [evalW_lt', evalW_var, hrj, he', Option.bind_some]
    split_ifs <;> simp [hfit0, hfit1]
  · intro hx
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      subst this; simp at hx
    have hjl : L.length - n < L.length := by omega
    have hxv : st.wa arrL (b + (L.length - n)) = L[L.length - n] := by
      rw [harr _ _ hLB]
      exact hseg (L.length - n) hjl
    have hLl' : b + (L.length - n) < st.wlen arrL := by rw [hlen]; omega
    have hBl' : L[L.length - n] < st.wlen arrB := by rw [hlen]; exact hBl _ (List.getElem_mem hjl)
    have hfitj : fit st.cap (b + (L.length - n) + 1) = some (b + (L.length - n) + 1) :=
      fit_of_lt (by rw [hcapst]; omega)
    apply runs_seq
    refine runs_wset (a := L[L.length - n]) (by simp [hrj, hLl', hxv]) ?_
    apply runs_seq
    refine runs_wstore (j := L[L.length - n]) (a := val) (by simp) (by simp [hfitv]) (by simpa using hBl') ?_
    refine runs_wset (a := b + (L.length - n) + 1) (by simp [hrj, hfit1, hfitj]) ?_
    refine ⟨n - 1, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.charge_w, State.setW_w, ↓reduceIte]
      omega
    · intro x
      have htk : L.take (L.length - (n - 1)) = L.take (L.length - n) ++ [L[L.length - n]] := by
        rw [show L.length - (n - 1) = L.length - n + 1 by omega, List.take_add_one,
          List.getElem?_eq_getElem hjl, Option.toList_some]
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and]
      rw [htk]
      by_cases hxe : x = L[L.length - n]
      · rw [if_pos hxe, if_pos (by rw [hxe]; exact List.mem_append_right _ (List.mem_singleton_self _))]
      · rw [if_neg hxe, hB x]
        have hiff : x ∈ List.take (L.length - n) L ++ [L[L.length - n]] ↔ x ∈ List.take (L.length - n) L := by
          rw [List.mem_append, List.mem_singleton]
          exact ⟨fun h => h.resolve_right hxe, Or.inl⟩
        by_cases hm : x ∈ List.take (L.length - n) L
        · rw [if_pos hm, if_pos (hiff.mpr hm)]
        · rw [if_neg hm, if_neg (fun h => hm (hiff.mp h))]
    · intro arr j harr'
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa]
      rw [if_neg (by rintro ⟨h, -⟩; exact harr' h)]
      exact harr arr j harr'
    · intro y hy1 hy2
      simp only [State.charge_w, State.setW_w, State.storeW_w, if_neg hy1, if_neg hy2]
      exact hreg y hy1 hy2
    · simp [hlen]
    · simp [hcapst]
    · simp only [State.charge_cost, State.setW_cost, State.storeW_cost]
      omega
  · intro hx
    have hn : n = 0 := by
      by_contra h
      have : b + (L.length - n) < b + L.length := by omega
      simp [this] at hx
    subst hn
    refine ⟨fun x => ?_, harr, hreg, hlen, hcapst, by simp; omega⟩
    have := hB x
    simpa using this

end Frontier.CHD.PartitionRAM
