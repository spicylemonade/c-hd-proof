import Frontier.RAMWP
import Frontier.RAMRep

/-!
# Frontier.CHD.RamBase — the heap-free base case of the spine (BC.1–BC.9), data layer

Owner: agent-08.  NON-GATE.

The running base case keeps its store `D` as an array **set** of vertices (proposal 12:4x on the
board): in `BMCost.BaseLoopC` every stored key equals the current label, so only the vertex set
is needed; extract-min is a linear scan over the set comparing current labels.

* `SetRep st n A`: `bc.set[0..bc.sz)` lists the members of `A ⊆ [0, n)`, `bc.pos[x] = i + 1` iff
  `bc.set[i] = x`, and `bc.pos[x] = 0` iff `x ∉ A`;
* `setAdd`: add the vertex in register `bc.x` if absent (O(1));
* `setDel`: remove the member at index `bc.i` by a swap with the last member (O(1)).
-/

namespace Frontier.CHD.RamBase

open Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V}

/-- The base-case set. -/
structure SetRep (st : State V) (n : ℕ) (A : Finset ℕ) : Prop where
  len_set : n ≤ st.wlen "bc.set"
  len_pos : n ≤ st.wlen "bc.pos"
  sz_le : st.w "bc.sz" ≤ n
  mem_lt : ∀ i < st.w "bc.sz", st.wa "bc.set" i < n
  pos : ∀ i < st.w "bc.sz", st.wa "bc.pos" (st.wa "bc.set" i) = i + 1
  pos0 : ∀ x < n, st.wa "bc.pos" x = 0 ∨
    ∃ i < st.w "bc.sz", st.wa "bc.pos" x = i + 1 ∧ st.wa "bc.set" i = x
  img : A = (Finset.range (st.w "bc.sz")).image (st.wa "bc.set")

theorem SetRep.mem_iff {st : State V} {n : ℕ} {A : Finset ℕ} (h : SetRep st n A) {x : ℕ}
    (hx : x < n) : x ∈ A ↔ st.wa "bc.pos" x ≠ 0 := by
  constructor
  · intro hA
    rw [h.img, Finset.mem_image] at hA
    obtain ⟨i, hi, rfl⟩ := hA
    rw [Finset.mem_range] at hi
    rw [h.pos i hi]; omega
  · intro h0
    rcases h.pos0 x hx with h1 | ⟨i, hi, _, hix⟩
    · exact absurd h1 h0
    · rw [h.img, Finset.mem_image]; exact ⟨i, Finset.mem_range.mpr hi, hix⟩

theorem SetRep.inj {st : State V} {n : ℕ} {A : Finset ℕ} (h : SetRep st n A) {i j : ℕ}
    (hi : i < st.w "bc.sz") (hj : j < st.w "bc.sz") (he : st.wa "bc.set" i = st.wa "bc.set" j) :
    i = j := by
  have h1 := h.pos i hi
  have h2 := h.pos j hj
  rw [he] at h1
  omega

theorem SetRep.card {st : State V} {n : ℕ} {A : Finset ℕ} (h : SetRep st n A) :
    A.card = st.w "bc.sz" := by
  rw [h.img, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  exact h.inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) he

theorem SetRep.sub_range {st : State V} {n : ℕ} {A : Finset ℕ} (h : SetRep st n A) :
    A ⊆ Finset.range n := by
  intro x hx
  rw [h.img, Finset.mem_image] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact Finset.mem_range.mpr (h.mem_lt i (Finset.mem_range.mp hi))

/-- Adding an absent vertex leaves room: the set has fewer than `n` members. -/
theorem SetRep.sz_lt {st : State V} {n : ℕ} {A : Finset ℕ} (h : SetRep st n A) {x : ℕ}
    (hx : x < n) (hxA : x ∉ A) : st.w "bc.sz" < n := by
  have hsub : insert x A ⊆ Finset.range n := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_range.mpr hx
    · exact h.sub_range hy
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxA, Finset.card_range, h.card] at this
  omega

/-- Array-level effect of appending an absent vertex. -/
theorem SetRep.add_of {st st' : State V} {n : ℕ} {A : Finset ℕ} (h : SetRep st n A) {x : ℕ}
    (hxn : x < n) (hA : x ∉ A) (hwl : st'.wlen = st.wlen)
    (hsz : st'.w "bc.sz" = st.w "bc.sz" + 1)
    (hset : ∀ i, st'.wa "bc.set" i = if i = st.w "bc.sz" then x else st.wa "bc.set" i)
    (hpos : ∀ y, st'.wa "bc.pos" y = if y = x then st.w "bc.sz" + 1 else st.wa "bc.pos" y) :
    SetRep st' n (insert x A) := by
  have hsz' : st.w "bc.sz" < n := h.sz_lt hxn hA
  have hxA' : ∀ i < st.w "bc.sz", st.wa "bc.set" i ≠ x := by
    intro i hi he; apply hA; rw [h.img, Finset.mem_image]
    exact ⟨i, Finset.mem_range.mpr hi, he⟩
  refine ⟨by rw [hwl]; exact h.len_set, by rw [hwl]; exact h.len_pos, by rw [hsz]; omega,
    fun i hi => ?_, fun i hi => ?_, fun x' hx' => ?_, ?_⟩
  · rw [hsz] at hi
    rw [hset]
    by_cases hi' : i = st.w "bc.sz"
    · rw [if_pos hi']; exact hxn
    · rw [if_neg hi']; exact h.mem_lt i (by omega)
  · rw [hsz] at hi
    rw [hset]
    by_cases hi' : i = st.w "bc.sz"
    · rw [if_pos hi', hpos, if_pos rfl, hi']
    · rw [if_neg hi', hpos, if_neg (hxA' i (by omega))]; exact h.pos i (by omega)
  · rw [hpos, hsz]
    by_cases hxx : x' = x
    · right; refine ⟨st.w "bc.sz", by omega, by rw [if_pos hxx], by rw [hset, if_pos rfl, hxx]⟩
    · rw [if_neg hxx]
      rcases h.pos0 x' hx' with h0 | ⟨i, hi, hpi, hsi⟩
      · left; exact h0
      · right; refine ⟨i, by omega, hpi, ?_⟩
        rw [hset, if_neg (by omega)]; exact hsi
  · rw [hsz, Finset.range_add_one, Finset.image_insert, hset, if_pos rfl, h.img]
    congr 1
    apply Finset.image_congr
    intro i hi
    rw [Finset.mem_coe, Finset.mem_range] at hi
    rw [hset, if_neg (Nat.ne_of_lt hi)]

/-! ## Adding a vertex -/

/-- `if pos[x] = 0 then (set[sz] := x; pos[x] := sz + 1; sz := sz + 1)` -/
def setAdd : Stmt :=
  ite (load "bc.pos" (var "bc.x")) skip
    (seq (wstore "bc.set" (var "bc.sz") (var "bc.x"))
    (seq (wstore "bc.pos" (var "bc.x") (add (var "bc.sz") (lit 1)))
         (wset "bc.sz" (add (var "bc.sz") (lit 1)))))

theorem setAdd_spec (st : State V) {n : ℕ} {A : Finset ℕ} (h : SetRep st n A) {x : ℕ}
    (hx : st.w "bc.x" = x) (hxn : x < n) (hcap : n < st.cap) :
    Runs ops setAdd st (fun st' => SetRep st' n (insert x A) ∧
      Unchanged st st' ["bc.set", "bc.pos"] [] ["bc.sz"] [] ∧ st'.cost ≤ st.cost + 4) := by
  have hpl : x < st.wlen "bc.pos" := by have := h.len_pos; omega
  by_cases hA : x ∈ A
  · -- already present: nothing to do
    have hp : st.wa "bc.pos" x ≠ 0 := (h.mem_iff hxn).mp hA
    apply wp_sound
    simp only [wp, setAdd, evalW_load', evalW_var, hx, Option.bind_some, hpl, ite_true]
    refine ⟨fun _ => ?_, fun h0 => absurd h0 hp⟩
    refine ⟨?_, ⟨fun a _ => ⟨rfl, rfl⟩, fun a _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl,
      rfl, rfl⟩, by simp⟩
    rw [Finset.insert_eq_of_mem hA]
    exact ⟨h.len_set, h.len_pos, h.sz_le, h.mem_lt, h.pos, h.pos0, h.img⟩
  · have hp : st.wa "bc.pos" x = 0 := by
      by_contra hne; exact hA ((h.mem_iff hxn).mpr hne)
    have hsz : st.w "bc.sz" < n := h.sz_lt hxn hA
    have hsl : st.w "bc.sz" < st.wlen "bc.set" := by have := h.len_set; omega
    have c1 : st.w "bc.sz" + 1 < st.cap := by omega
    have c0 : 1 < st.cap := by omega
    apply wp_sound
    simp (config := { decide := true }) only [wp, setAdd, evalW_load', evalW_var, hx,
      Option.bind_some, hpl, ite_true, hp, evalW_add', evalW_lit', fit_of_lt c0, fit_of_lt c1,
      State.charge_w, State.storeW_w, State.charge_wa, State.storeW_wa, State.charge_wlen,
      State.storeW_wlen, State.charge_cap, State.storeW_cap, hsl, State.setW_w]
    refine ⟨fun h0 => h0.elim, fun _ => ?_⟩
    simp only [true_and]
    refine ⟨SetRep.add_of h hxn hA rfl ?_ ?_ ?_, ⟨fun a ha => ⟨?_, rfl⟩, fun a _ => ⟨rfl, rfl⟩,
      fun z hz => ?_, fun _ _ => rfl, rfl, rfl⟩, ?_⟩
    · simp [State.storeW, State.charge, State.setW]
    · intro i; simp [State.storeW, State.charge, State.setW]
    · intro y; simp [State.storeW, State.charge, State.setW]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
      funext i; simp [State.storeW, State.charge, State.setW, ha.1, ha.2]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      simp [State.storeW, State.charge, State.setW, hz]
    · simp

/-! ## Removing the member at an index -/

/-- Array-level effect of removing the member at index `i` by a swap with the last member. -/
theorem SetRep.del_of {st st' : State V} {n : ℕ} {A : Finset ℕ} (h : SetRep st n A) {i : ℕ}
    (hi : i < st.w "bc.sz") (hwl : st'.wlen = st.wlen)
    (hsz : st'.w "bc.sz" = st.w "bc.sz" - 1)
    (hset : ∀ k, st'.wa "bc.set" k =
      if k = i then st.wa "bc.set" (st.w "bc.sz" - 1) else st.wa "bc.set" k)
    (hpos : ∀ z, st'.wa "bc.pos" z = if z = st.wa "bc.set" i then 0
      else if z = st.wa "bc.set" (st.w "bc.sz" - 1) then i + 1 else st.wa "bc.pos" z) :
    SetRep st' n (A.erase (st.wa "bc.set" i)) := by
  set u := st.wa "bc.set" i with hu
  set y := st.wa "bc.set" (st.w "bc.sz" - 1) with hy
  have hlast : st.w "bc.sz" - 1 < st.w "bc.sz" := by omega
  have hyu : i ≠ st.w "bc.sz" - 1 → y ≠ u := by
    intro hne he; exact hne (h.inj hi hlast he.symm)
  refine ⟨by rw [hwl]; exact h.len_set, by rw [hwl]; exact h.len_pos, by rw [hsz]; have := h.sz_le; omega,
    fun k hk => ?_, fun k hk => ?_, fun z hz => ?_, ?_⟩
  · rw [hsz] at hk
    rw [hset]
    split_ifs
    · exact h.mem_lt _ hlast
    · exact h.mem_lt k (by omega)
  · rw [hsz] at hk
    rw [hset]
    by_cases hki : k = i
    · rw [if_pos hki, hpos, if_neg (hyu (by omega)), if_pos rfl, hki]
    · rw [if_neg hki, hpos]
      have h1 : st.wa "bc.set" k ≠ u := fun he => hki (h.inj (by omega) hi he)
      have h2 : st.wa "bc.set" k ≠ y := fun he => (show k ≠ st.w "bc.sz" - 1 by omega)
        (h.inj (by omega) hlast he)
      rw [if_neg h1, if_neg h2]; exact h.pos k (by omega)
  · rw [hpos, hsz]
    by_cases hzu : z = u
    · left; rw [if_pos hzu]
    · rw [if_neg hzu]
      by_cases hzy : z = y
      · right
        rw [if_pos hzy]
        have hi' : i ≠ st.w "bc.sz" - 1 := by
          intro he; apply hzu; rw [hzy, hy, hu, he]
        refine ⟨i, by omega, rfl, ?_⟩
        rw [hset, if_pos rfl, hzy]
      · rw [if_neg hzy]
        rcases h.pos0 z hz with h0 | ⟨k, hk, hpk, hsk⟩
        · left; exact h0
        · right
          have hki : k ≠ i := by intro he; apply hzu; rw [← hsk, he]
          have hkl : k ≠ st.w "bc.sz" - 1 := by intro he; apply hzy; rw [← hsk, he]
          refine ⟨k, by omega, hpk, ?_⟩
          rw [hset, if_neg hki]; exact hsk
  · ext z
    rw [hsz, Finset.mem_erase, h.img, Finset.mem_image, Finset.mem_image]
    simp only [Finset.mem_range]
    constructor
    · rintro ⟨hzu, k, hk, rfl⟩
      by_cases hkl : k = st.w "bc.sz" - 1
      · -- the last member now sits at index `i`
        have hi' : i ≠ st.w "bc.sz" - 1 := by
          intro he; apply hzu; rw [hkl, ← he]
        refine ⟨i, by omega, ?_⟩
        rw [hset, if_pos rfl, hkl]
      · have hki : k ≠ i := by intro he; apply hzu; rw [he]
        exact ⟨k, by omega, by rw [hset, if_neg hki]⟩
    · rintro ⟨k, hk, rfl⟩
      rw [hset]
      by_cases hki : k = i
      · rw [if_pos hki]
        exact ⟨hyu (by omega), st.w "bc.sz" - 1, hlast, rfl⟩
      · rw [if_neg hki]
        exact ⟨fun he => hki (h.inj (by omega) hi he), k, by omega, rfl⟩

/-- `u := set[i]; y := set[sz-1]; set[i] := y; pos[y] := i+1; pos[u] := 0; sz := sz - 1` -/
def setDel : Stmt :=
  seq (wset "bc.u" (load "bc.set" (var "bc.i")))
  (seq (wset "bc.y" (load "bc.set" (sub (var "bc.sz") (lit 1))))
  (seq (wstore "bc.set" (var "bc.i") (var "bc.y"))
  (seq (wstore "bc.pos" (var "bc.y") (add (var "bc.i") (lit 1)))
  (seq (wstore "bc.pos" (var "bc.u") (lit 0))
       (wset "bc.sz" (sub (var "bc.sz") (lit 1)))))))

/-- **Swap-remove** of the member at index `bc.i` (6 steps); `bc.u` returns the member. -/
theorem setDel_spec (st : State V) {n : ℕ} {A : Finset ℕ} (h : SetRep st n A) {i : ℕ}
    (hi : st.w "bc.i" = i) (hisz : i < st.w "bc.sz") (hcap : n < st.cap) :
    Runs ops setDel st (fun st' => SetRep st' n (A.erase (st.wa "bc.set" i)) ∧
      st'.w "bc.u" = st.wa "bc.set" i ∧
      Unchanged st st' ["bc.set", "bc.pos"] [] ["bc.sz", "bc.u", "bc.y"] [] ∧
      st'.cost = st.cost + 6) := by
  have hn := h.sz_le
  have hlast : st.w "bc.sz" - 1 < st.w "bc.sz" := by omega
  have hl1 : i < st.wlen "bc.set" := by have := h.len_set; omega
  have hl2 : st.w "bc.sz" - 1 < st.wlen "bc.set" := by have := h.len_set; omega
  have hyn : st.wa "bc.set" (st.w "bc.sz" - 1) < n := h.mem_lt _ hlast
  have hun : st.wa "bc.set" i < n := h.mem_lt _ hisz
  have hl3 : st.wa "bc.set" (st.w "bc.sz" - 1) < st.wlen "bc.pos" := by
    have := h.len_pos; omega
  have hl4 : st.wa "bc.set" i < st.wlen "bc.pos" := by have := h.len_pos; omega
  have c1 : 1 < st.cap := by omega
  have c0 : 0 < st.cap := by omega
  have c2 : i + 1 < st.cap := by omega
  apply wp_sound
  simp (config := { decide := true }) only [wp, setDel, evalW_load', evalW_var, evalW_sub',
    evalW_add', evalW_lit', hi, Option.bind_some, fit_of_lt c1, fit_of_lt c0, fit_of_lt c2, hl1,
    hl2, ite_true, State.charge_w, State.setW_w, State.charge_wa, State.setW_wa,
    State.charge_wlen, State.setW_wlen, State.storeW_w, State.storeW_wa, State.storeW_wlen,
    State.charge_cap, State.setW_cap, State.storeW_cap, hl3, hl4, ite_false, true_and,
    false_and]
  refine ⟨SetRep.del_of h hisz rfl ?_ ?_ ?_, ⟨fun a ha => ⟨?_, rfl⟩, fun a _ => ⟨rfl, rfl⟩,
    fun z hz => ?_, fun _ _ => rfl, rfl, rfl⟩, ?_⟩
  · simp [State.storeW, State.charge, State.setW]
  · intro k; simp [State.storeW, State.charge, State.setW]
  · intro z
    simp only [State.storeW, State.charge, State.setW]
    by_cases h1 : z = st.wa "bc.set" i <;> by_cases h2 : z = st.wa "bc.set" (st.w "bc.sz" - 1) <;>
      simp [h1, h2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    funext k; simp [State.storeW, State.charge, State.setW, ha.1, ha.2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp [State.storeW, State.charge, State.setW, hz.1, hz.2.1, hz.2.2]
  · simp

end Frontier.CHD.RamBase
