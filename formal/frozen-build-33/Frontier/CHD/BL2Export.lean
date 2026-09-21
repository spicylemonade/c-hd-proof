import Frontier.CHD.BL2Find
import Frontier.CHD.RamLevel

/-!
# Frontier.CHD.BL2Export — B-L2: export of the region `W` to the spine's level row (owner agent-09,
NON-GATE)

After the invocation loop, `W` is listed at `fp.W[fp.ob ..]` (`WRep`) and marked in `fp.inW`.
`fpExport` appends the list to row `lvl` of the spine's arrays `W` / `W.len` (agent-08's
`RowRep`, used by BM.26) and clears `fp.inW` on the way, so the next invocation starts with
`Bits fp.inW ∅` again.  Cost `≤ 3 + 6 |W|`.
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt Frontier.CHD.RamLevel

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-- Export `W` to row `lvl` of `W` / `W.len`, clearing `fp.inW`. -/
def fpExport : Stmt :=
  seq (rowReset "W.len")
  (seq (wset "fp.i" (lit 0))
  (Stmt.while (lt (var "fp.i") (var "fp.wl"))
    (seq (wset "fp.y" (load "fp.W" (add (var "fp.ob") (var "fp.i"))))
    (seq (rowAppend "W" "W.len" (var "fp.y"))
    (seq (wstore "fp.inW" (var "fp.y") (lit 0))
         (wset "fp.i" (add (var "fp.i") (lit 1))))))))

theorem take_succ_map_val {wl : List (Fin G.n)} {i : ℕ} (hi : i < wl.length) :
    (wl.take (i + 1)).map Fin.val = (wl.take i).map Fin.val ++ [(wl[i] : ℕ)] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.map_append]; rfl

/-- **Export of `W`** into the spine's row `l`, clearing `fp.inW`. -/
theorem export_spec {st : State V} {W : Finset (Fin G.n)} {l : ℕ}
    (hW : WRep st W) (hl : st.w "lvl" = l) (hn : st.w "n" = G.n)
    (hlen : l < st.wlen "W.len") (hrow : (l + 1) * G.n ≤ st.wlen "W")
    (hcap : (l + 1) * G.n + st.w "fp.ob" + G.n + 2 < st.cap) :
    Runs ops fpExport st (fun st' => ∃ wl : List (Fin G.n), wl.Nodup ∧ wl.toFinset = W ∧
      RowRep st' "W" "W.len" G.n l (wl.map Fin.val) ∧ Bits (G := G) st' "fp.inW" ∅ ∧
      Unchanged st st' ["W", "W.len", "fp.inW"] [] ["fp.i", "fp.y"] [] ∧
      st'.wlen "W" = st.wlen "W" ∧ st'.wlen "W.len" = st.wlen "W.len" ∧
      (∀ j, j ≠ l → st'.wa "W.len" j = st.wa "W.len" j) ∧
      (∀ j, (j < l * G.n ∨ (l + 1) * G.n ≤ j) → st'.wa "W" j = st.wa "W" j) ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 3 + 6 * W.card) := by
  obtain ⟨wl, hnd, hset, hwl, harr, hbits, hWlen⟩ := hW
  have hcard : W.card = wl.length := by rw [← hset, List.toFinset_card_of_nodup hnd]
  have hwlen : wl.length ≤ G.n := by
    rw [← hcard]; exact (Finset.card_le_univ W).trans (by simp)
  have hcap0 : 0 < st.cap := by omega
  have hnrow : G.n ≤ (l + 1) * G.n := Nat.le_mul_of_pos_left _ (by omega)
  have hsm : (l + 1) * G.n = l * G.n + G.n := Nat.succ_mul l G.n
  unfold fpExport rowReset
  -- len[l] := 0
  refine runs_seq (runs_wstore (j := l) (a := 0) (by simp [hl]) (evalW_lit_of hcap0) hlen ?_)
  generalize hs1 : (st.storeW "W.len" l 0).charge 1 = s1
  have hu1 : Unchanged st s1 ["W.len"] [] [] [] := by
    rw [← hs1]; exact ((unch_storeW st "W.len" _ _).cat (unch_charge' _ 1)).mono (by simp)
      (by simp) (by simp) (by simp)
  have hcap1 : s1.cap = st.cap := hu1.cap
  refine runs_seq (runs_wset (a := 0) (evalW_lit_of (by rw [hcap1]; omega)) ?_)
  generalize hs2 : (s1.setW "fp.i" 0).charge 1 = s2
  have hu2 : Unchanged s1 s2 [] [] ["fp.i"] [] := by
    rw [← hs2]; exact ((unch_setW s1 "fp.i" 0).cat (unch_charge' _ 1)).mono (by simp) (by simp)
      (by simp) (by simp)
  have hc2 : s2.cost = st.cost + 2 := by rw [← hs2, ← hs1]; simp
  have hi2 : s2.w "fp.i" = 0 := by rw [← hs2]; simp
  let J : ℕ → State V → Prop := fun m s' => ∃ i, m = wl.length - i ∧ i ≤ wl.length ∧
    s'.w "fp.i" = i ∧ RowRep s' "W" "W.len" G.n l ((wl.take i).map Fin.val) ∧
    Bits (G := G) s' "fp.inW" (W \ (wl.take i).toFinset) ∧
    Unchanged st s' ["W", "W.len", "fp.inW"] [] ["fp.i", "fp.y"] [] ∧
    s'.wlen "W" = st.wlen "W" ∧ s'.wlen "W.len" = st.wlen "W.len" ∧
    (∀ j, j ≠ l → s'.wa "W.len" j = st.wa "W.len" j) ∧
    (∀ j, (j < l * G.n ∨ (l + 1) * G.n ≤ j) → s'.wa "W" j = st.wa "W" j) ∧
    st.cost ≤ s'.cost ∧ s'.cost ≤ st.cost + 2 + 6 * i
  have hu12 : Unchanged st s2 ["W", "W.len", "fp.inW"] [] ["fp.i", "fp.y"] [] :=
    (hu1.cat hu2).mono (by decide) (by simp) (by decide) (by simp)
  have hJ0 : J wl.length s2 := by
    refine ⟨0, by simp, by omega, hi2, ?_, ?_, hu12, ?_, ?_, fun j hj => ?_, fun j _ => ?_,
      by omega, by omega⟩
    · rw [List.take_zero, List.map_nil]
      refine ⟨by simp, ?_, ?_, ?_, fun i h => by simp at h⟩
      · rw [← hs2, ← hs1]; simpa using hrow
      · rw [← hs2, ← hs1]; simpa using hlen
      · rw [← hs2, ← hs1]; simp
    · rw [List.take_zero, List.toFinset_nil, Finset.sdiff_empty]
      refine ⟨?_, fun v => ?_⟩
      · rw [← hs2, ← hs1]; simpa using hbits.1
      · rw [← hs2, ← hs1]; simpa using hbits.2 v
    · rw [← hs2, ← hs1]; simp
    · rw [← hs2, ← hs1]; simp
    · rw [← hs2, ← hs1]; simp [hj]
    · rw [← hs2, ← hs1]; simp
  refine runs_while_nat J _ ?_ wl.length s2 hJ0
  intro m s' ⟨i, hm, hile, hi, hR', hB', hu', hWl', hWLl', hoL', hoW', hc0', hc'⟩
  have hcap' : s'.cap = st.cap := hu'.cap
  have hob' : s'.w "fp.ob" = st.w "fp.ob" := hu'.wreg _ (by decide)
  have hwl' : s'.w "fp.wl" = wl.length := by rw [hu'.wreg _ (by decide)]; exact hwl
  have hlvl' : s'.w "lvl" = l := by rw [hu'.wreg _ (by decide)]; exact hl
  have hn' : s'.w "n" = G.n := by rw [hu'.wreg _ (by decide)]; exact hn
  have hFW' := hu'.warr "fp.W" (by decide)
  refine ⟨if i < wl.length then 1 else 0,
    by rw [evalW_lt_of (x := i) (y := wl.length) (by simp [hi]) (by simp [hwl']) (by omega)],
    fun hne => ?_, fun h0 => ?_⟩
  · have hil : i < wl.length := by by_contra h; simp [h] at hne
    -- y := W[ob + i]
    have hidx : evalW (s'.charge 1) (add (var "fp.ob") (var "fp.i")) = some (st.w "fp.ob" + i) :=
      evalW_add_of (by simp [hob']) (by simp [hi]) (by simp [hcap']; omega)
    refine runs_seq (runs_wset (a := wl[i]) (by
      rw [evalW_load_of hidx (by simp [hFW'.2]; omega)]; simp [hFW'.1, harr i hil]) ?_)
    generalize hs3 : ((s'.charge 1).setW "fp.y" (wl[i] : ℕ)).charge 1 = s3
    have hu3 : Unchanged s' s3 [] [] ["fp.y"] [] := by
      rw [← hs3]; exact ((Unchanged.charge s' 1 [] [] [] []).cat ((unch_setW _ "fp.y" _).cat
        (unch_charge' _ 1))).mono (by simp) (by simp) (by simp) (by simp)
    have hc3 : s3.cost = s'.cost + 2 := by rw [← hs3]; simp
    have hy3 : s3.w "fp.y" = wl[i] := by rw [← hs3]; simp
    have hcap3 : s3.cap = st.cap := by rw [hu3.cap, hcap']
    have hR3 : RowRep s3 "W" "W.len" G.n l ((wl.take i).map Fin.val) :=
      hR'.of_eq (by rw [(hu3.warr "W" (by decide)).2]) (by rw [(hu3.warr "W.len" (by decide)).2])
        (by rw [(hu3.warr "W.len" (by decide)).1]) (fun j _ => by rw [(hu3.warr "W" (by decide)).1])
    have hlen_i : ((wl.take i).map Fin.val).length = i := by simp; omega
    refine runs_seq ((rowAppend_spec (ops := ops) s3 (v := (wl[i] : ℕ)) (by decide) hR3
      (by rw [hu3.wreg _ (by decide)]; exact hlvl') (by rw [hu3.wreg _ (by decide)]; exact hn')
      (by rw [hlen_i]; omega) (by simp [hy3]) (by rw [hcap3]; omega)).mono ?_)
    rintro s4 ⟨hR4, hu4, hoW4, hoL4, hoB4, hc4, hwl4⟩
    have hcap4 : s4.cap = st.cap := by rw [hu4.cap, hcap3]
    have hIL4 : s4.wlen "fp.inW" = G.n := by
      rw [hwl4, (hu3.warr "fp.inW" (by decide)).2]; exact hB'.1
    refine runs_seq (runs_wstore (j := wl[i]) (a := 0)
      (by simp [(hu4.wreg "fp.y" (by decide)), hy3]) (evalW_lit_of (by rw [hcap4]; omega))
      (by rw [hIL4]; exact wl[i].2) ?_)
    generalize hs5 : (s4.storeW "fp.inW" (wl[i] : ℕ) 0).charge 1 = s5
    have hu5 : Unchanged s4 s5 ["fp.inW"] [] [] [] := by
      rw [← hs5]; exact ((unch_storeW s4 "fp.inW" _ _).cat (unch_charge' _ 1)).mono (by simp)
        (by simp) (by simp) (by simp)
    have hc5 : s5.cost = s4.cost + 1 := by rw [← hs5]; simp
    have hcap5 : s5.cap = st.cap := by rw [hu5.cap, hcap4]
    have hi5 : s5.w "fp.i" = i := by
      rw [hu5.wreg _ (by simp), hu4.wreg _ (by simp), hu3.wreg _ (by decide)]; exact hi
    refine runs_wset (a := i + 1) (evalW_add_of (by simp [hi5]) (evalW_lit_of (by omega))
      (by rw [hcap5]; omega)) ?_
    generalize hs6 : (s5.setW "fp.i" (i + 1)).charge 1 = s6
    have hu6 : Unchanged s5 s6 [] [] ["fp.i"] [] := by
      rw [← hs6]; exact ((unch_setW s5 "fp.i" _).cat (unch_charge' _ 1)).mono (by simp) (by simp)
        (by simp) (by simp)
    have hc6 : s6.cost = s5.cost + 1 := by rw [← hs6]; simp
    -- the arrays of s6 versus s4
    have hW64 : (∀ j, s6.wa "W" j = s4.wa "W" j) ∧ s6.wlen "W" = s4.wlen "W" := by
      rw [← hs6, ← hs5]; simp
    have hL64 : (∀ j, s6.wa "W.len" j = s4.wa "W.len" j) ∧ s6.wlen "W.len" = s4.wlen "W.len" := by
      rw [← hs6, ← hs5]; simp
    refine ⟨wl.length - (i + 1), by omega, i + 1, rfl, by omega, by rw [← hs6]; simp, ?_, ?_, ?_,
      ?_, ?_, fun j hj => ?_, fun j hj => ?_, by omega, by omega⟩
    · rw [take_succ_map_val hil]
      exact hR4.of_eq hW64.2 hL64.2 (hL64.1 l) (fun j _ => hW64.1 _)
    · refine ⟨?_, fun v => ?_⟩
      · rw [← hs6, ← hs5]; simp [hIL4]
      · rw [← hs6, ← hs5]
        simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and]
        have hB4 : s4.wa "fp.inW" = s'.wa "fp.inW" := by
          rw [hoB4 "fp.inW" (by decide) (by decide), ← hs3]; simp
        by_cases hv : (v : ℕ) = wl[i]
        · rw [if_pos hv]
          have hv' : v = wl[i] := Fin.ext hv
          have hmem : v ∈ (wl.take (i + 1)).toFinset := by
            rw [hv', List.mem_toFinset]
            exact List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩
          simp [hmem]
        · rw [if_neg hv, hB4, hB'.2 v]
          have hvi : v ≠ wl[i] := fun h => hv (by rw [h])
          have hiff : v ∈ wl.take (i + 1) ↔ v ∈ wl.take i := by
            rw [List.take_add_one, List.getElem?_eq_getElem hil]
            simp only [List.mem_append, Option.toList_some, List.mem_singleton, hvi, or_false]
          simp only [Finset.mem_sdiff, List.mem_toFinset, hiff]
    · exact (((hu'.trans (hu3.mono (by simp) (by simp) (by decide) (by simp))).trans
        (hu4.mono (by decide) (by simp) (by simp) (by simp))).trans
        (hu5.mono (by decide) (by simp) (by simp) (by simp))).trans
        (hu6.mono (by simp) (by simp) (by decide) (by simp))
    · rw [hW64.2, hwl4, (hu3.warr "W" (by decide)).2]; exact hWl'
    · rw [hL64.2, hwl4, (hu3.warr "W.len" (by decide)).2]; exact hWLl'
    · rw [hL64.1, hoL4 j hj, (hu3.warr "W.len" (by decide)).1]; exact hoL' j hj
    · rw [hW64.1, hoW4 j (by rw [hlen_i]; omega), (hu3.warr "W" (by decide)).1]; exact hoW' j hj
  · have hieq : i = wl.length := by
      by_contra h; simp [show i < wl.length by omega] at h0
    subst hieq
    rw [List.take_length] at hR' hB'
    have hch : Unchanged s' (s'.charge 1) [] [] [] [] := Unchanged.charge s' 1 _ _ _ _
    refine ⟨wl, hnd, hset, hR'.of_eq (by simp) (by simp) (by simp) (fun _ _ => by simp), ?_,
      hu'.trans (hch.mono (by simp) (by simp) (by simp) (by simp)), by simpa using hWl',
      by simpa using hWLl', fun j hj => by simpa using hoL' j hj,
      fun j hj => by simpa using hoW' j hj, by simp; omega, by simp; omega⟩
    rw [hset, Finset.sdiff_self] at hB'
    exact ⟨by simpa using hB'.1, fun v => by simpa using hB'.2 v⟩

end Frontier.CHD.BL2
