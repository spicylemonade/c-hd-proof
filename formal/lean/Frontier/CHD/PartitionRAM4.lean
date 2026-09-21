import Frontier.CHD.PartitionRAM2
import Frontier.CHD.PartitionRAM3

/-!
# Frontier.CHD.PartitionRAM4 — the PT program of FindPivots-HD (owner agent-03)

**NON-GATE.** `ptProg` runs the forest loop (Algorithm 5 on every tree, `PartitionRAM2`), MakePivots over the
stored pieces (`PartitionRAM3`) and a clearing loop that resets the assignment bitmap `pt.as` at the grouped
vertices (cost `O(#grouped vertices)`, so `pt.as` is all-zero again for the next call).  The program refines
`makePivots S Q (forestPieces k trees)` (`= forestGroups S Q k trees`) at cost `O(Σ_T |T| + 1)`.
-/

namespace Frontier.CHD.PartitionRAM

open Frontier Frontier.RAM Frontier.CHD.Partition

section Mem

variable {α : Type*} [DecidableEq α]

/-- Accumulators and groups of Algorithm 5 stay inside any universe closed under the processed vertices and
their parents. -/
theorem run_mem {s : ℕ} {par : α → α} {U : List α} :
    ∀ (l : List α) (st : PState α), (∀ v ∈ l, v ∈ U ∧ par v ∈ U) →
      (∀ w ∈ U, ∀ x ∈ st.acc w, x ∈ U) → (∀ G ∈ st.groups, ∀ x ∈ G, x ∈ U) →
      (∀ w ∈ U, ∀ x ∈ (l.foldl (step s par) st).acc w, x ∈ U) ∧
        (∀ G ∈ (l.foldl (step s par) st).groups, ∀ x ∈ G, x ∈ U)
  | [], _, _, hacc, hgr => ⟨hacc, hgr⟩
  | v :: l, st, hl, hacc, hgr => by
    obtain ⟨hvU, hpU⟩ := hl v List.mem_cons_self
    refine run_mem l (step s par st v) (fun w hw => hl w (List.mem_cons_of_mem _ hw)) ?_ ?_
    · intro w hw x hx
      unfold step at hx
      split_ifs at hx
      · by_cases hwp : w = par v
        · subst hwp
          simp only [Function.update_self, List.mem_singleton] at hx
          rw [hx]; exact hpU
        · simp only [Function.update_of_ne hwp] at hx
          exact hacc w hw x hx
      · by_cases hwp : w = par v
        · subst hwp
          simp only [Function.update_self, List.mem_append] at hx
          rcases hx with h | h
          · exact hacc _ hpU x h
          · exact hacc _ hvU x h
        · simp only [Function.update_of_ne hwp] at hx
          exact hacc w hw x hx
    · intro G hG x hx
      unfold step at hG
      split_ifs at hG
      · simp only [List.mem_append, List.mem_singleton] at hG
        rcases hG with h | h
        · exact hgr G h x hx
        · subst h
          rcases List.mem_append.mp hx with h | h
          · exact hacc _ hpU x h
          · exact hacc _ hvU x h
      · exact hgr G hG x hx

/-- **Every vertex of a piece is a tree vertex.** -/
theorem pieces_mem {s : ℕ} {par : α → α} {rest : List α} {root : α} (ht : TreeOrder par rest root) :
    ∀ F ∈ pieces s par rest root, ∀ x ∈ F, x ∈ rest ++ [root] := by
  have hroot : root ∈ rest ++ [root] := List.mem_append_right _ (List.mem_singleton_self _)
  have hU : ∀ v ∈ rest, v ∈ rest ++ [root] ∧ par v ∈ rest ++ [root] := by
    intro v hv
    refine ⟨List.mem_append_left _ hv, ?_⟩
    obtain ⟨pre, post, h⟩ := List.append_of_mem hv
    rcases ht.childFirst pre post v h with h' | h'
    · refine List.mem_append_left _ ?_
      rw [h]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ h')
    · rw [h']; exact hroot
  obtain ⟨hacc, hgr⟩ := run_mem (s := s) (par := par) (U := rest ++ [root]) rest init hU
    (fun w hw x hx => by
      simp only [init, List.mem_singleton] at hx
      rw [hx]; exact hw)
    (fun G hG => by simp [init] at hG)
  intro F hF x hx
  unfold pieces at hF
  split at hF
  · rw [List.mem_singleton] at hF
    subst hF
    exact hacc root hroot x hx
  · next G hG =>
    rcases List.mem_append.mp hF with h | h
    · exact hgr F (List.dropLast_subset _ h) x hx
    · rw [List.mem_singleton] at h
      subst h
      rcases List.mem_append.mp hx with h | h
      · exact hacc root hroot x h
      · exact hgr G (List.mem_of_getLast? hG) x (List.mem_of_mem_tail h)

theorem forestPieces_mem {k : ℕ} {trees : List (TreeRec α)}
    (hpf : ∀ T ∈ trees, ParentFirst T.par T.root T.ord) :
    ∀ F ∈ forestPieces k trees, ∀ x ∈ F, ∃ T ∈ trees, x ∈ T.ord := by
  intro F hF x hx
  obtain ⟨T, hT, hFT⟩ := List.mem_flatMap.mp hF
  refine ⟨T, hT, ?_⟩
  rw [mem_ord_iff_of_parentFirst (hpf T hT)]
  exact pieces_mem (treeOrder_of_parentFirst (hpf T hT)) F hFT x hx

theorem forestPieces_nodup {k : ℕ} (hk : 2 ≤ k) {trees : List (TreeRec α)}
    (hpf : ∀ T ∈ trees, ParentFirst T.par T.root T.ord) : ∀ F ∈ forestPieces k trees, F.Nodup := by
  intro F hF
  obtain ⟨T, hT, hFT⟩ := List.mem_flatMap.mp hF
  exact pieces_nodup hk (treeOrder_of_parentFirst (hpf T hT)) F hFT

end Mem

/-- Total piece length is at most twice the number of tree vertices. -/
theorem forestPieces_total_le {k : ℕ} (hk : 2 ≤ k) :
    ∀ trees : List (TreeRec ℕ), (∀ T ∈ trees, ParentFirst T.par T.root T.ord) →
      ((forestPieces k trees).map List.length).sum ≤ 2 * (trees.map (fun T => T.ord.length)).sum
  | [], _ => by simp [forestPieces]
  | T :: ts, h => by
    have hT := h T List.mem_cons_self
    have ih := forestPieces_total_le hk ts (fun U hU => h U (List.mem_cons_of_mem _ hU))
    have h1 := pieces_total_length hk (treeOrder_of_parentFirst hT)
    have h2 := pieces_length_le hk (treeOrder_of_parentFirst hT)
    have h3 := length_ord_of_parentFirst hT
    simp only [forestPieces, List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons] at ih ⊢
    omega

variable {V : Type} {ops : VOps V}

/-! ## Clearing the assignment bitmap -/

/-- Clear `pt.as` at the grouped vertex `pt.GV[pt.j]`. -/
def clrBody : Stmt :=
  .seq (.wset "pt.x" (.load "pt.GV" (.var "pt.j"))) <|
  .seq (.wstore "pt.as" (.var "pt.x") (.lit 0))
       (.wset "pt.j" (.add (.var "pt.j") (.lit 1)))

/-- The clearing loop over `pt.GV[pt.j, pt.gv)`. -/
def clrLoop : Stmt := .while (.lt (.var "pt.j") (.var "pt.gv")) clrBody

/-- Invariant of the clearing loop with `n` grouped vertices left. -/
def CLI (st0 : State V) (L : List ℕ) (A : Finset ℕ) (N c0 n : ℕ) (st : State V) : Prop :=
  n ≤ L.length ∧ st.w "pt.j" = L.length - n ∧
  BitRep st "pt.as" (A \ (L.take (L.length - n)).toFinset) N ∧
  (∀ arr j, arr ≠ "pt.as" → st.wa arr j = st0.wa arr j) ∧
  (∀ y, y ≠ "pt.x" → y ≠ "pt.j" → st.w y = st0.w y) ∧ st.wlen = st0.wlen ∧ st.cap = st0.cap ∧
  st.cost + 4 * n ≤ c0

theorem clrLoop_spec {st0 : State V} {L : List ℕ} {A : Finset ℕ} {N c0 : ℕ}
    (hseg : SegAt st0 "pt.GV" 0 L) (hgv : st0.w "pt.gv" = L.length)
    (hGVl : L.length ≤ st0.wlen "pt.GV") (hLN : ∀ x ∈ L, x < N) (hNl : N ≤ st0.wlen "pt.as")
    (hcap : L.length + 1 < st0.cap) :
    ∀ n st, CLI st0 L A N c0 n st → Runs ops clrLoop st (fun st' =>
      BitRep st' "pt.as" (A \ L.toFinset) N ∧
      (∀ arr j, arr ≠ "pt.as" → st'.wa arr j = st0.wa arr j) ∧
      (∀ y, y ≠ "pt.x" → y ≠ "pt.j" → st'.w y = st0.w y) ∧ st'.wlen = st0.wlen ∧ st'.cap = st0.cap ∧
      st'.cost ≤ c0 + 1) := by
  apply runs_while_nat
  intro n st hCL
  obtain ⟨hnle, hrj, hA, harr, hreg, hlen, hcapst, hcost⟩ := hCL
  have hcap1 : 1 < st.cap := by rw [hcapst]; omega
  have hfit1 : fit st.cap 1 = some 1 := fit_of_lt hcap1
  have hfit0 : fit st.cap 0 = some 0 := fit_of_lt (by omega)
  have hgv' : st.w "pt.gv" = L.length := by rw [hreg _ (by decide) (by decide)]; exact hgv
  refine ⟨if L.length - n < L.length then 1 else 0, ?_, ?_, ?_⟩
  · simp only [evalW_lt', evalW_var, hrj, hgv', Option.bind_some]
    split_ifs <;> simp [hfit0, hfit1]
  · intro hx
    have hn0 : 0 < n := by
      by_contra h
      have : n = 0 := by omega
      subst this; simp at hx
    have hjl : L.length - n < L.length := by omega
    have hxv : st.wa "pt.GV" (L.length - n) = L[L.length - n] := by
      rw [harr _ _ (by decide)]
      have := hseg (L.length - n) hjl
      simpa using this
    have hxN : L[L.length - n] < N := hLN _ (List.getElem_mem hjl)
    have hGV' : L.length - n < st.wlen "pt.GV" := by rw [hlen]; omega
    have hasl : L[L.length - n] < st.wlen "pt.as" := by rw [hlen]; omega
    have hfitj : fit st.cap (L.length - n + 1) = some (L.length - n + 1) := fit_of_lt (by rw [hcapst]; omega)
    apply runs_seq
    refine runs_wset (a := L[L.length - n]) (by simp [hrj, hGV', hxv]) ?_
    apply runs_seq
    refine runs_wstore (j := L[L.length - n]) (a := 0) (by simp) (by simp [hfit0])
      (by simpa using hasl) ?_
    refine runs_wset (a := L.length - n + 1) (by simp [hrj, hfit1, hfitj]) ?_
    refine ⟨n - 1, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [State.charge_w, State.setW_w, State.storeW_w, ↓reduceIte]
      omega
    · intro x hx'
      have htk : L.take (L.length - (n - 1)) = L.take (L.length - n) ++ [L[L.length - n]] := by
        rw [show L.length - (n - 1) = L.length - n + 1 by omega, List.take_add_one,
          List.getElem?_eq_getElem hjl, Option.toList_some]
      simp only [State.charge_wa, State.setW_wa, State.storeW_wa, true_and]
      rw [htk, List.toFinset_append]
      by_cases hxe : x = L[L.length - n]
      · subst hxe; simp
      · rw [if_neg hxe, hA x hx']
        simp [hxe]
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
      have : L.length - n < L.length := by omega
      simp [this] at hx
    subst hn
    refine ⟨?_, harr, hreg, hlen, hcapst, by simp; omega⟩
    intro x hx'
    have := hA x hx'
    simpa using this

end Frontier.CHD.PartitionRAM
