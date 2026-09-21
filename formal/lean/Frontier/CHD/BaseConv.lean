import Frontier.CHD.InsSeg
import Frontier.CHD.IHeapLab

/-!
# Frontier.CHD.BaseConv — the base case's leftover conversion at RAM level (owner agent-03)

**NON-GATE** (B-L4 glue, Layer B).  `BMLazy.BaseDH` ends the heap base case by inserting the leftover heap keys (any
duplicate-free list `lK` of them) with their labels into a fresh level-0 structure `newC M₀ B`.  With agent-06's IHeap
as the base heap (`IHeapLab.HRL`), the leftover keys sit in the slot array `hp_A[0, hp_n)`:
* `HRL.slots`: the slot list is duplicate-free and enumerates the heap's set;
* `baseConv_spec`: `insSeg dsNew dsIns "hp_A" (lit 0) (var "hp_n")` (InsSeg) ends in `DR r (insManyC … lK g (newC M B))`
  for the slot list `lK` — exactly BaseDH's conversion, for agent-01's abstract `DNewI`/`DInsI` (B-L3).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.IHeapLab

open Frontier Frontier.RAM Frontier.CHD.IHeap Frontier.CHD.BM Frontier.CHD.RamInit

variable {G : Graph} {s : Fin G.n}

/-- **The heap's slot list** enumerates its vertex set without repetition. -/
theorem HRL.slots {st : State ℝ≥0} {T : Finset (Fin G.n)} {key : Fin G.n → WLab G s} (h : HRL st T key) :
    ∃ l : List (Fin G.n), l.Nodup ∧ l.toFinset = T ∧ l.length = T.card ∧
      ∀ j (hj : j < l.length), st.wa "hp_A" j = (l[j] : ℕ) := by
  obtain ⟨-, -, -, -, hpos, -, hT⟩ := h
  let F : Fin T.card → Fin G.n := fun j => ⟨st.wa "hp_A" j, (hpos.slots j j.2).1⟩
  refine ⟨List.ofFn F, ?_, ?_, by simp, fun j hj => by simp [F]⟩
  · rw [List.nodup_ofFn]
    intro i j hij
    have e : st.wa "hp_A" i = st.wa "hp_A" j := congrArg Fin.val hij
    exact Fin.ext (hpos.inj i.2 j.2 e)
  · ext v
    rw [List.mem_toFinset, List.mem_ofFn, ← mem_T_iff hT]
    simp only [IHeap.T, Finset.mem_image, Finset.mem_range, Set.mem_range]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.2, rfl⟩
    · rintro ⟨j, hj, e⟩
      exact ⟨⟨j, hj⟩, Fin.ext e⟩

/-- **BaseDH's leftover conversion**: the heap's keys, in slot order, into a fresh structure `newC M B`. -/
theorem baseConv_spec {dsNew dsIns : Stmt} {DR0 : State ℝ≥0 → DGl G s → Prop}
    {DR : State ℝ≥0 → DGl G s → DStrM G s → Prop} {Inv : DGl G s → DStrM G s → Prop}
    {f : Fin G.n → WLab G s} {T K C Cn M : ℕ} {B : WLab G s} {NA NVA NW NVR IA IVA IW IVR : List String}
    {Pv : Fin G.n → Prop} {U : State ℝ≥0 → ℕ} {Ucap : ℕ}
    (hN : DNewI realOps dsNew DR0 DR M B Cn NA NVA NW NVR U Ucap)
    (hI : DInsI realOps dsIns DR Inv f T K C IA IVA IW IVR cvRegs Pv U Ucap)
    (hNW : ∀ a ∈ NW, a ∉ cvRegs) (hNA : "hp_A" ∉ NA) (hIA : "hp_A" ∉ IA)
    (st : State ℝ≥0) (g : DGl G s) {H : Finset (Fin G.n)} {key : Fin G.n → WLab G s} (hH : HRL st H key)
    (hD0 : ∀ r : State ℝ≥0, Unchanged st r [] [] ["cv.b", "cv.e"] [] → DR0 r g)
    (hInv : ∀ l : List (Fin G.n), l.Nodup → l.toFinset = H → ∀ k ≤ l.length,
      Inv (BM.insManyC (dlOps G s) T f (l.take k) g (newC M B)).1
        (BM.insManyC (dlOps G s) T f (l.take k) g (newC M B)).2.1)
    (hPv : ∀ v ∈ H, Pv v)
    (hUb : ∀ l : List (Fin G.n), l.Nodup → l.toFinset = H →
      U st + 1 + (BM.insManyC (dlOps G s) T f l g (newC M B)).2.2 + l.length ≤ Ucap) :
    Runs realOps (insSeg dsNew dsIns "hp_A" (.lit 0) (.var "hp_n")) st (fun r =>
      ∃ lK : List (Fin G.n), lK.Nodup ∧ lK.toFinset = H ∧
        DR r (BM.insManyC (dlOps G s) T f lK g (newC M B)).1 (BM.insManyC (dlOps G s) T f lK g (newC M B)).2.1 ∧
        Unchanged st r (NA ++ IA) (NVA ++ IVA) (cvRegs ++ NW ++ IW) (NVR ++ IVR) ∧ st.cost ≤ r.cost ∧
        r.cost ≤ st.cost + Cn + 4 + K * (BM.insManyC (dlOps G s) T f lK g (newC M B)).2.2 +
          lK.length * (C + 5)) := by
  obtain ⟨l, hnd, hset, hlen, hA⟩ := hH.slots
  obtain ⟨hn, hlA, -, hcap, -, -, -⟩ := hH
  have hHn : H.card ≤ G.n := card_le_n H
  refine Runs.mono (insSeg_spec (ops := realOps) (L := l) (b := 0) hN hI hNW hNA hIA st g hD0
    (evalW_lit_of (by omega)) (by simp [hn, hlen]) (fun j hj => by rw [Nat.zero_add]; exact hA j hj)
    (by rw [hlA]; omega) (by omega) (hInv l hnd hset)
    (fun j hj => hPv _ (by rw [← hset]; exact List.mem_toFinset.mpr (List.getElem_mem hj)))
    (hUb l hnd hset)) ?_
  rintro r ⟨h1, h2, h3, h4⟩
  exact ⟨l, hnd, hset, h1, h2, h3, h4⟩

end Frontier.CHD.IHeapLab
