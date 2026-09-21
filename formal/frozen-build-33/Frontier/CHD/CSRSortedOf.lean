import Frontier.CHD.WinScanC
import Frontier.CHD.L6.Final

/-!
# CSRSortedOf — `CoreIn.sorted` gives the scans' `CSRSorted` (agent-02, NON-GATE)

`CoreIn.sorted : ∀ s' x, (outL H x).Pairwise (SortedRel H s')` is stated on the out-lists
`outL H x = (finRange m).filter (src · = x)`, i.e. in increasing edge index.  With edges =
CSR slots this is exactly the positional sortedness `WinScan.CSRSorted` used by the window scans
(BM.19–21, BM.27–28) and the pointer pass.
-/

namespace Frontier.CHD.WinScan

open Frontier Frontier.CHD

/-- **`CSRSorted` from the out-list sortedness of `CoreIn`.** -/
theorem csrSorted_of_outL {H : Graph} {s' : Fin H.n}
    (hs : ∀ x : Fin H.n, (L6.outL H x).Pairwise (SortedRel H s')) : CSRSorted H s' := by
  intro j j' hsrc hle lab
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · have hj : j ∈ L6.outL H (H.src j) := L6.outL_mem.mpr rfl
    have hj' : j' ∈ L6.outL H (H.src j) := L6.outL_mem.mpr hsrc.symm
    have hlt' : (L6.outL H (H.src j)).Pairwise (· < ·) :=
      (List.pairwise_lt_finRange H.m).filter _
    have hPR := List.pairwise_iff_getElem.mp ((hs (H.src j)).and hlt')
    obtain ⟨i, hi, hij⟩ := List.getElem_of_mem hj
    obtain ⟨i', hi', hij'⟩ := List.getElem_of_mem hj'
    rcases lt_trichotomy i i' with h | h | h
    · have := (hPR i i' hi hi' h).1 lab
      rw [hij, hij'] at this; exact this
    · subst h
      rw [hij] at hij'
      exact absurd (congrArg Fin.val hij') (by omega)
    · have := (hPR i' i hi' hi h).2
      rw [hij, hij'] at this
      exact absurd this (by rw [Fin.lt_def]; omega)
  · have : j = j' := Fin.ext heq
    subst this; exact le_rfl

end Frontier.CHD.WinScan
