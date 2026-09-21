import Frontier.CHD.BL2FPB
import Frontier.CHD.BL2Pro
import Frontier.CHD.L6.ProFinal

/-!
# Frontier.CHD.BL2Hook — B-L2's allocation hook of the spine prologue (owner agent-09, NON-GATE)

`fpHook`: agent-10's `L6.HookSpec` for `fpAlloc`, with post `(phiI …).PhiR r ∅` (B-L2's persistent
state with no deleted edge), footprint `fpAllocWA / [] / fpAllocWR / []`, cost `≤ 68 (Tnat + 1)`.
The two array-length facts `hHdL` / `hNxL` (L6's `gHd` / `gNxt` hold `n` / `m` cells) are not yet
exported by `CoreIn`; they are stated as conditions on hook states (see the board).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BL2Inst

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.BL2 Frontier.CHD.L6

theorem lgN_le_self' {n : ℕ} (hn : 1 ≤ n) : CostSkeleton.lgN n ≤ n := by
  unfold CostSkeleton.lgN
  have h2 : Nat.log 2 n ≤ n := by
    have h3 := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    have h4 : Nat.log 2 n < 2 ^ Nat.log 2 n := Nat.lt_two_pow_self
    omega
  exact max_le hn h2

set_option maxRecDepth 20000 in
/-- **B-L2's allocation hook** (`L6.HookSpec`): `fpAlloc` establishes `PhiR ∅` (the clean state
and the word capacity FindPivots needs at every level) for every reduced graph, source and size. -/
theorem fpHook (e : ℕ) (ps : List Stmt) (he : 3 ≤ e) (hins hext : ℕ)
    (hHdL : ∀ (H : Graph) (src : Fin H.n) (cn cm c0 : ℕ) (st : State ℝ≥0),
      HookIn e ps H src cn cm c0 st → H.n ≤ st.wlen "gHd")
    (hNxL : ∀ (H : Graph) (src : Fin H.n) (cn cm c0 : ℕ) (st : State ℝ≥0),
      HookIn e ps H src cn cm c0 st → H.m ≤ st.wlen "gNxt") :
    HookSpec e ps fpAlloc
      (fun H src cn cm r =>
        (phiI H src (CostSkeleton.kF cn cm) hins hext (CostSkeleton.LF cn cm)).PhiR r ∅)
      fpAllocWA [] fpAllocWR [] 68 := by
  refine ⟨by decide, fun _ h => absurd h List.not_mem_nil, by decide, ?_⟩
  intro H src cn cm c0 st hIn
  have hC := hIn.pre.core
  have hn := hC.sizeN
  have hc1 := hC.cn_pos
  have hm1 := hC.cm_pos
  have hlg := lgN_le_self' hc1
  have hLF : CostSkeleton.LF cn cm ≤ cn + 1 := by
    unfold CostSkeleton.LF
    have := Nat.div_le_self (CostSkeleton.lgN cn) (CostSkeleton.tF cn cm); omega
  have hkF : CostSkeleton.kF cn cm ≤ 16 + cn := by
    have := CostSkeleton.kF_le_tF cn cm; have := CostSkeleton.tF_le cn cm; omega
  have hb : (cn + 3) ^ 4 ≤ st.cap :=
    le_trans (le_trans (Nat.pow_le_pow_left (by omega : cn + 3 ≤ cn + cm + 2) 4)
      (Nat.pow_le_pow_right (by omega) (by omega : 4 ≤ e + 1))) hC.cap
  have hpoly : (2 * CostSkeleton.LF cn cm + 5) * H.n + 4 * CostSkeleton.LF cn cm +
      2 * CostSkeleton.kF cn cm + 8 < (cn + 3) ^ 4 := by
    have hm : (2 * CostSkeleton.LF cn cm + 5) * H.n ≤ (2 * (cn + 1) + 5) * (2 * cn) :=
      Nat.mul_le_mul (by omega) hn
    have h4 : 4 * cn ^ 2 + 20 * cn + 44 < (cn + 3) ^ 4 := by
      have : (cn + 3) ^ 4 = cn ^ 4 + 12 * cn ^ 3 + 54 * cn ^ 2 + 108 * cn + 81 := by ring
      rw [this]; nlinarith [Nat.zero_le (cn ^ 3), Nat.zero_le (cn ^ 4)]
    have h5 : (2 * (cn + 1) + 5) * (2 * cn) = 4 * cn ^ 2 + 14 * cn := by ring
    omega
  have hcap : 2 * H.n + 2 < st.cap := by
    have : 2 * H.n + 2 ≤ (2 * CostSkeleton.LF cn cm + 5) * H.n + 8 := by nlinarith
    omega
  refine (fpAlloc_phiR (s := src) (hins := hins) (hext := hext) hC.gN hIn.pre.k hC.gM hC.graph
    hC.csr (hHdL H src cn cm c0 st hIn) (hNxL H src cn cm c0 st hIn) hC.hd hC.nxt hcap).mono ?_
  rintro r ⟨hphi, hu, hc⟩
  refine ⟨⟨hphi, by rw [hu.cap]; omega⟩, hu, by omega, ?_⟩
  -- cost: 34 n + 2 k + 41 ≤ 68 (Tnat + 1)
  have hk : CostSkeleton.kF cn cm ≤ CostSkeleton.tF cn cm := CostSkeleton.kF_le_tF cn cm
  have hT : cn + CostSkeleton.tF cn cm ≤ CostSkeleton.Tnat cn cm := by
    unfold CostSkeleton.Tnat
    have : CostSkeleton.tF cn cm ≤ cm * (CostSkeleton.tF cn cm +
        Nat.log 2 (CostSkeleton.dd cn cm + 1) + 3) := by nlinarith
    omega
  rw [hc]; nlinarith

/-- agent-10's `hPb` for B-L2's `PhiI`: the persistent state avoids the slots, the `S` row and
the registers of `blowProg`. -/
theorem phiI_hPb (H : Graph) (src : Fin H.n) (k hins hext LF : ℕ) :
    (∀ a ∈ (phiI H src k hins hext LF).pWA, a ∉ slotW ++ ["S", "S.len"]) ∧
      (∀ a ∈ (phiI H src k hins hext LF).pWR, a ∉ L6.blowWR ++ ["lvl"]) := by
  show (∀ a ∈ phWA, a ∉ slotW ++ ["S", "S.len"]) ∧ (∀ a ∈ phWR, a ∉ L6.blowWR ++ ["lvl"])
  decide

end Frontier.CHD.BL2Inst
