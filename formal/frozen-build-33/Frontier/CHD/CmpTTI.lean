import Frontier.CHD.IHeapLab
import Frontier.CHD.RamInit

/-!
# CmpTTI — the B-LAB table–table comparison as agent-01's `RamInit.CmpI` (agent-02, NON-GATE)

`cmpLab "tt.ra" "tt.rb" "lab.bit"` (agent-06's `IHeapLab.cmpLab`, B-LAB `loadLab` + `cmp`)
computes `lab.bit := [d tt.ra < d tt.rb]` on the label table.  For every label table `d` in
`LabAt` form at `r0` it is an instance of `RamInit.CmpI` with keys `labKey d`, domain `labDom d`,
`C = 27`, budget `c0 + r0.cap`, write sets `"lab.bit" :: cmpScratchW` / `lessV`, and the key
representation `cmpKR d c0 r0.cap` (the label table represents `d`, same cap); `cmpKR` survives
every footprint that avoids the label arrays (`cmpKR.frame`), in particular the D layer's.
This is the compare needed by pivProg (BM.7) and reselect (BM.23).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.LabTab Frontier.CHD.MLab
  Frontier.CHD.IHeapLab

variable {G : Graph} {s : Fin G.n}

/-- The comparison keys: the label of `x` (`⊤` off the vertex range). -/
noncomputable def labKey (d : Labels G s) (x : ℕ) : WLab G s :=
  if h : x < G.n then d ⟨x, h⟩ else ⊤

/-- The vertices with a finite label. -/
def labDom (d : Labels G s) (x : ℕ) : Prop := ∃ h : x < G.n, d ⟨x, h⟩ ≠ ⊤

/-- The key representation: the label table represents `d` (some history), with the cap. -/
def cmpKR (d : Labels G s) (c0 cap : ℕ) (st : State ℝ≥0) : Prop :=
  (∃ H : Fin G.n → ℕ → List (Fin G.m), LabAt st d H c0) ∧ st.cap = cap

/-- `cmpKR` survives every footprint that avoids the label arrays. -/
theorem cmpKR.frame {d : Labels G s} {c0 cap : ℕ} {st r : State ℝ≥0}
    {wa va wr vr : List String} (h : cmpKR d c0 cap st) (hu : Unchanged st r wa va wr vr)
    (hw : ∀ a ∈ labW, a ∉ wa) (hv : "dlen" ∉ va) (hc : st.cost ≤ r.cost) : cmpKR d c0 cap r :=
  ⟨⟨h.1.choose, h.1.choose_spec.of_unchanged hu hw hv hc⟩, hu.cap.trans h.2⟩

open Classical in
/-- **The B-LAB compare as `RamInit.CmpI`.** -/
theorem cmpTT_cmpI (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ)
    (r0 : State ℝ≥0) (_hL : LabAt r0 d H c0) :
    RamInit.CmpI realOps (cmpLab ttRa ttRb "lab.bit") (cmpKR d c0 r0.cap) (labKey d) (labDom d)
      27 (c0 + r0.cap) ("lab.bit" :: cmpScratchW) lessV []
      (RamInit.gmRegs ++ ("lab.bit" :: cmpScratchW)) where
  run := fun st hK ha hb hB => by
    obtain ⟨⟨H', hL⟩, hcap⟩ := hK
    obtain ⟨ha', hda⟩ := ha
    obtain ⟨hb', hdb⟩ := hb
    have hcap1 : 1 < st.cap :=
      one_lt_cap_of_labAt hL ⟨st.w "tt.ra", ha'⟩ (by rw [hcap]; omega)
    refine (cmpLab_spec cmpRegs_tt d H' c0 hL hcap1 ⟨st.w "tt.ra", ha'⟩ ⟨st.w "tt.rb", hb'⟩
      rfl rfl).mono ?_
    rintro r ⟨hbit, hU, hc1, hc2, hLr⟩
    refine ⟨?_, hU, by omega, hc2, ⟨H', hLr⟩, hU.cap.trans hcap⟩
    rw [hbit]
    simp only [labKey, dif_pos ha', dif_pos hb']
  frame := fun st r hK hU hc => hK.frame hU (by simp) (by simp) hc
  bit_mem := by simp
  regs := by decide

end Frontier.CHD.WinScan
