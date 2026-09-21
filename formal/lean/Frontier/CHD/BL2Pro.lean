import Frontier.CHD.BL2Phi
import Frontier.CHD.RamBaseCase

/-!
# Frontier.CHD.BL2Pro — B-L2's part of the spine prologue (owner agent-09, NON-GATE)

`fpAlloc_phiR`: on the core's entry state (L6's CSR live lists, graph heads, `gN`, `gM`, `cp.k`),
`fpAlloc` establishes B-L2's persistent state `phiR … ∅` (no deleted edge) for agent-10's ProSpec.
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.RamBaseCase

variable {G : Graph} {s : Fin G.n}

/-- **B-L2's prologue**: `fpAlloc` establishes the persistent FindPivots state with no deleted
edge, from the facts L6 hands to the core. -/
theorem fpAlloc_phiR {st : State ℝ≥0} {k hins hext : ℕ} (hN : st.w "gN" = G.n)
    (hk : st.w "cp.k" = k) (hgM : st.w "gM" = G.m) (hgr : GraphAt st G) (hcsr : CSRAt st G)
    (hHdL : G.n ≤ st.wlen "gHd") (hNxL : G.m ≤ st.wlen "gNxt")
    (hd : ∀ x : Fin G.n,
      st.wa "gHd" x = if st.wa "gSt" x = st.wa "gSt" (x + 1) then G.m else st.wa "gSt" x)
    (hnxt : ∀ (x : Fin G.n) (p : ℕ), st.wa "gSt" x ≤ p → p < st.wa "gSt" (x + 1) →
      st.wa "gNxt" p = if p + 1 = st.wa "gSt" (x + 1) then G.m else p + 1)
    (hcap : 2 * G.n + 2 < st.cap) :
    Runs realOps fpAlloc st (fun st' => phiR G s k hins hext st' ∅ ∧
      Unchanged st st' fpAllocWA [] fpAllocWR [] ∧ st'.cost = st.cost + 34 * G.n + 2 * k + 41) := by
  have hHL : G.m ≤ st.wlen "gHead" := by simpa using hgr.head.1
  have hH : ∀ q : Fin G.m, st.wa "gHead" q = G.dst q := fun q => by simpa using hgr.head.2 q q.2
  refine (fpAlloc_spec (ops := realOps) (s := s) hN hk hgM hHL hH hcap).mono ?_
  rintro st' ⟨hC, hu, hc⟩
  have hO : OutRep st (pinCtx (G := G) (s := s) (L6.outL G) k hins hext ⊤ ⊤) ∅ :=
    outRep_init hHdL hNxL hcsr.le hcsr.le_m hcsr.src hd hnxt (fun u => rfl)
  exact ⟨(hC _ (fun _ => ⊤) rfl hO).toNH, hu, hc⟩

end Frontier.CHD.BL2
