import Frontier.CHD.BL2Search

/-!
# Frontier.CHD.BL2SearchStep — B-L2: one round of the local search refines one `Search` step
(agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {LI : LabI V ops G s} {X : LabX LI} {c : FPCtx G s} {T : Finset (Fin G.n)}
  {slB slX : String}

theorem SBook.step {st₀ st st' : State V} {n k : ℕ} {wa va wr vr : List String}
    (hB : SBook LI X st₀ st n) (hu : Unchanged st st' wa va wr vr)
    (hwa : wa ⊆ srchWA LI) (hva : va ⊆ srchVA LI) (hwr : wr ⊆ srchWR LI X)
    (hvr : vr ⊆ srchVR LI X) (hc0 : st.cost ≤ st'.cost) (hc : st'.cost ≤ st.cost + KS LI X * k) :
    SBook LI X st₀ st' (n + k) := by
  refine ⟨hB.unch.trans (hu.mono hwa hva hwr hvr), hB.cost0.trans hc0, ?_⟩
  have := hB.cost
  have : KS LI X * (n + k) = KS LI X * n + KS LI X * k := Nat.mul_add _ _ _
  omega

theorem scanWR_sub_srch : scanWR LI ⊆ srchWR LI X := by
  intro x hx; simp only [srchWR, List.mem_append]; tauto
theorem scanVR_sub_srch : scanVR LI ⊆ srchVR LI X := by
  intro x hx; simp only [srchVR, List.mem_append]; tauto
theorem extW_sub_srch : extRegs ++ [X.ra, X.rb] ++ X.ttWR ⊆ srchWR LI X := by
  intro x hx; simp only [srchWR, List.mem_append] at hx ⊢; tauto
theorem ttV_sub_srch : X.ttVR ⊆ srchVR LI X := by
  intro x hx; simp only [srchVR, List.mem_append]; tauto
theorem sg_sub_srch : ["fp.sres", "fp.sgo"] ⊆ srchWR LI X := by
  intro x hx; simp only [srchWR, List.mem_append]; tauto

end Frontier.CHD.BL2
