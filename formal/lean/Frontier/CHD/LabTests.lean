import Frontier.CHD.CmpTTI
import Frontier.CHD.RamT6
import Frontier.CHD.WinScanB

/-!
# LabTests — B-LAB vertex tests for BM.25 / BM.26 as agent-01's `RamInit.TestI` (agent-02, NON-GATE)

* `tstWp Kl klf`: `t6.b := [d px < B'f]` (the `W'` test of BM.26; `B'f` in block `Kl`);
* `tstT6 Kl klf Kb kbf`: `t6.b := [B'f ≤ d px ∧ d px < B]` (the `T6` test of BM.25), computed as
  `lo := [d px < B'f]; hi := [d px < B]; t6.b := [lo < hi]` (two `headLtB`).

Both read the label table only (no clock), write the scratch registers `tstW`/`t6.yl`, and are
turned into `TestI` instances for any representation `DR` that projects to the label table and
the bound blocks and survives those register writes (`tstWp_testI`, `tstT6_testI`).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.WinScan

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.LabTab Frontier.CHD.MLab
  WExpr Stmt

variable {G : Graph} {s : Fin G.n}

/-- The scratch label block of the tests. -/
def t6Y : LReg := ⟨"t6.yl", "t6.yh", "t6.yv", "t6.ye", "t6.yr"⟩

/-- Word registers written by the tests. -/
def tstW : List String :=
  ["t6.yf", "t6.yh", "t6.yv", "t6.ye", "t6.yr", "t6.c1", "t6.c2", "t6.b", "t6.lo", "t6.hi"]

/-- `t6.b := [d px < B'f]`. -/
def tstWp (Kl : LReg) (klf : String) : Stmt :=
  headLtB "px" t6Y Kl "t6.yf" klf "t6.c1" "t6.c2" "t6.b"

/-- `t6.b := [B'f ≤ d px ∧ d px < B]`. -/
def tstT6 (Kl : LReg) (klf : String) (Kb : LReg) (kbf : String) : Stmt :=
  seq (headLtB "px" t6Y Kl "t6.yf" klf "t6.c1" "t6.c2" "t6.lo")
  (seq (headLtB "px" t6Y Kb "t6.yf" kbf "t6.c1" "t6.c2" "t6.hi")
       (wset "t6.b" (lt (var "t6.lo") (var "t6.hi"))))

/-- Register hygiene of a bound block used by the tests. -/
structure TstHyg (K : LReg) (kf : String) : Prop where
  w : ∀ a ∈ K.ws ++ [kf], a ∉ tstW ++ ["px"]
  l : K.l ≠ "t6.yl"

theorem TstHyg.cmpFresh {K : LReg} {kf : String} (h : TstHyg K kf) :
    CmpFresh t6Y K "t6.c1" "t6.c2" :=
  ⟨by decide, by decide, by decide, fun hm => h.w "t6.c1" (by simp [hm]) (by decide),
    fun hm => h.w "t6.c2" (by simp [hm]) (by decide)⟩

/-- The scratch registers of one head test (besides its output bit). -/
def t6S : List String := ["t6.yf", "t6.yh", "t6.yv", "t6.ye", "t6.yr", "t6.c1", "t6.c2"]

open Classical in
/-- One head test through `Runs`, with the lower cost bound. -/
theorem headLtB_t6 {K : LReg} {kf out : String} (hK : TstHyg K kf)
    (st : State ℝ≥0) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ)
    (hL : LabAt st d H c0) (v : Fin G.n) (hv : st.w "px" = v) (Bl : WLab G s)
    (hKh : WHolds st K kf H (vc st) Bl) (hcap : 1 < st.cap) :
    Runs realOps (headLtB "px" t6Y K "t6.yf" kf "t6.c1" "t6.c2" out) st (fun r =>
      r.w out = (if d v < Bl then 1 else 0) ∧ Unchanged st r [] [] (t6S ++ [out]) ["t6.yl"] ∧
      st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 22) := by
  have hwp := headLtB_wp "px" t6Y K "t6.yf" kf "t6.c1" "t6.c2" out ⟨by decide, by decide⟩
    hK.cmpFresh (fun a ha hm => hK.w a (by simp [ha]) (by
      simp only [t6Y, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at hm
      simp only [tstW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto))
    (fun hm => hK.l (by simpa [t6Y] using hm)) (fun hm => hK.w kf (by simp) (by
      simp only [t6Y, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at hm
      simp only [tstW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; tauto))
    st d H c0 hL v hv Bl hKh hcap
  refine (Frontier.CHD.LabIInst.Runs.cost_ge (wp_sound (ops := realOps) _ _ _ hwp)).mono ?_
  rintro r ⟨⟨h1, h2, h3⟩, h4⟩
  refine ⟨h1, h2.mono (by simp) (by simp) ?_ (by simp [t6Y]), h4, h3⟩
  intro a ha
  simp only [t6Y, t6S, LReg.ws, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
  tauto

open Classical in
/-- **The `W'` test** `t6.b := [d px < B'f]`. -/
theorem tstWp_spec {Kl : LReg} {klf : String} (hK : TstHyg Kl klf) (st : State ℝ≥0)
    (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m)) (c0 : ℕ) (hL : LabAt st d H c0)
    (v : Fin G.n) (hv : st.w "px" = v) (Bf : WLab G s) (hKh : WHolds st Kl klf H (vc st) Bf)
    (hcap : 1 < st.cap) :
    Runs realOps (tstWp Kl klf) st (fun r => r.w "t6.b" = (if d v < Bf then 1 else 0) ∧
      Unchanged st r [] [] tstW ["t6.yl"] ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 22) :=
  (headLtB_t6 hK st d H c0 hL v hv Bf hKh hcap).mono fun _ ⟨h1, h2, h3, h4⟩ =>
    ⟨h1, h2.mono (by simp) (by simp) (by decide) (by simp), h3, h4⟩

open Classical in
/-- **The `T6` test** `t6.b := [B'f ≤ d px ∧ d px < B]`. -/
theorem tstT6_spec {Kl : LReg} {klf : String} {Kb : LReg} {kbf : String} (hKl : TstHyg Kl klf)
    (hKb : TstHyg Kb kbf) (st : State ℝ≥0) (d : Labels G s) (H : Fin G.n → ℕ → List (Fin G.m))
    (c0 : ℕ) (hL : LabAt st d H c0) (v : Fin G.n) (hv : st.w "px" = v) (Bf B : WLab G s)
    (hKlh : WHolds st Kl klf H (vc st) Bf) (hKbh : WHolds st Kb kbf H (vc st) B)
    (hcap : 1 < st.cap) :
    Runs realOps (tstT6 Kl klf Kb kbf) st (fun r =>
      r.w "t6.b" = (if Bf ≤ d v ∧ d v < B then 1 else 0) ∧
      Unchanged st r [] [] tstW ["t6.yl"] ∧ st.cost ≤ r.cost ∧ r.cost ≤ st.cost + 45) := by
  apply runs_seq
  refine (headLtB_t6 (out := "t6.lo") hKl st d H c0 hL v hv Bf hKlh hcap).mono ?_
  rintro r1 ⟨hlo, hU1, hc1a, hc1b⟩
  have hKw : ∀ a ∈ Kb.ws, a ∉ t6S ++ ["t6.lo"] := fun a ha hm => hKb.w a (by simp [ha])
    (by simp only [t6S, tstW, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hm ⊢; tauto)
  have hKf : kbf ∉ t6S ++ ["t6.lo"] := fun hm => hKb.w kbf (by simp)
    (by simp only [t6S, tstW, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hm ⊢; tauto)
  have hvc1 : vc (G := G) r1 = vc st := vc_of_unchanged hU1 (by simp)
  apply runs_seq
  refine (headLtB_t6 (out := "t6.hi") hKb r1 d H c0 (hL.of_unchanged hU1 (by simp) (by simp) hc1a)
    v (by rw [hU1.wreg "px" (by decide)]; exact hv) B
    (by rw [hvc1]; exact hKbh.of_unchanged hU1 hKw (by simpa using hKb.l) hKf)
    (by rw [hU1.cap]; exact hcap)).mono ?_
  rintro r2 ⟨hhi, hU2, hc2a, hc2b⟩
  have hlo2 : r2.w "t6.lo" = (if d v < Bf then 1 else 0) := by
    rw [hU2.wreg "t6.lo" (by decide)]; exact hlo
  have hcap2 : 1 < r2.cap := by rw [hU2.cap, hU1.cap]; exact hcap
  refine runs_wset_val (evalW_lt_of (x := if d v < Bf then 1 else 0)
    (y := if d v < B then 1 else 0) (by rw [evalW_var, hlo2]) (by rw [evalW_var, hhi]) hcap2)
    (fun r3 hb3 hU3 hc3 => ?_)
  refine ⟨?_, ((hU1.comp hU2).comp hU3).mono (by simp) (by simp) (by decide) (by simp),
    by omega, by omega⟩
  rw [hb3]
  by_cases h1 : d v < Bf
  · have h1' : ¬ Bf ≤ d v := not_le.mpr h1
    by_cases h2 : d v < B <;> simp [h1, h1', h2]
  · have h1' : Bf ≤ d v := not_lt.mp h1
    by_cases h2 : d v < B <;> simp [h1, h1', h2]

open Classical in
/-- **`tstWp` as `RamInit.TestI`**, for any representation `DR` that projects to the label table
and the `B'f` block and survives the tests' register writes. -/
theorem tstWp_testI {DR : State ℝ≥0 → BM.DGl G s → BM.DStrM G s → Prop} (d : Labels G s)
    (c0 : ℕ) {Kl : LReg} {klf : String} (hK : TstHyg Kl klf) (Bf : WLab G s)
    (hproj : ∀ st g D, DR st g D → ∃ H : Fin G.n → ℕ → List (Fin G.m),
      LabAt st d H c0 ∧ WHolds st Kl klf H (vc st) Bf ∧ 1 < st.cap)
    (hfr : ∀ st r g D, DR st g D → Unchanged st r [] [] tstW ["t6.yl"] → st.cost ≤ r.cost →
      DR r g D) :
    RamInit.TestI realOps (tstWp Kl klf) DR (fun x => labKey d x < Bf) 22 tstW ["t6.yl"] where
  run := fun st g D hD hpx => by
    obtain ⟨H, hL, hKh, hcap⟩ := hproj st g D hD
    refine (tstWp_spec hK st d H c0 hL ⟨st.w "px", hpx⟩ rfl Bf hKh hcap).mono ?_
    rintro r ⟨h1, h2, h3, h4⟩
    refine ⟨?_, h2, h3, h4, hfr st r g D hD h2 h3⟩
    rw [h1]; simp only [labKey, dif_pos hpx]
  regs := by decide
  bit := by decide

open Classical in
/-- **`tstT6` as `RamInit.TestI`**. -/
theorem tstT6_testI {DR : State ℝ≥0 → BM.DGl G s → BM.DStrM G s → Prop} (d : Labels G s)
    (c0 : ℕ) {Kl : LReg} {klf : String} {Kb : LReg} {kbf : String} (hKl : TstHyg Kl klf)
    (hKb : TstHyg Kb kbf) (Bf B : WLab G s)
    (hproj : ∀ st g D, DR st g D → ∃ H : Fin G.n → ℕ → List (Fin G.m),
      LabAt st d H c0 ∧ WHolds st Kl klf H (vc st) Bf ∧ WHolds st Kb kbf H (vc st) B ∧
      1 < st.cap)
    (hfr : ∀ st r g D, DR st g D → Unchanged st r [] [] tstW ["t6.yl"] → st.cost ≤ r.cost →
      DR r g D) :
    RamInit.TestI realOps (tstT6 Kl klf Kb kbf) DR (fun x => Bf ≤ labKey d x ∧ labKey d x < B) 45
      tstW ["t6.yl"] where
  run := fun st g D hD hpx => by
    obtain ⟨H, hL, hKlh, hKbh, hcap⟩ := hproj st g D hD
    refine (tstT6_spec hKl hKb st d H c0 hL ⟨st.w "px", hpx⟩ rfl Bf B hKlh hKbh hcap).mono ?_
    rintro r ⟨h1, h2, h3, h4⟩
    refine ⟨?_, h2, h3, h4, hfr st r g D hD h2 h3⟩
    rw [h1]; simp only [labKey, dif_pos hpx]
  regs := by decide
  bit := by decide

end Frontier.CHD.WinScan
