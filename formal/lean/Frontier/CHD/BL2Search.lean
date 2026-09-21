import Frontier.CHD.BL2Extract
import Frontier.CHD.BL2ScanSpec

/-!
# Frontier.CHD.BL2Search — B-L2: the local search loop (FH.5–FH.6) refines Layer A's `Search`
(agent-09, scratch, NON-GATE)

Loop body: if `|K| < k` and the heap is nonempty, extract a minimum-label vertex (`fpExtract`)
and scan its out-list (`fpScan`); result `fp.res` 0/1 continue, 2 = contact, 3 = full.
Result register `fp.sres`: 0 = failed (empty heap), 2 = contact, 3 = success (cap reached).
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

variable (LI : LabI V ops G s) (X : LabX LI)

/-- One round of the local search. -/
def fpSearchBody (slB slX : String) : Stmt :=
  ite (lt (var "fp.kl") (var "fp.k"))
    (ite (var "fp.hsz")
       (seq (fpExtract LI X)
       (seq (fpScan LI slB slX)
            (ite (lt (var "fp.res") (lit 2)) skip
               (seq (wset "fp.sres" (var "fp.res")) (wset "fp.sgo" (lit 0))))))
       (seq (wset "fp.sres" (lit 0)) (wset "fp.sgo" (lit 0))))
    (seq (wset "fp.sres" (lit 3)) (wset "fp.sgo" (lit 0)))

/-- FH.5–FH.6: the local search from the current state. -/
def fpSearch (slB slX : String) : Stmt :=
  seq (wset "fp.sgo" (lit 1)) (Stmt.while (var "fp.sgo") (fpSearchBody LI X slB slX))

/-- Search-level cost factor. -/
def KS : ℕ := Kit LI + X.Ctt + 40

/-- Result code of a finished search. -/
def SResCode (st : State V) (res : SearchRes) : Prop :=
  (res = .failed ∧ st.w "fp.sres" = 0) ∨ (res = .contact ∧ st.w "fp.sres" = 2) ∨
  (res = .success ∧ st.w "fp.sres" = 3)

end Frontier.CHD.BL2

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

variable (LI : LabI V ops G s) (X : LabX LI)

/-- Write sets of the search. -/
def srchWA : List String := scanWA LI
def srchVA : List String := scanVA LI
def srchWR : List String :=
  scanWR LI ++ extRegs ++ [X.ra, X.rb] ++ X.ttWR ++ ["fp.sres", "fp.sgo"]
def srchVR : List String := scanVR LI ++ X.ttVR

variable (c : FPCtx G s) (T : Finset (Fin G.n)) (slB slX : String)

/-- The machine representation of a search state. -/
structure SRep (σ : SSt G s) (g : LI.Gh) (st : State V) : Prop where
  lab : LabRep LI c slB slX σ.d g st
  my : MyRep c T σ st
  out : OutRep st c σ.D

/-- Bookkeeping of the search relative to its start state. -/
structure SBook (st₀ st : State V) (n : ℕ) : Prop where
  unch : Unchanged st₀ st (srchWA LI) (srchVA LI) (srchWR LI X) (srchVR LI X)
  cost0 : st₀.cost ≤ st.cost
  cost : st.cost ≤ st₀.cost + 2 + KS LI X * n

/-- Running search. -/
structure SRun (σ₀ : SSt G s) (g₀ : LI.Gh) (st₀ : State V) (σ : SSt G s) (n : ℕ) (g : LI.Gh)
    (st : State V) : Prop where
  rep : SRep LI c T slB slX σ g st
  inv : SInv c σ
  hist : LI.gext g₀ g
  cont : ∀ σ'' res n', Search c T σ σ'' res n' → Search c T σ₀ σ'' res (n + n')
  book : SBook LI X st₀ st n
  go : st.w "fp.sgo" = 1

/-- Finished search. -/
structure SStop (σ₀ : SSt G s) (g₀ : LI.Gh) (st₀ : State V) (σ' : SSt G s) (res : SearchRes)
    (n : ℕ) (g : LI.Gh) (st : State V) : Prop where
  srch : Search c T σ₀ σ' res n
  rep : SRep LI c T slB slX σ' g st
  inv : SInv c σ'
  code : SResCode st res
  hitc : res = .contact → ∃ a b : Fin G.n, σ'.hit = some (a, b) ∧ st.w "fp.cu" = a ∧
    st.w "fp.cv" = b
  hist : LI.gext g₀ g
  book : SBook LI X st₀ st n
  go : st.w "fp.sgo" = 0

/-- Loop invariant of the search, indexed by the measure. -/
def SLoopI (σ₀ : SSt G s) (g₀ : LI.Gh) (st₀ : State V) (m : ℕ) (st : State V) : Prop :=
  (∃ σ n g, m = G.n - σ.done.card + 1 ∧ SRun LI X c T slB slX σ₀ g₀ st₀ σ n g st) ∨
  (m = 0 ∧ ∃ σ' res n g, SStop LI X c T slB slX σ₀ g₀ st₀ σ' res n g st)

variable {LI X c T slB slX}

/-- Replacing the heap while other registers than `fp.hsz` may change (MyRep's other registers
are untouched). -/
theorem MyRep.setHeap' {st st' : State V} {σ : SSt G s} {H' : Finset (Fin G.n)}
    {wr vr : List String} (hM : MyRep c T σ st) (hH : HeapRep st' c.k H')
    (hu : Unchanged st st' ["fp.H", "fp.hp", "fp.inH"] [] wr vr)
    (hwr : Disj wr ["gM", "fp.kl", "fp.k"])
    (hsub : H' ⊆ σ.K.toFinset) : MyRep c T { σ with H := H' } st' := by
  have A : ∀ a, a ≠ "fp.H" → a ≠ "fp.hp" → a ≠ "fp.inH" →
      st'.wa a = st.wa a ∧ st'.wlen a = st.wlen a := fun a h1 h2 h3 =>
    hu.warr a (by simp [h1, h2, h3])
  have R : ∀ x ∈ ["gM", "fp.kl", "fp.k"], st'.w x = st.w x := fun x hx =>
    hu.wreg x (fun h => hwr x h hx)
  have aH := A "gHead" (by decide) (by decide) (by decide)
  have aK := A "fp.K" (by decide) (by decide) (by decide)
  have ainK := A "fp.inK" (by decide) (by decide) (by decide)
  have aval := A "fp.val" (by decide) (by decide) (by decide)
  have afm := A "fp.fm" (by decide) (by decide) (by decide)
  have akp := A "fp.kp" (by decide) (by decide) (by decide)
  exact ⟨by rw [R "gM" (by simp)]; exact hM.gM, by rw [aH.2]; exact hM.headL,
    fun q => by rw [aH.1]; exact hM.head q, hH,
    by rw [R "fp.kl" (by simp)]; exact hM.kl, by rw [aK.2]; exact hM.kcap,
    fun i hi => by rw [aK.1]; exact hM.karr i hi,
    ⟨by rw [ainK.2]; exact hM.inK.1, fun x => by rw [ainK.1]; exact hM.inK.2 x⟩,
    ⟨by rw [aval.2]; exact hM.val.1, fun x => by rw [aval.1]; exact hM.val.2 x⟩,
    ⟨by rw [afm.2]; exact hM.fm.1, fun x => by rw [afm.1]; exact hM.fm.2 x⟩,
    by rw [akp.2]; exact hM.kpL, fun x hx => by rw [akp.1]; exact hM.kp x hx,
    by rw [R "fp.k" (by simp)]; exact hM.kreg, hM.Knd, hsub⟩

/-- Finish the search with result code `a`. -/
theorem sstop_spec {st : State V} {e : WExpr} {a : ℕ} (he : evalW st e = some a)
    (h0 : 0 < st.cap) :
    Runs ops (seq (wset "fp.sres" e) (wset "fp.sgo" (lit 0))) st (fun st' =>
      st'.w "fp.sres" = a ∧ st'.w "fp.sgo" = 0 ∧
      (∀ x, x ≠ "fp.sres" → x ≠ "fp.sgo" → st'.w x = st.w x) ∧
      Unchanged st st' [] [] ["fp.sres", "fp.sgo"] [] ∧ st'.cost = st.cost + 2) := by
  refine runs_seq (runs_wset he (runs_wset (a := 0) (evalW_lit_of (by simpa using h0)) ?_))
  refine ⟨by simp, by simp, fun x h1 h2 => by simp [h1, h2], ?_, by simp⟩
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun x hx => ?_, fun _ _ => rfl, rfl, rfl⟩
  simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hx
  simp [hx.1, hx.2]

/-- Representation frame for register-only updates outside every footprint. -/
theorem SRep.frame_regs (hN : Names LI slB slX) {σ : SSt G s} {g : LI.Gh} {st st' : State V}
    {wr : List String} (h : SRep LI c T slB slX σ g st) (hu : Unchanged st st' [] [] wr [])
    (hmy : Disj wr myRepRegs) (hB : Disj wr (LI.slWR slB)) (hX : Disj wr (LI.slWR slX))
    (hc : st.cost ≤ st'.cost) : SRep LI c T slB slX σ g st' :=
  ⟨h.lab.frame hu (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) hB
    (Disj.nil_left _) (Disj.nil_left _) (Disj.nil_left _) hX (Disj.nil_left _) hc,
   h.my.frameR hu (Disj.nil_left _) hmy, h.out.frameR hu (Disj.nil_left _)⟩

end Frontier.CHD.BL2
