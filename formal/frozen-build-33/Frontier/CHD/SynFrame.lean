import Frontier.RAMLogic
import Frontier.RAMRep
import Frontier.CHD.L6.Util

/-!
# Syntactic frames for arbitrary RAM programs with procedures (agent-10)

`sWA c` / `sVA c` / `sWR c` / `sVR c` are the word arrays, value arrays, word registers and value
registers that the TEXT of `c` may write (stores, allocations, assignments).  `exec_frame`: every
terminating run of `c` from a state whose procedure table is `ps` changes nothing outside the
footprint of `c` plus the footprints of ALL procedure bodies of `ps` (calls may reach any of them),
and never changes `cap` or the procedure table.  `Runs.frame` attaches this `Unchanged` to any
`Runs` postcondition.  So an array or register that no statement of the program mentions as a
write target is preserved by construction (e.g. L6's `gKeep`/`gRep` and `coreTop`'s saved `core.*`
registers across the whole spine).
NON-GATE (Layer B tooling).
-/

namespace Frontier.RAM

open Stmt

variable {V : Type} {ops : VOps V}

/-- Word arrays the text may write. -/
def sWA : Stmt → List String
  | .wstore a _ _ => [a]
  | .walloc a _ => [a]
  | .seq a b => sWA a ++ sWA b
  | .ite _ a b => sWA a ++ sWA b
  | .while _ b => sWA b
  | _ => []

/-- Value arrays the text may write. -/
def sVA : Stmt → List String
  | .vstore a _ _ => [a]
  | .valloc a _ => [a]
  | .seq a b => sVA a ++ sVA b
  | .ite _ a b => sVA a ++ sVA b
  | .while _ b => sVA b
  | _ => []

/-- Word registers the text may write. -/
def sWR : Stmt → List String
  | .wset x _ => [x]
  | .vle x _ _ => [x]
  | .seq a b => sWR a ++ sWR b
  | .ite _ a b => sWR a ++ sWR b
  | .while _ b => sWR b
  | _ => []

/-- Value registers the text may write. -/
def sVR : Stmt → List String
  | .vset x _ => [x]
  | .seq a b => sVR a ++ sVR b
  | .ite _ a b => sVR a ++ sVR b
  | .while _ b => sVR b
  | _ => []

/-- The footprint of a statement under a procedure table. -/
def fWA (ps : List Stmt) (c : Stmt) : List String := sWA c ++ ps.flatMap sWA
def fVA (ps : List Stmt) (c : Stmt) : List String := sVA c ++ ps.flatMap sVA
def fWR (ps : List Stmt) (c : Stmt) : List String := sWR c ++ ps.flatMap sWR
def fVR (ps : List Stmt) (c : Stmt) : List String := sVR c ++ ps.flatMap sVR

theorem sub_flat {f : Stmt → List String} {ps : List Stmt} {b : Stmt} (hb : b ∈ ps) :
    f b ⊆ ps.flatMap f := by
  intro x hx
  exact List.mem_flatMap.mpr ⟨b, hb, hx⟩

/-- **The syntactic frame of a terminating run.** -/
theorem exec_frame (ps : List Stmt) : ∀ (f : ℕ) (c : Stmt) (s r : State V), s.procs = ps →
    exec ops f c s = some r →
    Unchanged s r (fWA ps c) (fVA ps c) (fWR ps c) (fVR ps c) := by
  intro f
  induction f with
  | zero => intro c s r _ h; simp [exec] at h
  | succ f ih =>
    intro c s r hps h
    cases c with
    | skip =>
      simp only [exec, Option.some.injEq] at h
      subst h; exact Unchanged.charge s 1 _ _ _ _
    | wset x e =>
      simp only [exec] at h
      cases he : evalW s e with
      | none => simp [he] at h
      | some a =>
        simp [he] at h
        subst h
        rw [unchanged_charge_iff, unchanged_setW_iff (by simp [fWR, sWR])]
        exact Unchanged.refl _ _ _ _ _
    | vset x e =>
      simp only [exec] at h
      cases he : evalV ops s e with
      | none => simp [he] at h
      | some a =>
        simp [he] at h
        subst h
        rw [unchanged_charge_iff, unchanged_setV_iff (by simp [fVR, sVR])]
        exact Unchanged.refl _ _ _ _ _
    | vle x a b =>
      simp only [exec] at h
      cases ha : evalV ops s a with
      | none => simp [ha] at h
      | some p =>
        cases hb : evalV ops s b with
        | none => simp [ha, hb] at h
        | some q =>
          cases hf : fit s.cap (if ops.le p q then 1 else 0) with
          | none => simp [ha, hb, hf] at h
          | some bit =>
            simp [ha, hb, hf] at h
            subst h
            rw [unchanged_charge_iff, unchanged_setW_iff (by simp [fWR, sWR])]
            exact Unchanged.refl _ _ _ _ _
    | wstore arr i e =>
      simp only [exec] at h
      cases hi : evalW s i with
      | none => simp [hi] at h
      | some j =>
        cases he : evalW s e with
        | none => simp [hi, he] at h
        | some a =>
          simp [hi, he] at h
          obtain ⟨-, h⟩ := h
          subst h
          rw [unchanged_charge_iff, unchanged_storeW_iff (by simp [fWA, sWA])]
          exact Unchanged.refl _ _ _ _ _
    | vstore arr i e =>
      simp only [exec] at h
      cases hi : evalW s i with
      | none => simp [hi] at h
      | some j =>
        cases he : evalV ops s e with
        | none => simp [hi, he] at h
        | some a =>
          simp [hi, he] at h
          obtain ⟨-, h⟩ := h
          subst h
          rw [unchanged_charge_iff, unchanged_storeV_iff (by simp [fVA, sVA])]
          exact Unchanged.refl _ _ _ _ _
    | walloc arr e =>
      simp only [exec] at h
      cases he : evalW s e with
      | none => simp [he] at h
      | some k =>
        simp [he] at h
        subst h
        rw [unchanged_charge_iff, unchanged_allocW_iff (by simp [fWA, sWA])]
        exact Unchanged.refl _ _ _ _ _
    | valloc arr e =>
      simp only [exec] at h
      cases he : evalW s e with
      | none => simp [he] at h
      | some k =>
        simp [he] at h
        subst h
        rw [unchanged_charge_iff, unchanged_allocV_iff (by simp [fVA, sVA])]
        exact Unchanged.refl _ _ _ _ _
    | seq a b =>
      simp only [exec] at h
      cases h1 : exec ops f a s with
      | none => simp [h1] at h
      | some s' =>
        simp only [h1, Option.bind_some] at h
        have hA := ih a s s' hps h1
        have hps' : s'.procs = ps := by rw [hA.procs, hps]
        have hB := ih b s' r hps' h
        refine (hA.mono ?_ ?_ ?_ ?_).trans (hB.mono ?_ ?_ ?_ ?_) <;>
          intro x hx <;> simp only [fWA, fVA, fWR, fVR, sWA, sVA, sWR, sVR, List.mem_append] at hx ⊢ <;>
          tauto
    | ite c a b =>
      simp only [exec] at h
      cases hc : evalW s c with
      | none => simp [hc] at h
      | some x =>
        have h0 : Unchanged s (s.charge 1) (fWA ps (.ite c a b)) (fVA ps (.ite c a b))
            (fWR ps (.ite c a b)) (fVR ps (.ite c a b)) := Unchanged.charge s 1 _ _ _ _
        have hps' : (s.charge 1).procs = ps := by simp [hps]
        by_cases hx : x = 0
        · simp [hc, hx] at h
          have hB := ih b (s.charge 1) r hps' h
          refine h0.trans (hB.mono ?_ ?_ ?_ ?_) <;>
            intro y hy <;> simp only [fWA, fVA, fWR, fVR, sWA, sVA, sWR, sVR, List.mem_append] at hy ⊢ <;>
            tauto
        · simp [hc, hx] at h
          have hA := ih a (s.charge 1) r hps' h
          refine h0.trans (hA.mono ?_ ?_ ?_ ?_) <;>
            intro y hy <;> simp only [fWA, fVA, fWR, fVR, sWA, sVA, sWR, sVR, List.mem_append] at hy ⊢ <;>
            tauto
    | «while» c b =>
      simp only [exec] at h
      cases hc : evalW s c with
      | none => simp [hc] at h
      | some x =>
        by_cases hx : x = 0
        · simp [hc, hx] at h
          subst h; exact Unchanged.charge s 1 _ _ _ _
        · cases h1 : exec ops f b (s.charge 1) with
          | none => simp [hc, hx, h1] at h
          | some s' =>
            have h' : exec ops f (.while c b) s' = some r := by simpa [hc, hx, h1] using h
            have hps' : (s.charge 1).procs = ps := by simp [hps]
            have hB := ih b (s.charge 1) s' hps' h1
            have hps'' : s'.procs = ps := by rw [hB.procs, hps']
            have hW := ih (.while c b) s' r hps'' h'
            have h0 : Unchanged s (s.charge 1) (fWA ps (.while c b)) (fVA ps (.while c b))
                (fWR ps (.while c b)) (fVR ps (.while c b)) := Unchanged.charge s 1 _ _ _ _
            refine (h0.trans (hB.mono ?_ ?_ ?_ ?_)).trans hW <;>
              intro y hy <;> simp only [fWA, fVA, fWR, fVR, sWA, sVA, sWR, sVR, List.mem_append] at hy ⊢ <;>
              tauto
    | call p =>
      simp only [exec] at h
      cases hp : s.procs[p]? with
      | none => simp [hp] at h
      | some body =>
        simp only [hp] at h
        have hbody : body ∈ ps := by
          rw [← hps]; exact List.mem_of_getElem? hp
        have hps' : s.enter.procs = ps := by simp [hps]
        have hB := ih body s.enter r hps' h
        have h0 : Unchanged s s.enter (fWA ps (.call p)) (fVA ps (.call p))
            (fWR ps (.call p)) (fVR ps (.call p)) := by
          rw [unchanged_enter_iff]; exact Unchanged.refl _ _ _ _ _
        refine h0.trans (hB.mono ?_ ?_ ?_ ?_)
        · intro y hy
          simp only [fWA, sWA, List.nil_append, List.mem_append] at hy ⊢
          rcases hy with hy | hy
          · exact sub_flat hbody hy
          · exact hy
        · intro y hy
          simp only [fVA, sVA, List.nil_append, List.mem_append] at hy ⊢
          rcases hy with hy | hy
          · exact sub_flat hbody hy
          · exact hy
        · intro y hy
          simp only [fWR, sWR, List.nil_append, List.mem_append] at hy ⊢
          rcases hy with hy | hy
          · exact sub_flat hbody hy
          · exact hy
        · intro y hy
          simp only [fVR, sVR, List.nil_append, List.mem_append] at hy ⊢
          rcases hy with hy | hy
          · exact sub_flat hbody hy
          · exact hy

/-- **Attach the syntactic frame to a `Runs` postcondition.** -/
theorem Runs.frame {c : Stmt} {s : State V} {Q : State V → Prop} {ps : List Stmt}
    (hps : s.procs = ps) (h : Runs ops c s Q) :
    Runs ops c s (fun r => Q r ∧ Unchanged s r (fWA ps c) (fVA ps c) (fWR ps c) (fVR ps c)) := by
  obtain ⟨f, r, hex, hQ⟩ := h
  exact ⟨f, r, hex, hQ, exec_frame ps f c s r hps hex⟩

end Frontier.RAM

#print axioms Frontier.RAM.exec_frame
