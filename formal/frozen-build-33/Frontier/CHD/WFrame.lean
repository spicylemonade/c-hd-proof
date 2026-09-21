import Frontier.RAMLogic
import Frontier.RAMRep

/-!
# Frontier.CHD.WFrame — syntactic frame lemma for word-only statements (owner agent-03)

**NON-GATE** (Layer B utility).  A statement built from `skip`, `wset`, `wstore`, `seq`, `ite`,
`while` (no value writes, no allocation, no calls) changes no value register/array, no array
length, not `cap` and not the procedure table; it changes only the word registers it assigns
(`wregsOf`) and the word arrays it stores to (`warrsOf`).  Used to discharge the `Unchanged`
footprints of the tree layer once, syntactically.
-/

namespace Frontier.RAM

variable {V : Type} {ops : VOps V}

/-- Word-only statements. -/
def WS : Stmt → Prop
  | .skip => True
  | .wset _ _ => True
  | .wstore _ _ _ => True
  | .seq a b => WS a ∧ WS b
  | .ite _ a b => WS a ∧ WS b
  | .while _ b => WS b
  | _ => False

/-- The word registers a statement may assign. -/
def wregsOf : Stmt → List String
  | .wset x _ => [x]
  | .vle x _ _ => [x]
  | .seq a b => wregsOf a ++ wregsOf b
  | .ite _ a b => wregsOf a ++ wregsOf b
  | .while _ b => wregsOf b
  | _ => []

/-- The word arrays a statement may store to or allocate. -/
def warrsOf : Stmt → List String
  | .wstore arr _ _ => [arr]
  | .walloc arr _ => [arr]
  | .seq a b => warrsOf a ++ warrsOf b
  | .ite _ a b => warrsOf a ++ warrsOf b
  | .while _ b => warrsOf b
  | _ => []

/-- What a word-only statement leaves unchanged. -/
structure WFr (s r : State V) (wr wa : List String) : Prop where
  v : r.v = s.v
  va : r.va = s.va
  vlen : r.vlen = s.vlen
  wlen : r.wlen = s.wlen
  cap : r.cap = s.cap
  procs : r.procs = s.procs
  w : ∀ y, y ∉ wr → r.w y = s.w y
  arr : ∀ a, a ∉ wa → r.wa a = s.wa a

theorem WFr.trans {s1 s2 s3 : State V} {wr wa wr' wa' : List String} (h1 : WFr s1 s2 wr wa)
    (h2 : WFr s2 s3 wr' wa') : WFr s1 s3 (wr ++ wr') (wa ++ wa') :=
  ⟨h2.v.trans h1.v, h2.va.trans h1.va, h2.vlen.trans h1.vlen, h2.wlen.trans h1.wlen, h2.cap.trans h1.cap,
    h2.procs.trans h1.procs,
    fun y hy => (h2.w y (fun h => hy (List.mem_append_right _ h))).trans (h1.w y (fun h => hy (List.mem_append_left _ h))),
    fun a ha => (h2.arr a (fun h => ha (List.mem_append_right _ h))).trans
      (h1.arr a (fun h => ha (List.mem_append_left _ h)))⟩

theorem WFr.mono {s r : State V} {wr wa wr' wa' : List String} (h : WFr s r wr wa) (hr : wr ⊆ wr')
    (ha : wa ⊆ wa') : WFr s r wr' wa' :=
  ⟨h.v, h.va, h.vlen, h.wlen, h.cap, h.procs, fun y hy => h.w y (fun h' => hy (hr h')),
    fun a ha' => h.arr a (fun h' => ha' (ha h'))⟩

theorem WFr.charge (s : State V) (k : ℕ) (wr wa : List String) : WFr s (s.charge k) wr wa :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem WFr.refl (s : State V) (wr wa : List String) : WFr s s wr wa :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Syntactic frame**: a run of a word-only statement changes only its assigned registers and
stored arrays. -/
theorem exec_WS : ∀ (f : ℕ) (c : Stmt) (s r : State V), WS c → exec ops f c s = some r →
    WFr s r (wregsOf c) (warrsOf c)
  | 0, _, _, _, _, h => by simp [exec] at h
  | f + 1, c, s, r, hc, h => by
    cases c with
    | skip =>
      simp only [exec, Option.some.injEq] at h; subst h; exact WFr.charge _ _ _ _
    | wset x e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨a, _, rfl⟩ := h
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_, fun _ _ => rfl⟩
      simp only [wregsOf, List.mem_singleton] at hy
      simp [State.charge, State.setW, hy]
    | wstore arr i e =>
      simp only [exec, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
      obtain ⟨j, _, a, _, h⟩ := h
      split_ifs at h with hj
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun b hb => ?_⟩
      simp only [warrsOf, List.mem_singleton] at hb
      funext k
      simp [State.charge, State.storeW, hb]
    | seq a b =>
      rw [exec_seq, Option.bind_eq_some_iff] at h
      obtain ⟨s', h1, h2⟩ := h
      exact (exec_WS f a s s' hc.1 h1).trans (exec_WS f b s' r hc.2 h2)
    | ite c a b =>
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h⟩ := h
      split_ifs at h
      · exact ((WFr.charge s 1 [] []).trans (exec_WS f a _ r hc.1 h)).mono
          (fun y hy => by simp only [List.nil_append] at hy; exact List.mem_append_left _ hy)
          (fun y hy => by simp only [List.nil_append] at hy; exact List.mem_append_left _ hy)
      · exact ((WFr.charge s 1 [] []).trans (exec_WS f b _ r hc.2 h)).mono
          (fun y hy => by simp only [List.nil_append] at hy; exact List.mem_append_right _ hy)
          (fun y hy => by simp only [List.nil_append] at hy; exact List.mem_append_right _ hy)
    | «while» c b =>
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h⟩ := h
      split_ifs at h
      · rw [Option.bind_eq_some_iff] at h
        obtain ⟨s', h1, h2⟩ := h
        have hb : WS b := hc
        have A := (WFr.charge s 1 [] []).trans (exec_WS f b _ s' hb h1)
        have B := exec_WS f (.while c b) s' r hc h2
        exact (A.trans B).mono (fun y hy => by simpa [wregsOf] using hy)
          (fun y hy => by simpa [warrsOf] using hy)
      · simp only [Option.some.injEq] at h; subst h; exact WFr.charge _ _ _ _
    | vset _ _ => exact hc.elim
    | vle _ _ _ => exact hc.elim
    | vstore _ _ _ => exact hc.elim
    | walloc _ _ => exact hc.elim
    | valloc _ _ => exact hc.elim
    | call _ => exact hc.elim

/-- Add the syntactic frame to any postcondition of a word-only statement. -/
theorem Runs.wframe {c : Stmt} {s : State V} {Q : State V → Prop} (hc : WS c) (h : Runs ops c s Q) :
    Runs ops c s (fun r => Q r ∧ WFr s r (wregsOf c) (warrsOf c)) := by
  obtain ⟨f, r, h1, h2⟩ := h
  exact ⟨f, r, h1, h2, exec_WS f c s r hc h1⟩

/-- A word-only frame gives `Unchanged` with any footprint lists covering the syntactic ones. -/
theorem WFr.unchanged {s r : State V} {wr wa : List String} (h : WFr s r wr wa) {wa' va' wr' vr' : List String}
    (hwa : wa ⊆ wa') (hwr : wr ⊆ wr') : Unchanged s r wa' va' wr' vr' :=
  ⟨fun a ha => ⟨h.arr a (fun h' => ha (hwa h')), by rw [h.wlen]⟩, fun a _ => ⟨by rw [h.va], by rw [h.vlen]⟩,
    fun y hy => h.w y (fun h' => hy (hwr h')), fun y _ => by rw [h.v], h.cap, h.procs⟩

end Frontier.RAM
