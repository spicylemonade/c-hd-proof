import Frontier.CHD.FPIface
import Frontier.CHD.LabRAM

/-!
# LabI instance — B-LAB implements agent-09's label-layer interface for FindPivots-HD
(agent-02, NON-GATE)

`labI c0 : BL2.LabI ℝ≥0 realOps G s` instantiates every field of `Frontier.CHD.BL2.LabI` with the
installed B-LAB fragments of `LabRAM`:

* `LT st d g`  = `LabAt st d g.1 c0 ∧ vc st = g.2 ∧ GraphAt st G ∧ G.m + 2 ≤ st.cap`
  (ghost `g = (H, V)`, extension `HExt`);
* `LS st sl L g` = the slot block `slotBlk sl` (registers `sl#l sl#h sl#v sl#e sl#r`, flag `sl#f`)
  holds the walk label `L` (`WHolds`);
* `LC` = `LT` plus the candidate block `X0` holding `cand (tabOf st) e`, `d (src e)` finite;
* `candB sl` = `LabRAM.candB`, `cmpTS sl` = `headLtB` on `lab.rv`, `relaxC` = `relaxCore`,
  `copySS` = register copy between slot blocks, `loadTS` = `loadLab` into a slot block.

Slot register names are `sl ++ "#x"`; no B-LAB scratch register ends in `#x`, so every name
disjointness holds for EVERY slot string (lemma `slot_not_mem`, decided by list suffixes).
-/

open scoped ENNReal NNReal

namespace Frontier.CHD.LabIInst

open Frontier Frontier.RAM Frontier.RAM.LabRAM Frontier.CHD Frontier.CHD.MLab Frontier.CHD.LabTab
  Frontier.CHD.BL2

variable {G : Graph} {s : Fin G.n}

/-! ### Cost never decreases (general machine fact) -/

theorem exec_cost_le {V : Type} (ops : VOps V) :
    ∀ (f : ℕ) (c : Stmt) (st r : State V), exec ops f c st = some r → st.cost ≤ r.cost := by
  intro f
  induction f with
  | zero => intro c st r h; simp [exec] at h
  | succ f ih =>
    intro c st r h
    cases c with
    | skip => simp [exec] at h; subst h; simp [State.charge]
    | wset x e =>
      cases he : evalW st e with
      | none => simp [exec, he] at h
      | some a => simp [exec, he] at h; subst h; simp [State.charge, State.setW]
    | vset x e =>
      cases he : evalV ops st e with
      | none => simp [exec, he] at h
      | some a => simp [exec, he] at h; subst h; simp [State.charge, State.setV]
    | vle x a b =>
      cases h1 : evalV ops st a with
      | none => simp [exec, h1] at h
      | some p =>
        cases h2 : evalV ops st b with
        | none => simp [exec, h1, h2] at h
        | some q =>
          cases h3 : fit st.cap (if ops.le p q then 1 else 0) with
          | none => simp [exec, h1, h2, h3] at h
          | some bit =>
            simp [exec, h1, h2, h3] at h; subst h; simp [State.charge, State.setW]
    | wstore arr i e =>
      cases h1 : evalW st i with
      | none => simp [exec, h1] at h
      | some j =>
        cases h2 : evalW st e with
        | none => simp [exec, h1, h2] at h
        | some a =>
          by_cases hj : j < st.wlen arr
          · simp [exec, h1, h2, hj] at h; subst h; simp [State.charge, State.storeW]
          · simp [exec, h1, h2, hj] at h
    | vstore arr i e =>
      cases h1 : evalW st i with
      | none => simp [exec, h1] at h
      | some j =>
        cases h2 : evalV ops st e with
        | none => simp [exec, h1, h2] at h
        | some a =>
          by_cases hj : j < st.vlen arr
          · simp [exec, h1, h2, hj] at h; subst h; simp [State.charge, State.storeV]
          · simp [exec, h1, h2, hj] at h
    | walloc arr e =>
      cases he : evalW st e with
      | none => simp [exec, he] at h
      | some k => simp [exec, he] at h; subst h; simp [State.charge, State.allocW]
    | valloc arr e =>
      cases he : evalW st e with
      | none => simp [exec, he] at h
      | some k => simp [exec, he] at h; subst h; simp [State.charge, State.allocV]
    | seq a b =>
      rw [exec_seq, Option.bind_eq_some_iff] at h
      obtain ⟨s', h1, h2⟩ := h
      exact (ih a st s' h1).trans (ih b s' r h2)
    | ite c a b =>
      rw [exec_ite, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · exact le_trans (by simp [State.charge]) (ih a _ r h2)
      · exact le_trans (by simp [State.charge]) (ih b _ r h2)
    | «while» c b =>
      rw [exec_while, Option.bind_eq_some_iff] at h
      obtain ⟨x, _, h2⟩ := h
      split_ifs at h2
      · rw [Option.bind_eq_some_iff] at h2
        obtain ⟨s', h3, h4⟩ := h2
        exact le_trans (by simp [State.charge]) ((ih b _ s' h3).trans (ih _ s' r h4))
      · simp at h2; subst h2; simp [State.charge]
    | call p =>
      rw [exec_call] at h
      cases hp : st.procs[p]? with
      | none => rw [hp] at h; simp at h
      | some body =>
        rw [hp] at h
        exact le_trans (by simp [State.enter]) (ih body _ r h)

theorem Runs.cost_ge {V : Type} {ops : VOps V} {c : Stmt} {st : State V} {Q : State V → Prop}
    (h : Runs ops c st Q) : Runs ops c st (fun r => Q r ∧ st.cost ≤ r.cost) := by
  obtain ⟨f, r, hr, hq⟩ := h
  exact ⟨f, r, hr, hq, exec_cost_le ops f c st r hr⟩

/-! ### Slot register names -/

/-- The register block of slot `sl`. -/
def slotBlk (sl : String) : LReg := ⟨sl ++ "#l", sl ++ "#h", sl ++ "#v", sl ++ "#e", sl ++ "#r"⟩
/-- The finiteness flag of slot `sl` (`0` = `⊤`). -/
def slotF (sl : String) : String := sl ++ "#f"

theorem append_ne_of_not_suffix {sl u t : String} (h : ¬ (u.toList <:+ t.toList)) : sl ++ u ≠ t := by
  intro heq
  apply h
  rw [← heq]
  simp only [String.toList_append]
  exact List.suffix_append _ _

theorem slot_not_mem {sl u : String} {l : List String} (h : ∀ t ∈ l, ¬ (u.toList <:+ t.toList)) :
    sl ++ u ∉ l := fun hm => append_ne_of_not_suffix (h _ hm) rfl

theorem append_right_cancel' {a b u : String} (h : a ++ u = b ++ u) : a = b := by
  have := congrArg String.toList h
  simp only [String.toList_append] at this
  exact String.toList_injective (List.append_cancel_right this)

theorem slotBlk_ws_not_mem {sl : String} {l : List String}
    (hl : ∀ t ∈ l, ∀ u ∈ ["#h", "#v", "#e", "#r"], ¬ (u.toList <:+ t.toList)) :
    ∀ a ∈ (slotBlk sl).ws, a ∉ l := by
  intro a ha
  simp only [slotBlk, LReg.ws, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact slot_not_mem (fun t ht => hl t ht "#h" (by simp))
  · exact slot_not_mem (fun t ht => hl t ht "#v" (by simp))
  · exact slot_not_mem (fun t ht => hl t ht "#e" (by simp))
  · exact slot_not_mem (fun t ht => hl t ht "#r" (by simp))

theorem slot_boundRegs (sl : String) : BoundRegs (slotBlk sl) (slotF sl) :=
  ⟨slotBlk_ws_not_mem (by decide), slot_not_mem (by decide), slot_not_mem (by decide)⟩

theorem append_ne_append_of_last {a b u v : String} (hu : u.toList ≠ []) (hv : v.toList ≠ [])
    (h : u.toList.getLast? ≠ v.toList.getLast?) : a ++ u ≠ b ++ v := by
  intro heq
  apply h
  have := congrArg (fun x : String => x.toList.getLast?) heq
  simp only [String.toList_append] at this
  rwa [List.getLast?_append_of_ne_nil _ hu, List.getLast?_append_of_ne_nil _ hv] at this

theorem ne_append_of_not_suffix {sl u t : String} (h : ¬ (u.toList <:+ t.toList)) : t ≠ sl ++ u :=
  fun heq => append_ne_of_not_suffix h heq.symm

/-- Slot registers of two DIFFERENT slots never coincide. -/
theorem slot_regs_ne {a b : String} (hab : a ≠ b) {u v : String}
    (hu : u ∈ ["#l", "#h", "#v", "#e", "#r", "#f"]) (hv : v ∈ ["#l", "#h", "#v", "#e", "#r", "#f"]) :
    a ++ u ≠ b ++ v := by
  by_cases huv : u = v
  · subst huv; exact fun h => hab (append_right_cancel' h)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
    apply append_ne_append_of_last
    · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | exact absurd rfl huv

/-- Slot registers of the SAME slot with different suffixes never coincide. -/
theorem slot_regs_ne_self (a : String) {u v : String} (huv : u ≠ v)
    (hu : u ∈ ["#l", "#h", "#v", "#e", "#r", "#f"]) (hv : v ∈ ["#l", "#h", "#v", "#e", "#r", "#f"]) :
    a ++ u ≠ a ++ v := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
  apply append_ne_append_of_last
  · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | exact absurd rfl huv

/-! ### Copying a slot block -/

open WExpr Stmt in
/-- `Y := X`, `yf := xf` (6 moves). -/
def copyBlk (X Y : LReg) (xf yf : String) : Stmt :=
  seq (vset Y.l (.var X.l)) (seq (wset Y.h (var X.h)) (seq (wset Y.v (var X.v))
  (seq (wset Y.e (var X.e)) (seq (wset Y.r (var X.r)) (wset yf (var xf))))))

/-- Copy between two different slots: the destination registers receive the source values. -/
theorem copyBlk_slots_wp (a b : String) (st : State ℝ≥0) :
    wp realOps (copyBlk (slotBlk a) (slotBlk b) (slotF a) (slotF b)) (fun r =>
      (a ≠ b → (r.v (slotBlk b).l = st.v (slotBlk a).l ∧ r.w (slotBlk b).h = st.w (slotBlk a).h ∧
        r.w (slotBlk b).v = st.w (slotBlk a).v ∧ r.w (slotBlk b).e = st.w (slotBlk a).e ∧
        r.w (slotBlk b).r = st.w (slotBlk a).r ∧ r.w (slotF b) = st.w (slotF a))) ∧
      (a = b → (r.v = st.v ∧ r.w = st.w)) ∧
      Unchanged st r [] [] ((slotBlk b).ws ++ [slotF b]) [(slotBlk b).l] ∧
      r.cost = st.cost + 6) st := by
  simp only [copyBlk, wp, evalV_var', evalW_var, State.charge_w, State.charge_v, State.setV_w,
    State.setW_v, State.setV_v, State.setW_w, State.charge_cost, State.setV_cost, State.setW_cost]
  refine ⟨fun hab => ?_, fun hab => ?_, ?_, by simp [State.charge, State.setW, State.setV]⟩
  · have n : ∀ u v, u ∈ ["#l", "#h", "#v", "#e", "#r", "#f"] → v ∈ ["#l", "#h", "#v", "#e", "#r", "#f"] →
        (a ++ u = b ++ v) = False := fun u v hu hv => eq_false (slot_regs_ne hab hu hv)
    have m : ∀ u v, u ≠ v → u ∈ ["#l", "#h", "#v", "#e", "#r", "#f"] →
        v ∈ ["#l", "#h", "#v", "#e", "#r", "#f"] → (b ++ u = b ++ v) = False :=
      fun u v huv hu hv => eq_false (slot_regs_ne_self b huv hu hv)
    simp only [slotBlk, slotF, ↓reduceIte,
      n "#h" "#h" (by simp) (by simp), n "#v" "#h" (by simp) (by simp),
      n "#e" "#h" (by simp) (by simp), n "#r" "#h" (by simp) (by simp),
      n "#v" "#v" (by simp) (by simp), n "#e" "#v" (by simp) (by simp),
      n "#r" "#v" (by simp) (by simp), n "#e" "#e" (by simp) (by simp),
      n "#r" "#e" (by simp) (by simp), n "#r" "#r" (by simp) (by simp),
      n "#f" "#h" (by simp) (by simp), n "#f" "#v" (by simp) (by simp),
      n "#f" "#e" (by simp) (by simp), n "#f" "#r" (by simp) (by simp),
      n "#f" "#f" (by simp) (by simp), n "#l" "#l" (by simp) (by simp),
      m "#h" "#v" (by decide) (by simp) (by simp), m "#h" "#e" (by decide) (by simp) (by simp),
      m "#h" "#r" (by decide) (by simp) (by simp), m "#h" "#f" (by decide) (by simp) (by simp),
      m "#v" "#e" (by decide) (by simp) (by simp), m "#v" "#r" (by decide) (by simp) (by simp),
      m "#v" "#f" (by decide) (by simp) (by simp), m "#e" "#r" (by decide) (by simp) (by simp),
      m "#e" "#f" (by decide) (by simp) (by simp), m "#r" "#f" (by decide) (by simp) (by simp),
      and_self]
  · subst hab
    have m : ∀ u v, u ≠ v → u ∈ ["#l", "#h", "#v", "#e", "#r", "#f"] →
        v ∈ ["#l", "#h", "#v", "#e", "#r", "#f"] → (a ++ u = a ++ v) = False :=
      fun u v huv hu hv => eq_false (slot_regs_ne_self a huv hu hv)
    simp only [slotBlk, slotF, ↓reduceIte,
      m "#v" "#h" (by decide) (by simp) (by simp), m "#e" "#h" (by decide) (by simp) (by simp),
      m "#r" "#h" (by decide) (by simp) (by simp), m "#e" "#v" (by decide) (by simp) (by simp),
      m "#r" "#v" (by decide) (by simp) (by simp), m "#r" "#e" (by decide) (by simp) (by simp),
      m "#f" "#h" (by decide) (by simp) (by simp), m "#f" "#v" (by decide) (by simp) (by simp),
      m "#f" "#e" (by decide) (by simp) (by simp), m "#f" "#r" (by decide) (by simp) (by simp)]
    constructor
    · funext z; by_cases hz : z = a ++ "#l" <;> simp [State.setV, hz]
    · funext z
      simp only [State.charge, State.setW, State.setV]
      split_ifs <;> subst_vars <;> rfl
  · simp only [unch_charge]
    rw [unch_setW (by simp [slotF]), unch_charge, unch_setW (by simp [slotBlk, LReg.ws]),
      unch_charge, unch_setW (by simp [slotBlk, LReg.ws]), unch_charge,
      unch_setW (by simp [slotBlk, LReg.ws]), unch_charge, unch_setW (by simp [slotBlk, LReg.ws]),
      unch_charge, unch_setV (by simp [slotBlk])]
    simp

/-! ### The interface predicates -/

/-- The ghost of the label layer: history and version counters. -/
abbrev Gh (G : Graph) := (Fin G.n → ℕ → List (Fin G.m)) × (Fin G.n → ℕ)

/-- `LT`: the label table represents `d` (with the static graph facts). -/
def LTp (c0 : ℕ) (st : State ℝ≥0) (d : Labels G s) (g : Gh G) : Prop :=
  LabAt (s := s) st d g.1 c0 ∧ vc (G := G) st = g.2 ∧ GraphAt st G ∧ G.m + 2 ≤ st.cap

/-- `LS`: slot `sl` holds the walk label `L`. -/
def LSp (st : State ℝ≥0) (sl : String) (L : WLab G s) (g : Gh G) : Prop :=
  WHolds (s := s) st (slotBlk sl) (slotF sl) g.1 g.2 L

/-- `LC`: table plus the candidate for `e` in `X0`. -/
def LCp (c0 : ℕ) (st : State ℝ≥0) (d : Labels G s) (g : Gh G) (e : Fin G.m) : Prop :=
  LTp c0 st d g ∧ Holds st X0 (cand (tabOf (G := G) st) e) ∧ d (G.src e) ≠ ⊤

theorem LTp_frame {c0 : ℕ} {st st' : State ℝ≥0} {d : Labels G s} {g : Gh G}
    {wa va wr vr : List String} (h : LTp c0 st d g) (hu : Unchanged st st' wa va wr vr)
    (hwa : Disj wa (labW ++ ["gHead"])) (hva : Disj va (labV ++ ["gW"]))
    (hc : st.cost ≤ st'.cost) : LTp c0 st' d g := by
  obtain ⟨hL, hvc, hg, hm⟩ := h
  have hw : ∀ a ∈ labW, a ∉ wa := fun a ha hwa' => hwa a hwa' (List.mem_append_left _ ha)
  have hv : "dlen" ∉ va := fun h => hva _ h (by simp [labV])
  refine ⟨hL.of_unchanged hu hw hv hc, ?_, graphAt_of_unchanged hu (fun h => hwa _ h (by simp))
    (fun h => hva _ h (by simp)) hg, by rw [hu.cap]; exact hm⟩
  rw [vc_of_unchanged hu (hw "vcnt" (by simp [labW]))]; exact hvc

theorem LCp_frame {c0 : ℕ} {st st' : State ℝ≥0} {d : Labels G s} {g : Gh G} {e : Fin G.m}
    {wa va wr vr : List String} (h : LCp c0 st d g e) (hu : Unchanged st st' wa va wr vr)
    (hwa : Disj wa (labW ++ ["gHead"])) (hva : Disj va (labV ++ ["gW"])) (hwr : Disj wr X0.ws)
    (hvr : Disj vr [X0.l]) (hc : st.cost ≤ st'.cost) : LCp c0 st' d g e := by
  obtain ⟨hT, hX, hu'⟩ := h
  have hw : ∀ a ∈ labW, a ∉ wa := fun a ha hwa' => hwa a hwa' (List.mem_append_left _ ha)
  have hv : "dlen" ∉ va := fun h => hva _ h (by simp [labV])
  have htab := (tabOf_of_unchanged (G := G) hu hw hv).1
  refine ⟨LTp_frame hT hu hwa hva hc, ?_, hu'⟩
  rw [htab]
  exact hX.of_unchanged hu (fun a ha h' => hwr a h' ha) (fun h' => hvr _ h' (by simp))

theorem LSp_frame {st st' : State ℝ≥0} {sl : String} {L : WLab G s} {g : Gh G}
    {wa va wr vr : List String} (h : LSp st sl L g) (hu : Unchanged st st' wa va wr vr)
    (hwr : Disj wr ((slotBlk sl).ws ++ [slotF sl])) (hvr : Disj vr [(slotBlk sl).l]) :
    LSp st' sl L g :=
  WHolds.of_unchanged h hu (fun a ha h' => hwr a h' (List.mem_append_left _ ha))
    (fun h' => hvr _ h' (by simp)) (fun h' => hwr _ h' (by simp))

/-! ### The fragment specifications in interface form -/

open Classical in
theorem candB_I (c0 : ℕ) {st : State ℝ≥0} {d : Labels G s} {g : Gh G} {sl : String}
    {B : WLab G s} {e : Fin G.m} (hT : LTp c0 st d g) (hS : LSp st sl B g)
    (hu : d (G.src e) ≠ ⊤) (hru : st.w "ru" = G.src e) (hre : st.w "re" = e)
    (hB : st.cost + 32 ≤ c0 + st.cap) :
    Runs realOps (LabRAM.candB (slotBlk sl) (slotF sl) "lab.bit") st (fun st' =>
      LCp c0 st' d g e ∧ st'.w "lab.bit" = (if ext (d (G.src e)) e < B then 1 else 0) ∧
      Unchanged st st' [] [] (X0.ws ++ ["lab.c1", "lab.c2", "lab.bit"]) [X0.l] ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 32) := by
  obtain ⟨hL, hvc, hg, hm⟩ := hT
  have hK : WHolds st (slotBlk sl) (slotF sl) g.1 (vc st) B := by rw [hvc]; exact hS
  refine (candB_spec st d g.1 c0 hL hg e hru hre hu (slotBlk sl) (slotF sl) "lab.bit"
    (slot_boundRegs sl) (by decide) B hK hB hm).mono ?_
  rintro r ⟨hLr, hvcr, hXr, hTr, hbit, hUr, hc1, hc2⟩
  refine ⟨⟨⟨hLr, hvcr.trans hvc, graphAt_of_unchanged hUr (by simp) (by simp) hg,
    by rw [hUr.cap]; exact hm⟩, by rw [hTr]; exact hXr, hu⟩, hbit, hUr, by omega, by omega⟩

open Classical in
theorem cmpTS_I (c0 : ℕ) {st : State ℝ≥0} {d : Labels G s} {g : Gh G} {sl : String}
    {L : WLab G s} {v : Fin G.n} (hT : LTp c0 st d g) (hS : LSp st sl L g)
    (hv : st.w "lab.rv" = v) (hB : st.cost + 22 ≤ c0 + st.cap) :
    Runs realOps (headLtB "lab.rv" Y0 (slotBlk sl) "lab.yf" (slotF sl) "lab.c1" "lab.c2" "lab.bit")
      st (fun st' => st'.w "lab.bit" = (if d v < L then 1 else 0) ∧
      Unchanged st st' [] [] (("lab.yf" :: Y0.ws) ++ ["lab.c1", "lab.c2", "lab.bit"]) [Y0.l] ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 22) := by
  obtain ⟨hL, hvc, hg, hm⟩ := hT
  have hK : WHolds st (slotBlk sl) (slotF sl) g.1 (vc st) L := by rw [hvc]; exact hS
  have hcap : 1 < st.cap := one_lt_cap_of_labAt hL v (by omega)
  have hc1 : "lab.c1" ∉ (slotBlk sl).ws := fun h =>
    slotBlk_ws_not_mem (sl := sl) (l := ["lab.c1"]) (by decide) _ h (by simp)
  have hc2 : "lab.c2" ∉ (slotBlk sl).ws := fun h =>
    slotBlk_ws_not_mem (sl := sl) (l := ["lab.c2"]) (by decide) _ h (by simp)
  have hW := headLtB_wp "lab.rv" Y0 (slotBlk sl) "lab.yf" (slotF sl) "lab.c1" "lab.c2" "lab.bit"
    ⟨by decide, by decide⟩ ⟨by decide, by decide, by decide, hc1, hc2⟩
    (slotBlk_ws_not_mem (by decide)) (slot_not_mem (by decide)) (slot_not_mem (by decide))
    st d g.1 c0 hL v hv L hK hcap
  have hR := wp_sound (ops := realOps) _ _ _ hW
  refine (Runs.cost_ge hR).mono ?_
  rintro r ⟨⟨h1, h2, h3⟩, h4⟩
  exact ⟨h1, h2, h4, h3⟩

open Classical in
theorem relaxC_I (c0 : ℕ) {st : State ℝ≥0} {d : Labels G s} {g : Gh G} {e : Fin G.m}
    (hC : LCp c0 st d g e) (hB : st.cost + 42 ≤ c0 + st.cap) :
    Runs realOps relaxCore st (fun st' => ∃ g' : Gh G, HExt g.1 g.2 g'.1 g'.2 ∧
      LTp c0 st' (relaxL d (G.src e) e) g' ∧ st'.w "ok" = (if Ok d (G.src e) e then 1 else 0) ∧
      Unchanged st st' labW labV relaxW relaxV ∧ st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 42) := by
  obtain ⟨⟨hL, hvc, hg, hm⟩, hX, hu⟩ := hC
  have hW := relaxCore_wp st d g.1 c0 hL e hX hu (by omega)
  have hR := wp_sound (ops := realOps) _ _ _ hW
  refine hR.mono ?_
  rintro r ⟨H', hL', hext, hok, -, -, hU, hc1, hc2⟩
  refine ⟨(H', vc r), by rw [← hvc]; exact hext,
    ⟨hL', rfl, graphAt_of_unchanged hU (by decide) (by decide) hg, by rw [hU.cap]; exact hm⟩,
    hok, hU, by omega, hc2⟩

theorem copySS_I {st : State ℝ≥0} {g : Gh G} {src dst : String} {L : WLab G s}
    (hS : LSp st src L g) :
    Runs realOps (copyBlk (slotBlk src) (slotBlk dst) (slotF src) (slotF dst)) st (fun st' =>
      LSp st' dst L g ∧
      Unchanged st st' [] [] ((slotBlk dst).ws ++ [slotF dst] ++ []) ([(slotBlk dst).l] ++ []) ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 6) := by
  apply wp_sound
  refine wp_mono _ ?_ _ (copyBlk_slots_wp src dst st)
  rintro r ⟨hne, heq, hU, hc⟩
  refine ⟨?_, by simpa using hU, by omega, by omega⟩
  by_cases hsd : src = dst
  · subst hsd
    obtain ⟨hv, hw⟩ := heq rfl
    obtain ⟨hf, hfin⟩ := hS
    refine ⟨by rw [hw]; exact hf, fun q hq => ?_⟩
    obtain ⟨x, ⟨x1, x2, x3, x4, x5⟩, hx⟩ := hfin q hq
    exact ⟨x, ⟨by rw [hv]; exact x1, by rw [hw]; exact x2, by rw [hw]; exact x3,
      by rw [hw]; exact x4, by rw [hw]; exact x5⟩, hx⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hne hsd
    obtain ⟨hf, hfin⟩ := hS
    refine ⟨by rw [h6]; exact hf, fun q hq => ?_⟩
    obtain ⟨x, ⟨x1, x2, x3, x4, x5⟩, hx⟩ := hfin q hq
    exact ⟨x, ⟨by rw [h1]; exact x1, by rw [h2]; exact x2, by rw [h3]; exact x3,
      by rw [h4]; exact x4, by rw [h5]; exact x5⟩, hx⟩

theorem append_left_cancel' {a u v : String} (h : a ++ u = a ++ v) : u = v := by
  have := congrArg String.toList h
  simp only [String.toList_append] at this
  exact String.toList_injective (List.append_cancel_left this)

theorem slot_loadFresh (sl : String) : LoadFresh "lab.rv" (slotBlk sl) (slotF sl) := by
  refine ⟨?_, ?_⟩
  · have hn : (["#h", "#v", "#e", "#r", "#f"] : List String).Nodup := by decide
    have := List.Nodup.map (f := (sl ++ ·)) (fun u v h => append_left_cancel' h) hn
    simpa [slotBlk, slotF] using this
  · simp only [slotBlk, slotF, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨ne_append_of_not_suffix (by decide), ne_append_of_not_suffix (by decide),
      ne_append_of_not_suffix (by decide), ne_append_of_not_suffix (by decide)⟩

theorem loadTS_I (c0 : ℕ) {st : State ℝ≥0} {d : Labels G s} {g : Gh G} {dst : String}
    {v : Fin G.n} (hT : LTp c0 st d g) (hv : st.w "lab.rv" = v) :
    Runs realOps (loadLab "lab.rv" (slotBlk dst) (slotF dst)) st (fun st' => LSp st' dst (d v) g ∧
      Unchanged st st' [] [] ((slotBlk dst).ws ++ [slotF dst] ++ []) ([(slotBlk dst).l] ++ []) ∧
      st.cost ≤ st'.cost ∧ st'.cost ≤ st.cost + 6) := by
  obtain ⟨hL, hvc, hg, hm⟩ := hT
  apply wp_sound
  refine wp_mono _ ?_ _ (loadLab_wp "lab.rv" (slotBlk dst) (slotF dst) (slot_loadFresh dst) st v
    hL.lens hv)
  rintro r ⟨hLd, hU, hc⟩
  refine ⟨⟨?_, fun q hq => ?_⟩, ?_, by omega, by omega⟩
  · rw [hLd.2.2.2.2.2]; exact hL.rep.fin_iff v
  · have hv' : d v ≠ ⊤ := by rw [hq]; exact WithTop.coe_ne_top
    refine ⟨(tabOf (G := G) st).lab v, Loaded.holds hLd hL.rep hv', ?_⟩
    rw [← hvc]; exact hL.rep.rep v q hq
  · refine hU.mono (by simp) (by simp) (fun a ha => ?_) (by simp)
    simp only [List.mem_cons] at ha
    simp only [List.append_nil, List.mem_append, List.mem_singleton]
    tauto

/-! ### The instance -/

/-- **B-LAB instantiates B-L2's label-layer interface** (`BL2.LabI`), for every clock origin. -/
noncomputable def labI (c0 : ℕ) : LabI ℝ≥0 realOps G s where
  c0 := c0
  Gh := Gh G
  gext g g' := HExt g.1 g.2 g'.1 g'.2
  gext_refl g := HExt.refl _ _
  gext_trans h1 h2 := HExt.trans h1 h2
  LT := LTp c0
  LS := LSp
  LC := LCp c0
  LC_LT h := h.1
  LS_ext h hg := WHolds.ext h hg
  tabWA := labW ++ ["gHead"]
  tabVA := labV ++ ["gW"]
  cWR := X0.ws
  cVR := [X0.l]
  slWA _ := []
  slVA _ := []
  slWR sl := (slotBlk sl).ws ++ [slotF sl]
  slVR sl := [(slotBlk sl).l]
  LT_frame h hu hwa hva hc := LTp_frame h hu hwa hva hc
  LC_frame h hu hwa hva hwr hvr hc := LCp_frame h hu hwa hva hwr hvr hc
  LS_frame h hu _ _ hwr hvr := LSp_frame h hu hwr hvr
  ru := "ru"
  re := "re"
  rv := "lab.rv"
  bit := "lab.bit"
  ok := "ok"
  candB sl := LabRAM.candB (slotBlk sl) (slotF sl) "lab.bit"
  cmpTS sl := headLtB "lab.rv" Y0 (slotBlk sl) "lab.yf" (slotF sl) "lab.c1" "lab.c2" "lab.bit"
  relaxC := relaxCore
  Ccand := 32
  Ccmp := 22
  Crel := 42
  candWR := X0.ws ++ ["lab.c1", "lab.c2", "lab.bit"]
  candVR := [X0.l]
  cmpWR := ("lab.yf" :: Y0.ws) ++ ["lab.c1", "lab.c2", "lab.bit"]
  cmpVR := [Y0.l]
  relWR := relaxW
  relVR := relaxV
  relWA := labW
  relVA := labV
  candB_spec hT hS hu hru hre hB := candB_I c0 hT hS hu hru hre hB
  cmpTS_spec hT hS hv hB := cmpTS_I c0 hT hS hv hB
  relaxC_spec hC _ hB := relaxC_I c0 hC hB
  copySS src dst := copyBlk (slotBlk src) (slotBlk dst) (slotF src) (slotF dst)
  loadTS dst := loadLab "lab.rv" (slotBlk dst) (slotF dst)
  Ccopy := 6
  cpWR := []
  cpVR := []
  copySS_spec hS _ := copySS_I hS
  loadTS_spec hT hv _ := loadTS_I c0 hT hv
  bit_candWR := by decide
  bit_cmpWR := by decide
  ok_relWR := by decide
  cmp_cWR := by unfold Disj; decide
  cmp_cVR := by unfold Disj; decide
  ru_cWR := by decide
  re_cWR := by decide
  rv_cWR := by decide

end Frontier.CHD.LabIInst
