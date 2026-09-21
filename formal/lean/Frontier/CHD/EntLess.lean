import Frontier.CHD.SelectRAM
import Frontier.CHD.DRep

/-!
# Frontier.CHD.EntLess — the key comparison of pool entries (instance of `SelectRAM.LessSpec`)

Owner: agent-05 (B-L3, F-SEL / F-SPLIT / F-PULL).  NON-GATE (Layer B).

`entLess` loads the machine labels of the pool entries `sl.x`, `sl.y` from agent-02's entry label
arrays `entA` into the register blocks `fs.X`, `fs.Y` and compares them with agent-02's `cmp`:
`sl.c := [κ sl.x < κ sl.y]`, where `κ i` is the walk value represented by entry `i`.
`entLess_spec` is the `LessSpec` instance used to run `SelectRAM.sel_spec` / `filt_spec` /
`filtGe_spec` on entry ids (F-SPLIT, F-PULL).
-/

open scoped ENNReal NNReal

namespace Frontier.RAM.SelectRAM

open Frontier Frontier.CHD Frontier.RAM WExpr Stmt LabRAM Frontier.CHD.MLab Frontier.CHD.LabTab

variable {G : Graph} {s : Fin G.n}

/-- register block for the first label -/
def fsX : LReg := ⟨"fs.Xl", "fs.Xh", "fs.Xv", "fs.Xe", "fs.Xr"⟩
/-- register block for the second label -/
def fsY : LReg := ⟨"fs.Yl", "fs.Yh", "fs.Yv", "fs.Ye", "fs.Yr"⟩

/-- **the entry comparison**: `sl.c := [κ(sl.x) < κ(sl.y)]` on pool entries -/
def entLess : Stmt :=
  seq (loadA DIns.entA "sl.x" fsX) (seq (loadA DIns.entA "sl.y" fsY) (cmp fsX fsY "fs.c1" "fs.c2" "sl.c"))

/-- scratch word registers of `entLess` -/
def entLessW : List String := fsX.ws ++ fsY.ws ++ ["fs.c1", "fs.c2"]
/-- scratch value registers of `entLess` -/
def entLessV : List String := [fsX.l, fsY.l]

theorem entLessW_disj : ∀ x ∈ entLessW, x ∉ myRegs := by
  intro x hx
  simp only [entLessW, fsX, fsY, LReg.ws, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with ((h | h | h | h) | (h | h | h | h)) | (h | h) <;> subst h <;>
    simp [myRegs, lessRegs, csRegs, selRegs]

/-- **`entLess` meets `LessSpec`** for any key representation `KR` that (i) represents the value
`κ i` of every `ok` entry `i` by the machine label stored in `entA` (agent-02's `EntRep` shape,
under a good history) and (ii) depends on the arrays other than `sel.w` only. -/
theorem entLess_spec {KR : State ℝ≥0 → Prop} {ok : ℕ → Prop}
    {H : Fin G.n → ℕ → List (Fin G.m)} {V : Fin G.n → ℕ} (hH : GoodHist (s := s) H V)
    (κ : ℕ → WLab G s)
    (hrep : ∀ st, KR st → ∀ i, ok i → DIns.entA.InB st i ∧ ∃ (m : MLabel G) (p : List (Fin G.m)),
      AHolds st DIns.entA i m ∧ Rep (s := s) H V m p ∧ κ i = ((toW (s := s) p : WalkOrd G s) : WLab G s))
    (hKRf : ∀ s r, KR s → (∀ b, b ≠ "sel.w" → r.wa b = s.wa b) → r.wlen = s.wlen → r.va = s.va →
      r.vlen = s.vlen → r.cap = s.cap → KR r)
    (hcap : ∀ st, KR st → 1 < st.cap) :
    LessSpec realOps entLess KR ok κ 23 entLessW entLessV where
  run := by
    classical
    intro st hK hx hy
    obtain ⟨hbx, mx, px, hax, hrx, hκx⟩ := hrep st hK _ hx
    obtain ⟨hby, my, py, hay, hry, hκy⟩ := hrep st hK _ hy
    have hFX : LoadAFresh "sl.x" fsX := ⟨by simp [fsX, LReg.ws], by simp [fsX]⟩
    have hFY : LoadAFresh "sl.y" fsY := ⟨by simp [fsY, LReg.ws], by simp [fsY]⟩
    unfold entLess
    apply runs_seq
    refine (wp_sound _ _ _ (loadA_wp DIns.entA "sl.x" fsX hFX st _ rfl hbx mx hax)).mono
      (fun r1 ⟨hX1, hu1, hc1⟩ => ?_)
    have hwa1 : r1.wa = st.wa := funext fun b => (hu1.warr b (by simp)).1
    have hwl1 : r1.wlen = st.wlen := funext fun b => (hu1.warr b (by simp)).2
    have hva1 : r1.va = st.va := funext fun b => (hu1.varr b (by simp)).1
    have hvl1 : r1.vlen = st.vlen := funext fun b => (hu1.varr b (by simp)).2
    have hy1 : r1.w "sl.y" = st.w "sl.y" := hu1.wreg _ (by simp [fsX, LReg.ws])
    have hby1 : DIns.entA.InB r1 (st.w "sl.y") := by
      obtain ⟨b1, b2, b3, b4, b5⟩ := hby
      exact ⟨by rw [hvl1]; exact b1, by rw [hwl1]; exact b2, by rw [hwl1]; exact b3,
        by rw [hwl1]; exact b4, by rw [hwl1]; exact b5⟩
    have hay1 : AHolds r1 DIns.entA (st.w "sl.y") my := by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hay
      exact ⟨by rw [hva1]; exact a1, by rw [hwa1]; exact a2, by rw [hwa1]; exact a3,
        by rw [hwa1]; exact a4, by rw [hwa1]; exact a5⟩
    apply runs_seq
    refine (wp_sound _ _ _ (loadA_wp DIns.entA "sl.y" fsY hFY r1 _ hy1 hby1 my hay1)).mono
      (fun r2 ⟨hY2, hu2, hc2⟩ => ?_)
    have hX2 : Holds r2 fsX mx := by
      obtain ⟨x1, x2, x3, x4, x5⟩ := hX1
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [hu2.vreg _ (by simp [fsX, fsY])]; exact x1
      · rw [hu2.wreg _ (by simp [fsX, fsY, LReg.ws])]; exact x2
      · rw [hu2.wreg _ (by simp [fsX, fsY, LReg.ws])]; exact x3
      · rw [hu2.wreg _ (by simp [fsX, fsY, LReg.ws])]; exact x4
      · rw [hu2.wreg _ (by simp [fsX, fsY, LReg.ws])]; exact x5
    have hcap2 : 1 < r2.cap := by rw [hu2.cap, hu1.cap]; exact hcap st hK
    have hCF : CmpFresh fsX fsY "fs.c1" "fs.c2" :=
      ⟨by simp, by simp [fsX, LReg.ws], by simp [fsX, LReg.ws], by simp [fsY, LReg.ws],
        by simp [fsY, LReg.ws]⟩
    refine (wp_sound _ _ _ (cmp_wp (ops := realOps) (fun a b => rfl) "sl.c" hCF r2 hcap2)).mono
      (fun r ⟨hout, hu3, _, hc3⟩ => ?_)
    have hlt : (if mx.lt my then 1 else 0) = (if κ (st.w "sl.x") < κ (st.w "sl.y") then 1 else 0) := by
      rw [hκx, hκy]
      by_cases h : mx.lt my
      · have := (lt_iff hH hrx hry).mp h
        rw [if_pos h, if_pos (WithTop.coe_lt_coe.mpr this)]
      · have : ¬ toW (s := s) px < toW py := fun h' => h ((lt_iff hH hrx hry).mpr h')
        rw [if_neg h, if_neg (fun h' => this (WithTop.coe_lt_coe.mp h'))]
    refine ⟨by rw [hout, cbit_eq hX2 hY2, hlt], ?_, by omega, ?_⟩
    · have W : "sl.c" :: entLessW = "sl.c" :: entLessW := rfl
      refine (hu1.mono (List.Subset.refl _) (List.Subset.refl _) (by
          intro y hy; simp only [entLessW, List.mem_cons, List.mem_append]; right; left; left; exact hy)
          (by intro y hy; simp [entLessV] at hy ⊢; left; exact hy)).trans
        ((hu2.mono (List.Subset.refl _) (List.Subset.refl _) (by
          intro y hy; simp only [entLessW, List.mem_cons, List.mem_append]; right; left; right; exact hy)
          (by intro y hy; simp [entLessV] at hy ⊢; right; exact hy)).trans
        (hu3.mono (List.Subset.refl _) (List.Subset.refl _) (by
          intro y hy
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl | rfl <;> simp [entLessW])
          (List.nil_subset _)))
    · have hwa : r.wa = st.wa := by
        funext b; rw [(hu3.warr b (by simp)).1, (hu2.warr b (by simp)).1, (hu1.warr b (by simp)).1]
      have hwl : r.wlen = st.wlen := by
        funext b; rw [(hu3.warr b (by simp)).2, (hu2.warr b (by simp)).2, (hu1.warr b (by simp)).2]
      have hva : r.va = st.va := by
        funext b; rw [(hu3.varr b (by simp)).1, (hu2.varr b (by simp)).1, (hu1.varr b (by simp)).1]
      have hvl : r.vlen = st.vlen := by
        funext b; rw [(hu3.varr b (by simp)).2, (hu2.varr b (by simp)).2, (hu1.varr b (by simp)).2]
      exact hKRf st r hK (fun b _ => by rw [hwa]) hwl hva hvl (by rw [hu3.cap, hu2.cap, hu1.cap])
  frame := fun s r hK hwa hwl hva hvl _ hcp _ _ => hKRf s r hK hwa hwl hva hvl hcp
  disj := entLessW_disj

end Frontier.RAM.SelectRAM
