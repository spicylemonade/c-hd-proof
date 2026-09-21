import Frontier.CHD.BL2InvCode

/-!
# Frontier.CHD.BL2InvInit — B-L2: search initialization (FH.4) (agent-09, scratch, NON-GATE)
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}
variable {c : FPCtx G s} {T : Finset (Fin G.n)}

/-- The empty search state (clean marks between searches). -/
def emptySt (d : Labels G s) (D : Finset (Fin G.m)) : SSt G s :=
  { d := d, D := D, H := ∅, K := [], val := ∅, done := ∅, kpar := id, hit := none }

theorem initSearch_spec {st : State V} {d d' : Labels G s} {D D' : Finset (Fin G.m)} {x : Fin G.n}
    (hM : MyRep c T (emptySt d D) st) (hx : st.w "fp.x" = x) (hk : 1 ≤ c.k)
    (hcap : 1 < st.cap) :
    Runs ops fpInitSearch st (fun st' => MyRep c T (initSt d' D' x) st' ∧
      Unchanged st st' ["fp.H", "fp.hp", "fp.inH", "fp.K", "fp.inK", "fp.val", "fp.kp"] []
        ["fp.hsz", "fp.kl"] [] ∧ st'.cost = st.cost + 9) := by
  obtain ⟨hl, hnd, hset, hsz, hcapH, harr, hpL, hpos, hbL, hb⟩ := hM.heap
  have hxn := x.isLt
  have hH0 : 0 < st.wlen "fp.H" := by omega
  have hK0 : 0 < st.wlen "fp.K" := lt_of_lt_of_le hk hM.kcap
  have hxhp : (x : ℕ) < st.wlen "fp.hp" := by rw [hpL]; exact hxn
  have hxH : (x : ℕ) < st.wlen "fp.inH" := by rw [hbL]; exact hxn
  have hxK : (x : ℕ) < st.wlen "fp.inK" := by rw [hM.inK.1]; exact hxn
  have hxv : (x : ℕ) < st.wlen "fp.val" := by rw [hM.val.1]; exact hxn
  have hxkp : (x : ℕ) < st.wlen "fp.kp" := by rw [hM.kpL]; exact hxn
  have h0 : 0 < st.cap := by omega
  apply wp_sound
  simp [fpInitSearch, wp, hx, hH0, hK0, hxhp, hxH, hxK, hxv, hxkp, fit, hcap, h0]
  have hb0 : ∀ v : Fin G.n, st.wa "fp.inH" v = 0 := fun v => by rw [hb v]; simp [emptySt]
  have hk0 : ∀ v : Fin G.n, st.wa "fp.inK" v = 0 := fun v => by rw [hM.inK.2 v]; simp [emptySt]
  have hv0 : ∀ v : Fin G.n, st.wa "fp.val" v = 0 := fun v => by rw [hM.val.2 v]; simp [emptySt]
  refine ⟨⟨by simpa using hM.gM, by simpa using hM.headL, fun q => by simpa using hM.head q,
    ⟨[x], List.nodup_singleton x, by simp [initSt], by simp, by simpa using hcapH,
      fun i hi => by simp at hi; subst hi; simp, by simpa using hpL,
      fun i hi => by simp at hi; subst hi; simp, by simpa using hbL, fun v => ?_⟩,
    by simp [initSt], by simpa using hM.kcap, fun i hi => by simp [initSt] at hi; subst hi; simp [initSt],
    ⟨by simpa using hM.inK.1, fun v => ?_⟩, ⟨by simpa using hM.val.1, fun v => ?_⟩,
    ⟨by simpa using hM.fm.1, fun v => by simpa using hM.fm.2 v⟩, by simpa using hM.kpL,
    fun v hv => by simp [initSt] at hv; subst hv; simp [initSt], by simpa using hM.kreg,
    by simp [initSt], by simp [initSt]⟩, ?_⟩
  · by_cases hvx : v = x
    · subst hvx; simp [initSt]
    · have : (v : ℕ) ≠ x := fun h => hvx (Fin.ext h)
      simp [this, hvx, hb0 v, initSt]
  · by_cases hvx : v = x
    · subst hvx; simp [initSt]
    · have : (v : ℕ) ≠ x := fun h => hvx (Fin.ext h)
      simp [this, hvx, hk0 v, initSt]
  · by_cases hvx : v = x
    · subst hvx; simp [initSt]
    · have : (v : ℕ) ≠ x := fun h => hvx (Fin.ext h)
      simp [this, hvx, hv0 v, initSt]
  · refine ⟨fun a ha => ?_, fun _ _ => ⟨rfl, rfl⟩, fun y hy => ?_, fun _ _ => rfl, rfl, rfl⟩
    · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at ha
      refine ⟨?_, by simp⟩
      funext j; simp [ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2.1,
        ha.2.2.2.2.2.2]
    · simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hy
      simp [hy.1, hy.2]

end Frontier.CHD.BL2
