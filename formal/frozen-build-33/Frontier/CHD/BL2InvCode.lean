import Frontier.CHD.BL2Tree

/-!
# Frontier.CHD.BL2InvCode — B-L2: program text of the invocation loop (FH.2–FH.4, FH.21–FH.25)
(agent-09, scratch, NON-GATE)

Roots are read from the word array `sA` at `[fp.sb, fp.sb + fp.sn)` (the spine's S segment).
Outputs: `W` at `fp.W[fp.ob ..][0..fp.wl)` (membership bitmap `fp.inW`, no duplicates),
`Q` at `fp.Q[fp.ob ..][0..fp.ql)`; forest via the tree layer `TI`; tree marks `fp.fm`.
Between searches the per-search marks are clean: `fp.inK = fp.val = fp.inH = ∅`, `kl = hsz = 0`.
-/

namespace Frontier.CHD.BL2

open Frontier Frontier.RAM WExpr Stmt

variable {V : Type} {ops : VOps V} {G : Graph} {s : Fin G.n}

/-- FH.4: the initial search state `initSt d D x` (`H = {x}`, `K = [x]`, `val = {x}`, `kp[x] = x`). -/
def fpInitSearch : Stmt :=
  seq (wstore "fp.H" (lit 0) (var "fp.x"))
  (seq (wstore "fp.hp" (var "fp.x") (lit 0))
  (seq (wstore "fp.inH" (var "fp.x") (lit 1))
  (seq (wset "fp.hsz" (lit 1))
  (seq (wstore "fp.K" (lit 0) (var "fp.x"))
  (seq (wstore "fp.inK" (var "fp.x") (lit 1))
  (seq (wset "fp.kl" (lit 1))
  (seq (wstore "fp.val" (var "fp.x") (lit 1))
       (wstore "fp.kp" (var "fp.x") (var "fp.x")))))))))

/-- FH.21 (failed search): `W += val` (skipping vertices already in `W`), `Q += x`. -/
def fpFailOut : Stmt :=
  seq (wset "fp.i" (lit 0))
  (seq (Stmt.while (lt (var "fp.i") (var "fp.kl"))
    (seq (wset "fp.y" (load "fp.K" (var "fp.i")))
    (seq (ite (load "fp.val" (var "fp.y"))
            (ite (load "fp.inW" (var "fp.y")) skip
              (seq (wstore "fp.W" (add (var "fp.ob") (var "fp.wl")) (var "fp.y"))
              (seq (wset "fp.wl" (add (var "fp.wl") (lit 1)))
                   (wstore "fp.inW" (var "fp.y") (lit 1)))))
            skip)
         (wset "fp.i" (add (var "fp.i") (lit 1))))))
  (seq (wstore "fp.Q" (add (var "fp.ob") (var "fp.ql")) (var "fp.x"))
       (wset "fp.ql" (add (var "fp.ql") (lit 1)))))

/-- Clear the per-search marks over `K`. -/
def fpClear : Stmt :=
  seq (wset "fp.i" (lit 0))
  (seq (Stmt.while (lt (var "fp.i") (var "fp.kl"))
    (seq (wset "fp.y" (load "fp.K" (var "fp.i")))
    (seq (wstore "fp.inK" (var "fp.y") (lit 0))
    (seq (wstore "fp.val" (var "fp.y") (lit 0))
    (seq (wstore "fp.inH" (var "fp.y") (lit 0))
         (wset "fp.i" (add (var "fp.i") (lit 1))))))))
  (seq (wset "fp.kl" (lit 0)) (wset "fp.hsz" (lit 0))))

variable (LI : LabI V ops G s) (X : LabX LI) (TI : TreeI V ops G s)

/-- One root of the invocation loop (FH.3–FH.25). -/
def fpRoot (sA slB slX : String) : Stmt :=
  seq (wset "fp.x" (load sA (add (var "fp.sb") (var "fp.j"))))
  (seq (ite (load "fp.fm" (var "fp.x")) skip
        (seq fpInitSearch
        (seq (fpSearch LI X slB slX)
        (seq (ite (var "fp.sres") TI.grow fpFailOut) fpClear))))
       (wset "fp.j" (add (var "fp.j") (lit 1))))

/-- FH.2–FH.25: the invocation loop over the roots. -/
def fpInvoke (sA slB slX : String) : Stmt :=
  seq TI.init
  (seq (wset "fp.j" (lit 0))
  (seq (wset "fp.wl" (lit 0))
  (seq (wset "fp.ql" (lit 0))
       (Stmt.while (lt (var "fp.j") (var "fp.sn")) (fpRoot LI X TI sA slB slX)))))

end Frontier.CHD.BL2
