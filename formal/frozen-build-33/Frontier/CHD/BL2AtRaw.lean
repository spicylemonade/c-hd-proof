import Frontier.CHD.BL2FPB

/-!
# Frontier.CHD.BL2AtRaw — the level FindPivots call as a literal, axiom-free `Stmt` (owner agent-09, NON-GATE)

`fpAtRaw` is the normal form of `BL2Inst.fpAt`, printed by `repr` (generated file); `fpAt_eq_raw`
identifies them by `rfl`, so every theorem about `fpAt` holds for the literal program, whose
`#print axioms` is empty.
-/

set_option maxRecDepth 100000

namespace Frontier.CHD.BL2Inst

/-- **The level FindPivots call, literally** (generated from `repr fpAt`). -/
def fpAtRaw : Frontier.RAM.Stmt :=
  Frontier.RAM.Stmt.seq
    (Frontier.RAM.Stmt.seq
      (Frontier.RAM.Stmt.wset "sl.i" (Frontier.RAM.WExpr.mul (Frontier.RAM.WExpr.lit 4) (Frontier.RAM.WExpr.var "lvl")))
      (Frontier.RAM.Stmt.seq
        (Frontier.RAM.Stmt.seq
          (Frontier.RAM.Stmt.vset "fp.B#l" (Frontier.RAM.VExpr.load "sl.l" (Frontier.RAM.WExpr.var "sl.i")))
          (Frontier.RAM.Stmt.seq
            (Frontier.RAM.Stmt.wset "fp.B#h" (Frontier.RAM.WExpr.load "sl.h" (Frontier.RAM.WExpr.var "sl.i")))
            (Frontier.RAM.Stmt.seq
              (Frontier.RAM.Stmt.wset "fp.B#v" (Frontier.RAM.WExpr.load "sl.v" (Frontier.RAM.WExpr.var "sl.i")))
              (Frontier.RAM.Stmt.seq
                (Frontier.RAM.Stmt.wset "fp.B#e" (Frontier.RAM.WExpr.load "sl.e" (Frontier.RAM.WExpr.var "sl.i")))
                (Frontier.RAM.Stmt.seq
                  (Frontier.RAM.Stmt.wset "fp.B#r" (Frontier.RAM.WExpr.load "sl.r" (Frontier.RAM.WExpr.var "sl.i")))
                  (Frontier.RAM.Stmt.wset "fp.B#f" (Frontier.RAM.WExpr.load "sl.f" (Frontier.RAM.WExpr.var "sl.i"))))))))
        (Frontier.RAM.Stmt.seq
          (Frontier.RAM.Stmt.wset
            "fp.sb"
            (Frontier.RAM.WExpr.mul (Frontier.RAM.WExpr.var "lvl") (Frontier.RAM.WExpr.var "n")))
          (Frontier.RAM.Stmt.wset "fp.sn" (Frontier.RAM.WExpr.load "S.len" (Frontier.RAM.WExpr.var "lvl"))))))
    (Frontier.RAM.Stmt.seq
      (Frontier.RAM.Stmt.seq
        (Frontier.RAM.Stmt.seq
          (Frontier.RAM.Stmt.vset "fp.LX#l" (Frontier.RAM.VExpr.var "fp.B#l"))
          (Frontier.RAM.Stmt.seq
            (Frontier.RAM.Stmt.wset "fp.LX#h" (Frontier.RAM.WExpr.var "fp.B#h"))
            (Frontier.RAM.Stmt.seq
              (Frontier.RAM.Stmt.wset "fp.LX#v" (Frontier.RAM.WExpr.var "fp.B#v"))
              (Frontier.RAM.Stmt.seq
                (Frontier.RAM.Stmt.wset "fp.LX#e" (Frontier.RAM.WExpr.var "fp.B#e"))
                (Frontier.RAM.Stmt.seq
                  (Frontier.RAM.Stmt.wset "fp.LX#r" (Frontier.RAM.WExpr.var "fp.B#r"))
                  (Frontier.RAM.Stmt.wset "fp.LX#f" (Frontier.RAM.WExpr.var "fp.B#f")))))))
        (Frontier.RAM.Stmt.seq
          (Frontier.RAM.Stmt.wset "fp.j" (Frontier.RAM.WExpr.lit 0))
          (Frontier.RAM.Stmt.while
            (Frontier.RAM.WExpr.lt (Frontier.RAM.WExpr.var "fp.j") (Frontier.RAM.WExpr.var "fp.sn"))
            (Frontier.RAM.Stmt.seq
              (Frontier.RAM.Stmt.wset
                "lab.rv"
                (Frontier.RAM.WExpr.load
                  "S"
                  (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "fp.sb") (Frontier.RAM.WExpr.var "fp.j"))))
              (Frontier.RAM.Stmt.seq
                (Frontier.RAM.Stmt.seq
                  (Frontier.RAM.Stmt.seq
                    (Frontier.RAM.Stmt.vset "lab.yl" (Frontier.RAM.VExpr.load "dlen" (Frontier.RAM.WExpr.var "lab.rv")))
                    (Frontier.RAM.Stmt.seq
                      (Frontier.RAM.Stmt.wset
                        "lab.yh"
                        (Frontier.RAM.WExpr.load "dhops" (Frontier.RAM.WExpr.var "lab.rv")))
                      (Frontier.RAM.Stmt.seq
                        (Frontier.RAM.Stmt.wset "lab.ye" (Frontier.RAM.WExpr.load "de" (Frontier.RAM.WExpr.var "lab.rv")))
                        (Frontier.RAM.Stmt.seq
                          (Frontier.RAM.Stmt.wset
                            "lab.yr"
                            (Frontier.RAM.WExpr.load "dver" (Frontier.RAM.WExpr.var "lab.rv")))
                          (Frontier.RAM.Stmt.seq
                            (Frontier.RAM.Stmt.wset
                              "lab.yf"
                              (Frontier.RAM.WExpr.load "dfin" (Frontier.RAM.WExpr.var "lab.rv")))
                            (Frontier.RAM.Stmt.wset "lab.yv" (Frontier.RAM.WExpr.var "lab.rv")))))))
                  (Frontier.RAM.Stmt.ite
                    (Frontier.RAM.WExpr.var "lab.yf")
                    (Frontier.RAM.Stmt.ite
                      (Frontier.RAM.WExpr.var "fp.LX#f")
                      (Frontier.RAM.Stmt.seq
                        (Frontier.RAM.Stmt.vle
                          "lab.c1"
                          (Frontier.RAM.VExpr.var "lab.yl")
                          (Frontier.RAM.VExpr.var "fp.LX#l"))
                        (Frontier.RAM.Stmt.seq
                          (Frontier.RAM.Stmt.vle
                            "lab.c2"
                            (Frontier.RAM.VExpr.var "fp.LX#l")
                            (Frontier.RAM.VExpr.var "lab.yl"))
                          (Frontier.RAM.Stmt.ite
                            (Frontier.RAM.WExpr.var "lab.c2")
                            (Frontier.RAM.Stmt.ite
                              (Frontier.RAM.WExpr.var "lab.c1")
                              (Frontier.RAM.Stmt.ite
                                (Frontier.RAM.WExpr.lt
                                  (Frontier.RAM.WExpr.var "lab.yh")
                                  (Frontier.RAM.WExpr.var "fp.LX#h"))
                                (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 1))
                                (Frontier.RAM.Stmt.ite
                                  (Frontier.RAM.WExpr.lt
                                    (Frontier.RAM.WExpr.var "fp.LX#h")
                                    (Frontier.RAM.WExpr.var "lab.yh"))
                                  (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 0))
                                  (Frontier.RAM.Stmt.ite
                                    (Frontier.RAM.WExpr.lt
                                      (Frontier.RAM.WExpr.var "lab.yv")
                                      (Frontier.RAM.WExpr.var "fp.LX#v"))
                                    (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 1))
                                    (Frontier.RAM.Stmt.ite
                                      (Frontier.RAM.WExpr.lt
                                        (Frontier.RAM.WExpr.var "fp.LX#v")
                                        (Frontier.RAM.WExpr.var "lab.yv"))
                                      (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 0))
                                      (Frontier.RAM.Stmt.ite
                                        (Frontier.RAM.WExpr.lt
                                          (Frontier.RAM.WExpr.var "lab.ye")
                                          (Frontier.RAM.WExpr.var "fp.LX#e"))
                                        (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 1))
                                        (Frontier.RAM.Stmt.ite
                                          (Frontier.RAM.WExpr.lt
                                            (Frontier.RAM.WExpr.var "fp.LX#e")
                                            (Frontier.RAM.WExpr.var "lab.ye"))
                                          (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 0))
                                          (Frontier.RAM.Stmt.ite
                                            (Frontier.RAM.WExpr.lt
                                              (Frontier.RAM.WExpr.var "fp.LX#r")
                                              (Frontier.RAM.WExpr.var "lab.yr"))
                                            (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 1))
                                            (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 0)))))))))
                              (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 0)))
                            (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 1)))))
                      (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 1)))
                    (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 0))))
                (Frontier.RAM.Stmt.seq
                  (Frontier.RAM.Stmt.ite
                    (Frontier.RAM.WExpr.var "lab.bit")
                    (Frontier.RAM.Stmt.seq
                      (Frontier.RAM.Stmt.vset
                        "fp.LX#l"
                        (Frontier.RAM.VExpr.load "dlen" (Frontier.RAM.WExpr.var "lab.rv")))
                      (Frontier.RAM.Stmt.seq
                        (Frontier.RAM.Stmt.wset
                          "fp.LX#h"
                          (Frontier.RAM.WExpr.load "dhops" (Frontier.RAM.WExpr.var "lab.rv")))
                        (Frontier.RAM.Stmt.seq
                          (Frontier.RAM.Stmt.wset
                            "fp.LX#e"
                            (Frontier.RAM.WExpr.load "de" (Frontier.RAM.WExpr.var "lab.rv")))
                          (Frontier.RAM.Stmt.seq
                            (Frontier.RAM.Stmt.wset
                              "fp.LX#r"
                              (Frontier.RAM.WExpr.load "dver" (Frontier.RAM.WExpr.var "lab.rv")))
                            (Frontier.RAM.Stmt.seq
                              (Frontier.RAM.Stmt.wset
                                "fp.LX#f"
                                (Frontier.RAM.WExpr.load "dfin" (Frontier.RAM.WExpr.var "lab.rv")))
                              (Frontier.RAM.Stmt.wset "fp.LX#v" (Frontier.RAM.WExpr.var "lab.rv")))))))
                    (Frontier.RAM.Stmt.skip))
                  (Frontier.RAM.Stmt.wset
                    "fp.j"
                    (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "fp.j") (Frontier.RAM.WExpr.lit 1)))))))))
      (Frontier.RAM.Stmt.seq
        (Frontier.RAM.Stmt.seq
          (Frontier.RAM.Stmt.seq
            (Frontier.RAM.Stmt.wset "tr.nt" (Frontier.RAM.WExpr.lit 0))
            (Frontier.RAM.Stmt.seq
              (Frontier.RAM.Stmt.wset "fp.j" (Frontier.RAM.WExpr.lit 0))
              (Frontier.RAM.Stmt.seq
                (Frontier.RAM.Stmt.wset "fp.wl" (Frontier.RAM.WExpr.lit 0))
                (Frontier.RAM.Stmt.seq
                  (Frontier.RAM.Stmt.wset "fp.ql" (Frontier.RAM.WExpr.lit 0))
                  (Frontier.RAM.Stmt.while
                    (Frontier.RAM.WExpr.lt (Frontier.RAM.WExpr.var "fp.j") (Frontier.RAM.WExpr.var "fp.sn"))
                    (Frontier.RAM.Stmt.seq
                      (Frontier.RAM.Stmt.wset
                        "fp.x"
                        (Frontier.RAM.WExpr.load
                          "S"
                          (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "fp.sb") (Frontier.RAM.WExpr.var "fp.j"))))
                      (Frontier.RAM.Stmt.seq
                        (Frontier.RAM.Stmt.ite
                          (Frontier.RAM.WExpr.load "fp.fm" (Frontier.RAM.WExpr.var "fp.x"))
                          (Frontier.RAM.Stmt.skip)
                          (Frontier.RAM.Stmt.seq
                            (Frontier.RAM.Stmt.seq
                              (Frontier.RAM.Stmt.wstore "fp.H" (Frontier.RAM.WExpr.lit 0) (Frontier.RAM.WExpr.var "fp.x"))
                              (Frontier.RAM.Stmt.seq
                                (Frontier.RAM.Stmt.wstore
                                  "fp.hp"
                                  (Frontier.RAM.WExpr.var "fp.x")
                                  (Frontier.RAM.WExpr.lit 0))
                                (Frontier.RAM.Stmt.seq
                                  (Frontier.RAM.Stmt.wstore
                                    "fp.inH"
                                    (Frontier.RAM.WExpr.var "fp.x")
                                    (Frontier.RAM.WExpr.lit 1))
                                  (Frontier.RAM.Stmt.seq
                                    (Frontier.RAM.Stmt.wset "fp.hsz" (Frontier.RAM.WExpr.lit 1))
                                    (Frontier.RAM.Stmt.seq
                                      (Frontier.RAM.Stmt.wstore
                                        "fp.K"
                                        (Frontier.RAM.WExpr.lit 0)
                                        (Frontier.RAM.WExpr.var "fp.x"))
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.wstore
                                          "fp.inK"
                                          (Frontier.RAM.WExpr.var "fp.x")
                                          (Frontier.RAM.WExpr.lit 1))
                                        (Frontier.RAM.Stmt.seq
                                          (Frontier.RAM.Stmt.wset "fp.kl" (Frontier.RAM.WExpr.lit 1))
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.wstore
                                              "fp.val"
                                              (Frontier.RAM.WExpr.var "fp.x")
                                              (Frontier.RAM.WExpr.lit 1))
                                            (Frontier.RAM.Stmt.wstore
                                              "fp.kp"
                                              (Frontier.RAM.WExpr.var "fp.x")
                                              (Frontier.RAM.WExpr.var "fp.x"))))))))))
                            (Frontier.RAM.Stmt.seq
                              (Frontier.RAM.Stmt.seq
                                (Frontier.RAM.Stmt.wset "fp.sgo" (Frontier.RAM.WExpr.lit 1))
                                (Frontier.RAM.Stmt.while
                                  (Frontier.RAM.WExpr.var "fp.sgo")
                                  (Frontier.RAM.Stmt.ite
                                    (Frontier.RAM.WExpr.lt
                                      (Frontier.RAM.WExpr.var "fp.kl")
                                      (Frontier.RAM.WExpr.var "fp.k"))
                                    (Frontier.RAM.Stmt.ite
                                      (Frontier.RAM.WExpr.var "fp.hsz")
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.seq
                                          (Frontier.RAM.Stmt.wset "fp.bi" (Frontier.RAM.WExpr.lit 0))
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.wset "fp.i" (Frontier.RAM.WExpr.lit 1))
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.while
                                                (Frontier.RAM.WExpr.lt
                                                  (Frontier.RAM.WExpr.var "fp.i")
                                                  (Frontier.RAM.WExpr.var "fp.hsz"))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wset
                                                    "tt.ra"
                                                    (Frontier.RAM.WExpr.load "fp.H" (Frontier.RAM.WExpr.var "fp.i")))
                                                  (Frontier.RAM.Stmt.seq
                                                    (Frontier.RAM.Stmt.wset
                                                      "tt.rb"
                                                      (Frontier.RAM.WExpr.load "fp.H" (Frontier.RAM.WExpr.var "fp.bi")))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.vset
                                                            "hq_xl"
                                                            (Frontier.RAM.VExpr.load
                                                              "dlen"
                                                              (Frontier.RAM.WExpr.var "tt.ra")))
                                                          (Frontier.RAM.Stmt.seq
                                                            (Frontier.RAM.Stmt.wset
                                                              "hq_xh"
                                                              (Frontier.RAM.WExpr.load
                                                                "dhops"
                                                                (Frontier.RAM.WExpr.var "tt.ra")))
                                                            (Frontier.RAM.Stmt.seq
                                                              (Frontier.RAM.Stmt.wset
                                                                "hq_xe"
                                                                (Frontier.RAM.WExpr.load
                                                                  "de"
                                                                  (Frontier.RAM.WExpr.var "tt.ra")))
                                                              (Frontier.RAM.Stmt.seq
                                                                (Frontier.RAM.Stmt.wset
                                                                  "hq_xr"
                                                                  (Frontier.RAM.WExpr.load
                                                                    "dver"
                                                                    (Frontier.RAM.WExpr.var "tt.ra")))
                                                                (Frontier.RAM.Stmt.seq
                                                                  (Frontier.RAM.Stmt.wset
                                                                    "hq_xf"
                                                                    (Frontier.RAM.WExpr.load
                                                                      "dfin"
                                                                      (Frontier.RAM.WExpr.var "tt.ra")))
                                                                  (Frontier.RAM.Stmt.wset
                                                                    "hq_xv"
                                                                    (Frontier.RAM.WExpr.var "tt.ra")))))))
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.seq
                                                            (Frontier.RAM.Stmt.vset
                                                              "hq_yl"
                                                              (Frontier.RAM.VExpr.load
                                                                "dlen"
                                                                (Frontier.RAM.WExpr.var "tt.rb")))
                                                            (Frontier.RAM.Stmt.seq
                                                              (Frontier.RAM.Stmt.wset
                                                                "hq_yh"
                                                                (Frontier.RAM.WExpr.load
                                                                  "dhops"
                                                                  (Frontier.RAM.WExpr.var "tt.rb")))
                                                              (Frontier.RAM.Stmt.seq
                                                                (Frontier.RAM.Stmt.wset
                                                                  "hq_ye"
                                                                  (Frontier.RAM.WExpr.load
                                                                    "de"
                                                                    (Frontier.RAM.WExpr.var "tt.rb")))
                                                                (Frontier.RAM.Stmt.seq
                                                                  (Frontier.RAM.Stmt.wset
                                                                    "hq_yr"
                                                                    (Frontier.RAM.WExpr.load
                                                                      "dver"
                                                                      (Frontier.RAM.WExpr.var "tt.rb")))
                                                                  (Frontier.RAM.Stmt.seq
                                                                    (Frontier.RAM.Stmt.wset
                                                                      "hq_yf"
                                                                      (Frontier.RAM.WExpr.load
                                                                        "dfin"
                                                                        (Frontier.RAM.WExpr.var "tt.rb")))
                                                                    (Frontier.RAM.Stmt.wset
                                                                      "hq_yv"
                                                                      (Frontier.RAM.WExpr.var "tt.rb")))))))
                                                          (Frontier.RAM.Stmt.ite
                                                            (Frontier.RAM.WExpr.var "hq_xf")
                                                            (Frontier.RAM.Stmt.ite
                                                              (Frontier.RAM.WExpr.var "hq_yf")
                                                              (Frontier.RAM.Stmt.seq
                                                                (Frontier.RAM.Stmt.vle
                                                                  "hq_c1"
                                                                  (Frontier.RAM.VExpr.var "hq_xl")
                                                                  (Frontier.RAM.VExpr.var "hq_yl"))
                                                                (Frontier.RAM.Stmt.seq
                                                                  (Frontier.RAM.Stmt.vle
                                                                    "hq_c2"
                                                                    (Frontier.RAM.VExpr.var "hq_yl")
                                                                    (Frontier.RAM.VExpr.var "hq_xl"))
                                                                  (Frontier.RAM.Stmt.ite
                                                                    (Frontier.RAM.WExpr.var "hq_c2")
                                                                    (Frontier.RAM.Stmt.ite
                                                                      (Frontier.RAM.WExpr.var "hq_c1")
                                                                      (Frontier.RAM.Stmt.ite
                                                                        (Frontier.RAM.WExpr.lt
                                                                          (Frontier.RAM.WExpr.var "hq_xh")
                                                                          (Frontier.RAM.WExpr.var "hq_yh"))
                                                                        (Frontier.RAM.Stmt.wset
                                                                          "lab.bit"
                                                                          (Frontier.RAM.WExpr.lit 1))
                                                                        (Frontier.RAM.Stmt.ite
                                                                          (Frontier.RAM.WExpr.lt
                                                                            (Frontier.RAM.WExpr.var "hq_yh")
                                                                            (Frontier.RAM.WExpr.var "hq_xh"))
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "lab.bit"
                                                                            (Frontier.RAM.WExpr.lit 0))
                                                                          (Frontier.RAM.Stmt.ite
                                                                            (Frontier.RAM.WExpr.lt
                                                                              (Frontier.RAM.WExpr.var "hq_xv")
                                                                              (Frontier.RAM.WExpr.var "hq_yv"))
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "lab.bit"
                                                                              (Frontier.RAM.WExpr.lit 1))
                                                                            (Frontier.RAM.Stmt.ite
                                                                              (Frontier.RAM.WExpr.lt
                                                                                (Frontier.RAM.WExpr.var "hq_yv")
                                                                                (Frontier.RAM.WExpr.var "hq_xv"))
                                                                              (Frontier.RAM.Stmt.wset
                                                                                "lab.bit"
                                                                                (Frontier.RAM.WExpr.lit 0))
                                                                              (Frontier.RAM.Stmt.ite
                                                                                (Frontier.RAM.WExpr.lt
                                                                                  (Frontier.RAM.WExpr.var "hq_xe")
                                                                                  (Frontier.RAM.WExpr.var "hq_ye"))
                                                                                (Frontier.RAM.Stmt.wset
                                                                                  "lab.bit"
                                                                                  (Frontier.RAM.WExpr.lit 1))
                                                                                (Frontier.RAM.Stmt.ite
                                                                                  (Frontier.RAM.WExpr.lt
                                                                                    (Frontier.RAM.WExpr.var "hq_ye")
                                                                                    (Frontier.RAM.WExpr.var "hq_xe"))
                                                                                  (Frontier.RAM.Stmt.wset
                                                                                    "lab.bit"
                                                                                    (Frontier.RAM.WExpr.lit 0))
                                                                                  (Frontier.RAM.Stmt.ite
                                                                                    (Frontier.RAM.WExpr.lt
                                                                                      (Frontier.RAM.WExpr.var "hq_yr")
                                                                                      (Frontier.RAM.WExpr.var "hq_xr"))
                                                                                    (Frontier.RAM.Stmt.wset
                                                                                      "lab.bit"
                                                                                      (Frontier.RAM.WExpr.lit 1))
                                                                                    (Frontier.RAM.Stmt.wset
                                                                                      "lab.bit"
                                                                                      (Frontier.RAM.WExpr.lit 0)))))))))
                                                                      (Frontier.RAM.Stmt.wset
                                                                        "lab.bit"
                                                                        (Frontier.RAM.WExpr.lit 0)))
                                                                    (Frontier.RAM.Stmt.wset
                                                                      "lab.bit"
                                                                      (Frontier.RAM.WExpr.lit 1)))))
                                                              (Frontier.RAM.Stmt.wset
                                                                "lab.bit"
                                                                (Frontier.RAM.WExpr.lit 1)))
                                                            (Frontier.RAM.Stmt.wset
                                                              "lab.bit"
                                                              (Frontier.RAM.WExpr.lit 0)))))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.ite
                                                          (Frontier.RAM.WExpr.var "lab.bit")
                                                          (Frontier.RAM.Stmt.wset "fp.bi" (Frontier.RAM.WExpr.var "fp.i"))
                                                          (Frontier.RAM.Stmt.skip))
                                                        (Frontier.RAM.Stmt.wset
                                                          "fp.i"
                                                          (Frontier.RAM.WExpr.add
                                                            (Frontier.RAM.WExpr.var "fp.i")
                                                            (Frontier.RAM.WExpr.lit 1))))))))
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.wset
                                                  "fp.u"
                                                  (Frontier.RAM.WExpr.load "fp.H" (Frontier.RAM.WExpr.var "fp.bi")))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wset
                                                    "fp.hsz"
                                                    (Frontier.RAM.WExpr.sub
                                                      (Frontier.RAM.WExpr.var "fp.hsz")
                                                      (Frontier.RAM.WExpr.lit 1)))
                                                  (Frontier.RAM.Stmt.seq
                                                    (Frontier.RAM.Stmt.wset
                                                      "fp.t"
                                                      (Frontier.RAM.WExpr.load "fp.H" (Frontier.RAM.WExpr.var "fp.hsz")))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wstore
                                                        "fp.H"
                                                        (Frontier.RAM.WExpr.var "fp.bi")
                                                        (Frontier.RAM.WExpr.var "fp.t"))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wstore
                                                          "fp.hp"
                                                          (Frontier.RAM.WExpr.var "fp.t")
                                                          (Frontier.RAM.WExpr.var "fp.bi"))
                                                        (Frontier.RAM.Stmt.wstore
                                                          "fp.inH"
                                                          (Frontier.RAM.WExpr.var "fp.u")
                                                          (Frontier.RAM.WExpr.lit 0))))))))))
                                        (Frontier.RAM.Stmt.seq
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.wset
                                                "fp.p"
                                                (Frontier.RAM.WExpr.load "gHd" (Frontier.RAM.WExpr.var "fp.u")))
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.wset "fp.pp" (Frontier.RAM.WExpr.var "gM"))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wset "fp.res" (Frontier.RAM.WExpr.lit 0))
                                                  (Frontier.RAM.Stmt.wset
                                                    "fp.go"
                                                    (Frontier.RAM.WExpr.lt
                                                      (Frontier.RAM.WExpr.var "fp.p")
                                                      (Frontier.RAM.WExpr.var "gM"))))))
                                            (Frontier.RAM.Stmt.while
                                              (Frontier.RAM.WExpr.var "fp.go")
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.wset
                                                  "fp.v"
                                                  (Frontier.RAM.WExpr.load "gHead" (Frontier.RAM.WExpr.var "fp.p")))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wset "ru" (Frontier.RAM.WExpr.var "fp.u"))
                                                  (Frontier.RAM.Stmt.seq
                                                    (Frontier.RAM.Stmt.wset "re" (Frontier.RAM.WExpr.var "fp.p"))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.vset
                                                            "lab.xl"
                                                            (Frontier.RAM.VExpr.add
                                                              (Frontier.RAM.VExpr.load
                                                                "dlen"
                                                                (Frontier.RAM.WExpr.var "ru"))
                                                              (Frontier.RAM.VExpr.load
                                                                "gW"
                                                                (Frontier.RAM.WExpr.var "re"))))
                                                          (Frontier.RAM.Stmt.seq
                                                            (Frontier.RAM.Stmt.wset
                                                              "lab.xh"
                                                              (Frontier.RAM.WExpr.add
                                                                (Frontier.RAM.WExpr.load
                                                                  "dhops"
                                                                  (Frontier.RAM.WExpr.var "ru"))
                                                                (Frontier.RAM.WExpr.lit 1)))
                                                            (Frontier.RAM.Stmt.seq
                                                              (Frontier.RAM.Stmt.wset
                                                                "lab.xv"
                                                                (Frontier.RAM.WExpr.load
                                                                  "gHead"
                                                                  (Frontier.RAM.WExpr.var "re")))
                                                              (Frontier.RAM.Stmt.seq
                                                                (Frontier.RAM.Stmt.wset
                                                                  "lab.xe"
                                                                  (Frontier.RAM.WExpr.add
                                                                    (Frontier.RAM.WExpr.var "re")
                                                                    (Frontier.RAM.WExpr.lit 1)))
                                                                (Frontier.RAM.Stmt.wset
                                                                  "lab.xr"
                                                                  (Frontier.RAM.WExpr.load
                                                                    "vcnt"
                                                                    (Frontier.RAM.WExpr.var "ru")))))))
                                                        (Frontier.RAM.Stmt.ite
                                                          (Frontier.RAM.WExpr.var "fp.B#f")
                                                          (Frontier.RAM.Stmt.seq
                                                            (Frontier.RAM.Stmt.vle
                                                              "lab.c1"
                                                              (Frontier.RAM.VExpr.var "lab.xl")
                                                              (Frontier.RAM.VExpr.var "fp.B#l"))
                                                            (Frontier.RAM.Stmt.seq
                                                              (Frontier.RAM.Stmt.vle
                                                                "lab.c2"
                                                                (Frontier.RAM.VExpr.var "fp.B#l")
                                                                (Frontier.RAM.VExpr.var "lab.xl"))
                                                              (Frontier.RAM.Stmt.ite
                                                                (Frontier.RAM.WExpr.var "lab.c2")
                                                                (Frontier.RAM.Stmt.ite
                                                                  (Frontier.RAM.WExpr.var "lab.c1")
                                                                  (Frontier.RAM.Stmt.ite
                                                                    (Frontier.RAM.WExpr.lt
                                                                      (Frontier.RAM.WExpr.var "lab.xh")
                                                                      (Frontier.RAM.WExpr.var "fp.B#h"))
                                                                    (Frontier.RAM.Stmt.wset
                                                                      "lab.bit"
                                                                      (Frontier.RAM.WExpr.lit 1))
                                                                    (Frontier.RAM.Stmt.ite
                                                                      (Frontier.RAM.WExpr.lt
                                                                        (Frontier.RAM.WExpr.var "fp.B#h")
                                                                        (Frontier.RAM.WExpr.var "lab.xh"))
                                                                      (Frontier.RAM.Stmt.wset
                                                                        "lab.bit"
                                                                        (Frontier.RAM.WExpr.lit 0))
                                                                      (Frontier.RAM.Stmt.ite
                                                                        (Frontier.RAM.WExpr.lt
                                                                          (Frontier.RAM.WExpr.var "lab.xv")
                                                                          (Frontier.RAM.WExpr.var "fp.B#v"))
                                                                        (Frontier.RAM.Stmt.wset
                                                                          "lab.bit"
                                                                          (Frontier.RAM.WExpr.lit 1))
                                                                        (Frontier.RAM.Stmt.ite
                                                                          (Frontier.RAM.WExpr.lt
                                                                            (Frontier.RAM.WExpr.var "fp.B#v")
                                                                            (Frontier.RAM.WExpr.var "lab.xv"))
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "lab.bit"
                                                                            (Frontier.RAM.WExpr.lit 0))
                                                                          (Frontier.RAM.Stmt.ite
                                                                            (Frontier.RAM.WExpr.lt
                                                                              (Frontier.RAM.WExpr.var "lab.xe")
                                                                              (Frontier.RAM.WExpr.var "fp.B#e"))
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "lab.bit"
                                                                              (Frontier.RAM.WExpr.lit 1))
                                                                            (Frontier.RAM.Stmt.ite
                                                                              (Frontier.RAM.WExpr.lt
                                                                                (Frontier.RAM.WExpr.var "fp.B#e")
                                                                                (Frontier.RAM.WExpr.var "lab.xe"))
                                                                              (Frontier.RAM.Stmt.wset
                                                                                "lab.bit"
                                                                                (Frontier.RAM.WExpr.lit 0))
                                                                              (Frontier.RAM.Stmt.ite
                                                                                (Frontier.RAM.WExpr.lt
                                                                                  (Frontier.RAM.WExpr.var "fp.B#r")
                                                                                  (Frontier.RAM.WExpr.var "lab.xr"))
                                                                                (Frontier.RAM.Stmt.wset
                                                                                  "lab.bit"
                                                                                  (Frontier.RAM.WExpr.lit 1))
                                                                                (Frontier.RAM.Stmt.wset
                                                                                  "lab.bit"
                                                                                  (Frontier.RAM.WExpr.lit 0)))))))))
                                                                  (Frontier.RAM.Stmt.wset
                                                                    "lab.bit"
                                                                    (Frontier.RAM.WExpr.lit 0)))
                                                                (Frontier.RAM.Stmt.wset
                                                                  "lab.bit"
                                                                  (Frontier.RAM.WExpr.lit 1)))))
                                                          (Frontier.RAM.Stmt.wset "lab.bit" (Frontier.RAM.WExpr.lit 1))))
                                                      (Frontier.RAM.Stmt.ite
                                                        (Frontier.RAM.WExpr.var "lab.bit")
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.wset
                                                            "lab.rv"
                                                            (Frontier.RAM.WExpr.var "fp.v"))
                                                          (Frontier.RAM.Stmt.seq
                                                            (Frontier.RAM.Stmt.seq
                                                              (Frontier.RAM.Stmt.seq
                                                                (Frontier.RAM.Stmt.vset
                                                                  "lab.yl"
                                                                  (Frontier.RAM.VExpr.load
                                                                    "dlen"
                                                                    (Frontier.RAM.WExpr.var "lab.rv")))
                                                                (Frontier.RAM.Stmt.seq
                                                                  (Frontier.RAM.Stmt.wset
                                                                    "lab.yh"
                                                                    (Frontier.RAM.WExpr.load
                                                                      "dhops"
                                                                      (Frontier.RAM.WExpr.var "lab.rv")))
                                                                  (Frontier.RAM.Stmt.seq
                                                                    (Frontier.RAM.Stmt.wset
                                                                      "lab.ye"
                                                                      (Frontier.RAM.WExpr.load
                                                                        "de"
                                                                        (Frontier.RAM.WExpr.var "lab.rv")))
                                                                    (Frontier.RAM.Stmt.seq
                                                                      (Frontier.RAM.Stmt.wset
                                                                        "lab.yr"
                                                                        (Frontier.RAM.WExpr.load
                                                                          "dver"
                                                                          (Frontier.RAM.WExpr.var "lab.rv")))
                                                                      (Frontier.RAM.Stmt.seq
                                                                        (Frontier.RAM.Stmt.wset
                                                                          "lab.yf"
                                                                          (Frontier.RAM.WExpr.load
                                                                            "dfin"
                                                                            (Frontier.RAM.WExpr.var "lab.rv")))
                                                                        (Frontier.RAM.Stmt.wset
                                                                          "lab.yv"
                                                                          (Frontier.RAM.WExpr.var "lab.rv")))))))
                                                              (Frontier.RAM.Stmt.ite
                                                                (Frontier.RAM.WExpr.var "lab.yf")
                                                                (Frontier.RAM.Stmt.ite
                                                                  (Frontier.RAM.WExpr.var "fp.LX#f")
                                                                  (Frontier.RAM.Stmt.seq
                                                                    (Frontier.RAM.Stmt.vle
                                                                      "lab.c1"
                                                                      (Frontier.RAM.VExpr.var "lab.yl")
                                                                      (Frontier.RAM.VExpr.var "fp.LX#l"))
                                                                    (Frontier.RAM.Stmt.seq
                                                                      (Frontier.RAM.Stmt.vle
                                                                        "lab.c2"
                                                                        (Frontier.RAM.VExpr.var "fp.LX#l")
                                                                        (Frontier.RAM.VExpr.var "lab.yl"))
                                                                      (Frontier.RAM.Stmt.ite
                                                                        (Frontier.RAM.WExpr.var "lab.c2")
                                                                        (Frontier.RAM.Stmt.ite
                                                                          (Frontier.RAM.WExpr.var "lab.c1")
                                                                          (Frontier.RAM.Stmt.ite
                                                                            (Frontier.RAM.WExpr.lt
                                                                              (Frontier.RAM.WExpr.var "lab.yh")
                                                                              (Frontier.RAM.WExpr.var "fp.LX#h"))
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "lab.bit"
                                                                              (Frontier.RAM.WExpr.lit 1))
                                                                            (Frontier.RAM.Stmt.ite
                                                                              (Frontier.RAM.WExpr.lt
                                                                                (Frontier.RAM.WExpr.var "fp.LX#h")
                                                                                (Frontier.RAM.WExpr.var "lab.yh"))
                                                                              (Frontier.RAM.Stmt.wset
                                                                                "lab.bit"
                                                                                (Frontier.RAM.WExpr.lit 0))
                                                                              (Frontier.RAM.Stmt.ite
                                                                                (Frontier.RAM.WExpr.lt
                                                                                  (Frontier.RAM.WExpr.var "lab.yv")
                                                                                  (Frontier.RAM.WExpr.var "fp.LX#v"))
                                                                                (Frontier.RAM.Stmt.wset
                                                                                  "lab.bit"
                                                                                  (Frontier.RAM.WExpr.lit 1))
                                                                                (Frontier.RAM.Stmt.ite
                                                                                  (Frontier.RAM.WExpr.lt
                                                                                    (Frontier.RAM.WExpr.var "fp.LX#v")
                                                                                    (Frontier.RAM.WExpr.var "lab.yv"))
                                                                                  (Frontier.RAM.Stmt.wset
                                                                                    "lab.bit"
                                                                                    (Frontier.RAM.WExpr.lit 0))
                                                                                  (Frontier.RAM.Stmt.ite
                                                                                    (Frontier.RAM.WExpr.lt
                                                                                      (Frontier.RAM.WExpr.var "lab.ye")
                                                                                      (Frontier.RAM.WExpr.var "fp.LX#e"))
                                                                                    (Frontier.RAM.Stmt.wset
                                                                                      "lab.bit"
                                                                                      (Frontier.RAM.WExpr.lit 1))
                                                                                    (Frontier.RAM.Stmt.ite
                                                                                      (Frontier.RAM.WExpr.lt
                                                                                        (Frontier.RAM.WExpr.var "fp.LX#e")
                                                                                        (Frontier.RAM.WExpr.var "lab.ye"))
                                                                                      (Frontier.RAM.Stmt.wset
                                                                                        "lab.bit"
                                                                                        (Frontier.RAM.WExpr.lit 0))
                                                                                      (Frontier.RAM.Stmt.ite
                                                                                        (Frontier.RAM.WExpr.lt
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "fp.LX#r")
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.yr"))
                                                                                        (Frontier.RAM.Stmt.wset
                                                                                          "lab.bit"
                                                                                          (Frontier.RAM.WExpr.lit 1))
                                                                                        (Frontier.RAM.Stmt.wset
                                                                                          "lab.bit"
                                                                                          (Frontier.RAM.WExpr.lit
                                                                                            0)))))))))
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "lab.bit"
                                                                            (Frontier.RAM.WExpr.lit 0)))
                                                                        (Frontier.RAM.Stmt.wset
                                                                          "lab.bit"
                                                                          (Frontier.RAM.WExpr.lit 1)))))
                                                                  (Frontier.RAM.Stmt.wset
                                                                    "lab.bit"
                                                                    (Frontier.RAM.WExpr.lit 1)))
                                                                (Frontier.RAM.Stmt.wset
                                                                  "lab.bit"
                                                                  (Frontier.RAM.WExpr.lit 0))))
                                                            (Frontier.RAM.Stmt.ite
                                                              (Frontier.RAM.WExpr.var "lab.bit")
                                                              (Frontier.RAM.Stmt.seq
                                                                (Frontier.RAM.Stmt.ite
                                                                  (Frontier.RAM.WExpr.eq
                                                                    (Frontier.RAM.WExpr.var "fp.pp")
                                                                    (Frontier.RAM.WExpr.var "gM"))
                                                                  (Frontier.RAM.Stmt.wstore
                                                                    "gHd"
                                                                    (Frontier.RAM.WExpr.var "fp.u")
                                                                    (Frontier.RAM.WExpr.load
                                                                      "gNxt"
                                                                      (Frontier.RAM.WExpr.var "fp.p")))
                                                                  (Frontier.RAM.Stmt.wstore
                                                                    "gNxt"
                                                                    (Frontier.RAM.WExpr.var "fp.pp")
                                                                    (Frontier.RAM.WExpr.load
                                                                      "gNxt"
                                                                      (Frontier.RAM.WExpr.var "fp.p"))))
                                                                (Frontier.RAM.Stmt.seq
                                                                  (Frontier.RAM.Stmt.wset
                                                                    "fp.p"
                                                                    (Frontier.RAM.WExpr.load
                                                                      "gNxt"
                                                                      (Frontier.RAM.WExpr.var "fp.p")))
                                                                  (Frontier.RAM.Stmt.wset
                                                                    "fp.go"
                                                                    (Frontier.RAM.WExpr.lt
                                                                      (Frontier.RAM.WExpr.var "fp.p")
                                                                      (Frontier.RAM.WExpr.var "gM")))))
                                                              (Frontier.RAM.Stmt.ite
                                                                (Frontier.RAM.WExpr.load
                                                                  "fp.fm"
                                                                  (Frontier.RAM.WExpr.var "fp.v"))
                                                                (Frontier.RAM.Stmt.seq
                                                                  (Frontier.RAM.Stmt.seq
                                                                    (Frontier.RAM.Stmt.seq
                                                                      (Frontier.RAM.Stmt.vset
                                                                        "lab.yl"
                                                                        (Frontier.RAM.VExpr.load
                                                                          "dlen"
                                                                          (Frontier.RAM.WExpr.var "lab.xv")))
                                                                      (Frontier.RAM.Stmt.seq
                                                                        (Frontier.RAM.Stmt.wset
                                                                          "lab.yh"
                                                                          (Frontier.RAM.WExpr.load
                                                                            "dhops"
                                                                            (Frontier.RAM.WExpr.var "lab.xv")))
                                                                        (Frontier.RAM.Stmt.seq
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "lab.ye"
                                                                            (Frontier.RAM.WExpr.load
                                                                              "de"
                                                                              (Frontier.RAM.WExpr.var "lab.xv")))
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "lab.yr"
                                                                              (Frontier.RAM.WExpr.load
                                                                                "dver"
                                                                                (Frontier.RAM.WExpr.var "lab.xv")))
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.wset
                                                                                "lab.yf"
                                                                                (Frontier.RAM.WExpr.load
                                                                                  "dfin"
                                                                                  (Frontier.RAM.WExpr.var "lab.xv")))
                                                                              (Frontier.RAM.Stmt.wset
                                                                                "lab.yv"
                                                                                (Frontier.RAM.WExpr.var "lab.xv")))))))
                                                                    (Frontier.RAM.Stmt.seq
                                                                      (Frontier.RAM.Stmt.ite
                                                                        (Frontier.RAM.WExpr.var "lab.yf")
                                                                        (Frontier.RAM.Stmt.seq
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.vle
                                                                              "lab.c1"
                                                                              (Frontier.RAM.VExpr.var "lab.xl")
                                                                              (Frontier.RAM.VExpr.var "lab.yl"))
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.vle
                                                                                "lab.c2"
                                                                                (Frontier.RAM.VExpr.var "lab.yl")
                                                                                (Frontier.RAM.VExpr.var "lab.xl"))
                                                                              (Frontier.RAM.Stmt.ite
                                                                                (Frontier.RAM.WExpr.var "lab.c2")
                                                                                (Frontier.RAM.Stmt.ite
                                                                                  (Frontier.RAM.WExpr.var "lab.c1")
                                                                                  (Frontier.RAM.Stmt.ite
                                                                                    (Frontier.RAM.WExpr.lt
                                                                                      (Frontier.RAM.WExpr.var "lab.xh")
                                                                                      (Frontier.RAM.WExpr.var "lab.yh"))
                                                                                    (Frontier.RAM.Stmt.wset
                                                                                      "lab.lt"
                                                                                      (Frontier.RAM.WExpr.lit 1))
                                                                                    (Frontier.RAM.Stmt.ite
                                                                                      (Frontier.RAM.WExpr.lt
                                                                                        (Frontier.RAM.WExpr.var "lab.yh")
                                                                                        (Frontier.RAM.WExpr.var "lab.xh"))
                                                                                      (Frontier.RAM.Stmt.wset
                                                                                        "lab.lt"
                                                                                        (Frontier.RAM.WExpr.lit 0))
                                                                                      (Frontier.RAM.Stmt.ite
                                                                                        (Frontier.RAM.WExpr.lt
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.xv")
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.yv"))
                                                                                        (Frontier.RAM.Stmt.wset
                                                                                          "lab.lt"
                                                                                          (Frontier.RAM.WExpr.lit 1))
                                                                                        (Frontier.RAM.Stmt.ite
                                                                                          (Frontier.RAM.WExpr.lt
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.yv")
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.xv"))
                                                                                          (Frontier.RAM.Stmt.wset
                                                                                            "lab.lt"
                                                                                            (Frontier.RAM.WExpr.lit 0))
                                                                                          (Frontier.RAM.Stmt.ite
                                                                                            (Frontier.RAM.WExpr.lt
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.xe")
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.ye"))
                                                                                            (Frontier.RAM.Stmt.wset
                                                                                              "lab.lt"
                                                                                              (Frontier.RAM.WExpr.lit 1))
                                                                                            (Frontier.RAM.Stmt.ite
                                                                                              (Frontier.RAM.WExpr.lt
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.ye")
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.xe"))
                                                                                              (Frontier.RAM.Stmt.wset
                                                                                                "lab.lt"
                                                                                                (Frontier.RAM.WExpr.lit
                                                                                                  0))
                                                                                              (Frontier.RAM.Stmt.ite
                                                                                                (Frontier.RAM.WExpr.lt
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.yr")
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.xr"))
                                                                                                (Frontier.RAM.Stmt.wset
                                                                                                  "lab.lt"
                                                                                                  (Frontier.RAM.WExpr.lit
                                                                                                    1))
                                                                                                (Frontier.RAM.Stmt.wset
                                                                                                  "lab.lt"
                                                                                                  (Frontier.RAM.WExpr.lit
                                                                                                    0)))))))))
                                                                                  (Frontier.RAM.Stmt.wset
                                                                                    "lab.lt"
                                                                                    (Frontier.RAM.WExpr.lit 0)))
                                                                                (Frontier.RAM.Stmt.wset
                                                                                  "lab.lt"
                                                                                  (Frontier.RAM.WExpr.lit 1)))))
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.vle
                                                                              "lab.c1"
                                                                              (Frontier.RAM.VExpr.var "lab.yl")
                                                                              (Frontier.RAM.VExpr.var "lab.xl"))
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.vle
                                                                                "lab.c2"
                                                                                (Frontier.RAM.VExpr.var "lab.xl")
                                                                                (Frontier.RAM.VExpr.var "lab.yl"))
                                                                              (Frontier.RAM.Stmt.ite
                                                                                (Frontier.RAM.WExpr.var "lab.c2")
                                                                                (Frontier.RAM.Stmt.ite
                                                                                  (Frontier.RAM.WExpr.var "lab.c1")
                                                                                  (Frontier.RAM.Stmt.ite
                                                                                    (Frontier.RAM.WExpr.lt
                                                                                      (Frontier.RAM.WExpr.var "lab.yh")
                                                                                      (Frontier.RAM.WExpr.var "lab.xh"))
                                                                                    (Frontier.RAM.Stmt.wset
                                                                                      "lab.gt"
                                                                                      (Frontier.RAM.WExpr.lit 1))
                                                                                    (Frontier.RAM.Stmt.ite
                                                                                      (Frontier.RAM.WExpr.lt
                                                                                        (Frontier.RAM.WExpr.var "lab.xh")
                                                                                        (Frontier.RAM.WExpr.var "lab.yh"))
                                                                                      (Frontier.RAM.Stmt.wset
                                                                                        "lab.gt"
                                                                                        (Frontier.RAM.WExpr.lit 0))
                                                                                      (Frontier.RAM.Stmt.ite
                                                                                        (Frontier.RAM.WExpr.lt
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.yv")
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.xv"))
                                                                                        (Frontier.RAM.Stmt.wset
                                                                                          "lab.gt"
                                                                                          (Frontier.RAM.WExpr.lit 1))
                                                                                        (Frontier.RAM.Stmt.ite
                                                                                          (Frontier.RAM.WExpr.lt
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.xv")
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.yv"))
                                                                                          (Frontier.RAM.Stmt.wset
                                                                                            "lab.gt"
                                                                                            (Frontier.RAM.WExpr.lit 0))
                                                                                          (Frontier.RAM.Stmt.ite
                                                                                            (Frontier.RAM.WExpr.lt
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.ye")
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.xe"))
                                                                                            (Frontier.RAM.Stmt.wset
                                                                                              "lab.gt"
                                                                                              (Frontier.RAM.WExpr.lit 1))
                                                                                            (Frontier.RAM.Stmt.ite
                                                                                              (Frontier.RAM.WExpr.lt
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.xe")
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.ye"))
                                                                                              (Frontier.RAM.Stmt.wset
                                                                                                "lab.gt"
                                                                                                (Frontier.RAM.WExpr.lit
                                                                                                  0))
                                                                                              (Frontier.RAM.Stmt.ite
                                                                                                (Frontier.RAM.WExpr.lt
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.xr")
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.yr"))
                                                                                                (Frontier.RAM.Stmt.wset
                                                                                                  "lab.gt"
                                                                                                  (Frontier.RAM.WExpr.lit
                                                                                                    1))
                                                                                                (Frontier.RAM.Stmt.wset
                                                                                                  "lab.gt"
                                                                                                  (Frontier.RAM.WExpr.lit
                                                                                                    0)))))))))
                                                                                  (Frontier.RAM.Stmt.wset
                                                                                    "lab.gt"
                                                                                    (Frontier.RAM.WExpr.lit 0)))
                                                                                (Frontier.RAM.Stmt.wset
                                                                                  "lab.gt"
                                                                                  (Frontier.RAM.WExpr.lit 1))))))
                                                                        (Frontier.RAM.Stmt.seq
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "lab.lt"
                                                                            (Frontier.RAM.WExpr.lit 1))
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "lab.gt"
                                                                            (Frontier.RAM.WExpr.lit 0))))
                                                                      (Frontier.RAM.Stmt.seq
                                                                        (Frontier.RAM.Stmt.wset
                                                                          "ok"
                                                                          (Frontier.RAM.WExpr.eq
                                                                            (Frontier.RAM.WExpr.var "lab.gt")
                                                                            (Frontier.RAM.WExpr.lit 0)))
                                                                        (Frontier.RAM.Stmt.ite
                                                                          (Frontier.RAM.WExpr.var "lab.lt")
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.vstore
                                                                              "dlen"
                                                                              (Frontier.RAM.WExpr.var "lab.xv")
                                                                              (Frontier.RAM.VExpr.var "lab.xl"))
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.wstore
                                                                                "dhops"
                                                                                (Frontier.RAM.WExpr.var "lab.xv")
                                                                                (Frontier.RAM.WExpr.var "lab.xh"))
                                                                              (Frontier.RAM.Stmt.seq
                                                                                (Frontier.RAM.Stmt.wstore
                                                                                  "de"
                                                                                  (Frontier.RAM.WExpr.var "lab.xv")
                                                                                  (Frontier.RAM.WExpr.var "lab.xe"))
                                                                                (Frontier.RAM.Stmt.seq
                                                                                  (Frontier.RAM.Stmt.wstore
                                                                                    "dver"
                                                                                    (Frontier.RAM.WExpr.var "lab.xv")
                                                                                    (Frontier.RAM.WExpr.var "lab.xr"))
                                                                                  (Frontier.RAM.Stmt.seq
                                                                                    (Frontier.RAM.Stmt.wstore
                                                                                      "dfin"
                                                                                      (Frontier.RAM.WExpr.var "lab.xv")
                                                                                      (Frontier.RAM.WExpr.lit 1))
                                                                                    (Frontier.RAM.Stmt.wstore
                                                                                      "vcnt"
                                                                                      (Frontier.RAM.WExpr.var "lab.xv")
                                                                                      (Frontier.RAM.WExpr.add
                                                                                        (Frontier.RAM.WExpr.load
                                                                                          "vcnt"
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.xv"))
                                                                                        (Frontier.RAM.WExpr.lit 1))))))))
                                                                          (Frontier.RAM.Stmt.skip)))))
                                                                  (Frontier.RAM.Stmt.seq
                                                                    (Frontier.RAM.Stmt.wset
                                                                      "fp.cu"
                                                                      (Frontier.RAM.WExpr.var "fp.u"))
                                                                    (Frontier.RAM.Stmt.seq
                                                                      (Frontier.RAM.Stmt.wset
                                                                        "fp.cv"
                                                                        (Frontier.RAM.WExpr.var "fp.v"))
                                                                      (Frontier.RAM.Stmt.seq
                                                                        (Frontier.RAM.Stmt.wset
                                                                          "fp.res"
                                                                          (Frontier.RAM.WExpr.lit 2))
                                                                        (Frontier.RAM.Stmt.wset
                                                                          "fp.go"
                                                                          (Frontier.RAM.WExpr.lit 0))))))
                                                                (Frontier.RAM.Stmt.ite
                                                                  (Frontier.RAM.WExpr.load
                                                                    "fp.inK"
                                                                    (Frontier.RAM.WExpr.var "fp.v"))
                                                                  (Frontier.RAM.Stmt.seq
                                                                    (Frontier.RAM.Stmt.seq
                                                                      (Frontier.RAM.Stmt.seq
                                                                        (Frontier.RAM.Stmt.vset
                                                                          "lab.yl"
                                                                          (Frontier.RAM.VExpr.load
                                                                            "dlen"
                                                                            (Frontier.RAM.WExpr.var "lab.xv")))
                                                                        (Frontier.RAM.Stmt.seq
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "lab.yh"
                                                                            (Frontier.RAM.WExpr.load
                                                                              "dhops"
                                                                              (Frontier.RAM.WExpr.var "lab.xv")))
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "lab.ye"
                                                                              (Frontier.RAM.WExpr.load
                                                                                "de"
                                                                                (Frontier.RAM.WExpr.var "lab.xv")))
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.wset
                                                                                "lab.yr"
                                                                                (Frontier.RAM.WExpr.load
                                                                                  "dver"
                                                                                  (Frontier.RAM.WExpr.var "lab.xv")))
                                                                              (Frontier.RAM.Stmt.seq
                                                                                (Frontier.RAM.Stmt.wset
                                                                                  "lab.yf"
                                                                                  (Frontier.RAM.WExpr.load
                                                                                    "dfin"
                                                                                    (Frontier.RAM.WExpr.var "lab.xv")))
                                                                                (Frontier.RAM.Stmt.wset
                                                                                  "lab.yv"
                                                                                  (Frontier.RAM.WExpr.var "lab.xv")))))))
                                                                      (Frontier.RAM.Stmt.seq
                                                                        (Frontier.RAM.Stmt.ite
                                                                          (Frontier.RAM.WExpr.var "lab.yf")
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.vle
                                                                                "lab.c1"
                                                                                (Frontier.RAM.VExpr.var "lab.xl")
                                                                                (Frontier.RAM.VExpr.var "lab.yl"))
                                                                              (Frontier.RAM.Stmt.seq
                                                                                (Frontier.RAM.Stmt.vle
                                                                                  "lab.c2"
                                                                                  (Frontier.RAM.VExpr.var "lab.yl")
                                                                                  (Frontier.RAM.VExpr.var "lab.xl"))
                                                                                (Frontier.RAM.Stmt.ite
                                                                                  (Frontier.RAM.WExpr.var "lab.c2")
                                                                                  (Frontier.RAM.Stmt.ite
                                                                                    (Frontier.RAM.WExpr.var "lab.c1")
                                                                                    (Frontier.RAM.Stmt.ite
                                                                                      (Frontier.RAM.WExpr.lt
                                                                                        (Frontier.RAM.WExpr.var "lab.xh")
                                                                                        (Frontier.RAM.WExpr.var "lab.yh"))
                                                                                      (Frontier.RAM.Stmt.wset
                                                                                        "lab.lt"
                                                                                        (Frontier.RAM.WExpr.lit 1))
                                                                                      (Frontier.RAM.Stmt.ite
                                                                                        (Frontier.RAM.WExpr.lt
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.yh")
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.xh"))
                                                                                        (Frontier.RAM.Stmt.wset
                                                                                          "lab.lt"
                                                                                          (Frontier.RAM.WExpr.lit 0))
                                                                                        (Frontier.RAM.Stmt.ite
                                                                                          (Frontier.RAM.WExpr.lt
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.xv")
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.yv"))
                                                                                          (Frontier.RAM.Stmt.wset
                                                                                            "lab.lt"
                                                                                            (Frontier.RAM.WExpr.lit 1))
                                                                                          (Frontier.RAM.Stmt.ite
                                                                                            (Frontier.RAM.WExpr.lt
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.yv")
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.xv"))
                                                                                            (Frontier.RAM.Stmt.wset
                                                                                              "lab.lt"
                                                                                              (Frontier.RAM.WExpr.lit 0))
                                                                                            (Frontier.RAM.Stmt.ite
                                                                                              (Frontier.RAM.WExpr.lt
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.xe")
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.ye"))
                                                                                              (Frontier.RAM.Stmt.wset
                                                                                                "lab.lt"
                                                                                                (Frontier.RAM.WExpr.lit
                                                                                                  1))
                                                                                              (Frontier.RAM.Stmt.ite
                                                                                                (Frontier.RAM.WExpr.lt
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.ye")
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.xe"))
                                                                                                (Frontier.RAM.Stmt.wset
                                                                                                  "lab.lt"
                                                                                                  (Frontier.RAM.WExpr.lit
                                                                                                    0))
                                                                                                (Frontier.RAM.Stmt.ite
                                                                                                  (Frontier.RAM.WExpr.lt
                                                                                                    (Frontier.RAM.WExpr.var
                                                                                                      "lab.yr")
                                                                                                    (Frontier.RAM.WExpr.var
                                                                                                      "lab.xr"))
                                                                                                  (Frontier.RAM.Stmt.wset
                                                                                                    "lab.lt"
                                                                                                    (Frontier.RAM.WExpr.lit
                                                                                                      1))
                                                                                                  (Frontier.RAM.Stmt.wset
                                                                                                    "lab.lt"
                                                                                                    (Frontier.RAM.WExpr.lit
                                                                                                      0)))))))))
                                                                                    (Frontier.RAM.Stmt.wset
                                                                                      "lab.lt"
                                                                                      (Frontier.RAM.WExpr.lit 0)))
                                                                                  (Frontier.RAM.Stmt.wset
                                                                                    "lab.lt"
                                                                                    (Frontier.RAM.WExpr.lit 1)))))
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.vle
                                                                                "lab.c1"
                                                                                (Frontier.RAM.VExpr.var "lab.yl")
                                                                                (Frontier.RAM.VExpr.var "lab.xl"))
                                                                              (Frontier.RAM.Stmt.seq
                                                                                (Frontier.RAM.Stmt.vle
                                                                                  "lab.c2"
                                                                                  (Frontier.RAM.VExpr.var "lab.xl")
                                                                                  (Frontier.RAM.VExpr.var "lab.yl"))
                                                                                (Frontier.RAM.Stmt.ite
                                                                                  (Frontier.RAM.WExpr.var "lab.c2")
                                                                                  (Frontier.RAM.Stmt.ite
                                                                                    (Frontier.RAM.WExpr.var "lab.c1")
                                                                                    (Frontier.RAM.Stmt.ite
                                                                                      (Frontier.RAM.WExpr.lt
                                                                                        (Frontier.RAM.WExpr.var "lab.yh")
                                                                                        (Frontier.RAM.WExpr.var "lab.xh"))
                                                                                      (Frontier.RAM.Stmt.wset
                                                                                        "lab.gt"
                                                                                        (Frontier.RAM.WExpr.lit 1))
                                                                                      (Frontier.RAM.Stmt.ite
                                                                                        (Frontier.RAM.WExpr.lt
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.xh")
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.yh"))
                                                                                        (Frontier.RAM.Stmt.wset
                                                                                          "lab.gt"
                                                                                          (Frontier.RAM.WExpr.lit 0))
                                                                                        (Frontier.RAM.Stmt.ite
                                                                                          (Frontier.RAM.WExpr.lt
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.yv")
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.xv"))
                                                                                          (Frontier.RAM.Stmt.wset
                                                                                            "lab.gt"
                                                                                            (Frontier.RAM.WExpr.lit 1))
                                                                                          (Frontier.RAM.Stmt.ite
                                                                                            (Frontier.RAM.WExpr.lt
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.xv")
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.yv"))
                                                                                            (Frontier.RAM.Stmt.wset
                                                                                              "lab.gt"
                                                                                              (Frontier.RAM.WExpr.lit 0))
                                                                                            (Frontier.RAM.Stmt.ite
                                                                                              (Frontier.RAM.WExpr.lt
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.ye")
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.xe"))
                                                                                              (Frontier.RAM.Stmt.wset
                                                                                                "lab.gt"
                                                                                                (Frontier.RAM.WExpr.lit
                                                                                                  1))
                                                                                              (Frontier.RAM.Stmt.ite
                                                                                                (Frontier.RAM.WExpr.lt
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.xe")
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.ye"))
                                                                                                (Frontier.RAM.Stmt.wset
                                                                                                  "lab.gt"
                                                                                                  (Frontier.RAM.WExpr.lit
                                                                                                    0))
                                                                                                (Frontier.RAM.Stmt.ite
                                                                                                  (Frontier.RAM.WExpr.lt
                                                                                                    (Frontier.RAM.WExpr.var
                                                                                                      "lab.xr")
                                                                                                    (Frontier.RAM.WExpr.var
                                                                                                      "lab.yr"))
                                                                                                  (Frontier.RAM.Stmt.wset
                                                                                                    "lab.gt"
                                                                                                    (Frontier.RAM.WExpr.lit
                                                                                                      1))
                                                                                                  (Frontier.RAM.Stmt.wset
                                                                                                    "lab.gt"
                                                                                                    (Frontier.RAM.WExpr.lit
                                                                                                      0)))))))))
                                                                                    (Frontier.RAM.Stmt.wset
                                                                                      "lab.gt"
                                                                                      (Frontier.RAM.WExpr.lit 0)))
                                                                                  (Frontier.RAM.Stmt.wset
                                                                                    "lab.gt"
                                                                                    (Frontier.RAM.WExpr.lit 1))))))
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "lab.lt"
                                                                              (Frontier.RAM.WExpr.lit 1))
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "lab.gt"
                                                                              (Frontier.RAM.WExpr.lit 0))))
                                                                        (Frontier.RAM.Stmt.seq
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "ok"
                                                                            (Frontier.RAM.WExpr.eq
                                                                              (Frontier.RAM.WExpr.var "lab.gt")
                                                                              (Frontier.RAM.WExpr.lit 0)))
                                                                          (Frontier.RAM.Stmt.ite
                                                                            (Frontier.RAM.WExpr.var "lab.lt")
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.vstore
                                                                                "dlen"
                                                                                (Frontier.RAM.WExpr.var "lab.xv")
                                                                                (Frontier.RAM.VExpr.var "lab.xl"))
                                                                              (Frontier.RAM.Stmt.seq
                                                                                (Frontier.RAM.Stmt.wstore
                                                                                  "dhops"
                                                                                  (Frontier.RAM.WExpr.var "lab.xv")
                                                                                  (Frontier.RAM.WExpr.var "lab.xh"))
                                                                                (Frontier.RAM.Stmt.seq
                                                                                  (Frontier.RAM.Stmt.wstore
                                                                                    "de"
                                                                                    (Frontier.RAM.WExpr.var "lab.xv")
                                                                                    (Frontier.RAM.WExpr.var "lab.xe"))
                                                                                  (Frontier.RAM.Stmt.seq
                                                                                    (Frontier.RAM.Stmt.wstore
                                                                                      "dver"
                                                                                      (Frontier.RAM.WExpr.var "lab.xv")
                                                                                      (Frontier.RAM.WExpr.var "lab.xr"))
                                                                                    (Frontier.RAM.Stmt.seq
                                                                                      (Frontier.RAM.Stmt.wstore
                                                                                        "dfin"
                                                                                        (Frontier.RAM.WExpr.var "lab.xv")
                                                                                        (Frontier.RAM.WExpr.lit 1))
                                                                                      (Frontier.RAM.Stmt.wstore
                                                                                        "vcnt"
                                                                                        (Frontier.RAM.WExpr.var "lab.xv")
                                                                                        (Frontier.RAM.WExpr.add
                                                                                          (Frontier.RAM.WExpr.load
                                                                                            "vcnt"
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.xv"))
                                                                                          (Frontier.RAM.WExpr.lit
                                                                                            1))))))))
                                                                            (Frontier.RAM.Stmt.skip)))))
                                                                    (Frontier.RAM.Stmt.seq
                                                                      (Frontier.RAM.Stmt.ite
                                                                        (Frontier.RAM.WExpr.var "ok")
                                                                        (Frontier.RAM.Stmt.seq
                                                                          (Frontier.RAM.Stmt.wstore
                                                                            "fp.val"
                                                                            (Frontier.RAM.WExpr.var "fp.v")
                                                                            (Frontier.RAM.WExpr.lit 1))
                                                                          (Frontier.RAM.Stmt.ite
                                                                            (Frontier.RAM.WExpr.load
                                                                              "fp.inH"
                                                                              (Frontier.RAM.WExpr.var "fp.v"))
                                                                            (Frontier.RAM.Stmt.skip)
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.wstore
                                                                                "fp.H"
                                                                                (Frontier.RAM.WExpr.var "fp.hsz")
                                                                                (Frontier.RAM.WExpr.var "fp.v"))
                                                                              (Frontier.RAM.Stmt.seq
                                                                                (Frontier.RAM.Stmt.wstore
                                                                                  "fp.hp"
                                                                                  (Frontier.RAM.WExpr.var "fp.v")
                                                                                  (Frontier.RAM.WExpr.var "fp.hsz"))
                                                                                (Frontier.RAM.Stmt.seq
                                                                                  (Frontier.RAM.Stmt.wstore
                                                                                    "fp.inH"
                                                                                    (Frontier.RAM.WExpr.var "fp.v")
                                                                                    (Frontier.RAM.WExpr.lit 1))
                                                                                  (Frontier.RAM.Stmt.wset
                                                                                    "fp.hsz"
                                                                                    (Frontier.RAM.WExpr.add
                                                                                      (Frontier.RAM.WExpr.var "fp.hsz")
                                                                                      (Frontier.RAM.WExpr.lit 1))))))))
                                                                        (Frontier.RAM.Stmt.skip))
                                                                      (Frontier.RAM.Stmt.seq
                                                                        (Frontier.RAM.Stmt.wset
                                                                          "fp.pp"
                                                                          (Frontier.RAM.WExpr.var "fp.p"))
                                                                        (Frontier.RAM.Stmt.seq
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "fp.p"
                                                                            (Frontier.RAM.WExpr.load
                                                                              "gNxt"
                                                                              (Frontier.RAM.WExpr.var "fp.p")))
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "fp.go"
                                                                            (Frontier.RAM.WExpr.lt
                                                                              (Frontier.RAM.WExpr.var "fp.p")
                                                                              (Frontier.RAM.WExpr.var "gM")))))))
                                                                  (Frontier.RAM.Stmt.seq
                                                                    (Frontier.RAM.Stmt.seq
                                                                      (Frontier.RAM.Stmt.seq
                                                                        (Frontier.RAM.Stmt.vset
                                                                          "lab.yl"
                                                                          (Frontier.RAM.VExpr.load
                                                                            "dlen"
                                                                            (Frontier.RAM.WExpr.var "lab.xv")))
                                                                        (Frontier.RAM.Stmt.seq
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "lab.yh"
                                                                            (Frontier.RAM.WExpr.load
                                                                              "dhops"
                                                                              (Frontier.RAM.WExpr.var "lab.xv")))
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "lab.ye"
                                                                              (Frontier.RAM.WExpr.load
                                                                                "de"
                                                                                (Frontier.RAM.WExpr.var "lab.xv")))
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.wset
                                                                                "lab.yr"
                                                                                (Frontier.RAM.WExpr.load
                                                                                  "dver"
                                                                                  (Frontier.RAM.WExpr.var "lab.xv")))
                                                                              (Frontier.RAM.Stmt.seq
                                                                                (Frontier.RAM.Stmt.wset
                                                                                  "lab.yf"
                                                                                  (Frontier.RAM.WExpr.load
                                                                                    "dfin"
                                                                                    (Frontier.RAM.WExpr.var "lab.xv")))
                                                                                (Frontier.RAM.Stmt.wset
                                                                                  "lab.yv"
                                                                                  (Frontier.RAM.WExpr.var "lab.xv")))))))
                                                                      (Frontier.RAM.Stmt.seq
                                                                        (Frontier.RAM.Stmt.ite
                                                                          (Frontier.RAM.WExpr.var "lab.yf")
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.vle
                                                                                "lab.c1"
                                                                                (Frontier.RAM.VExpr.var "lab.xl")
                                                                                (Frontier.RAM.VExpr.var "lab.yl"))
                                                                              (Frontier.RAM.Stmt.seq
                                                                                (Frontier.RAM.Stmt.vle
                                                                                  "lab.c2"
                                                                                  (Frontier.RAM.VExpr.var "lab.yl")
                                                                                  (Frontier.RAM.VExpr.var "lab.xl"))
                                                                                (Frontier.RAM.Stmt.ite
                                                                                  (Frontier.RAM.WExpr.var "lab.c2")
                                                                                  (Frontier.RAM.Stmt.ite
                                                                                    (Frontier.RAM.WExpr.var "lab.c1")
                                                                                    (Frontier.RAM.Stmt.ite
                                                                                      (Frontier.RAM.WExpr.lt
                                                                                        (Frontier.RAM.WExpr.var "lab.xh")
                                                                                        (Frontier.RAM.WExpr.var "lab.yh"))
                                                                                      (Frontier.RAM.Stmt.wset
                                                                                        "lab.lt"
                                                                                        (Frontier.RAM.WExpr.lit 1))
                                                                                      (Frontier.RAM.Stmt.ite
                                                                                        (Frontier.RAM.WExpr.lt
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.yh")
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.xh"))
                                                                                        (Frontier.RAM.Stmt.wset
                                                                                          "lab.lt"
                                                                                          (Frontier.RAM.WExpr.lit 0))
                                                                                        (Frontier.RAM.Stmt.ite
                                                                                          (Frontier.RAM.WExpr.lt
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.xv")
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.yv"))
                                                                                          (Frontier.RAM.Stmt.wset
                                                                                            "lab.lt"
                                                                                            (Frontier.RAM.WExpr.lit 1))
                                                                                          (Frontier.RAM.Stmt.ite
                                                                                            (Frontier.RAM.WExpr.lt
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.yv")
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.xv"))
                                                                                            (Frontier.RAM.Stmt.wset
                                                                                              "lab.lt"
                                                                                              (Frontier.RAM.WExpr.lit 0))
                                                                                            (Frontier.RAM.Stmt.ite
                                                                                              (Frontier.RAM.WExpr.lt
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.xe")
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.ye"))
                                                                                              (Frontier.RAM.Stmt.wset
                                                                                                "lab.lt"
                                                                                                (Frontier.RAM.WExpr.lit
                                                                                                  1))
                                                                                              (Frontier.RAM.Stmt.ite
                                                                                                (Frontier.RAM.WExpr.lt
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.ye")
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.xe"))
                                                                                                (Frontier.RAM.Stmt.wset
                                                                                                  "lab.lt"
                                                                                                  (Frontier.RAM.WExpr.lit
                                                                                                    0))
                                                                                                (Frontier.RAM.Stmt.ite
                                                                                                  (Frontier.RAM.WExpr.lt
                                                                                                    (Frontier.RAM.WExpr.var
                                                                                                      "lab.yr")
                                                                                                    (Frontier.RAM.WExpr.var
                                                                                                      "lab.xr"))
                                                                                                  (Frontier.RAM.Stmt.wset
                                                                                                    "lab.lt"
                                                                                                    (Frontier.RAM.WExpr.lit
                                                                                                      1))
                                                                                                  (Frontier.RAM.Stmt.wset
                                                                                                    "lab.lt"
                                                                                                    (Frontier.RAM.WExpr.lit
                                                                                                      0)))))))))
                                                                                    (Frontier.RAM.Stmt.wset
                                                                                      "lab.lt"
                                                                                      (Frontier.RAM.WExpr.lit 0)))
                                                                                  (Frontier.RAM.Stmt.wset
                                                                                    "lab.lt"
                                                                                    (Frontier.RAM.WExpr.lit 1)))))
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.vle
                                                                                "lab.c1"
                                                                                (Frontier.RAM.VExpr.var "lab.yl")
                                                                                (Frontier.RAM.VExpr.var "lab.xl"))
                                                                              (Frontier.RAM.Stmt.seq
                                                                                (Frontier.RAM.Stmt.vle
                                                                                  "lab.c2"
                                                                                  (Frontier.RAM.VExpr.var "lab.xl")
                                                                                  (Frontier.RAM.VExpr.var "lab.yl"))
                                                                                (Frontier.RAM.Stmt.ite
                                                                                  (Frontier.RAM.WExpr.var "lab.c2")
                                                                                  (Frontier.RAM.Stmt.ite
                                                                                    (Frontier.RAM.WExpr.var "lab.c1")
                                                                                    (Frontier.RAM.Stmt.ite
                                                                                      (Frontier.RAM.WExpr.lt
                                                                                        (Frontier.RAM.WExpr.var "lab.yh")
                                                                                        (Frontier.RAM.WExpr.var "lab.xh"))
                                                                                      (Frontier.RAM.Stmt.wset
                                                                                        "lab.gt"
                                                                                        (Frontier.RAM.WExpr.lit 1))
                                                                                      (Frontier.RAM.Stmt.ite
                                                                                        (Frontier.RAM.WExpr.lt
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.xh")
                                                                                          (Frontier.RAM.WExpr.var
                                                                                            "lab.yh"))
                                                                                        (Frontier.RAM.Stmt.wset
                                                                                          "lab.gt"
                                                                                          (Frontier.RAM.WExpr.lit 0))
                                                                                        (Frontier.RAM.Stmt.ite
                                                                                          (Frontier.RAM.WExpr.lt
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.yv")
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.xv"))
                                                                                          (Frontier.RAM.Stmt.wset
                                                                                            "lab.gt"
                                                                                            (Frontier.RAM.WExpr.lit 1))
                                                                                          (Frontier.RAM.Stmt.ite
                                                                                            (Frontier.RAM.WExpr.lt
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.xv")
                                                                                              (Frontier.RAM.WExpr.var
                                                                                                "lab.yv"))
                                                                                            (Frontier.RAM.Stmt.wset
                                                                                              "lab.gt"
                                                                                              (Frontier.RAM.WExpr.lit 0))
                                                                                            (Frontier.RAM.Stmt.ite
                                                                                              (Frontier.RAM.WExpr.lt
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.ye")
                                                                                                (Frontier.RAM.WExpr.var
                                                                                                  "lab.xe"))
                                                                                              (Frontier.RAM.Stmt.wset
                                                                                                "lab.gt"
                                                                                                (Frontier.RAM.WExpr.lit
                                                                                                  1))
                                                                                              (Frontier.RAM.Stmt.ite
                                                                                                (Frontier.RAM.WExpr.lt
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.xe")
                                                                                                  (Frontier.RAM.WExpr.var
                                                                                                    "lab.ye"))
                                                                                                (Frontier.RAM.Stmt.wset
                                                                                                  "lab.gt"
                                                                                                  (Frontier.RAM.WExpr.lit
                                                                                                    0))
                                                                                                (Frontier.RAM.Stmt.ite
                                                                                                  (Frontier.RAM.WExpr.lt
                                                                                                    (Frontier.RAM.WExpr.var
                                                                                                      "lab.xr")
                                                                                                    (Frontier.RAM.WExpr.var
                                                                                                      "lab.yr"))
                                                                                                  (Frontier.RAM.Stmt.wset
                                                                                                    "lab.gt"
                                                                                                    (Frontier.RAM.WExpr.lit
                                                                                                      1))
                                                                                                  (Frontier.RAM.Stmt.wset
                                                                                                    "lab.gt"
                                                                                                    (Frontier.RAM.WExpr.lit
                                                                                                      0)))))))))
                                                                                    (Frontier.RAM.Stmt.wset
                                                                                      "lab.gt"
                                                                                      (Frontier.RAM.WExpr.lit 0)))
                                                                                  (Frontier.RAM.Stmt.wset
                                                                                    "lab.gt"
                                                                                    (Frontier.RAM.WExpr.lit 1))))))
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "lab.lt"
                                                                              (Frontier.RAM.WExpr.lit 1))
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "lab.gt"
                                                                              (Frontier.RAM.WExpr.lit 0))))
                                                                        (Frontier.RAM.Stmt.seq
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "ok"
                                                                            (Frontier.RAM.WExpr.eq
                                                                              (Frontier.RAM.WExpr.var "lab.gt")
                                                                              (Frontier.RAM.WExpr.lit 0)))
                                                                          (Frontier.RAM.Stmt.ite
                                                                            (Frontier.RAM.WExpr.var "lab.lt")
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.vstore
                                                                                "dlen"
                                                                                (Frontier.RAM.WExpr.var "lab.xv")
                                                                                (Frontier.RAM.VExpr.var "lab.xl"))
                                                                              (Frontier.RAM.Stmt.seq
                                                                                (Frontier.RAM.Stmt.wstore
                                                                                  "dhops"
                                                                                  (Frontier.RAM.WExpr.var "lab.xv")
                                                                                  (Frontier.RAM.WExpr.var "lab.xh"))
                                                                                (Frontier.RAM.Stmt.seq
                                                                                  (Frontier.RAM.Stmt.wstore
                                                                                    "de"
                                                                                    (Frontier.RAM.WExpr.var "lab.xv")
                                                                                    (Frontier.RAM.WExpr.var "lab.xe"))
                                                                                  (Frontier.RAM.Stmt.seq
                                                                                    (Frontier.RAM.Stmt.wstore
                                                                                      "dver"
                                                                                      (Frontier.RAM.WExpr.var "lab.xv")
                                                                                      (Frontier.RAM.WExpr.var "lab.xr"))
                                                                                    (Frontier.RAM.Stmt.seq
                                                                                      (Frontier.RAM.Stmt.wstore
                                                                                        "dfin"
                                                                                        (Frontier.RAM.WExpr.var "lab.xv")
                                                                                        (Frontier.RAM.WExpr.lit 1))
                                                                                      (Frontier.RAM.Stmt.wstore
                                                                                        "vcnt"
                                                                                        (Frontier.RAM.WExpr.var "lab.xv")
                                                                                        (Frontier.RAM.WExpr.add
                                                                                          (Frontier.RAM.WExpr.load
                                                                                            "vcnt"
                                                                                            (Frontier.RAM.WExpr.var
                                                                                              "lab.xv"))
                                                                                          (Frontier.RAM.WExpr.lit
                                                                                            1))))))))
                                                                            (Frontier.RAM.Stmt.skip)))))
                                                                    (Frontier.RAM.Stmt.seq
                                                                      (Frontier.RAM.Stmt.seq
                                                                        (Frontier.RAM.Stmt.wstore
                                                                          "fp.K"
                                                                          (Frontier.RAM.WExpr.var "fp.kl")
                                                                          (Frontier.RAM.WExpr.var "fp.v"))
                                                                        (Frontier.RAM.Stmt.seq
                                                                          (Frontier.RAM.Stmt.wset
                                                                            "fp.kl"
                                                                            (Frontier.RAM.WExpr.add
                                                                              (Frontier.RAM.WExpr.var "fp.kl")
                                                                              (Frontier.RAM.WExpr.lit 1)))
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.wstore
                                                                              "fp.inK"
                                                                              (Frontier.RAM.WExpr.var "fp.v")
                                                                              (Frontier.RAM.WExpr.lit 1))
                                                                            (Frontier.RAM.Stmt.wstore
                                                                              "fp.kp"
                                                                              (Frontier.RAM.WExpr.var "fp.v")
                                                                              (Frontier.RAM.WExpr.var "fp.u")))))
                                                                      (Frontier.RAM.Stmt.seq
                                                                        (Frontier.RAM.Stmt.ite
                                                                          (Frontier.RAM.WExpr.var "ok")
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.wstore
                                                                              "fp.val"
                                                                              (Frontier.RAM.WExpr.var "fp.v")
                                                                              (Frontier.RAM.WExpr.lit 1))
                                                                            (Frontier.RAM.Stmt.ite
                                                                              (Frontier.RAM.WExpr.load
                                                                                "fp.inH"
                                                                                (Frontier.RAM.WExpr.var "fp.v"))
                                                                              (Frontier.RAM.Stmt.skip)
                                                                              (Frontier.RAM.Stmt.seq
                                                                                (Frontier.RAM.Stmt.wstore
                                                                                  "fp.H"
                                                                                  (Frontier.RAM.WExpr.var "fp.hsz")
                                                                                  (Frontier.RAM.WExpr.var "fp.v"))
                                                                                (Frontier.RAM.Stmt.seq
                                                                                  (Frontier.RAM.Stmt.wstore
                                                                                    "fp.hp"
                                                                                    (Frontier.RAM.WExpr.var "fp.v")
                                                                                    (Frontier.RAM.WExpr.var "fp.hsz"))
                                                                                  (Frontier.RAM.Stmt.seq
                                                                                    (Frontier.RAM.Stmt.wstore
                                                                                      "fp.inH"
                                                                                      (Frontier.RAM.WExpr.var "fp.v")
                                                                                      (Frontier.RAM.WExpr.lit 1))
                                                                                    (Frontier.RAM.Stmt.wset
                                                                                      "fp.hsz"
                                                                                      (Frontier.RAM.WExpr.add
                                                                                        (Frontier.RAM.WExpr.var "fp.hsz")
                                                                                        (Frontier.RAM.WExpr.lit 1))))))))
                                                                          (Frontier.RAM.Stmt.skip))
                                                                        (Frontier.RAM.Stmt.ite
                                                                          (Frontier.RAM.WExpr.lt
                                                                            (Frontier.RAM.WExpr.var "fp.kl")
                                                                            (Frontier.RAM.WExpr.var "fp.k"))
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "fp.pp"
                                                                              (Frontier.RAM.WExpr.var "fp.p"))
                                                                            (Frontier.RAM.Stmt.seq
                                                                              (Frontier.RAM.Stmt.wset
                                                                                "fp.p"
                                                                                (Frontier.RAM.WExpr.load
                                                                                  "gNxt"
                                                                                  (Frontier.RAM.WExpr.var "fp.p")))
                                                                              (Frontier.RAM.Stmt.wset
                                                                                "fp.go"
                                                                                (Frontier.RAM.WExpr.lt
                                                                                  (Frontier.RAM.WExpr.var "fp.p")
                                                                                  (Frontier.RAM.WExpr.var "gM")))))
                                                                          (Frontier.RAM.Stmt.seq
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "fp.res"
                                                                              (Frontier.RAM.WExpr.lit 3))
                                                                            (Frontier.RAM.Stmt.wset
                                                                              "fp.go"
                                                                              (Frontier.RAM.WExpr.lit 0))))))))))))
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.wset "fp.res" (Frontier.RAM.WExpr.lit 1))
                                                          (Frontier.RAM.Stmt.wset
                                                            "fp.go"
                                                            (Frontier.RAM.WExpr.lit 0))))))))))
                                          (Frontier.RAM.Stmt.ite
                                            (Frontier.RAM.WExpr.lt
                                              (Frontier.RAM.WExpr.var "fp.res")
                                              (Frontier.RAM.WExpr.lit 2))
                                            (Frontier.RAM.Stmt.skip)
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.wset "fp.sres" (Frontier.RAM.WExpr.var "fp.res"))
                                              (Frontier.RAM.Stmt.wset "fp.sgo" (Frontier.RAM.WExpr.lit 0))))))
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.wset "fp.sres" (Frontier.RAM.WExpr.lit 0))
                                        (Frontier.RAM.Stmt.wset "fp.sgo" (Frontier.RAM.WExpr.lit 0))))
                                    (Frontier.RAM.Stmt.seq
                                      (Frontier.RAM.Stmt.wset "fp.sres" (Frontier.RAM.WExpr.lit 3))
                                      (Frontier.RAM.Stmt.wset "fp.sgo" (Frontier.RAM.WExpr.lit 0))))))
                              (Frontier.RAM.Stmt.seq
                                (Frontier.RAM.Stmt.ite
                                  (Frontier.RAM.WExpr.var "fp.sres")
                                  (Frontier.RAM.Stmt.ite
                                    (Frontier.RAM.WExpr.eq (Frontier.RAM.WExpr.var "fp.sres") (Frontier.RAM.WExpr.lit 3))
                                    (Frontier.RAM.Stmt.seq
                                      (Frontier.RAM.Stmt.wset "tr.t" (Frontier.RAM.WExpr.var "tr.nt"))
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.wset
                                          "tr.w"
                                          (Frontier.RAM.WExpr.load "fp.K" (Frontier.RAM.WExpr.lit 0)))
                                        (Frontier.RAM.Stmt.seq
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.wstore
                                              "fp.fm"
                                              (Frontier.RAM.WExpr.var "tr.w")
                                              (Frontier.RAM.WExpr.lit 1))
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.wstore
                                                "tr.tid"
                                                (Frontier.RAM.WExpr.var "tr.w")
                                                (Frontier.RAM.WExpr.var "tr.t"))
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.wset
                                                  "tr.a"
                                                  (Frontier.RAM.WExpr.load "fp.kp" (Frontier.RAM.WExpr.var "tr.w")))
                                                (Frontier.RAM.Stmt.wstore
                                                  "fp.par"
                                                  (Frontier.RAM.WExpr.var "tr.w")
                                                  (Frontier.RAM.WExpr.var "tr.a")))))
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.wstore
                                              "tr.hd"
                                              (Frontier.RAM.WExpr.var "tr.t")
                                              (Frontier.RAM.WExpr.var "tr.w"))
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.wset "tr.pv" (Frontier.RAM.WExpr.var "tr.w"))
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.wset "tr.j" (Frontier.RAM.WExpr.lit 1))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.while
                                                    (Frontier.RAM.WExpr.lt
                                                      (Frontier.RAM.WExpr.var "tr.j")
                                                      (Frontier.RAM.WExpr.var "fp.kl"))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wset
                                                        "tr.w"
                                                        (Frontier.RAM.WExpr.load "fp.K" (Frontier.RAM.WExpr.var "tr.j")))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.wstore
                                                            "fp.fm"
                                                            (Frontier.RAM.WExpr.var "tr.w")
                                                            (Frontier.RAM.WExpr.lit 1))
                                                          (Frontier.RAM.Stmt.seq
                                                            (Frontier.RAM.Stmt.wstore
                                                              "tr.tid"
                                                              (Frontier.RAM.WExpr.var "tr.w")
                                                              (Frontier.RAM.WExpr.var "tr.t"))
                                                            (Frontier.RAM.Stmt.seq
                                                              (Frontier.RAM.Stmt.wset
                                                                "tr.a"
                                                                (Frontier.RAM.WExpr.load
                                                                  "fp.kp"
                                                                  (Frontier.RAM.WExpr.var "tr.w")))
                                                              (Frontier.RAM.Stmt.wstore
                                                                "fp.par"
                                                                (Frontier.RAM.WExpr.var "tr.w")
                                                                (Frontier.RAM.WExpr.var "tr.a")))))
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.wstore
                                                            "tr.nx"
                                                            (Frontier.RAM.WExpr.var "tr.pv")
                                                            (Frontier.RAM.WExpr.var "tr.w"))
                                                          (Frontier.RAM.Stmt.seq
                                                            (Frontier.RAM.Stmt.wset
                                                              "tr.pv"
                                                              (Frontier.RAM.WExpr.var "tr.w"))
                                                            (Frontier.RAM.Stmt.wset
                                                              "tr.j"
                                                              (Frontier.RAM.WExpr.add
                                                                (Frontier.RAM.WExpr.var "tr.j")
                                                                (Frontier.RAM.WExpr.lit 1))))))))
                                                  (Frontier.RAM.Stmt.seq
                                                    (Frontier.RAM.Stmt.wstore
                                                      "tr.tl"
                                                      (Frontier.RAM.WExpr.var "tr.t")
                                                      (Frontier.RAM.WExpr.var "tr.pv"))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wstore
                                                        "tr.ln"
                                                        (Frontier.RAM.WExpr.var "tr.t")
                                                        (Frontier.RAM.WExpr.var "fp.kl"))
                                                      (Frontier.RAM.Stmt.wset
                                                        "tr.nt"
                                                        (Frontier.RAM.WExpr.add
                                                          (Frontier.RAM.WExpr.var "tr.t")
                                                          (Frontier.RAM.WExpr.lit 1))))))))))))
                                    (Frontier.RAM.Stmt.seq
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.wset
                                          "tr.t"
                                          (Frontier.RAM.WExpr.load "tr.tid" (Frontier.RAM.WExpr.var "fp.cv")))
                                        (Frontier.RAM.Stmt.seq
                                          (Frontier.RAM.Stmt.wset
                                            "tr.pv"
                                            (Frontier.RAM.WExpr.load "tr.tl" (Frontier.RAM.WExpr.var "tr.t")))
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.wset "tr.u" (Frontier.RAM.WExpr.var "fp.cv"))
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.wset "tr.c" (Frontier.RAM.WExpr.var "fp.cu"))
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.wset "tr.f" (Frontier.RAM.WExpr.var "fp.kl"))
                                                (Frontier.RAM.Stmt.wset "tr.x" (Frontier.RAM.WExpr.lit 1)))))))
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.while
                                          (Frontier.RAM.WExpr.var "tr.x")
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.wstore
                                                "tr.inP"
                                                (Frontier.RAM.WExpr.var "tr.c")
                                                (Frontier.RAM.WExpr.lit 1))
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.wstore
                                                  "tr.tid"
                                                  (Frontier.RAM.WExpr.var "tr.c")
                                                  (Frontier.RAM.WExpr.var "tr.t"))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wstore
                                                    "fp.fm"
                                                    (Frontier.RAM.WExpr.var "tr.c")
                                                    (Frontier.RAM.WExpr.lit 1))
                                                  (Frontier.RAM.Stmt.seq
                                                    (Frontier.RAM.Stmt.wstore
                                                      "fp.par"
                                                      (Frontier.RAM.WExpr.var "tr.c")
                                                      (Frontier.RAM.WExpr.var "tr.u"))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wstore
                                                        "tr.nx"
                                                        (Frontier.RAM.WExpr.var "tr.pv")
                                                        (Frontier.RAM.WExpr.var "tr.c"))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wset "tr.pv" (Frontier.RAM.WExpr.var "tr.c"))
                                                        (Frontier.RAM.Stmt.wset
                                                          "tr.u"
                                                          (Frontier.RAM.WExpr.var "tr.c"))))))))
                                            (Frontier.RAM.Stmt.ite
                                              (Frontier.RAM.WExpr.eq
                                                (Frontier.RAM.WExpr.var "tr.c")
                                                (Frontier.RAM.WExpr.var "fp.x"))
                                              (Frontier.RAM.Stmt.wset "tr.x" (Frontier.RAM.WExpr.lit 0))
                                              (Frontier.RAM.Stmt.ite
                                                (Frontier.RAM.WExpr.eq
                                                  (Frontier.RAM.WExpr.var "tr.f")
                                                  (Frontier.RAM.WExpr.lit 0))
                                                (Frontier.RAM.Stmt.wset "tr.x" (Frontier.RAM.WExpr.lit 0))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wset
                                                    "tr.c"
                                                    (Frontier.RAM.WExpr.load "fp.kp" (Frontier.RAM.WExpr.var "tr.c")))
                                                  (Frontier.RAM.Stmt.wset
                                                    "tr.f"
                                                    (Frontier.RAM.WExpr.sub
                                                      (Frontier.RAM.WExpr.var "tr.f")
                                                      (Frontier.RAM.WExpr.lit 1))))))))
                                        (Frontier.RAM.Stmt.seq
                                          (Frontier.RAM.Stmt.wset "tr.j" (Frontier.RAM.WExpr.lit 0))
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.while
                                              (Frontier.RAM.WExpr.lt
                                                (Frontier.RAM.WExpr.var "tr.j")
                                                (Frontier.RAM.WExpr.var "fp.kl"))
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.wset
                                                  "tr.w"
                                                  (Frontier.RAM.WExpr.load "fp.K" (Frontier.RAM.WExpr.var "tr.j")))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wset
                                                    "tr.a"
                                                    (Frontier.RAM.WExpr.load "tr.inP" (Frontier.RAM.WExpr.var "tr.w")))
                                                  (Frontier.RAM.Stmt.seq
                                                    (Frontier.RAM.Stmt.ite
                                                      (Frontier.RAM.WExpr.eq
                                                        (Frontier.RAM.WExpr.var "tr.a")
                                                        (Frontier.RAM.WExpr.lit 0))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wstore
                                                          "tr.nx"
                                                          (Frontier.RAM.WExpr.var "tr.pv")
                                                          (Frontier.RAM.WExpr.var "tr.w"))
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.wset "tr.pv" (Frontier.RAM.WExpr.var "tr.w"))
                                                          (Frontier.RAM.Stmt.seq
                                                            (Frontier.RAM.Stmt.wset
                                                              "tr.a"
                                                              (Frontier.RAM.WExpr.load
                                                                "fp.kp"
                                                                (Frontier.RAM.WExpr.var "tr.w")))
                                                            (Frontier.RAM.Stmt.seq
                                                              (Frontier.RAM.Stmt.wstore
                                                                "fp.par"
                                                                (Frontier.RAM.WExpr.var "tr.w")
                                                                (Frontier.RAM.WExpr.var "tr.a"))
                                                              (Frontier.RAM.Stmt.seq
                                                                (Frontier.RAM.Stmt.wstore
                                                                  "tr.tid"
                                                                  (Frontier.RAM.WExpr.var "tr.w")
                                                                  (Frontier.RAM.WExpr.var "tr.t"))
                                                                (Frontier.RAM.Stmt.wstore
                                                                  "fp.fm"
                                                                  (Frontier.RAM.WExpr.var "tr.w")
                                                                  (Frontier.RAM.WExpr.lit 1)))))))
                                                      (Frontier.RAM.Stmt.skip))
                                                    (Frontier.RAM.Stmt.wset
                                                      "tr.j"
                                                      (Frontier.RAM.WExpr.add
                                                        (Frontier.RAM.WExpr.var "tr.j")
                                                        (Frontier.RAM.WExpr.lit 1)))))))
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.wstore
                                                  "tr.tl"
                                                  (Frontier.RAM.WExpr.var "tr.t")
                                                  (Frontier.RAM.WExpr.var "tr.pv"))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wset
                                                    "tr.a"
                                                    (Frontier.RAM.WExpr.load "tr.ln" (Frontier.RAM.WExpr.var "tr.t")))
                                                  (Frontier.RAM.Stmt.seq
                                                    (Frontier.RAM.Stmt.wstore
                                                      "tr.ln"
                                                      (Frontier.RAM.WExpr.var "tr.t")
                                                      (Frontier.RAM.WExpr.add
                                                        (Frontier.RAM.WExpr.var "tr.a")
                                                        (Frontier.RAM.WExpr.var "fp.kl")))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wset "tr.c" (Frontier.RAM.WExpr.var "fp.cu"))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wset "tr.f" (Frontier.RAM.WExpr.var "fp.kl"))
                                                        (Frontier.RAM.Stmt.wset "tr.x" (Frontier.RAM.WExpr.lit 1)))))))
                                              (Frontier.RAM.Stmt.while
                                                (Frontier.RAM.WExpr.var "tr.x")
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wstore
                                                    "tr.inP"
                                                    (Frontier.RAM.WExpr.var "tr.c")
                                                    (Frontier.RAM.WExpr.lit 0))
                                                  (Frontier.RAM.Stmt.ite
                                                    (Frontier.RAM.WExpr.eq
                                                      (Frontier.RAM.WExpr.var "tr.c")
                                                      (Frontier.RAM.WExpr.var "fp.x"))
                                                    (Frontier.RAM.Stmt.wset "tr.x" (Frontier.RAM.WExpr.lit 0))
                                                    (Frontier.RAM.Stmt.ite
                                                      (Frontier.RAM.WExpr.eq
                                                        (Frontier.RAM.WExpr.var "tr.f")
                                                        (Frontier.RAM.WExpr.lit 0))
                                                      (Frontier.RAM.Stmt.wset "tr.x" (Frontier.RAM.WExpr.lit 0))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wset
                                                          "tr.c"
                                                          (Frontier.RAM.WExpr.load
                                                            "fp.kp"
                                                            (Frontier.RAM.WExpr.var "tr.c")))
                                                        (Frontier.RAM.Stmt.wset
                                                          "tr.f"
                                                          (Frontier.RAM.WExpr.sub
                                                            (Frontier.RAM.WExpr.var "tr.f")
                                                            (Frontier.RAM.WExpr.lit 1))))))))))))))
                                  (Frontier.RAM.Stmt.seq
                                    (Frontier.RAM.Stmt.wset "fp.i" (Frontier.RAM.WExpr.lit 0))
                                    (Frontier.RAM.Stmt.seq
                                      (Frontier.RAM.Stmt.while
                                        (Frontier.RAM.WExpr.lt
                                          (Frontier.RAM.WExpr.var "fp.i")
                                          (Frontier.RAM.WExpr.var "fp.kl"))
                                        (Frontier.RAM.Stmt.seq
                                          (Frontier.RAM.Stmt.wset
                                            "fp.y"
                                            (Frontier.RAM.WExpr.load "fp.K" (Frontier.RAM.WExpr.var "fp.i")))
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.ite
                                              (Frontier.RAM.WExpr.load "fp.val" (Frontier.RAM.WExpr.var "fp.y"))
                                              (Frontier.RAM.Stmt.ite
                                                (Frontier.RAM.WExpr.load "fp.inW" (Frontier.RAM.WExpr.var "fp.y"))
                                                (Frontier.RAM.Stmt.skip)
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wstore
                                                    "fp.W"
                                                    (Frontier.RAM.WExpr.add
                                                      (Frontier.RAM.WExpr.var "fp.ob")
                                                      (Frontier.RAM.WExpr.var "fp.wl"))
                                                    (Frontier.RAM.WExpr.var "fp.y"))
                                                  (Frontier.RAM.Stmt.seq
                                                    (Frontier.RAM.Stmt.wset
                                                      "fp.wl"
                                                      (Frontier.RAM.WExpr.add
                                                        (Frontier.RAM.WExpr.var "fp.wl")
                                                        (Frontier.RAM.WExpr.lit 1)))
                                                    (Frontier.RAM.Stmt.wstore
                                                      "fp.inW"
                                                      (Frontier.RAM.WExpr.var "fp.y")
                                                      (Frontier.RAM.WExpr.lit 1)))))
                                              (Frontier.RAM.Stmt.skip))
                                            (Frontier.RAM.Stmt.wset
                                              "fp.i"
                                              (Frontier.RAM.WExpr.add
                                                (Frontier.RAM.WExpr.var "fp.i")
                                                (Frontier.RAM.WExpr.lit 1))))))
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.wstore
                                          "fp.Q"
                                          (Frontier.RAM.WExpr.add
                                            (Frontier.RAM.WExpr.var "fp.ob")
                                            (Frontier.RAM.WExpr.var "fp.ql"))
                                          (Frontier.RAM.WExpr.var "fp.x"))
                                        (Frontier.RAM.Stmt.wset
                                          "fp.ql"
                                          (Frontier.RAM.WExpr.add
                                            (Frontier.RAM.WExpr.var "fp.ql")
                                            (Frontier.RAM.WExpr.lit 1)))))))
                                (Frontier.RAM.Stmt.seq
                                  (Frontier.RAM.Stmt.wset "fp.i" (Frontier.RAM.WExpr.lit 0))
                                  (Frontier.RAM.Stmt.seq
                                    (Frontier.RAM.Stmt.while
                                      (Frontier.RAM.WExpr.lt
                                        (Frontier.RAM.WExpr.var "fp.i")
                                        (Frontier.RAM.WExpr.var "fp.kl"))
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.wset
                                          "fp.y"
                                          (Frontier.RAM.WExpr.load "fp.K" (Frontier.RAM.WExpr.var "fp.i")))
                                        (Frontier.RAM.Stmt.seq
                                          (Frontier.RAM.Stmt.wstore
                                            "fp.inK"
                                            (Frontier.RAM.WExpr.var "fp.y")
                                            (Frontier.RAM.WExpr.lit 0))
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.wstore
                                              "fp.val"
                                              (Frontier.RAM.WExpr.var "fp.y")
                                              (Frontier.RAM.WExpr.lit 0))
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.wstore
                                                "fp.inH"
                                                (Frontier.RAM.WExpr.var "fp.y")
                                                (Frontier.RAM.WExpr.lit 0))
                                              (Frontier.RAM.Stmt.wset
                                                "fp.i"
                                                (Frontier.RAM.WExpr.add
                                                  (Frontier.RAM.WExpr.var "fp.i")
                                                  (Frontier.RAM.WExpr.lit 1))))))))
                                    (Frontier.RAM.Stmt.seq
                                      (Frontier.RAM.Stmt.wset "fp.kl" (Frontier.RAM.WExpr.lit 0))
                                      (Frontier.RAM.Stmt.wset "fp.hsz" (Frontier.RAM.WExpr.lit 0)))))))))
                        (Frontier.RAM.Stmt.wset
                          "fp.j"
                          (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "fp.j") (Frontier.RAM.WExpr.lit 1))))))))))
          (Frontier.RAM.Stmt.seq
            (Frontier.RAM.Stmt.seq
              (Frontier.RAM.Stmt.wset "ct.t" (Frontier.RAM.WExpr.lit 0))
              (Frontier.RAM.Stmt.seq
                (Frontier.RAM.Stmt.wset "ct.o" (Frontier.RAM.WExpr.lit 0))
                (Frontier.RAM.Stmt.seq
                  (Frontier.RAM.Stmt.while
                    (Frontier.RAM.WExpr.lt (Frontier.RAM.WExpr.var "ct.t") (Frontier.RAM.WExpr.var "tr.nt"))
                    (Frontier.RAM.Stmt.seq
                      (Frontier.RAM.Stmt.wstore "fp.toff" (Frontier.RAM.WExpr.var "ct.t") (Frontier.RAM.WExpr.var "ct.o"))
                      (Frontier.RAM.Stmt.seq
                        (Frontier.RAM.Stmt.wset "ct.l" (Frontier.RAM.WExpr.load "tr.ln" (Frontier.RAM.WExpr.var "ct.t")))
                        (Frontier.RAM.Stmt.seq
                          (Frontier.RAM.Stmt.wstore
                            "fp.tlen"
                            (Frontier.RAM.WExpr.var "ct.t")
                            (Frontier.RAM.WExpr.var "ct.l"))
                          (Frontier.RAM.Stmt.seq
                            (Frontier.RAM.Stmt.wset
                              "ct.w"
                              (Frontier.RAM.WExpr.load "tr.hd" (Frontier.RAM.WExpr.var "ct.t")))
                            (Frontier.RAM.Stmt.seq
                              (Frontier.RAM.Stmt.wset "ct.i" (Frontier.RAM.WExpr.lit 0))
                              (Frontier.RAM.Stmt.seq
                                (Frontier.RAM.Stmt.while
                                  (Frontier.RAM.WExpr.lt (Frontier.RAM.WExpr.var "ct.i") (Frontier.RAM.WExpr.var "ct.l"))
                                  (Frontier.RAM.Stmt.seq
                                    (Frontier.RAM.Stmt.wstore
                                      "fp.TV"
                                      (Frontier.RAM.WExpr.var "ct.o")
                                      (Frontier.RAM.WExpr.var "ct.w"))
                                    (Frontier.RAM.Stmt.seq
                                      (Frontier.RAM.Stmt.wset
                                        "ct.o"
                                        (Frontier.RAM.WExpr.add
                                          (Frontier.RAM.WExpr.var "ct.o")
                                          (Frontier.RAM.WExpr.lit 1)))
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.wset
                                          "ct.w"
                                          (Frontier.RAM.WExpr.load "tr.nx" (Frontier.RAM.WExpr.var "ct.w")))
                                        (Frontier.RAM.Stmt.wset
                                          "ct.i"
                                          (Frontier.RAM.WExpr.add
                                            (Frontier.RAM.WExpr.var "ct.i")
                                            (Frontier.RAM.WExpr.lit 1)))))))
                                (Frontier.RAM.Stmt.wset
                                  "ct.t"
                                  (Frontier.RAM.WExpr.add
                                    (Frontier.RAM.WExpr.var "ct.t")
                                    (Frontier.RAM.WExpr.lit 1))))))))))
                  (Frontier.RAM.Stmt.wset "fp.nt" (Frontier.RAM.WExpr.var "tr.nt")))))
            (Frontier.RAM.Stmt.seq
              (Frontier.RAM.Stmt.seq
                (Frontier.RAM.Stmt.wset "mk.j" (Frontier.RAM.WExpr.var "fp.sb"))
                (Frontier.RAM.Stmt.seq
                  (Frontier.RAM.Stmt.wset
                    "mk.e"
                    (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "fp.sb") (Frontier.RAM.WExpr.var "fp.sn")))
                  (Frontier.RAM.Stmt.while
                    (Frontier.RAM.WExpr.lt (Frontier.RAM.WExpr.var "mk.j") (Frontier.RAM.WExpr.var "mk.e"))
                    (Frontier.RAM.Stmt.seq
                      (Frontier.RAM.Stmt.wset "mk.x" (Frontier.RAM.WExpr.load "S" (Frontier.RAM.WExpr.var "mk.j")))
                      (Frontier.RAM.Stmt.seq
                        (Frontier.RAM.Stmt.wstore "fp.inS" (Frontier.RAM.WExpr.var "mk.x") (Frontier.RAM.WExpr.lit 1))
                        (Frontier.RAM.Stmt.wset
                          "mk.j"
                          (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "mk.j") (Frontier.RAM.WExpr.lit 1))))))))
              (Frontier.RAM.Stmt.seq
                (Frontier.RAM.Stmt.seq
                  (Frontier.RAM.Stmt.wset "mk.j" (Frontier.RAM.WExpr.var "fp.ob"))
                  (Frontier.RAM.Stmt.seq
                    (Frontier.RAM.Stmt.wset
                      "mk.e"
                      (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "fp.ob") (Frontier.RAM.WExpr.var "fp.ql")))
                    (Frontier.RAM.Stmt.while
                      (Frontier.RAM.WExpr.lt (Frontier.RAM.WExpr.var "mk.j") (Frontier.RAM.WExpr.var "mk.e"))
                      (Frontier.RAM.Stmt.seq
                        (Frontier.RAM.Stmt.wset "mk.x" (Frontier.RAM.WExpr.load "fp.Q" (Frontier.RAM.WExpr.var "mk.j")))
                        (Frontier.RAM.Stmt.seq
                          (Frontier.RAM.Stmt.wstore "fp.inQ" (Frontier.RAM.WExpr.var "mk.x") (Frontier.RAM.WExpr.lit 1))
                          (Frontier.RAM.Stmt.wset
                            "mk.j"
                            (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "mk.j") (Frontier.RAM.WExpr.lit 1))))))))
                (Frontier.RAM.Stmt.seq
                  (Frontier.RAM.Stmt.wset
                    "pt.km1"
                    (Frontier.RAM.WExpr.sub (Frontier.RAM.WExpr.var "fp.k") (Frontier.RAM.WExpr.lit 1)))
                  (Frontier.RAM.Stmt.seq
                    (Frontier.RAM.Stmt.seq
                      (Frontier.RAM.Stmt.wset "pt.t" (Frontier.RAM.WExpr.lit 0))
                      (Frontier.RAM.Stmt.seq
                        (Frontier.RAM.Stmt.wset "pt.np" (Frontier.RAM.WExpr.lit 0))
                        (Frontier.RAM.Stmt.seq
                          (Frontier.RAM.Stmt.while
                            (Frontier.RAM.WExpr.lt (Frontier.RAM.WExpr.var "pt.t") (Frontier.RAM.WExpr.var "fp.nt"))
                            (Frontier.RAM.Stmt.seq
                              (Frontier.RAM.Stmt.wset
                                "pt.b"
                                (Frontier.RAM.WExpr.load "fp.toff" (Frontier.RAM.WExpr.var "pt.t")))
                              (Frontier.RAM.Stmt.seq
                                (Frontier.RAM.Stmt.wset
                                  "pt.len"
                                  (Frontier.RAM.WExpr.load "fp.tlen" (Frontier.RAM.WExpr.var "pt.t")))
                                (Frontier.RAM.Stmt.seq
                                  (Frontier.RAM.Stmt.seq
                                    (Frontier.RAM.Stmt.wset "pt.np0" (Frontier.RAM.WExpr.var "pt.np"))
                                    (Frontier.RAM.Stmt.seq
                                      (Frontier.RAM.Stmt.wset "pt.i" (Frontier.RAM.WExpr.var "pt.len"))
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.while
                                          (Frontier.RAM.WExpr.lt
                                            (Frontier.RAM.WExpr.lit 0)
                                            (Frontier.RAM.WExpr.var "pt.i"))
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.wset
                                              "pt.i"
                                              (Frontier.RAM.WExpr.sub
                                                (Frontier.RAM.WExpr.var "pt.i")
                                                (Frontier.RAM.WExpr.lit 1)))
                                            (Frontier.RAM.Stmt.wstore
                                              "pt.an"
                                              (Frontier.RAM.WExpr.load
                                                "fp.TV"
                                                (Frontier.RAM.WExpr.add
                                                  (Frontier.RAM.WExpr.var "pt.b")
                                                  (Frontier.RAM.WExpr.var "pt.i")))
                                              (Frontier.RAM.WExpr.lit 0))))
                                        (Frontier.RAM.Stmt.seq
                                          (Frontier.RAM.Stmt.wset
                                            "pt.i"
                                            (Frontier.RAM.WExpr.sub
                                              (Frontier.RAM.WExpr.var "pt.len")
                                              (Frontier.RAM.WExpr.lit 1)))
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.while
                                              (Frontier.RAM.WExpr.lt
                                                (Frontier.RAM.WExpr.lit 0)
                                                (Frontier.RAM.WExpr.var "pt.i"))
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.seq
                                                    (Frontier.RAM.Stmt.wset
                                                      "pt.v"
                                                      (Frontier.RAM.WExpr.load
                                                        "fp.TV"
                                                        (Frontier.RAM.WExpr.add
                                                          (Frontier.RAM.WExpr.var "pt.b")
                                                          (Frontier.RAM.WExpr.var "pt.i"))))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wset
                                                        "pt.p"
                                                        (Frontier.RAM.WExpr.load
                                                          "fp.par"
                                                          (Frontier.RAM.WExpr.var "pt.v")))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wset
                                                          "pt.ap"
                                                          (Frontier.RAM.WExpr.load
                                                            "pt.an"
                                                            (Frontier.RAM.WExpr.var "pt.p")))
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.wset
                                                            "pt.av"
                                                            (Frontier.RAM.WExpr.load
                                                              "pt.an"
                                                              (Frontier.RAM.WExpr.var "pt.v")))
                                                          (Frontier.RAM.Stmt.seq
                                                            (Frontier.RAM.Stmt.ite
                                                              (Frontier.RAM.WExpr.eq
                                                                (Frontier.RAM.WExpr.var "pt.ap")
                                                                (Frontier.RAM.WExpr.lit 0))
                                                              (Frontier.RAM.Stmt.wstore
                                                                "pt.af"
                                                                (Frontier.RAM.WExpr.var "pt.p")
                                                                (Frontier.RAM.WExpr.var "pt.v"))
                                                              (Frontier.RAM.Stmt.wstore
                                                                "pt.nx"
                                                                (Frontier.RAM.WExpr.load
                                                                  "pt.al"
                                                                  (Frontier.RAM.WExpr.var "pt.p"))
                                                                (Frontier.RAM.WExpr.var "pt.v")))
                                                            (Frontier.RAM.Stmt.seq
                                                              (Frontier.RAM.Stmt.ite
                                                                (Frontier.RAM.WExpr.eq
                                                                  (Frontier.RAM.WExpr.var "pt.av")
                                                                  (Frontier.RAM.WExpr.lit 0))
                                                                (Frontier.RAM.Stmt.wstore
                                                                  "pt.al"
                                                                  (Frontier.RAM.WExpr.var "pt.p")
                                                                  (Frontier.RAM.WExpr.var "pt.v"))
                                                                (Frontier.RAM.Stmt.seq
                                                                  (Frontier.RAM.Stmt.wstore
                                                                    "pt.nx"
                                                                    (Frontier.RAM.WExpr.var "pt.v")
                                                                    (Frontier.RAM.WExpr.load
                                                                      "pt.af"
                                                                      (Frontier.RAM.WExpr.var "pt.v")))
                                                                  (Frontier.RAM.Stmt.wstore
                                                                    "pt.al"
                                                                    (Frontier.RAM.WExpr.var "pt.p")
                                                                    (Frontier.RAM.WExpr.load
                                                                      "pt.al"
                                                                      (Frontier.RAM.WExpr.var "pt.v")))))
                                                              (Frontier.RAM.Stmt.seq
                                                                (Frontier.RAM.Stmt.wset
                                                                  "pt.ap"
                                                                  (Frontier.RAM.WExpr.add
                                                                    (Frontier.RAM.WExpr.add
                                                                      (Frontier.RAM.WExpr.var "pt.ap")
                                                                      (Frontier.RAM.WExpr.lit 1))
                                                                    (Frontier.RAM.WExpr.var "pt.av")))
                                                                (Frontier.RAM.Stmt.wstore
                                                                  "pt.an"
                                                                  (Frontier.RAM.WExpr.var "pt.p")
                                                                  (Frontier.RAM.WExpr.var "pt.ap")))))))))
                                                  (Frontier.RAM.Stmt.ite
                                                    (Frontier.RAM.WExpr.lt
                                                      (Frontier.RAM.WExpr.var "pt.ap")
                                                      (Frontier.RAM.WExpr.var "pt.km1"))
                                                    (Frontier.RAM.Stmt.skip)
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wstore
                                                        "pt.PT"
                                                        (Frontier.RAM.WExpr.var "pt.np")
                                                        (Frontier.RAM.WExpr.var "pt.p"))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wstore
                                                          "pt.PF"
                                                          (Frontier.RAM.WExpr.var "pt.np")
                                                          (Frontier.RAM.WExpr.load
                                                            "pt.af"
                                                            (Frontier.RAM.WExpr.var "pt.p")))
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.wstore
                                                            "pt.PL"
                                                            (Frontier.RAM.WExpr.var "pt.np")
                                                            (Frontier.RAM.WExpr.load
                                                              "pt.al"
                                                              (Frontier.RAM.WExpr.var "pt.p")))
                                                          (Frontier.RAM.Stmt.seq
                                                            (Frontier.RAM.Stmt.wstore
                                                              "pt.PN"
                                                              (Frontier.RAM.WExpr.var "pt.np")
                                                              (Frontier.RAM.WExpr.var "pt.ap"))
                                                            (Frontier.RAM.Stmt.seq
                                                              (Frontier.RAM.Stmt.wset
                                                                "pt.np"
                                                                (Frontier.RAM.WExpr.add
                                                                  (Frontier.RAM.WExpr.var "pt.np")
                                                                  (Frontier.RAM.WExpr.lit 1)))
                                                              (Frontier.RAM.Stmt.wstore
                                                                "pt.an"
                                                                (Frontier.RAM.WExpr.var "pt.p")
                                                                (Frontier.RAM.WExpr.lit 0)))))))))
                                                (Frontier.RAM.Stmt.wset
                                                  "pt.i"
                                                  (Frontier.RAM.WExpr.sub
                                                    (Frontier.RAM.WExpr.var "pt.i")
                                                    (Frontier.RAM.WExpr.lit 1)))))
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.wset
                                                "pt.r"
                                                (Frontier.RAM.WExpr.load "fp.TV" (Frontier.RAM.WExpr.var "pt.b")))
                                              (Frontier.RAM.Stmt.ite
                                                (Frontier.RAM.WExpr.eq
                                                  (Frontier.RAM.WExpr.var "pt.np")
                                                  (Frontier.RAM.WExpr.var "pt.np0"))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wstore
                                                    "pt.PT"
                                                    (Frontier.RAM.WExpr.var "pt.np")
                                                    (Frontier.RAM.WExpr.var "pt.r"))
                                                  (Frontier.RAM.Stmt.seq
                                                    (Frontier.RAM.Stmt.wstore
                                                      "pt.PF"
                                                      (Frontier.RAM.WExpr.var "pt.np")
                                                      (Frontier.RAM.WExpr.load "pt.af" (Frontier.RAM.WExpr.var "pt.r")))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wstore
                                                        "pt.PL"
                                                        (Frontier.RAM.WExpr.var "pt.np")
                                                        (Frontier.RAM.WExpr.load "pt.al" (Frontier.RAM.WExpr.var "pt.r")))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wstore
                                                          "pt.PN"
                                                          (Frontier.RAM.WExpr.var "pt.np")
                                                          (Frontier.RAM.WExpr.load
                                                            "pt.an"
                                                            (Frontier.RAM.WExpr.var "pt.r")))
                                                        (Frontier.RAM.Stmt.wset
                                                          "pt.np"
                                                          (Frontier.RAM.WExpr.add
                                                            (Frontier.RAM.WExpr.var "pt.np")
                                                            (Frontier.RAM.WExpr.lit 1)))))))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.wset
                                                    "pt.g"
                                                    (Frontier.RAM.WExpr.sub
                                                      (Frontier.RAM.WExpr.var "pt.np")
                                                      (Frontier.RAM.WExpr.lit 1)))
                                                  (Frontier.RAM.Stmt.ite
                                                    (Frontier.RAM.WExpr.eq
                                                      (Frontier.RAM.WExpr.load "pt.an" (Frontier.RAM.WExpr.var "pt.r"))
                                                      (Frontier.RAM.WExpr.lit 0))
                                                    (Frontier.RAM.Stmt.wstore
                                                      "pt.PT"
                                                      (Frontier.RAM.WExpr.var "pt.g")
                                                      (Frontier.RAM.WExpr.var "pt.r"))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wstore
                                                        "pt.nx"
                                                        (Frontier.RAM.WExpr.load "pt.al" (Frontier.RAM.WExpr.var "pt.r"))
                                                        (Frontier.RAM.WExpr.load "pt.PF" (Frontier.RAM.WExpr.var "pt.g")))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wstore
                                                          "pt.PF"
                                                          (Frontier.RAM.WExpr.var "pt.g")
                                                          (Frontier.RAM.WExpr.load
                                                            "pt.af"
                                                            (Frontier.RAM.WExpr.var "pt.r")))
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.wstore
                                                            "pt.PT"
                                                            (Frontier.RAM.WExpr.var "pt.g")
                                                            (Frontier.RAM.WExpr.var "pt.r"))
                                                          (Frontier.RAM.Stmt.wstore
                                                            "pt.PN"
                                                            (Frontier.RAM.WExpr.var "pt.g")
                                                            (Frontier.RAM.WExpr.add
                                                              (Frontier.RAM.WExpr.load
                                                                "pt.an"
                                                                (Frontier.RAM.WExpr.var "pt.r"))
                                                              (Frontier.RAM.WExpr.load
                                                                "pt.PN"
                                                                (Frontier.RAM.WExpr.var "pt.g"))))))))))))))))
                                  (Frontier.RAM.Stmt.wset
                                    "pt.t"
                                    (Frontier.RAM.WExpr.add
                                      (Frontier.RAM.WExpr.var "pt.t")
                                      (Frontier.RAM.WExpr.lit 1)))))))
                          (Frontier.RAM.Stmt.seq
                            (Frontier.RAM.Stmt.wset "pt.g" (Frontier.RAM.WExpr.lit 0))
                            (Frontier.RAM.Stmt.seq
                              (Frontier.RAM.Stmt.wset "pt.ng" (Frontier.RAM.WExpr.lit 0))
                              (Frontier.RAM.Stmt.seq
                                (Frontier.RAM.Stmt.wset "pt.gv" (Frontier.RAM.WExpr.lit 0))
                                (Frontier.RAM.Stmt.seq
                                  (Frontier.RAM.Stmt.while
                                    (Frontier.RAM.WExpr.lt
                                      (Frontier.RAM.WExpr.var "pt.g")
                                      (Frontier.RAM.WExpr.var "pt.np"))
                                    (Frontier.RAM.Stmt.seq
                                      (Frontier.RAM.Stmt.wset "pt.gs" (Frontier.RAM.WExpr.var "pt.gv"))
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.wset
                                          "pt.x"
                                          (Frontier.RAM.WExpr.load "pt.PT" (Frontier.RAM.WExpr.var "pt.g")))
                                        (Frontier.RAM.Stmt.seq
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.wset
                                              "pt.tS"
                                              (Frontier.RAM.WExpr.load "fp.inS" (Frontier.RAM.WExpr.var "pt.x")))
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.wset
                                                "pt.tQ"
                                                (Frontier.RAM.WExpr.load "fp.inQ" (Frontier.RAM.WExpr.var "pt.x")))
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.wset
                                                  "pt.tA"
                                                  (Frontier.RAM.WExpr.load "pt.as" (Frontier.RAM.WExpr.var "pt.x")))
                                                (Frontier.RAM.Stmt.ite
                                                  (Frontier.RAM.WExpr.eq
                                                    (Frontier.RAM.WExpr.var "pt.tS")
                                                    (Frontier.RAM.WExpr.lit 1))
                                                  (Frontier.RAM.Stmt.ite
                                                    (Frontier.RAM.WExpr.eq
                                                      (Frontier.RAM.WExpr.var "pt.tQ")
                                                      (Frontier.RAM.WExpr.lit 0))
                                                    (Frontier.RAM.Stmt.ite
                                                      (Frontier.RAM.WExpr.eq
                                                        (Frontier.RAM.WExpr.var "pt.tA")
                                                        (Frontier.RAM.WExpr.lit 0))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wstore
                                                          "pt.as"
                                                          (Frontier.RAM.WExpr.var "pt.x")
                                                          (Frontier.RAM.WExpr.lit 1))
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.wstore
                                                            "pt.GV"
                                                            (Frontier.RAM.WExpr.var "pt.gv")
                                                            (Frontier.RAM.WExpr.var "pt.x"))
                                                          (Frontier.RAM.Stmt.wset
                                                            "pt.gv"
                                                            (Frontier.RAM.WExpr.add
                                                              (Frontier.RAM.WExpr.var "pt.gv")
                                                              (Frontier.RAM.WExpr.lit 1)))))
                                                      (Frontier.RAM.Stmt.skip))
                                                    (Frontier.RAM.Stmt.skip))
                                                  (Frontier.RAM.Stmt.skip)))))
                                          (Frontier.RAM.Stmt.seq
                                            (Frontier.RAM.Stmt.wset
                                              "pt.x"
                                              (Frontier.RAM.WExpr.load "pt.PF" (Frontier.RAM.WExpr.var "pt.g")))
                                            (Frontier.RAM.Stmt.seq
                                              (Frontier.RAM.Stmt.wset
                                                "pt.c"
                                                (Frontier.RAM.WExpr.load "pt.PN" (Frontier.RAM.WExpr.var "pt.g")))
                                              (Frontier.RAM.Stmt.seq
                                                (Frontier.RAM.Stmt.while
                                                  (Frontier.RAM.WExpr.lt
                                                    (Frontier.RAM.WExpr.lit 0)
                                                    (Frontier.RAM.WExpr.var "pt.c"))
                                                  (Frontier.RAM.Stmt.seq
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wset
                                                        "pt.tS"
                                                        (Frontier.RAM.WExpr.load
                                                          "fp.inS"
                                                          (Frontier.RAM.WExpr.var "pt.x")))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wset
                                                          "pt.tQ"
                                                          (Frontier.RAM.WExpr.load
                                                            "fp.inQ"
                                                            (Frontier.RAM.WExpr.var "pt.x")))
                                                        (Frontier.RAM.Stmt.seq
                                                          (Frontier.RAM.Stmt.wset
                                                            "pt.tA"
                                                            (Frontier.RAM.WExpr.load
                                                              "pt.as"
                                                              (Frontier.RAM.WExpr.var "pt.x")))
                                                          (Frontier.RAM.Stmt.ite
                                                            (Frontier.RAM.WExpr.eq
                                                              (Frontier.RAM.WExpr.var "pt.tS")
                                                              (Frontier.RAM.WExpr.lit 1))
                                                            (Frontier.RAM.Stmt.ite
                                                              (Frontier.RAM.WExpr.eq
                                                                (Frontier.RAM.WExpr.var "pt.tQ")
                                                                (Frontier.RAM.WExpr.lit 0))
                                                              (Frontier.RAM.Stmt.ite
                                                                (Frontier.RAM.WExpr.eq
                                                                  (Frontier.RAM.WExpr.var "pt.tA")
                                                                  (Frontier.RAM.WExpr.lit 0))
                                                                (Frontier.RAM.Stmt.seq
                                                                  (Frontier.RAM.Stmt.wstore
                                                                    "pt.as"
                                                                    (Frontier.RAM.WExpr.var "pt.x")
                                                                    (Frontier.RAM.WExpr.lit 1))
                                                                  (Frontier.RAM.Stmt.seq
                                                                    (Frontier.RAM.Stmt.wstore
                                                                      "pt.GV"
                                                                      (Frontier.RAM.WExpr.var "pt.gv")
                                                                      (Frontier.RAM.WExpr.var "pt.x"))
                                                                    (Frontier.RAM.Stmt.wset
                                                                      "pt.gv"
                                                                      (Frontier.RAM.WExpr.add
                                                                        (Frontier.RAM.WExpr.var "pt.gv")
                                                                        (Frontier.RAM.WExpr.lit 1)))))
                                                                (Frontier.RAM.Stmt.skip))
                                                              (Frontier.RAM.Stmt.skip))
                                                            (Frontier.RAM.Stmt.skip)))))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wset
                                                        "pt.x"
                                                        (Frontier.RAM.WExpr.load "pt.nx" (Frontier.RAM.WExpr.var "pt.x")))
                                                      (Frontier.RAM.Stmt.wset
                                                        "pt.c"
                                                        (Frontier.RAM.WExpr.sub
                                                          (Frontier.RAM.WExpr.var "pt.c")
                                                          (Frontier.RAM.WExpr.lit 1))))))
                                                (Frontier.RAM.Stmt.seq
                                                  (Frontier.RAM.Stmt.ite
                                                    (Frontier.RAM.WExpr.lt
                                                      (Frontier.RAM.WExpr.var "pt.gs")
                                                      (Frontier.RAM.WExpr.var "pt.gv"))
                                                    (Frontier.RAM.Stmt.seq
                                                      (Frontier.RAM.Stmt.wstore
                                                        "pt.GO"
                                                        (Frontier.RAM.WExpr.var "pt.ng")
                                                        (Frontier.RAM.WExpr.var "pt.gs"))
                                                      (Frontier.RAM.Stmt.seq
                                                        (Frontier.RAM.Stmt.wstore
                                                          "pt.GL"
                                                          (Frontier.RAM.WExpr.var "pt.ng")
                                                          (Frontier.RAM.WExpr.sub
                                                            (Frontier.RAM.WExpr.var "pt.gv")
                                                            (Frontier.RAM.WExpr.var "pt.gs")))
                                                        (Frontier.RAM.Stmt.wset
                                                          "pt.ng"
                                                          (Frontier.RAM.WExpr.add
                                                            (Frontier.RAM.WExpr.var "pt.ng")
                                                            (Frontier.RAM.WExpr.lit 1)))))
                                                    (Frontier.RAM.Stmt.skip))
                                                  (Frontier.RAM.Stmt.wset
                                                    "pt.g"
                                                    (Frontier.RAM.WExpr.add
                                                      (Frontier.RAM.WExpr.var "pt.g")
                                                      (Frontier.RAM.WExpr.lit 1)))))))))))
                                  (Frontier.RAM.Stmt.seq
                                    (Frontier.RAM.Stmt.wset "pt.j" (Frontier.RAM.WExpr.lit 0))
                                    (Frontier.RAM.Stmt.while
                                      (Frontier.RAM.WExpr.lt
                                        (Frontier.RAM.WExpr.var "pt.j")
                                        (Frontier.RAM.WExpr.var "pt.gv"))
                                      (Frontier.RAM.Stmt.seq
                                        (Frontier.RAM.Stmt.wset
                                          "pt.x"
                                          (Frontier.RAM.WExpr.load "pt.GV" (Frontier.RAM.WExpr.var "pt.j")))
                                        (Frontier.RAM.Stmt.seq
                                          (Frontier.RAM.Stmt.wstore
                                            "pt.as"
                                            (Frontier.RAM.WExpr.var "pt.x")
                                            (Frontier.RAM.WExpr.lit 0))
                                          (Frontier.RAM.Stmt.wset
                                            "pt.j"
                                            (Frontier.RAM.WExpr.add
                                              (Frontier.RAM.WExpr.var "pt.j")
                                              (Frontier.RAM.WExpr.lit 1))))))))))))))
                    (Frontier.RAM.Stmt.seq
                      (Frontier.RAM.Stmt.seq
                        (Frontier.RAM.Stmt.wset "mk.j" (Frontier.RAM.WExpr.var "fp.sb"))
                        (Frontier.RAM.Stmt.seq
                          (Frontier.RAM.Stmt.wset
                            "mk.e"
                            (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "fp.sb") (Frontier.RAM.WExpr.var "fp.sn")))
                          (Frontier.RAM.Stmt.while
                            (Frontier.RAM.WExpr.lt (Frontier.RAM.WExpr.var "mk.j") (Frontier.RAM.WExpr.var "mk.e"))
                            (Frontier.RAM.Stmt.seq
                              (Frontier.RAM.Stmt.wset
                                "mk.x"
                                (Frontier.RAM.WExpr.load "S" (Frontier.RAM.WExpr.var "mk.j")))
                              (Frontier.RAM.Stmt.seq
                                (Frontier.RAM.Stmt.wstore
                                  "fp.inS"
                                  (Frontier.RAM.WExpr.var "mk.x")
                                  (Frontier.RAM.WExpr.lit 0))
                                (Frontier.RAM.Stmt.wset
                                  "mk.j"
                                  (Frontier.RAM.WExpr.add
                                    (Frontier.RAM.WExpr.var "mk.j")
                                    (Frontier.RAM.WExpr.lit 1))))))))
                      (Frontier.RAM.Stmt.seq
                        (Frontier.RAM.Stmt.seq
                          (Frontier.RAM.Stmt.wset "mk.j" (Frontier.RAM.WExpr.var "fp.ob"))
                          (Frontier.RAM.Stmt.seq
                            (Frontier.RAM.Stmt.wset
                              "mk.e"
                              (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "fp.ob") (Frontier.RAM.WExpr.var "fp.ql")))
                            (Frontier.RAM.Stmt.while
                              (Frontier.RAM.WExpr.lt (Frontier.RAM.WExpr.var "mk.j") (Frontier.RAM.WExpr.var "mk.e"))
                              (Frontier.RAM.Stmt.seq
                                (Frontier.RAM.Stmt.wset
                                  "mk.x"
                                  (Frontier.RAM.WExpr.load "fp.Q" (Frontier.RAM.WExpr.var "mk.j")))
                                (Frontier.RAM.Stmt.seq
                                  (Frontier.RAM.Stmt.wstore
                                    "fp.inQ"
                                    (Frontier.RAM.WExpr.var "mk.x")
                                    (Frontier.RAM.WExpr.lit 0))
                                  (Frontier.RAM.Stmt.wset
                                    "mk.j"
                                    (Frontier.RAM.WExpr.add
                                      (Frontier.RAM.WExpr.var "mk.j")
                                      (Frontier.RAM.WExpr.lit 1))))))))
                        (Frontier.RAM.Stmt.seq
                          (Frontier.RAM.Stmt.wset "mk.j" (Frontier.RAM.WExpr.lit 0))
                          (Frontier.RAM.Stmt.seq
                            (Frontier.RAM.Stmt.wset "mk.e" (Frontier.RAM.WExpr.var "ct.o"))
                            (Frontier.RAM.Stmt.while
                              (Frontier.RAM.WExpr.lt (Frontier.RAM.WExpr.var "mk.j") (Frontier.RAM.WExpr.var "mk.e"))
                              (Frontier.RAM.Stmt.seq
                                (Frontier.RAM.Stmt.wset
                                  "mk.x"
                                  (Frontier.RAM.WExpr.load "fp.TV" (Frontier.RAM.WExpr.var "mk.j")))
                                (Frontier.RAM.Stmt.seq
                                  (Frontier.RAM.Stmt.wstore
                                    "fp.fm"
                                    (Frontier.RAM.WExpr.var "mk.x")
                                    (Frontier.RAM.WExpr.lit 0))
                                  (Frontier.RAM.Stmt.wset
                                    "mk.j"
                                    (Frontier.RAM.WExpr.add
                                      (Frontier.RAM.WExpr.var "mk.j")
                                      (Frontier.RAM.WExpr.lit 1))))))))))))))))
        (Frontier.RAM.Stmt.seq
          (Frontier.RAM.Stmt.wstore "W.len" (Frontier.RAM.WExpr.var "lvl") (Frontier.RAM.WExpr.lit 0))
          (Frontier.RAM.Stmt.seq
            (Frontier.RAM.Stmt.wset "fp.i" (Frontier.RAM.WExpr.lit 0))
            (Frontier.RAM.Stmt.while
              (Frontier.RAM.WExpr.lt (Frontier.RAM.WExpr.var "fp.i") (Frontier.RAM.WExpr.var "fp.wl"))
              (Frontier.RAM.Stmt.seq
                (Frontier.RAM.Stmt.wset
                  "fp.y"
                  (Frontier.RAM.WExpr.load
                    "fp.W"
                    (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "fp.ob") (Frontier.RAM.WExpr.var "fp.i"))))
                (Frontier.RAM.Stmt.seq
                  (Frontier.RAM.Stmt.seq
                    (Frontier.RAM.Stmt.wstore
                      "W"
                      (Frontier.RAM.WExpr.add
                        (Frontier.RAM.WExpr.mul (Frontier.RAM.WExpr.var "lvl") (Frontier.RAM.WExpr.var "n"))
                        (Frontier.RAM.WExpr.load "W.len" (Frontier.RAM.WExpr.var "lvl")))
                      (Frontier.RAM.WExpr.var "fp.y"))
                    (Frontier.RAM.Stmt.wstore
                      "W.len"
                      (Frontier.RAM.WExpr.var "lvl")
                      (Frontier.RAM.WExpr.add
                        (Frontier.RAM.WExpr.load "W.len" (Frontier.RAM.WExpr.var "lvl"))
                        (Frontier.RAM.WExpr.lit 1))))
                  (Frontier.RAM.Stmt.seq
                    (Frontier.RAM.Stmt.wstore "fp.inW" (Frontier.RAM.WExpr.var "fp.y") (Frontier.RAM.WExpr.lit 0))
                    (Frontier.RAM.Stmt.wset
                      "fp.i"
                      (Frontier.RAM.WExpr.add (Frontier.RAM.WExpr.var "fp.i") (Frontier.RAM.WExpr.lit 1)))))))))))

theorem fpAt_eq_raw : fpAt = fpAtRaw := rfl

open Frontier Frontier.RAM Frontier.CHD Frontier.CHD.BL2 Frontier.CHD.RamSpine in
/-- **agent-01's `FPB` for the literal program.** -/
theorem fpB_raw {G : Graph} {s : Fin G.n} {T : ℕ → ℕ} (DL : DLayer G s T)
    (Inv : Finset (Fin G.m) → Prop) {k hins hext LF : ℕ} {body : Stmt} {τf Mf : ℕ → ℕ} {l : ℕ}
    (hk2 : 2 ≤ k) (hhext : k ≤ hext) (hsort : ∀ u, (L6.outL G u).Pairwise (SortedRel G s))
    (hDLA : ∀ a ∈ DL.dWA, a ∉ fpAtWA (G := G) (s := s))
    (hDLV : ∀ a ∈ DL.dVA, a ∉ fpAtVA (G := G) (s := s))
    (hDLR : ∀ a ∈ DL.dWR, a ∉ fpAtWR (G := G) (s := s)) :
    RamBody.FPB DL (phiI G s k hins hext LF) Inv (fpC G s (L6.outL G) k hins hext) LF body fpAtRaw
      τf Mf 524 351 l := by
  rw [← fpAt_eq_raw]; exact fpB_inst DL Inv hk2 hhext hsort hDLA hDLV hDLR

end Frontier.CHD.BL2Inst
