(set-logic QF_UF)
(declare-sort U 0)
(declare-fun x () U)
(declare-fun y () U)
(declare-fun z () U)
(declare-fun f (U U) U)
(assert (= x y))
(assert (not (= (f z x) (f z y))))
(check-sat)
(exit)

