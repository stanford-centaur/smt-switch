(set-logic QF_S)

(declare-fun x () String)
(declare-fun y () String)

(assert (not (= x y)))

(check-sat)

