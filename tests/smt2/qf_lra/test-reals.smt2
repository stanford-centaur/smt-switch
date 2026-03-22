(set-logic QF_LRA)

(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)

(assert (> x 0.0))          ; x > 0
(assert (< y 5.0))          ; y < 5
(assert (= z (+ x y)))      ; z = x + y
(assert (> z (to_real 3)))  ; z > 3

(check-sat)
