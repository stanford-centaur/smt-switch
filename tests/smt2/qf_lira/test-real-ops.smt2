(set-logic QF_LIRA)
(set-option :incremental true)
(declare-const x Real)
(declare-const i Int)
; as in the SMT-LIB logic AUFLIRA, an operator over Reals takes an Int
; argument next to a Real one as a Real, and / takes every Int argument so
(assert (= (* 2 x) 1.0))
(assert (= x (/ 1 2)))
(assert (> (- x 1) (- 1)))
(check-sat)
; i < 1/2 < i + 1, so i is 0
(push 1)
(assert (< i x (+ i 1)))
(assert (distinct i 0))
(check-sat)
(pop 1)
; i / 2 is 1/2, so i is 1
(push 1)
(assert (= (/ i 2) x))
(check-sat)
(assert (distinct i 1))
(check-sat)
(pop 1)
