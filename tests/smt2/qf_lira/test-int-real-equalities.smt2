(set-logic QF_LIRA)
(set-option :incremental true)
(declare-const x Real)
(declare-const i Int)
; outside strict mode, = and distinct take an Int argument next to a Real
; one as a Real too
(assert (= (* 2 x) 1))
(check-sat)
; x is 1/2, so no Int equals it
(push 1)
(assert (= x i))
(check-sat)
(pop 1)
(assert (distinct i x 0))
(check-sat)
(assert (< (- 1) i 1))
(check-sat)
