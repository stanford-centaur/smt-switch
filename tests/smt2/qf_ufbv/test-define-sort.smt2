(set-logic QF_UFBV)
(define-sort Word () (_ BitVec 32))
(declare-const x Word)
(declare-const y Word)
(assert (= ((_ extract 31 31) x) #b1))
(assert (= ((_ extract 31 31) y) #b0))
(assert (bvult x y))
(check-sat)

