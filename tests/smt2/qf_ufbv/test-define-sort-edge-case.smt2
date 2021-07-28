;; this file tests an edge case
;; SMT-LIB allows using sort symbols as
;; the name of defined sort as long as
;; it's not included in the current logic
;; (i.e. the name Int is available if there
;;  are no integers in the logic's signature)
(set-logic QF_UFBV)
(define-sort Int () (_ BitVec 32))
(declare-const x Int)
(declare-const y Int)
(assert (= ((_ extract 31 31) x) #b1))
(assert (= ((_ extract 31 31) y) #b0))
(assert (bvult x y))
(check-sat)

