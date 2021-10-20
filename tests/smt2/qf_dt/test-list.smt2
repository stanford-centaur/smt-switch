(set-logic QF_DTLIA)
(set-option :incremental true)
(set-option :produce-unsat-assumptions true)

(declare-datatypes ((list 0)) (
 (
    (cons (head Int) (tail list))
    (nil)
 )
))

(declare-const l0 list)
(declare-const l1 list)

(assert (= l0 l1))
(check-sat-assuming ( (distinct (tail l0) (tail l1))
                      (distinct (head l0) (head l1))))
(get-unsat-assumptions)