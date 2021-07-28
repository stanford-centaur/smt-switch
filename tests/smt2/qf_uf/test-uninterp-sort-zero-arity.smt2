(set-logic QF_UF)
(declare-sort color 0)
(declare-const red color)
(declare-const green color)
(declare-const blue color)

(assert (distinct red green blue))

(define-fun rgb ((c color)) Bool (or (= c red) (= c green) (= c blue)))

(declare-const c0 color)
(declare-const c1 color)
(declare-const c2 color)

(assert (rgb c0))
(assert (rgb c1))
(assert (rgb c2))

(check-sat)