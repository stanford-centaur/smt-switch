(set-logic QF_DT)
(declare-datatype Color  (
   (red) (green) (blue) )
)

(declare-const c0 Color)
(declare-const c1 Color)
(declare-const c2 Color)

(assert (or ((_ is red) c0) ((_ is red) c1)))
(assert (or ((_ is green) c1) ((_ is green) c2)))
(assert ((_ is blue) c2))

;; so far only satisfiable model is c0 = red, c1 = green, c2 = blue
;; to prove this, assert the negation of that
(assert (not (and
              ((_ is red) c0)
              ((_ is green) c1)
              ((_ is blue) c2))))

(check-sat)