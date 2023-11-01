(set-logic QF_SLIA)

(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const lenx Int)
(declare-const leny Int)
(declare-const lenz Int)

(assert (= lenx (str.len x)))
(assert (= leny (str.len y)))

(declare-const xy String)
(declare-const yx String)

(assert (= xy (str.++ x y)))
(assert (= yx (str.++ y x)))

;StrLt
(assert (str.< x y))
(assert (str.< yx xy))
;StrLeq StrConcat
(assert (str.<= z xy))
;StrLen
(assert (< 0 lenz))
;StrConcat
(assert (not (= xy yx)))

(check-sat)
