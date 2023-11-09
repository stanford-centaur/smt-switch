(set-logic QF_SLIA)

(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const substryx String)
(declare-const empty String)
(declare-const lenx Int)
(declare-const leny Int)
(declare-const lenz Int)

(assert (= lenx (str.len x)))
(assert (= leny (str.len y)))
(assert (= lenz (str.len z)))

(declare-const xx String)
(declare-const xy String)
(declare-const yx String)
(declare-const xxx String)
(declare-const xyy String)

(assert (= xx (str.++ x x)))
(assert (= xy (str.++ x y)))
(assert (= yx (str.++ y x)))
(assert (= xxx (str.++ xx x)))
(assert (= xyy (str.++ xy y)))

(assert (= substryx (str.substr yx leny lenx)))
(assert (= empty ""))

;StrLt
(assert (str.< x y))
(assert (str.< yx xy))
;StrLeq StrConcat
(assert (str.<= z xy))
;StrLen
(assert (< 0 lenz))
;StrConcat
(assert (not (= xy yx)))
;StrSubstr
(assert (= x substryx))
(assert (not (= y substryx)))
(assert (= empty (str.substr x lenx lenx)))
(assert (= empty (str.substr x (- 1) lenx)))
;StrAt
(assert (= (str.len (str.at y 0)) 1))
(assert (= empty (str.at x lenx)))
(assert (= empty (str.at x (- 1))))
;StrContains
(assert (not (str.contains x y)))
(assert (str.contains xy y))
;StrIndexof
(assert (= lenx (str.indexof xyy y (- lenx 1))))
(assert (= 0 (str.indexof xy empty 0)))
(assert (= (- 1) (str.indexof xy x (- 1))))
(assert (= (- 1) (str.indexof x y lenx)))
(assert (= (- 1) (str.indexof x y 0)))
;StrReplace
(assert (= xx (str.replace xy y x)))
(assert (= xy (str.replace y empty x)))
;StrReplaceAll
(assert (= xxx (str.replace_all xyy y x)))
(assert (= xyy (str.replace_all xyy empty x)))
;StrPrefixof
(assert (str.prefixof x xyy))
(assert (not (str.prefixof "1" "A")))
;StrSuffixof
(assert (str.suffixof y xyy))
(assert (not (str.suffixof "1" "A")))
;StrIsDigit
(assert (str.is_digit "1"))
(assert (not (str.is_digit "A")))
(assert (not (str.is_digit "10")))

(check-sat)
