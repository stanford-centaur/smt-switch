(set-logic QF_UF)
(declare-const |a b| Bool)
(declare-const a Bool)

(assert |a b|)
; |a| is the symbol a
(assert (not |a|))

(set-info :status sat)
(check-sat)

(assert a)

(set-info :status unsat)
(check-sat)
