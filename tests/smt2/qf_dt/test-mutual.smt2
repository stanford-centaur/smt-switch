(set-logic QF_DTLIA)
(declare-datatypes ( (Tree 0) (TreeList 0) ) (
   ; Tree
   ( (node (value Int) (children TreeList )) )
   ( (empty) (insert (head Tree) (tail TreeList)) )
 ))

(declare-const emptytl TreeList)
(declare-const t Tree)
(declare-const start Tree)
(declare-const x Int)
(declare-const y Int)

(assert (= emptytl empty))
(assert (= t (node x emptytl)))
(assert (= (value t) y))
(check-sat)

(assert (distinct x y))
(check-sat)