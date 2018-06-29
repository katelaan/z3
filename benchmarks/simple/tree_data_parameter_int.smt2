(declare-const x (TreeLoc Int))
(declare-const z Int)

(define-sort BV () (_ BitVec 4))
(declare-const tint1 (TreeLoc Int))
(declare-const tint2 (TreeLoc Int))
(declare-const tbv1 (TreeLoc BV))
(declare-const tbv2 (TreeLoc BV))
(declare-const tbv3 (TreeLoc (_ BitVec 3)))

(assert     (tree (left (< alpha beta)) (right (> alpha beta)) x) )

(assert (tree tint1 tint2)) ; fail two different sorts