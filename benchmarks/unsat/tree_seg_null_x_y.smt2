(set-logic SLSTAR)
(declare-const x TreeLoc)
(declare-const y TreeLoc)

(assert (tree tree.null x y) )

(check-sat)