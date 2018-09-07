(set-logic SLSTAR)
(declare-const x TreeLoc)
(declare-const y TreeLoc)

(assert (tree (as null TreeLoc) x y) )

(check-sat)