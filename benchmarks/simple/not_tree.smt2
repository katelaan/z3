(set-logic SLSTAR)
(declare-const x TreeLoc)
(assert (not (tree x)))
(check-sat)