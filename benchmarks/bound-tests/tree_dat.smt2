(set-logic SLSTAR)
(declare-const x TreeLoc)
(declare-const y ListLoc)
(declare-const z ListLoc)

(assert (not (tree (left (< alpha beta)) (right (> alpha beta)) x) ) )

(check-sat)

