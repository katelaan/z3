(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const y ListLoc)
(declare-const z ListLoc)

(assert (not (list (next (= alpha beta)) x) ) )

(check-sat)

