(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const y ListLoc)
(declare-const z ListLoc)

(assert (not (list (unary (= alpha 0)) x) ) )

(check-sat)

