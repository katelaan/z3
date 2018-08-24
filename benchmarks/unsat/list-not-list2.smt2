(set-logic SLSTAR)

(declare-const a ListLoc)
(declare-const b ListLoc)
(declare-const c ListLoc)

(assert (list a))

(assert (not (list a)))

(check-sat)
