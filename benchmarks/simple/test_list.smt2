(set-logic SLSTAR)
(declare-const a ListLoc)

(assert (list a))
(check-sat)
