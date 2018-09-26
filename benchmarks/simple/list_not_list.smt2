(set-logic SLSTAR)

(declare-const a ListLoc)

(assert (list a))
(assert (not(list a)))

(check-sat)