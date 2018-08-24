(set-logic SLSTAR)
(declare-const a Bool)
(declare-const b ListLoc)

(assert (sep (list b) a ))
(assert (= a false))

(check-sat)