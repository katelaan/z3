(set-logic SLSTAR)
(declare-const a Bool)
(declare-const b ListLoc)

(assert (sep (list b) a (= a false) ))

(check-sat)