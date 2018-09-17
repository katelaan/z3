(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const d Int)

(assert (ptod x d) )
(check-sat)
(get-model)