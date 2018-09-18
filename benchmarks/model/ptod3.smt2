(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const d Int)

(assert (list x) )
(assert (list (as null ListLoc) ))
(check-sat)
(get-model)