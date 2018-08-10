(set-logic SLSTAR)
(declare-const a ListLoc)
(declare-const b ListLoc)

(assert (sep 
    (list a)
    (list b)))
(check-sat)
