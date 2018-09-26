(set-logic SLSTAR)

(declare-const a ListLoc)
(declare-const b ListLoc)

(assert (list a))
(assert (= a b))
(assert (list b))

;(assert (list b))
;(assert true)
;(assert (list b))

(check-sat)