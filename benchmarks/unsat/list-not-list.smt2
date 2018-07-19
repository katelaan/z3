(set-logic SLSTAR)

(declare-const a ListLoc)
(declare-const b ListLoc)
(declare-const c ListLoc)

(assert (sep 
	  (list a)
	  (list b)
	  (list c)))

(assert (not(sep 
	  (list a)
	  (list b)
	  (list c))))

(check-sat)
