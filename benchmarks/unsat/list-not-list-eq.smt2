(set-logic SLSTAR)

(declare-const a ListLoc)
(declare-const b ListLoc)
(declare-const c ListLoc)
(declare-const d ListLoc)

(assert (sep 
          (list a)
          (list b)
          (list d)
          (= c d)
        ))

(assert (not(sep 
          (list a)
          (list b)
          (list c)
        )))

(check-sat)