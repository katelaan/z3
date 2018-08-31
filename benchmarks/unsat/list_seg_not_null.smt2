(set-logic SLSTAR)
(declare-const x ListLoc)

(assert  (sep 
    (list list.null x)
    (distinct x list.null)    
))

(check-sat)