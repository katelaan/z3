(set-logic SLSTAR)
(declare-const x ListLoc)

(assert  (sep 
    (list (as null ListLoc) x)
    (distinct x (as null ListLoc))    
))

(check-sat)