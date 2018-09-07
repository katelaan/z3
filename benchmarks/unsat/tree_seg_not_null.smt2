(set-logic SLSTAR)
(declare-const x TreeLoc)

(assert  (sep 
    (tree (as null TreeLoc) x) 
    (distinct x (as null TreeLoc))    
))

(check-sat)