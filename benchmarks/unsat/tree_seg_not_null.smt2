(set-logic SLSTAR)
(declare-const x TreeLoc)

(assert  (sep 
    (tree tree.null x) 
    (distinct x tree.null)    
))

(check-sat)