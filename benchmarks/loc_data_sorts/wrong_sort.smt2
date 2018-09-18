(set-logic SLSTAR)

(declare-const x (ListLoc Int Bool ))
(declare-const y (ListLoc Int Bool ))
(declare-const z (ListLoc Int Bool ))

(assert (list (unary (= (as alpha Bool) true)) x ))

(assert (sep 
   (pton x y) 
   (ptod x 5)
   ))

(check-sat)