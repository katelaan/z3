(set-logic SLSTAR)

(declare-const x (ListLoc Int Real))
(declare-const y (ListLoc Int Real))
(declare-const z (ListLoc Int Real))

(assert (list (unary (= (as alpha Real) 0.5)) x ))

(assert (sep 
   (pton x y) 
   (ptod x 0.5)
   (pton y z)
   (ptod y 0.5)
   ))

(check-sat)
(get-model)