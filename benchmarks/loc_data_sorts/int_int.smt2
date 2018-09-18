(set-logic SLSTAR)

(declare-const x (ListLoc Int Int))
(declare-const y (ListLoc Int Int))
(declare-const z (ListLoc Int Int))

(assert (list (unary (= alpha 5)) x ))

(assert (sep 
   (pton x y) 
   (ptod x 5)
   (pton y z)
   (ptod y 5)
   ))

(check-sat)
(get-model)