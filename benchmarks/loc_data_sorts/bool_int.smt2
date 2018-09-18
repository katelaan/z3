(set-logic SLSTAR)

(declare-const x (ListLoc Bool Int))
(declare-const y (ListLoc Bool Int))
(declare-const z (ListLoc Bool Int))

(assert (list (unary (= alpha 5)) x ))

(assert (sep 
   (pton x y) 
   (ptod x 5)
   ))

(check-sat)
(get-model)