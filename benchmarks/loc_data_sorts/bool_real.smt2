(set-logic SLSTAR)

(declare-const x (ListLoc Bool Real))
(declare-const y (ListLoc Bool Real))
(declare-const z (ListLoc Bool Real))

(assert (list (unary (= (as alpha Real) 0.5)) x ))

(assert (sep 
   (pton x y) 
   (ptod x 0.5)
   ))

(check-sat)
(get-model)