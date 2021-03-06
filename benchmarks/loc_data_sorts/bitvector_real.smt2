(set-logic SLSTAR)
(define-sort BV () (_ BitVec 3))

(declare-const x (ListLoc BV Real))
(declare-const y (ListLoc BV Real))
(declare-const z (ListLoc BV Real))

(assert (list (unary (= (as alpha Real) 0.5)) x ))

(assert (sep 
   (pton x y) 
   (ptod x 0.5)
   (pton y z)
   (ptod y 0.5)
   ))

(check-sat)
(get-model)