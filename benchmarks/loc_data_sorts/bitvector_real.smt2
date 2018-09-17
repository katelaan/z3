(set-logic SLSTAR)
(define-sort BV () (_ BitVec 3))

(declare-const x (ListLoc BV))
(declare-const y (ListLoc BV))
(declare-const z (ListLoc BV))

(assert (list (unary (= (as alpha Real) 0.5)) x ))

(assert (sep 
   (pton x y) 
   (ptod x 0.5)
   (pton y z)
   ))

(check-sat)
(get-model)