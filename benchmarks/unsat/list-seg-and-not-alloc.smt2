(set-logic SLSTAR)

(declare-const x ListLoc)
(declare-const y ListLoc)
(declare-const z ListLoc)

(assert (list (unary (= alpha 5)) x ))

(assert (sep 
   (pton x y) 
   (ptod x 5)
   (pton y z)
   ))

(check-sat)