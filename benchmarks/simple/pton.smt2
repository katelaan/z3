(set-logic SLSTAR)
(declare-const y ListLoc)
(declare-const z ListLoc)

(assert 
   (pton y z)
)
(check-sat)

