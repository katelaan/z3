(set-logic SLSTAR)
(declare-const y ListLoc)
(declare-const z ListLoc)

(assert 
   (sep (pton y z) (pton y (as null ListLoc)))
)
(check-sat)

