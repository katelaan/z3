(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const y ListLoc)
(declare-const z ListLoc)

(assert (list y))
(assert 
  (sep  (pton x y) (pton y z) ) 
)
(check-sat)

