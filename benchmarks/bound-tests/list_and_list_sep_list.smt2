(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const y ListLoc)
(declare-const z ListLoc)
(assert (and 
          (sep
            (list y) 
            (list x)
            (list z))
          (list y) 
         ))
(check-sat)
