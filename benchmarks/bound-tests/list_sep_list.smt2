(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const y ListLoc)
(declare-const z ListLoc)

(assert (sep
            (list y) 
            (list x)
            (list z) 
        ))
(check-sat)

