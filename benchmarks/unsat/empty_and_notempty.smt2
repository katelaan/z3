(set-logic SLSTAR)
(declare-const y ListLoc)
(declare-const z ListLoc)

(assert 
    (and 
        (sep 
            (pton y z) 
            (= y y) )
        (= y y) ) )
(check-sat)
