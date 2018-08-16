(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const y ListLoc)
(declare-const z ListLoc)

(assert 
    (sep 
        (pton y z) 
        (pton x null)
        (= y x))
)
(check-sat)
(get-model)
