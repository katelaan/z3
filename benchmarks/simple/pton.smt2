(set-logic SLSTAR)
(declare-const y ListLoc)
(declare-const z ListLoc)
(declare-const x ListLoc)

(assert 
    (sep 
        (pton y z)
        (pton z (as null ListLoc))
        (pton x (as null ListLoc))
    )
)
(check-sat)

