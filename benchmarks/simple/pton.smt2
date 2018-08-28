(set-logic SLSTAR)
(declare-const y ListLoc)
(declare-const z ListLoc)
(declare-const x ListLoc)

(assert 
    (sep 
        (pton y z)
        (pton z list.null)
        (pton x list.null)
    )
)
(check-sat)

