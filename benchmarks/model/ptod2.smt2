(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const d Int)
(assert (list x))
(assert ( sep 
    (ptod x d) 
    (pton x (as null ListLoc))
    (= d 5)
    ))

(check-sat)
(get-model)