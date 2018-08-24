(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const y ListLoc)

(assert 
  (and  
    (list x) 
    (sep 
      (list x) 
      (list y) )))
(check-sat)
(get-model)
