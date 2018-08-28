(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const y ListLoc)

(assert 
  (and  
    (list x) 
    (sep 
      (list x) 
      (list y)
      (distinct y list.null) )))
(check-sat)
