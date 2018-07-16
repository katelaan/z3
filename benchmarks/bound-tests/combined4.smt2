(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const y ListLoc)
(declare-const z ListLoc)
(declare-const a TreeLoc)
(declare-const b TreeLoc)
(declare-const c TreeLoc)
(assert (and 
          (sep
            (list y) 
            (list x)
            (list z) 
            (tree a) 
            (tree b c) )
          (list y) 
         ))
(check-sat)


