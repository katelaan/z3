(set-logic SLSTAR)
(declare-const x TreeLoc)
(declare-const y TreeLoc)
(declare-const z TreeLoc)

(assert (sep
            (tree y) 
            (tree x z)
        ))
(check-sat)
