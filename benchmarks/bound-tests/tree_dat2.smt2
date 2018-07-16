(set-logic SLSTAR)
(declare-const x TreeLoc)
(declare-const y TreeLoc)

(assert 
    (not (sep
        (tree (left  (> alpha beta)) x)
        (tree (right (< alpha beta)) y)
        (tree (right (< alpha beta)) y)
    )))

(check-sat)