(declare-const a TreeLoc)

(assert (tree a))
(assert (tree Real (unary (> alpha beta )) a))

(check-sat)
(get-model)