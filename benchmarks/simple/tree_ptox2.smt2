(set-logic SLSTAR)

(declare-const x  TreeLoc)
(declare-const l  TreeLoc)
(declare-const r  TreeLoc)
(declare-const ll TreeLoc)
;(declare-const lr TreeLoc)
;(declare-const rl TreeLoc)
;(declare-const rr TreeLoc)
(declare-const xdata Int)
(declare-const ldata Int)
(declare-const rdata Int)
;(assert (tree (left (> alpha beta)) (right (> alpha beta)) x))
(assert (tree x))
;; Assert a few pointers as a classical conjunction to force size
(assert 
      (sep
            (ptolr x l r)
            (ptolr l null null)
            (ptolr r null null)
            (ptod x xdata)
            (ptod r rdata)
            (ptod l ldata) ))
(check-sat)