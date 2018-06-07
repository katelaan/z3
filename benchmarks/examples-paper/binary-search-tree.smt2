;(declare-const x sl.tree.loc)
;(declare-const l sl.tree.loc)
;(declare-const r sl.tree.loc)
;(declare-const ll sl.tree.loc)
;(declare-const lr sl.tree.loc)
;(declare-const rl sl.tree.loc)
;(declare-const rr sl.tree.loc)
;(declare-const xdata Int)
;(declare-const ldata Int)
;(declare-const rdata Int)
;(assert (sl.tree.dpred.left (> sl.alpha sl.beta) x))
;(assert (sl.tree.dpred.right (< sl.alpha sl.beta) x))
;; Assert a few pointers as a classical conjunction to force size
;(assert (sl.sepcon
;         (sl.sepcon (sl.tree.pointsto x l r)
;                    (sl.sepcon (sl.tree.pointsto l ll lr)
;                               (sl.tree.pointsto r rl rr)))
;         (sl.sepcon (sl.tree.data x xdata)
;                    (sl.sepcon (sl.tree.data l ldata)
;                               (sl.tree.data r rdata)))))


(declare-const x TreeLoc)
(declare-const l TreeLoc)
(declare-const r TreeLoc)
(declare-const ll TreeLoc)
(declare-const lr TreeLoc)
(declare-const rl TreeLoc)
(declare-const rr TreeLoc)
(declare-const xdata Int)
(declare-const ldata Int)
(declare-const rdata Int)
(assert    (tree (left (< alpha beta)) (right (> alpha beta)) x) )
; Assert a few pointers as a classical conjunction to force size
(assert 
      (sep
            (ptolr x l r)
            (ptolr l ll lr)
            (ptolr r rl rr)
            (ptod x xdata)
            (ptod r rdata)
            (ptod l ldata) ))

