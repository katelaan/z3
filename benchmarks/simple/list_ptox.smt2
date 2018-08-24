(set-logic SLSTAR)

(declare-const x  ListLoc)
(declare-const y  ListLoc)
(declare-const z  ListLoc)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (list (next (> alpha beta)) x))
;; Assert a few pointers as a classical conjunction to force size
(assert 
      (sep
            (pton x y)
            (pton y z)
            (ptod x a)
            (ptod y b)))
(check-sat)