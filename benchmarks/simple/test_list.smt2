(set-logic SLSTAR)
(declare-const x ListLoc)
(declare-const y ListLoc)
(declare-const z ListLoc)
(declare-const z1 ListLoc)
(declare-const z2 ListLoc)

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(define-fun eq3 ((x!1 Int) ) Bool
   (= x!1 3)
)

;(assert (list (next (< alpha beta)) x z2) )
;(assert (list (unary (eq3 alpha)) x ) )
;(assert 
;  (sep
;   (pton x y)
;   (pton y z)
;   (pton z z1)
;   (ptod x a) 
;   (ptod y b)
;   (ptod z c)
;   (distinct z1 z2)
;   ;(distinct x y z z1)
;  ))

(assert (not (list x)))


(check-sat)
(get-model)