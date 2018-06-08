(declare-const t TreeLoc)
(declare-const l ListLoc)
(define-sort BV () (_ BitVec 4))
(declare-const x BV)

;(assert (tree BV (unary (> alpha beta)) t) ) ;will fail
;(assert (tree BV (unary (bvsgt alpha beta)) t) ) ;correct
;(assert (tree Real (unary (> alpha beta)) t) ) ;correct
(assert (tree (unary (+ alpha beta)) t) ) ;will fail function is not bool
(assert (tree t t t t (unary (+ alpha beta)) ) ) ;will fail dpred at the end
(assert (tree t t t t ) ) ;correct
(assert (tree t ) ) ;correct
(assert (tree (unary (+ alpha beta)) (unary (+ alpha beta)) (left (+ alpha beta)) t t t t ) ) ;correct
(assert (tree (unary (+ alpha beta)) (unary (+ alpha beta)) (left (+ alpha beta)) t t t t 2 ) ) ;will fail, Int at end
(assert (tree (unary (+ alpha beta)) (unary (+ alpha beta)) (left (+ alpha beta)) t t 2 t t ) ) ;will fail, Int in between
(assert tree ) ; will fail no arguments
(assert (tree (unary (+ alpha beta)) )) ; will fail no tree loc
(assert (tree (next (+ alpha beta)) t )) ; invalid dpred for tree but syntax correct


(assert (list (unary (+ alpha beta)) l) ) ;will fail function is not bool
(assert (list l l l l (unary (+ alpha beta)) ) ) ;will fail dpred at the end
(assert (list l l l l ) ) ;correct
(assert (list l ) ) ;correct
(assert (list (unary (+ alpha beta)) (unary (+ alpha beta)) (left (+ alpha beta)) l l l l ) ) ;correct
(assert (list (unary (+ alpha beta)) (unary (+ alpha beta)) (left (+ alpha beta)) l l l l 2 ) ) ;will fail, Int at end
(assert (list (unary (+ alpha beta)) (unary (+ alpha beta)) (left (+ alpha beta)) l l 2 l l ) ) ;will fail, Int in between
(assert list ) ; will fail no arguments
(assert (list (unary (+ alpha beta)) )) ; will fail no list loc
(assert (list (next (+ alpha beta)) l )) ; invalid dpred for list but syntax correct

(assert (pton l l)) ; correct
(assert (pton l)) ; fail only one arg
(assert (pton l l l )) ; fail three arg
(assert (pton l t )) ; fail list to tree

(assert (ptol t t)) ; correct
(assert (ptol t)) ; fail only one arg
(assert (ptol t t t )) ; fail three arg
(assert (ptol t l )) ; fail tree to list

(assert (ptor t t)) ; correct
(assert (ptor t)) ; fail only one arg
(assert (ptor t t t )) ; fail three arg
(assert (ptor t l )) ; fail tree to list

(assert (ptolr t t t)) ; correct
(assert (ptolr t t )) ; fail only two args
(assert (ptolr t t t t)) ; fail four arg
(assert (ptolr t t l )) ; fail tree to list
(assert (ptolr l t l )) ; fail tree to list
(assert (ptolr t l t )) ; fail tree to list
