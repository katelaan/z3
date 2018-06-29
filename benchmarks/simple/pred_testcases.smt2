; syntax tests for sl-star predicates

(declare-const t TreeLoc)
(declare-const l ListLoc)


(define-sort BV () (_ BitVec 4))

(declare-const lint1 (ListLoc Int))
(declare-const lint2 (ListLoc Int))
(declare-const lbv1 (ListLoc BV))
(declare-const lbv2 (ListLoc BV))
(declare-const lbv3 (ListLoc (_ BitVec 3)))

(declare-const tint1 (TreeLoc Int))
(declare-const tint2 (TreeLoc Int))
(declare-const tbv1 (TreeLoc BV))
(declare-const tbv2 (TreeLoc BV))
(declare-const tbv3 (TreeLoc (_ BitVec 3)))

(declare-const x BV)
(declare-const y Int)

(assert (tree (unary (+ alpha beta)) t) ) ;will fail function is not bool TODOsl currently ok
(assert (tree t t t t (unary (> alpha beta)) ) ) ;will fail dpred at the end
(assert (tree t t t t ) ) ;correct
(assert (tree t ) ) ;correct
(assert (tree (unary (> alpha beta)) (unary (> alpha beta)) (left (> alpha beta)) t t t t ) ) ;correct
(assert (tree (unary (> alpha beta)) (unary (> alpha beta)) (left (> alpha beta)) t t t t 2 ) ) ;will fail, Int at end
(assert (tree (unary (> alpha beta)) (unary (> alpha beta)) (left (> alpha beta)) t t 2 t t ) ) ;will fail, Int in between
(assert tree ) ; will fail no arguments
(assert (tree (unary (> alpha beta)) )) ; will fail no tree loc
(assert (tree (next (> alpha beta)) t )) ; invalid dpred for tree but syntax correct

(assert (list (unary (+ alpha beta)) l) ) ;will fail function is not bool  TODOsl currently ok
(assert (list (next (+ alpha beta)) l )) ;will fail function is not bool  TODOsl currently ok
(assert (list l l l l (unary (> alpha beta)) ) ) ;will fail dpred at the end
(assert (list l l l l ) ) ;correct
(assert (list l ) ) ;correct
(assert (list (unary (> alpha beta)) (unary (> alpha beta)) (left (> alpha beta)) l l l l ) ) ;correct
(assert (list (unary (> alpha beta)) (unary (> alpha beta)) (left (> alpha beta)) l l l l 2 ) ) ;will fail, Int at end
(assert (list (unary (> alpha beta)) (unary (> alpha beta)) (left (> alpha beta)) l l 2 l l ) ) ;will fail, Int in between
(assert list ) ; will fail no arguments
(assert (list (unary (> alpha beta)) )) ; will fail no list loc
(assert (list (next (> alpha beta)) l )) ; invalid dpred for list but syntax correct

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

(assert (ptod tint1 x)) ; correct
(assert (ptod tint2 x)) ; correct
(assert (ptod lint1 x)) ; correct
(assert (ptod lint2 x)) ; correct
(assert (ptod x tint1)) ; fail 1st argument must be Tree or ListLoc

(assert (tree l)) ; fail tree uses ListLoc
(assert (list t)) ; fail list uses TreeLoc
(assert (list tint1 lint2)) ; fail list uses TreeLoc

(assert (tree tint1 tint2)) ; correct
(assert (tree tint1 tbv1)) ; fail two different sorts
(assert (tree tint1 tint2 tbv1)) ; fail two different sorts
(assert (tree tbv1 tbv2 tbv3)) ; fail same sort different parameters TODOsl currently ok

(assert (list lint1 lint2)) ; fail list uses TreeLoc
(assert (list lint1 lbv1)) ; fail two different sorts
(assert (list lint1 lint2 lbv1)) ; fail two different sorts
(assert (list lbv1 lbv2 lbv3)) ; fail same sort different parameters TODOsl currently ok