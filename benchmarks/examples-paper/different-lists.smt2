;(declare-const x sl.list.loc)
;(declare-const y sl.list.loc)
;(declare-const b sl.list.loc)
;(declare-const d sl.list.loc)
;(declare-const xdata Int)
;(declare-const ydata Int)
;(declare-const bdata Int)
;(declare-const ddata Int)
;(declare-const A Int)
;(assert (sl.sepcon (sl.list.dpred.unary (= sl.alpha sl.alpha) x)
;                   (sl.list.dpred.unary (not (= sl.alpha A)) y)))
;; Should force A to occur in the list that starts in X. But currently doesn't...
;(assert (not (sl.sepcon (sl.list.dpred.unary (not (= sl.alpha A)) x)
;                        (sl.list.dpred.unary (= sl.alpha sl.alpha) y))))
;(assert (sl.sepcon (sl.sepcon (= A 9001)
;                              (sl.sepcon
;                               (sl.sepcon (sl.list.pointsto x b) (sl.list.pointsto b sl.list.null))
;                               (sl.sepcon (sl.list.pointsto y d) (sl.list.pointsto d sl.list.null))))
;                              (sl.sepcon
;                               (sl.sepcon (sl.list.data x xdata) (sl.list.data b bdata))
;                               (sl.sepcon (sl.list.data y ydata) (sl.list.data d ddata)))))


(declare-const x ListLoc)
(declare-const y ListLoc)
(declare-const b ListLoc)
(declare-const d ListLoc)
(declare-const xdata Int)
(declare-const ydata Int)
(declare-const bdata Int)
(declare-const ddata Int)
(declare-const A Int)

(define-fun notA ( (x Int) ) Bool (not (= x A)) )
(assert 
    (sep 
        (List (data =) x)
        (List (data notA) y) ))
; Should force A to occur in the list that starts in X. But currently doesn't...
(assert (not (sep 
            (List (data notA) x)
            (List (data =) y) )))
(assert (sep 
            (= A 9001)
            (List x b null) 
            (List y d null) 
            (pto x xdata) 
            (pto b bdata)
            (pto y ydata) 
            (pto d ddata) ))