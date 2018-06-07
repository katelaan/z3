;(declare-const x sl.list.loc) ;; head of first list
;(declare-const m sl.list.loc) ;; pivot element
;(declare-const y sl.list.loc) ;; head of second list
;(declare-const a sl.list.loc)
;(declare-const b sl.list.loc)
;(declare-const d sl.list.loc)
;(declare-const e sl.list.loc)
;(declare-const f sl.list.loc)
;(declare-const g sl.list.loc)
;(declare-const xdata Int)
;(declare-const mdata Int)
;(declare-const ydata Int)
;(declare-const adata Int)
;(declare-const bdata Int)
;(declare-const ddata Int)
;(declare-const edata Int)
;(declare-const fdata Int)
;(declare-const M Int) ;; the pivot data
;(assert (sl.sepcon
;         (sl.sepcon
;          (sl.list.dpred.unary1 (< sl.alpha M) x m)
;          (sl.list.dpred.unary (> sl.alpha M) y))
;         (sl.sepcon
;          (sl.list.next m y)
;          (sl.list.data m M))))
;;; Additionally assert that all elements are distinct
;(assert (sl.list.dpred.next (not (= sl.alpha sl.beta)) x))
;;; Assert a few pointers as a classical conjunction to force length
;(assert (sl.sepcon
;         (sl.sepcon
;          (sl.sepcon
;           (sl.sepcon (sl.list.pointsto x a) (sl.list.pointsto a b))
;           (sl.sepcon (sl.list.pointsto b m) (sl.list.pointsto m y)))
;          (sl.sepcon
;           (sl.sepcon (sl.list.pointsto y d) (sl.list.pointsto d e))
;           (sl.sepcon (sl.list.pointsto e f) (sl.list.pointsto f g))))
;         (sl.sepcon
;          (sl.sepcon
;           (sl.sepcon (sl.list.data x xdata) (sl.list.data a adata))
;           (sl.sepcon (sl.list.data b bdata) (sl.list.data m mdata)))
;          (sl.sepcon
;           (sl.sepcon (sl.list.data y ydata) (sl.list.data d ddata))
;           (sl.sepcon (sl.list.data e edata) (sl.list.data f fdata))))))


(declare-const x ListLoc) ;; head of first list
(declare-const m ListLoc) ;; pivot element
(declare-const y ListLoc) ;; head of second list
(declare-const a ListLoc)
(declare-const b ListLoc)
(declare-const d ListLoc)
(declare-const e ListLoc)
(declare-const f ListLoc)
(declare-const g ListLoc)
(declare-const xdata Int)
(declare-const mdata Int)
(declare-const ydata Int)
(declare-const adata Int)
(declare-const bdata Int)
(declare-const ddata Int)
(declare-const edata Int)
(declare-const fdata Int)
(declare-const M Int) ;; the pivot data

(define-fun lt-M ((x Int)) Bool (< x M) )
(define-fun gt-M ((x Int)) Bool (> x M) )
(assert (sep
          (list (unary (lt-M alpha)) x m)
          (list (unary (gt-M alpha)) y)
          (pton m y)
          (pton m M) ))
;; Additionally assert that all elements are distinct
(assert (list (next (distinct alpha beta)) x))
;; Assert a few pointers as a classical conjunction to force length
(assert 
  (sep
    (pton x a) (pton a b) (pton b m) (pton m y)
    (pton y d) (pton d e) (pton e f) (pton f g)
    (ptod x xdata) 
    (ptod a adata)
    (ptod b bdata) 
    (ptod m mdata)
    (ptod y ydata) 
    (ptod d ddata)
    (ptod e edata) 
    (ptod f fdata) ))
