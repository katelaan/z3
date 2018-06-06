;(declare-const a sl.list.loc)
;(declare-const b sl.list.loc)
;(declare-const c sl.list.loc)
;(declare-const d sl.list.loc)
;(declare-const e sl.list.loc)
;(declare-const adata Int)
;(declare-const bdata Int)
;(declare-const cdata Int)
;(declare-const ddata Int)
;(assert (sl.list.dpred.next (< sl.alpha sl.beta) a))
;;; Assert a few pointers as a classical conjunction to force length
;(assert (sl.sepcon
;         (sl.sepcon
;          (sl.sepcon (sl.list.pointsto a b) (sl.list.pointsto b c))
;          (sl.sepcon (sl.list.pointsto c d) (sl.list.pointsto d e)))
;         (sl.sepcon
;          (sl.sepcon (sl.list.data a adata) (sl.list.data b bdata))
;          (sl.sepcon (sl.list.data c cdata) (sl.list.data d ddata)))))


(declare-const a ListLoc)
(declare-const b ListLoc)
(declare-const c ListLoc)
(declare-const d ListLoc)
(declare-const e ListLoc)
(declare-const adata Int)
(declare-const bdata Int)
(declare-const cdata Int)
(declare-const ddata Int)

(assert (List (data <) a))
;; Assert a few pointers as a classical conjunction to force length
(assert 
    (sep
        (List a b c d e) 
        (pto a adata)
        (pto b bdata)
        (pto c cdata)
        (pto d ddata) ))