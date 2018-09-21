(set-logic SLSTAR)

(declare-const a ListLoc)
(declare-const b ListLoc)
(declare-const c ListLoc)
(declare-const d ListLoc)
(declare-const e ListLoc)
(declare-const f ListLoc)

(assert (sep 
          (list a)
          (list b)
          (list d)
          (= c d)
          (= b e)
        ))

(assert (sep 
          (list d)
          (list e)
          (list f)
        ))

(check-sat)
(get-model)