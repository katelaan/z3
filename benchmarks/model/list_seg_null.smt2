(set-logic SLSTAR)
(declare-const x ListLoc)

(assert  (list (as null ListLoc) x ))

(check-sat)
(get-model)