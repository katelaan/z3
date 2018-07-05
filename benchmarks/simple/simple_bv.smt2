(set-logic QF_BV)

(declare-const a (_ BitVec 2) )
(declare-const b (_ BitVec 2) )
(declare-const c (_ BitVec 2) )

(assert (= a #b00))
(assert (= b #b10))
;(assert (= c (bvor a b)))
(assert (bvult b c))

(check-sat)
(get-model)