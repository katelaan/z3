(declare-fun a () Float32)
(declare-fun b () Float32)
(declare-fun c () (_ BitVec 32))

(assert (= a (fp #b0 #b10000011 #b00000000000000000000000 ) ) )
(assert (fp.geq b (_ +zero 8 24) ) )
(assert (fp.eq b (fp.sqrt roundNearestTiesToEven a)))
(check-sat)
(get-model)
