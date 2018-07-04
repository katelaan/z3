(declare-const a (_ FloatingPoint 2 3) )
(declare-const b (_ FloatingPoint 2 3) )
(declare-const c (_ FloatingPoint 2 3) )

(assert (= a (fp #b0 #b01 #b01)))
(assert (= b (fp #b0 #b01 #b10)))
(assert (= c (fp.add roundNearestTiesToEven a b)))

(check-sat)
(get-model)