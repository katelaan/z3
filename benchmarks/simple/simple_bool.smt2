(set-logic SLSTAR)
; (set-logic QF_UF)

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun x (Bool) Bool)

(assert (not (or a (not (not b)) )) )

(assert (and (x false) (not (x true)) ) )
(check-sat)
(get-model)

(check-sat-assuming ((not a)) )
