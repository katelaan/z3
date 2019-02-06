;; This should be SAT!

(set-logic SLSTAR)

(assert  (not (list (as null ListLoc))))

(check-sat)
