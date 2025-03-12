(set-logic NRA)
(assert (forall ((x Real)) (exists ((y Real)) (and (= (* x x) y) (>= y 0)))))
(check-sat)