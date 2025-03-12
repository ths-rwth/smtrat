(set-logic NRA)
(declare-fun t () Real)
(assert (forall ((x Real)) (exists ((y Real)) (and (= (* x x) y) (>= y t)))))
(apply qe)