(set-logic NRA)
(assert (exists ((r Real)) (forall ((x Real)) (forall ((y Real)) (or (<=  (+ (* r (- 1)) x) 0) (<=  (+ (* r (- 1)) y) 0) (>  (+ (* x x) (* y (+ (* x (* x 4)) (* y (+ (- 1) (* x (* x 2))))))) 0))))))
(apply qe)
