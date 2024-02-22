(set-logic NRA)
(assert (exists ((z Real)) (exists ((x Real)) (exists ((y Real)) (and (<  (+ (+ (+ (- 1) (* x x)) (* y y)) (* z z)) 0) (<  (+ (+ (+ 3 (* x x)) (* y (+ (- 4) y))) (* z (+ (+ (- 4) (* y 2)) z))) 0))))))
(apply qe)
