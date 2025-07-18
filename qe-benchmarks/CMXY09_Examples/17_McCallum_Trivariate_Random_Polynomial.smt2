(set-logic NRA)
(assert (exists ((x Real)) (exists ((y Real)) (exists ((z Real)) (=  (+ y (* z (+ (+ (+ (- 1) (* x (- 1))) y) (* z (+ (+ x (* y (* x (- 1)))) (* z (+ x (* z (+ (- 1) y))))))))) 0)))))
(apply qe)
