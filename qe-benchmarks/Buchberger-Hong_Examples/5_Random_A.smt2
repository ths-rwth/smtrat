(set-logic NRA)
(assert (exists ((x Real)) (forall ((y Real)) (exists ((z Real)) (and (= (* (- 1) (+ (+ (+ (- 1) (* x (* x (- 16)))) (* y (* y (* x (- 4))))) (* z 4))) 0) (=  (+ (+ 1 (* x 4)) (* z (* y (* y 2)))) 0) (=  (+ (+ (* x (- 1)) (* y (* y (- 2)))) (* z (* x (* x 2)))) 0))))))
(apply qe)
