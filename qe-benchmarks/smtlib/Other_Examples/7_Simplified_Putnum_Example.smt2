(set-logic NRA)
(declare-fun y () Real)
(declare-fun x () Real)
(assert (exists ((a Real)) (exists ((d Real)) (and (=  (+ (+ (+ (- 1) (* a a)) (* d d)) (* y (+ (* d (- 4)) (* y 4)))) 0) (=  (+ (+ (+ 91 (* a (+ 20 a))) (* d d)) (* x (+ (+ (- 40) (* a (- 4))) (* x 4)))) 0)))))
(apply qe)
