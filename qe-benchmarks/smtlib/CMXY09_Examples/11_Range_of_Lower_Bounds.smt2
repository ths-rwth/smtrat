(set-logic NRA)
(declare-fun y () Real)
(assert (forall ((x Real)) (forall ((a Real)) (forall ((b Real)) (forall ((c Real)) (exists ((z Real)) (or (<=  a 0) (=  (+ c (* z (+ b (* z a)))) 0) (<  (+ (+ (* c (- 1)) (* x (+ (* b (- 1)) (* x (* a (- 1)))))) y) 0))))))))
(apply qe)
