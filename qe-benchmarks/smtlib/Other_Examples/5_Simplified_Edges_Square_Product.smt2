(set-logic NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (exists ((a Real)) (and (<= (* (- 1) a) 0) (<=  (+ (- 2) a) 0) (<= (* (- 1) (+ 1 x)) 0) (<=  (+ (- 9) x) 0) (<= (* (- 1) (+ 6 y)) 0) (<=  (+ (- 6) y) 0) (not (=  (+ 1 (* a a)) 0)) (<= (* (- 1) (+ 1 (* a a)) (+ (+ (+ (- 2) (* a (* a (- 2)))) (* x a)) y)) 0) (<= (* (+ 1 (* a a)) (+ (+ (+ (- 1) (* a (* a (- 1)))) (* x (- 1))) (* y a))) 0) (<= (* (- 1) (+ 1 (* a a)) (+ (+ (+ 1 (* a a)) (* x (- 1))) (* y a))) 0) (<= (* (+ 1 (* a a)) (+ (+ (+ (- 4) (* a (* a (- 4)))) (* x a)) y)) 0))))
(apply qe)
