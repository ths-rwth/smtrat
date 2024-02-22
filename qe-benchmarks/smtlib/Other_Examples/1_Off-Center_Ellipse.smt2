(set-logic NRA)
(declare-fun a () Real)
(assert (forall ((x Real)) (forall ((y Real)) (and (not (=  a 0)) (or (not (=  (+ (+ (+ 1 (* a (* a (- 3)))) (* x (+ (- 4) (* x 4)))) (* y (+ (* a (* a (- 8))) (* y (* a (* a 16)))))) 0)) (<=  (+ (+ (- 1) (* x x)) (* y y)) 0))))))
(apply qe)
