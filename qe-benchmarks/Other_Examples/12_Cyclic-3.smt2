(set-logic NRA)
(declare-fun c () Real)
(assert (exists ((b Real)) (exists ((a Real)) (and (=  (+ (+ a b) c) 0) (=  (+ (* b a) (* c (+ a b))) 0) (=  (+ (- 1) (* c (* b a))) 0)))))
(apply qe)
