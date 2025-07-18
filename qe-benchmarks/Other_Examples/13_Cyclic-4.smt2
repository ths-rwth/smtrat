(set-logic NRA)
(declare-fun d () Real)
(assert (exists ((c Real)) (exists ((b Real)) (exists ((a Real)) (and (=  (+ (+ (+ a b) c) d) 0) (= (* (+ a c) (+ b d)) 0) (=  (+ (* c (* b a)) (* d (+ (* b a) (* c (+ a b))))) 0) (=  (+ (- 1) (* d (* c (* b a)))) 0))))))
(apply qe)
