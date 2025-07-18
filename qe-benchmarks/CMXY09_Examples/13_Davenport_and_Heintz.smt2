(set-logic NRA)
(declare-fun d () Real)
(assert (exists ((c Real)) (forall ((b Real)) (forall ((a Real)) (or (= (* (- 1) (+ (* a (* a (- 1))) b)) 0) (and (or (not (= (* (- 1) (+ (* a (- 1)) d)) 0)) (not (= (* (- 1) (+ (* b (- 1)) c)) 0))) (or (not (= (* (- 1) (+ (* a (- 1)) c)) 0)) (not (=  (+ (- 1) b) 0)))))))))
(apply qe)
