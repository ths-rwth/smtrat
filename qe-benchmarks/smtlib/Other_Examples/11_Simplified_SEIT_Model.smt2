(set-logic NRA)
(declare-fun d () Real)
(declare-fun r () Real)
(declare-fun u () Real)
(declare-fun q () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun v () Real)
(assert (exists ((J Real)) (and (< (* (- 1) d) 0) (= (* (- 1) d v v v c (+ d (* J b)) (+ (+ (+ (+ (* d (* d d)) (* r (* d d))) (* u (+ (* d d) (* r d)))) (* v (+ (+ (* d d) (* q (* u d))) (* b (* d (- 1)))))) (* J (+ (+ (+ (* b (+ (+ (* d d) (* r d)) (* u (+ d r)))) (* c (+ (* d d) (* u d)))) (* v (+ (* b (+ d (* q u))) (* c (+ d (* b (- 1))))))) (* J (+ (* c (* b (+ d u))) (* v (* c b)))))))) 0) (< (* (- 1) d (+ d (* J b))) 0) (< (* (- 1) r) 0) (< (* (- 1) u) 0) (< (* (- 1) q) 0) (<  (+ (* b (- 1)) c) 0) (< (* (- 1) v) 0) (not (= (* (- 1) v) 0)) (< (* (- 1) v J (+ d u)) 0) (not (= (* v c) 0)) (< (* (- 1) v c (+ d (* J b)) (+ (+ (+ (+ (* d (* d d)) (* r (* d d))) (* u (+ (* d d) (* r d)))) (* v (+ (+ (* d d) (* q (* u d))) (* c (* d (- 1)))))) (* J (+ (* b (+ (+ (* d d) (* r d)) (* u (+ d r)))) (* v (* b (+ d (* q u)))))))) 0) (< (* (- 1) J) 0) (< (* (- 1) b) 0) (< (* (- 1) c) 0) (not (=  (+ d (* J b)) 0)))))
(apply qe)
