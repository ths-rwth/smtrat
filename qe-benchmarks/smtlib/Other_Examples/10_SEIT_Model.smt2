(set-logic NRA)
(declare-fun b () Real)
(declare-fun d () Real)
(declare-fun u () Real)
(declare-fun v () Real)
(declare-fun c () Real)
(declare-fun q () Real)
(declare-fun r () Real)
(assert (exists ((s Real)) (exists ((F Real)) (exists ((J Real)) (exists ((T Real)) (and (= (* (- 1) (+ (* d (- 1)) (* s (+ (* b J) d)))) 0) (=  (+ (+ (* d (* J (- 1))) (* u (* J (- 1)))) (* v F)) 0) (= (* (- 1) (+ (+ (+ (+ (+ (+ (* b (* J (- 1))) (* F d)) (* u (* J (- 1)))) (* v F)) (* c (* T (* J (- 1))))) (* q (* u J))) (* r F))) 0) (=  (+ (+ (* T (+ (* b (* b (* J (- 1)))) (* d (- 1)))) (* q (* u J))) (* r F)) 0) (>  F 0) (>  J 0) (>  T 0) (>  s 0) (>  b 0) (>  d 0) (>  v 0) (>  r 0) (>  u 0) (>  q 0) (> (* (- 1) (+ (* b (- 1)) c)) 0)))))))
(apply qe)
