(set-logic NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (and (=  (+ (+ (+ (- 1) (* x x)) (* y y)) (* z z)) 0) (=  (+ y (* z (+ x (* z z)))) 0)))
(apply qe)
