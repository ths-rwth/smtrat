(set-logic NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (or (and (=  (+ (+ (+ (- 1) (* x x)) (* y y)) (* z z)) 0) (<  (+ (- 1) (* z (* y (* x 4)))) 0)) (and (=  (+ (+ (+ 20 (* x (+ (- 8) x))) (* y (+ (- 2) y))) (* z (+ (- 4) z))) 0) (<  (+ (+ (+ (- 33) (* x 8)) (* y (+ 32 (* x (- 8))))) (* z (+ (+ 16 (* x (- 4))) (* y (+ (- 16) (* x 4)))))) 0))))
(apply qe)
