(set-option :verbose true)
(set-option :use_locals)
(assert (forall ((x Int)) (= x x)))
(assert (forall ((x Int) (y Int)) (= x y)))
(assert (forall ((x Int) (y Int) (z Int)) (= x y z)))

(assert (exists ((x Int)) (= x x)))
(assert (exists ((x Int) (y Int)) (= x y)))
(assert (exists ((x Int) (y Int) (z Int)) (= x y z)))

(assert (let ((x 5)) (= x x)))
(assert (let ((x 5) (y 5)) (= x y)))
(assert (let ((x 5) (y 5) (z 5)) (= x y z)))
