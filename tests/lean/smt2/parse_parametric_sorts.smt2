(set-option :verbose true)
(set-option :use_locals)
(declare-sort F 1)
(declare-sort X)
(declare-sort Y)

(declare-const x X)
(declare-const x1 X)
(declare-const x2 X)
(declare-const y Y)

(declare-fun f (X) (F X))
(assert (= (f x) (f x1) (f x2)))
