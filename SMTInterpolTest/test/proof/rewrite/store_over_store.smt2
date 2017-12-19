(set-option :produce-proofs true)
(set-option :proof-check-mode true)
(set-option :model-check-mode true)
(set-option :print-terms-cse false)

(set-logic QF_ALIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Int)
(declare-fun w () Int)

(assert (= (store (store a (+ i j) v) (+ j i) w) b))
(assert (not (= (store a (+ i j) w) b)))
(check-sat)
(get-proof)
