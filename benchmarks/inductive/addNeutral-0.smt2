(set-logic UFDT)
(declare-datatypes ((nat 0)) (((zero) (s (s0 nat)))))
(declare-fun add (nat nat) nat)
(declare-fun mul (nat nat) nat)
(assert (forall ((y nat)) (= (add zero y) y)))
(assert (forall ((x nat) (y nat)) (= (add (s x) y) (s (add x y)))))
(assert (forall ((y nat)) (= (mul zero y) zero)))
(assert (forall ((x nat) (y nat)) (= (mul (s x) y) (add y (mul x y)))))
(assert (not (forall ((x nat)) (= (mul x (s zero)) x))))
(check-sat)
