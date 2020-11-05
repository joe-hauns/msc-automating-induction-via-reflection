(set-logic UFDT)
(declare-sort env 0)
(declare-sort form 0)
(declare-sort var_nat 0)
(declare-sort term_nat 0)
(declare-datatypes ((nat 0)) (((zero) (s (s0 nat)))))
(declare-fun add (nat nat) nat)
(declare-fun mul (nat nat) nat)
(declare-fun v0_nat () var_nat)
(declare-fun next_nat (var_nat) var_nat)
(declare-fun inj_nat (var_nat) term_nat)
(declare-fun zeroR () term_nat)
(declare-fun sR (term_nat) term_nat)
(declare-fun addR (term_nat term_nat) term_nat)
(declare-fun mulR (term_nat term_nat) term_nat)
(declare-fun leqR (term_nat term_nat) form)
(declare-fun eq_nat (term_nat term_nat) form)
(declare-fun falseR () form)
(declare-fun orR (form form) form)
(declare-fun notR (form) form)
(declare-fun forallR_nat (var_nat form) form)
(declare-fun empty () env)
(declare-fun push_nat (env var_nat nat) env)
(declare-fun evalV_nat (env var_nat) nat)
(declare-fun eval_nat (env term_nat) nat)
(declare-fun leq (nat nat) Bool)
(declare-fun models (env form) Bool)
(assert (forall ((x nat)) (leq x x)))
(assert (forall ((x nat) (y nat)) (=> (leq x y) (leq x (s y)))))
(assert (forall ((y nat)) (= (add zero y) y)))
(assert (forall ((x nat) (y nat)) (= (add (s x) y) (s (add x y)))))
(assert (forall ((y nat)) (= (mul zero y) zero)))
(assert (forall ((x nat) (y nat)) (= (mul (s x) y) (add y (mul x y)))))
(assert (forall ((env env) (v var_nat) (x nat)) (= (evalV_nat (push_nat env v x) v) x)))
(assert (forall ((env env) (v var_nat) (w var_nat) (x nat)) (=> (not (= v w)) (= (evalV_nat (push_nat env w x) v) (evalV_nat env v)))))
(assert (forall ((env env) (v var_nat)) (= (eval_nat env (inj_nat v)) (evalV_nat env v))))
(assert (forall ((env env)) (= (eval_nat env zeroR) zero)))
(assert (forall ((env env) (t0 term_nat)) (= (eval_nat env (sR t0)) (s (eval_nat env t0)))))
(assert (forall ((env env) (t0 term_nat) (t1 term_nat)) (= (eval_nat env (addR t0 t1)) (add (eval_nat env t0) (eval_nat env t1)))))
(assert (forall ((env env) (t0 term_nat) (t1 term_nat)) (= (eval_nat env (mulR t0 t1)) (mul (eval_nat env t0) (eval_nat env t1)))))
(assert (forall ((env env) (x term_nat) (y term_nat)) (= (models env (eq_nat x y)) (= (eval_nat env x) (eval_nat env y)))))
(assert (forall ((env env) (t0 term_nat) (t1 term_nat)) (= (models env (leqR t0 t1)) (leq (eval_nat env t0) (eval_nat env t1)))))
(assert (forall ((env env)) (= (models env falseR) false)))
(assert (forall ((env env) (phi form)) (= (models env (notR phi)) (not (models env phi)))))
(assert (forall ((env env) (phi form) (psi form)) (= (models env (orR phi psi)) (or (models env phi) (models env psi)))))
(assert (forall ((env env) (phi form) (v var_nat)) (= (models env (forallR_nat v phi)) (forall ((x nat)) (models (push_nat env v x) phi)))))
(assert (not (models empty (forallR_nat v0_nat (eq_nat (mulR zeroR (inj_nat v0_nat)) zeroR)))))
(check-sat)
