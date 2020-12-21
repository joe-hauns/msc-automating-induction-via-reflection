(set-info :smt-lib-version 2.6)
(set-logic UF)
(set-info :source |
Generated by: Johannes Schoisswohl
Generated on: 2020-12-21
Application: Replacing structural induction by a conservative extension
Target solver: CVC4, Vampire, Z3
Generator: https://github.com/joe-hauns/msc-automating-induction-via-reflection
Publications: Automated Induction by Reflection ( https://doi.org/10.34726/hss.2020.75342 )
|)
(set-logic :category "crafted")
(declare-sort nat 0)
(declare-sort env 0)
(declare-sort form 0)
(declare-sort var_nat 0)
(declare-sort term_nat 0)

(declare-fun zero () nat)
(declare-fun s (nat) nat)
(declare-fun add (nat nat) nat)
(declare-fun mul (nat nat) nat)
(declare-fun v0_nat () var_nat)
(declare-fun next_nat (var_nat) var_nat)
(declare-fun inj_nat (var_nat) term_nat)
(declare-fun zeroR () term_nat)
(declare-fun sR (term_nat) term_nat)
(declare-fun addR (term_nat term_nat) term_nat)
(declare-fun mulR (term_nat term_nat) term_nat)
(declare-fun eq_nat (term_nat term_nat) form)
(declare-fun falseR () form)
(declare-fun orR (form form) form)
(declare-fun notR (form) form)
(declare-fun forallR_nat (var_nat form) form)
(declare-fun empty () env)
(declare-fun push_nat (env var_nat nat) env)
(declare-fun evalV_nat (env var_nat) nat)
(declare-fun eval_nat (env term_nat) nat)
(declare-fun models (env form) Bool)
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
(assert (forall ((env env)) (= (models env falseR) false)))
(assert (forall ((env env) (phi form)) (= (models env (notR phi)) (not (models env phi)))))
(assert (forall ((env env) (phi form) (psi form)) (= (models env (orR phi psi)) (or (models env phi) (models env psi)))))
(assert (forall ((env env) (phi form) (v var_nat)) (= (models env (forallR_nat v phi)) (forall ((x nat)) (models (push_nat env v x) phi)))))
(assert (forall ((phi form)) (=> (and (=> true (models (push_nat empty v0_nat zero) phi)) (forall ((x0 nat)) (=> (models (push_nat empty v0_nat x0) phi) (models (push_nat empty v0_nat (s x0)) phi)))) (forall ((x nat)) (models (push_nat empty v0_nat x) phi)))))
(assert (forall ((x0 nat)) (not (= zero (s x0)))))
(assert (forall ((x0 nat) (x1 nat)) (=> (= (s x0) (s x1)) (= x0 x1))))
(assert (not (forall ((x nat)) (= (mul x (s zero)) x))))
(check-sat)
