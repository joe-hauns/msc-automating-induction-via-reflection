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
(declare-sort lst 0)
(declare-sort env 0)
(declare-sort form 0)
(declare-sort var_nat 0)
(declare-sort var_lst 0)
(declare-sort term_nat 0)
(declare-sort term_lst 0)

(declare-fun zero () nat)
(declare-fun s (nat) nat)
(declare-fun nil () lst)
(declare-fun cons (nat lst) lst)
(declare-fun app (lst lst) lst)
(declare-fun v0_nat () var_nat)
(declare-fun v0_lst () var_lst)
(declare-fun next_nat (var_nat) var_nat)
(declare-fun next_lst (var_lst) var_lst)
(declare-fun inj_nat (var_nat) term_nat)
(declare-fun inj_lst (var_lst) term_lst)
(declare-fun zeroR () term_nat)
(declare-fun sR (term_nat) term_nat)
(declare-fun nilR () term_lst)
(declare-fun consR (term_nat term_lst) term_lst)
(declare-fun appR (term_lst term_lst) term_lst)
(declare-fun eq_nat (term_nat term_nat) form)
(declare-fun eq_lst (term_lst term_lst) form)
(declare-fun falseR () form)
(declare-fun orR (form form) form)
(declare-fun notR (form) form)
(declare-fun forallR_nat (var_nat form) form)
(declare-fun forallR_lst (var_lst form) form)
(declare-fun empty () env)
(declare-fun push_nat (env var_nat nat) env)
(declare-fun push_lst (env var_lst lst) env)
(declare-fun evalV_nat (env var_nat) nat)
(declare-fun evalV_lst (env var_lst) lst)
(declare-fun eval_nat (env term_nat) nat)
(declare-fun eval_lst (env term_lst) lst)
(declare-fun models (env form) Bool)
(assert (forall ((r lst)) (= (app nil r) r)))
(assert (forall ((a nat) (l lst) (r lst)) (= (app (cons a l) r) (cons a (app l r)))))
(assert (forall ((env env) (v var_nat) (x nat)) (= (evalV_nat (push_nat env v x) v) x)))
(assert (forall ((env env) (v var_lst) (x lst)) (= (evalV_lst (push_lst env v x) v) x)))
(assert (forall ((env env) (v var_nat) (w var_nat) (x nat)) (=> (not (= v w)) (= (evalV_nat (push_nat env w x) v) (evalV_nat env v)))))
(assert (forall ((env env) (v var_lst) (w var_lst) (x lst)) (=> (not (= v w)) (= (evalV_lst (push_lst env w x) v) (evalV_lst env v)))))
(assert (forall ((env env) (v var_nat) (w var_lst) (x lst)) (= (evalV_nat (push_lst env w x) v) (evalV_nat env v))))
(assert (forall ((env env) (v var_lst) (w var_nat) (x nat)) (= (evalV_lst (push_nat env w x) v) (evalV_lst env v))))
(assert (forall ((env env) (v var_nat)) (= (eval_nat env (inj_nat v)) (evalV_nat env v))))
(assert (forall ((env env) (v var_lst)) (= (eval_lst env (inj_lst v)) (evalV_lst env v))))
(assert (forall ((env env)) (= (eval_nat env zeroR) zero)))
(assert (forall ((env env) (t0 term_nat)) (= (eval_nat env (sR t0)) (s (eval_nat env t0)))))
(assert (forall ((env env)) (= (eval_lst env nilR) nil)))
(assert (forall ((env env) (t0 term_nat) (t1 term_lst)) (= (eval_lst env (consR t0 t1)) (cons (eval_nat env t0) (eval_lst env t1)))))
(assert (forall ((env env) (t0 term_lst) (t1 term_lst)) (= (eval_lst env (appR t0 t1)) (app (eval_lst env t0) (eval_lst env t1)))))
(assert (forall ((env env) (x term_nat) (y term_nat)) (= (models env (eq_nat x y)) (= (eval_nat env x) (eval_nat env y)))))
(assert (forall ((env env) (x term_lst) (y term_lst)) (= (models env (eq_lst x y)) (= (eval_lst env x) (eval_lst env y)))))
(assert (forall ((env env)) (= (models env falseR) false)))
(assert (forall ((env env) (phi form)) (= (models env (notR phi)) (not (models env phi)))))
(assert (forall ((env env) (phi form) (psi form)) (= (models env (orR phi psi)) (or (models env phi) (models env psi)))))
(assert (forall ((env env) (phi form) (v var_nat)) (= (models env (forallR_nat v phi)) (forall ((x nat)) (models (push_nat env v x) phi)))))
(assert (forall ((env env) (phi form) (v var_lst)) (= (models env (forallR_lst v phi)) (forall ((x lst)) (models (push_lst env v x) phi)))))
(assert (forall ((phi form)) (=> (and (=> true (models (push_nat empty v0_nat zero) phi)) (forall ((x0 nat)) (=> (models (push_nat empty v0_nat x0) phi) (models (push_nat empty v0_nat (s x0)) phi)))) (forall ((x nat)) (models (push_nat empty v0_nat x) phi)))))
(assert (forall ((phi form)) (=> (and (=> true (models (push_lst empty v0_lst nil) phi)) (forall ((x0 nat) (x1 lst)) (=> (models (push_lst empty v0_lst x1) phi) (models (push_lst empty v0_lst (cons x0 x1)) phi)))) (forall ((x lst)) (models (push_lst empty v0_lst x) phi)))))
(assert (forall ((x0 nat)) (not (= zero (s x0)))))
(assert (forall ((x0 nat) (x1 lst)) (not (= nil (cons x0 x1)))))
(assert (forall ((x0 nat) (x1 nat)) (=> (= (s x0) (s x1)) (= x0 x1))))
(assert (forall ((x0 nat) (x1 lst) (x2 nat) (x3 lst)) (=> (= (cons x0 x1) (cons x2 x3)) (and (= x0 x2) (= x1 x3)))))
(assert (not (forall ((x lst) (y lst) (z lst)) (= (app x (app y z)) (app (app x y) z)))))
(check-sat)
