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
(declare-sort alpha 0)
(declare-sort env 0)
(declare-sort form 0)
(declare-sort var_alpha 0)
(declare-sort term_alpha 0)

(declare-fun a () alpha)
(declare-fun b () alpha)
(declare-fun c () alpha)
(declare-fun v0_alpha () var_alpha)
(declare-fun next_alpha (var_alpha) var_alpha)
(declare-fun inj_alpha (var_alpha) term_alpha)
(declare-fun aR () term_alpha)
(declare-fun bR () term_alpha)
(declare-fun cR () term_alpha)
(declare-fun pR (term_alpha) form)
(declare-fun qR (term_alpha) form)
(declare-fun rR (term_alpha) form)
(declare-fun eq_alpha (term_alpha term_alpha) form)
(declare-fun falseR () form)
(declare-fun orR (form form) form)
(declare-fun notR (form) form)
(declare-fun forallR_alpha (var_alpha form) form)
(declare-fun empty () env)
(declare-fun push_alpha (env var_alpha alpha) env)
(declare-fun evalV_alpha (env var_alpha) alpha)
(declare-fun eval_alpha (env term_alpha) alpha)
(declare-fun p (alpha) Bool)
(declare-fun q (alpha) Bool)
(declare-fun r (alpha) Bool)
(declare-fun models (env form) Bool)
(assert (forall ((env env) (v var_alpha) (x alpha)) (= (evalV_alpha (push_alpha env v x) v) x)))
(assert (forall ((env env) (v var_alpha) (w var_alpha) (x alpha)) (=> (not (= v w)) (= (evalV_alpha (push_alpha env w x) v) (evalV_alpha env v)))))
(assert (forall ((env env) (v var_alpha)) (= (eval_alpha env (inj_alpha v)) (evalV_alpha env v))))
(assert (forall ((env env)) (= (eval_alpha env aR) a)))
(assert (forall ((env env)) (= (eval_alpha env bR) b)))
(assert (forall ((env env)) (= (eval_alpha env cR) c)))
(assert (forall ((env env) (x term_alpha) (y term_alpha)) (= (models env (eq_alpha x y)) (= (eval_alpha env x) (eval_alpha env y)))))
(assert (forall ((env env) (t0 term_alpha)) (= (models env (pR t0)) (p (eval_alpha env t0)))))
(assert (forall ((env env) (t0 term_alpha)) (= (models env (qR t0)) (q (eval_alpha env t0)))))
(assert (forall ((env env) (t0 term_alpha)) (= (models env (rR t0)) (r (eval_alpha env t0)))))
(assert (forall ((env env)) (= (models env falseR) false)))
(assert (forall ((env env) (phi form)) (= (models env (notR phi)) (not (models env phi)))))
(assert (forall ((env env) (phi form) (psi form)) (= (models env (orR phi psi)) (or (models env phi) (models env psi)))))
(assert (forall ((env env) (phi form) (v var_alpha)) (= (models env (forallR_alpha v phi)) (forall ((x alpha)) (models (push_alpha env v x) phi)))))
(assert (not (models empty (orR (pR aR) (notR (pR aR))))))
(check-sat)
