(set-info :smt-lib-version 2.6)
(set-logic UFDT)
(set-info :source |
Generated by: Johannes Schoisswohl
Generated on: 2020-12-21
Application: Replacing structural induction by a conservative extension
Target solver: CVC4, Vampire, Z3
Generator: https://github.com/joe-hauns/msc-automating-induction-via-reflection
Publications: Automated Induction by Reflection ( https://doi.org/10.34726/hss.2020.75342 )
|)
(set-logic :category "crafted")
(declare-datatypes ((nat 0)) (((zero) (s (s0 nat)))))
(declare-fun add (nat nat) nat)
(declare-fun id (nat) nat)
(assert (forall ((y nat)) (= (add zero y) y)))
(assert (forall ((x nat) (y nat)) (= (add (s x) y) (s (add x y)))))
(assert (forall ((x nat)) (= (id x) x)))
(assert (not (forall ((x nat) (y nat)) (= (add (id x) y) (add y x)))))
(check-sat)
