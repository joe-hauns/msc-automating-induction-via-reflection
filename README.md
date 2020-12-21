This software is the implementation of the techniques for reflective, and inductive reasoning described in the Master Thesis *Automated Induction via Reflection*.

The main purpose of this software is generaing the benchmarks described in the thesis, and runnig different theorem provers on them. 
Using command line calls the following functionality is provided:

```
$ stack run genMscBenchmarks <output_directory>
```
Generates the benchmarks described in the thesis in various formats.
The generated benchmarks can also be found in the directory `benchmarks`.


```
$ cat examples/01.logic | stack run logicInto <fmt>
```

Translates `examples/01.logic` files into one of multiple output formats.
These output formats are
* `smt2`: the input format of SMTLIB version 2
* `logic`: the DSL native to this program with non-ascii characters for quantifiers, and connectives
* `ascii.logic`: the DSL native to this program with ascii characters only
* `zf`: zipperpositions native input format
* `rewrite.zf`: zipperpositions native input with equations tranlasted to rewrite rules where easily possible
* `zeno.hs`: input format of the inductive theorem prover zeno
* `icaml`: The Caml dialect supported by imandra



```
$ cat examples/01.logic| stack run toIndRefl
```

Translates `01.logic` into the same problem, but with induction replaced by its reflective reasoning.



```
$ cat examples/01.logic| stack run toRefl
```

Translates `01.logic` into the same problem, but with reflective axioms of the theory added, and the conclusion translated into its gödelized form.
