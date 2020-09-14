# lean-omin

A project to formalize the theory of [o-minimal structures](https://en.wikipedia.org/wiki/O-minimal_theory) in Lean.

## Current features

* Semilinear sets form an o-minimal structure.

* Lemma 1 of the monotonicity theorem.

* Definable choice (`sorry`-free draft version).

## Directory layout

* `omin` is a playground for new ideas,
  and may contain unfinished proofs or even definitions,
  temporary names, and so on.

* `src/o_minimal` is the "official" formalization
  and is supposed to avoid `sorry`,
  although it is still at a highly experimental phase.

* `src/for_mathlib` contains supporting developments.

## References

* [vdD] Lou van den Dries, *Tame topology and o-minimal structures.*
  https://doi.org/10.1017/CBO9780511525919
