# Erdős Problem 132: four-point counterexample

This Lean 4 project proves the known four-point counterexample from
[formal-conjectures PR #4389](https://github.com/google-deepmind/formal-conjectures/pull/4389).
It does not solve either open question in Erdős Problem 132.

`Erdos132Proof.four_points` proves:

```lean
∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
  P.card = 4 ∧ (lowMultiplicityDistances P).ncard < 2
```

`distanceMultiplicity` and `lowMultiplicityDistances` reproduce the definitions
in [PR commit 3a217e1](https://github.com/google-deepmind/formal-conjectures/blob/3a217e1d322da7ddae7fb9c2c5beca24556f1946/FormalConjectures/ErdosProblems/132.lean).
Only the namespace and the abbreviation `Plane` differ.

The witness consists of the vertices `(0,0)`, `(1,0)`, `(1/2,√3/2)`, and
`(3/2,√3/2)`. Five unordered pairs have distance 1. The remaining pair has
distance √3. Thus the only distance with multiplicity between 1 and 4 is √3.

The geometric proof comes from
[AItoBit's proof comment](https://github.com/google-deepmind/formal-conjectures/pull/4389#issuecomment-5864136056).
The bridge `lowMultiplicityDistances_subset` transfers its finite-set result
to the PR's exact set-based statement. It also establishes finite support
before comparing `ncard` with `Finset.card`.

## Verification

Lean and Mathlib are pinned to version 4.33.1; `lake-manifest.json` pins the
exact dependency revisions. Run:

```sh
lake exe cache get
lake --wfail build
```

The file prints the axioms of both principal theorems during compilation.
Both have only `propext`, `Classical.choice`, and `Quot.sound` as dependencies.
The proof contains no placeholders, custom axioms, or native evaluation.

An independent statement and proof audit confirmed the exact target, the
rhombus construction, and the finite-support justification for `ncard`.

## License

Apache-2.0. The copied PR definitions retain the Formal Conjectures attribution.
