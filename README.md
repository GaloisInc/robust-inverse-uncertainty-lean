# Lean formalization of the hidden-coset core

The library checks the exact hidden-coset algebra and the quantitative robust
inverse-uncertainty theorem on `F₂ⁿ`.

Verified without proof placeholders or added axioms:

- bilinearity and nondegeneracy of the Boolean dot product;
- Walsh-character orthogonality on the cube and on a subspace;
- `|H| |Hᗮ| = 2ⁿ`;
- the four-point identity;
- the exact Fourier support of a modulated affine-subspace indicator;
- the sharp small-doubling subgroup step, using Mathlib's `< 3/2` theorem;
- evaluation of the dual-coset Fourier projector as a character kernel;
- commutation of the primal and dual coset projectors;
- identification of either composition with the same rank-one operator.

`LeanFormalization/Combinatorial.lean` additionally verifies:

- real Walsh orthogonality and indicator Parseval;
- finite Markov and high-bias sumset bounds;
- conversion of `< 3/2` doubling into a `ZMod 2` submodule;
- the explicit saturated almost-orthogonality theorem
  `saturated_almost_orthogonality`: if `0 < q ≤ 1/100`,
  `(1-q)2ⁿ ≤ |A||B|`, and the number of bad pairs is at most
  `q²|A||B|`, then some `L` satisfies
  `|A ∆ Lᗮ| ≤ 5q|A|` and `|B ∆ L| ≤ 12q|B|`.

`LeanFormalization/Analytic.lean` additionally verifies:

- real and complex Walsh Parseval for arbitrary functions;
- coordinate-restriction energy identities;
- the exact elementary rank-one Frobenius residual identity;
- sign-mismatch count bounded by the Frobenius residual;
- the four-point implication turning every translated bad pair into a
  mismatch at one of its four rectangle corners.

`LeanFormalization/Robust.lean` proves the implementation theorem. Its concise
public form is `robust_inverse_uncertainty_phase` in
`LeanFormalization/Theorem.lean`. The statement separates concentration loss
`ε` from support-product excess `δ`. Given `0 < q ≤ 1/100`,
`ε ≤ q⁴/1024`, `δ ≤ q²/16`, a unit-energy `f` with primal and Fourier
concentration losses at most `ε`, and support product at most `(1 + δ)2ⁿ`,
it produces affine primal and dual cosets with symmetric-difference errors
`5q` and `12q`. It also produces a unit-modulus phase whose normalized coset
wave has squared `ℓ₂` distance at most `264q` from `f`.

Equivalently, for independent errors one may take

```text
q = max((1024 ε)^(1/4), 4 sqrt(δ)),
```

provided this number lies in `(0, 1/100]`.

## Audit surface

Start with `LeanFormalization/Specification.lean`. It imports only focused
Mathlib modules and transparently defines the Boolean cube, squared mass,
Walsh transform, affine and dual cosets, normalized coset state, hypotheses,
and conclusion. It does not import any proof module.

Next read `LeanFormalization/Theorem.lean`. It contains only a mathematical
docstring, the complete public theorem type, and a one-line proof delegation:

```lean
theorem robust_inverse_uncertainty_phase
    (h : NearExtremizer ε δ q S T f) :
    ∃ H a b c, HiddenCosetApproximation q S T f H a b c
```

The conversion between the public specification and the detailed proof is
isolated in `LeanFormalization/Internal/Bridge.lean`; it is not needed to
understand the theorem statement.

Build with:

```bash
lake build
```

## Mathematical note

The source and compiled version of the accompanying note are
`paper/main.tex` and `paper/main.pdf`. Rebuild it with:

```bash
cd paper
latexmk -pdf main.tex
```
