/-
Copyright (c) 2026 Galois, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
Authors: Marios Georgiou
-/

import LeanFormalization.Specification
import LeanFormalization.Internal.Bridge

/-!
# Robust inverse uncertainty on the Boolean cube

This is the public theorem module. The mathematical vocabulary used in its
type is defined transparently in `Specification.lean`, which imports only
Mathlib. Proof implementation details are isolated under `Internal/`.
-/

namespace RobustInverseUncertainty

open Specification

/--
Let $V = \mathbb F_2^n$ and $N = |V| = 2^n$. For a function
$g : V \to \mathbb C$ and a finite set $A \subseteq V$, write

$$
  E_A(g) = \sum_{x \in A} |g(x)|^2.
$$

We use the unnormalized Walsh-Hadamard transform

$$
  \widehat f(y) = \sum_{x \in V} (-1)^{x \cdot y} f(x).
$$

The hypothesis `NearExtremizer ε δ q S T f` separates the two approximation
errors.  The number $\varepsilon$ is the concentration loss, $\delta$ is the
support-product excess, and $q$ is the scale at which the conclusion is
requested.  Precisely,

$$
\begin{aligned}
  &\varepsilon,\delta\geq 0,\qquad
    0 < q \leq 1/100,\qquad
    \varepsilon\leq q^4/1024,\qquad \delta\leq q^2/16,\\
  &S,T \neq \varnothing,\qquad E_V(f)=1,\\
  &E_S(f) \geq 1-\varepsilon,\\
  &E_T(\widehat f) \geq (1-\varepsilon)N,\\
  &|S|\,|T| \leq (1+\delta)N.
\end{aligned}
$$

The conclusion provides a linear subspace $H \leq \mathbb F_2^n$, offsets
$a,b \in \mathbb F_2^n$, and a phase $c \in \mathbb C$ with $|c|^2=1$.
Writing $H^\perp$ for the orthogonal complement of $H$, it guarantees

$$
  |S \mathbin{\triangle} (a+H)| \leq 5q|S|,
  \qquad
  |T \mathbin{\triangle} (b+H^\perp)| \leq 12q|T|,
$$

and

$$
  \sum_{x \in V} |f(x)-\phi(x)|^2 \leq 264q,
  \qquad
  \phi(x)=
  \frac{c\,(-1)^{b\cdot x}}{\sqrt{|H|}}\,
  \mathbf 1_{a+H}(x).
$$

Thus every near-minimizer of Boolean support uncertainty is quantitatively
close, up to global phase, to a normalized hidden-coset state.
-/
theorem robust_inverse_uncertainty_phase {n : ℕ} {ε δ q : ℝ}
    {S T : Finset (Cube n)} {f : Cube n → ℂ}
    (h : NearExtremizer ε δ q S T f) :
    ∃ (H : Submodule (ZMod 2) (Cube n)) (a b : Cube n) (c : ℂ),
      HiddenCosetApproximation q S T f H a b c :=
  Internal.robust_inverse_uncertainty_phase_from_implementation h

end RobustInverseUncertainty
