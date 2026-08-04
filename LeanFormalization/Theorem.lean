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

The hypothesis `NearExtremizer q S T f` says precisely that

$$
\begin{aligned}
  &0 < q \leq 1/100,\qquad S,T \neq \varnothing,\qquad E_V(f)=1,\\
  &E_S(f) \geq 1-q^4/8192,\\
  &E_T(\widehat f) \geq (1-q^4/8192)N,\\
  &|S|\,|T| \leq (1+q^2/16)N.
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
  \sum_{x \in V} |f(x)-\phi(x)|^2 \leq 528q,
  \qquad
  \phi(x)=
  \frac{c\,(-1)^{b\cdot x}}{\sqrt{|H|}}\,
  \mathbf 1_{a+H}(x).
$$

Thus every near-minimizer of Boolean support uncertainty is quantitatively
close, up to global phase, to a normalized hidden-coset state.
-/
theorem robust_inverse_uncertainty_phase {n : ℕ} {q : ℝ}
    {S T : Finset (Cube n)} {f : Cube n → ℂ}
    (h : NearExtremizer q S T f) :
    ∃ (H : Submodule (ZMod 2) (Cube n)) (a b : Cube n) (c : ℂ),
      HiddenCosetApproximation q S T f H a b c :=
  Internal.robust_inverse_uncertainty_phase_from_implementation h

end RobustInverseUncertainty
