# Equational Magma Theorems

Lean 4 formalizations of structural theorems about magma equational theories.

## Spine Isolation Theorem for Magma Implications

The first result formalized here: **pure left-spine equations are isolated** from
equations with incompatible spine structure.

Given a magma equation `x = t` where the LHS is a single variable, classify
the RHS term `t` by its *spine* — the path from the root to the leftmost occurrence
of `x`:

- **Pure left-spine** of depth `n`: `x = (...((x ◇ T₁) ◇ T₂) ◇ ... ◇ Tₙ)` — the
  leftmost leaf is `x`, reached by going left at every node.
- **Pure right-spine**: the leftmost leaf is NOT `x` (it appears only on the right).
- **Mixed spine**: `x` appears but the path from root to `x` contains both left
  and right steps.

### Theorem

**(a)** A pure left-spine equation of depth `n` cannot imply a pure left-spine
equation of depth `m` when `n ∤ m`.

**(b)** A pure left-spine equation cannot imply a pure right-spine equation.

**(c)** A pure left-spine equation cannot imply a mixed-spine equation.

### Proofs

- **Parts (b) + (c):** The *left-zero magma* (`a ◇ b = a`) satisfies every
  left-spine equation (evaluation collapses to `f(x)`) but fails any equation
  whose leftmost leaf differs from `x`.

- **Part (a):** The *cyclic successor magma* on `Fin n` with `a ◇ b = (a+1) mod n`
  satisfies depth-`n` equations (since `n ≡ 0 mod n`) but fails depth-`m` equations
  when `n ∤ m` (since `m ≢ 0 mod n`).

### Validation

Verified with zero exceptions on the complete 4694×4694 implication graph from
the [Equational Theories Project](https://github.com/teorth/equational_theories)
(Tao et al., arXiv:2512.07087), covering 1.54 million ordered pairs.

### Prior art

The left-zero magma argument extends **ETP Corollary 10.4** (the "first letter"
invariant). Our contribution is the systematic spine-type classification combined
with the depth divisibility characterization via cyclic magmas.

### Paper

A. McKenna, "A Spine Isolation Theorem for Magma Implications," 2026.
Available at https://zenodo.org/records/19380600

## Data

- `equations.txt` — the 4,694 magma equations from the ETP catalog, one per line.

## Analysis

- `analysis/count_mirrors.py` — counts equations whose left-right mirror
  (recursively swapping left/right children at every operation node) is not
  present in the catalog. Result: 266 of 4,694 equations have no mirror image.

```bash
python3 analysis/count_mirrors.py           # auto-finds equations.txt
python3 analysis/count_mirrors.py path/to/equations.txt
```

## Building

Requires [Lean 4](https://leanprover.github.io/) (v4.29.0). No external
dependencies (no Mathlib required).

```bash
lake build
```

## Structure

```
SpineIsolation/
  Defs.lean      -- MagmaTerm, MagmaEq, IsLeftSpine, IsRightSpine
  LeftZero.lean   -- Left-zero magma, Parts (b)+(c)
  Cyclic.lean     -- Cyclic successor magma, Part (a)
```

## License

Apache 2.0
