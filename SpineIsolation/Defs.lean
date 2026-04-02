/-
Copyright (c) 2026 Adam Flounder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Magma Terms, Equations, and Spine Classification

We define magma terms over natural-number variables, equation satisfaction,
and the spine classification used in the Left-Spine Isolation Theorem.

## References

* Tao et al., "Equational Theories Project", arXiv:2512.07087
  (Corollary 10.4: the first-letter invariant via left-zero magmas)
-/

universe u

/-- Terms in the language of magmas, with variables indexed by `Nat`. -/
inductive MagmaTerm where
  /-- A variable. -/
  | var : Nat → MagmaTerm
  /-- A binary magma operation. -/
  | op : MagmaTerm → MagmaTerm → MagmaTerm
  deriving Repr, DecidableEq

namespace MagmaTerm

/-- Evaluate a magma term given a variable assignment `f` and operation `μ`. -/
def eval (f : Nat → α) (μ : α → α → α) : MagmaTerm → α
  | .var n => f n
  | .op l r => μ (l.eval f μ) (r.eval f μ)

/-- The leftmost leaf variable of a term. -/
def leftmostVar : MagmaTerm → Nat
  | .var n => n
  | .op l _ => l.leftmostVar

/-- The left-spine depth: number of `op` nodes on the path from root
    to the leftmost leaf. -/
def leftSpineDepth : MagmaTerm → Nat
  | .var _ => 0
  | .op l _ => l.leftSpineDepth + 1

/-- The rightmost leaf variable of a term. -/
def rightmostVar : MagmaTerm → Nat
  | .var n => n
  | .op _ r => r.rightmostVar

/-- The right-spine depth: number of `op` nodes on the path from root
    to the rightmost leaf. -/
def rightSpineDepth : MagmaTerm → Nat
  | .var _ => 0
  | .op _ r => r.rightSpineDepth + 1

end MagmaTerm

/-- A term `t` is a pure left-spine of depth `n` rooted at variable `x` if it
    has the form `(...((var x ◇ T₁) ◇ T₂) ◇ ... ◇ Tₙ)`. -/
inductive IsLeftSpine (x : Nat) : Nat → MagmaTerm → Prop where
  /-- Base case: `var x` is a left-spine of depth 0. -/
  | base : IsLeftSpine x 0 (.var x)
  /-- Step: if `l` is a left-spine of depth `n`, then `op l r` is depth `n + 1`. -/
  | step : IsLeftSpine x n l → IsLeftSpine x (n + 1) (.op l r)

/-- A term `t` is a pure right-spine of depth `n` rooted at variable `x` if it
    has the form `T₁ ◇ (T₂ ◇ (... ◇ (Tₙ ◇ var x)...))`. -/
inductive IsRightSpine (x : Nat) : Nat → MagmaTerm → Prop where
  /-- Base case: `var x` is a right-spine of depth 0. -/
  | base : IsRightSpine x 0 (.var x)
  /-- Step: if `r` is a right-spine of depth `n`, then `op l r` is depth `n + 1`. -/
  | step : IsRightSpine x n r → IsRightSpine x (n + 1) (.op l r)

/-- A magma equation `x = t` where the LHS is a single variable. -/
structure MagmaEq where
  /-- The LHS variable index. -/
  lhsVar : Nat
  /-- The RHS term. -/
  rhs : MagmaTerm
  deriving Repr

namespace MagmaEq

/-- An equation `x = t` holds in a magma `(α, μ)` if for every assignment,
    `f(x) = eval(t, f, μ)`. -/
def holds (eq : MagmaEq) (α : Type u) (μ : α → α → α) : Prop :=
  ∀ (f : Nat → α), f eq.lhsVar = eq.rhs.eval f μ

/-- `e₁` does NOT imply `e₂`: there exists a magma satisfying `e₁` but not `e₂`. -/
def notImplies (e₁ e₂ : MagmaEq) : Prop :=
  ∃ (α : Type) (μ : α → α → α),
    (∀ f : Nat → α, f e₁.lhsVar = e₁.rhs.eval f μ) ∧
    (∃ f : Nat → α, f e₂.lhsVar ≠ e₂.rhs.eval f μ)

end MagmaEq

/-- Left-spine implies leftmostVar and leftSpineDepth agree with the predicate. -/
theorem IsLeftSpine.leftmostVar_eq {x n : Nat} {t : MagmaTerm}
    (h : IsLeftSpine x n t) : t.leftmostVar = x := by
  induction h with
  | base => rfl
  | step _ ih => exact ih

theorem IsLeftSpine.leftSpineDepth_eq {x n : Nat} {t : MagmaTerm}
    (h : IsLeftSpine x n t) : t.leftSpineDepth = n := by
  induction h with
  | base => rfl
  | step _ ih => simp [MagmaTerm.leftSpineDepth, ih]

/-- Right-spine implies rightmostVar and rightSpineDepth agree. -/
theorem IsRightSpine.rightmostVar_eq {x n : Nat} {t : MagmaTerm}
    (h : IsRightSpine x n t) : t.rightmostVar = x := by
  induction h with
  | base => rfl
  | step _ ih => exact ih

theorem IsRightSpine.rightSpineDepth_eq {x n : Nat} {t : MagmaTerm}
    (h : IsRightSpine x n t) : t.rightSpineDepth = n := by
  induction h with
  | base => rfl
  | step _ ih => simp [MagmaTerm.rightSpineDepth, ih]
