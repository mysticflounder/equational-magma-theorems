/-
Copyright (c) 2026 Adam Flounder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpineIsolation.Defs

/-!
# Left-Zero Magma Separation

The left-zero magma (a ◇ b = a) satisfies every pure left-spine equation
and provides a universal counterexample separating left-spine from
right-spine and mixed-spine equations.

This proves Parts (b) and (c) of the Spine Isolation Theorem for Magma Implications.

## Main results

* `leftZero_eval_eq_leftmostVar`: In left-zero, evaluating any term yields the
  assignment at its leftmost leaf variable.
* `leftZero_satisfies_leftSpine`: Left-zero satisfies any pure left-spine equation.
* `leftSpine_notImplies_nonLeftSpine`: A pure left-spine equation cannot imply
  any equation whose RHS leftmost leaf differs from the LHS variable.
-/

namespace SpineIsolation

/-- The left-zero magma operation: `a ◇ b = a`. -/
def leftZeroOp (a _b : α) : α := a

/-- In the left-zero magma, evaluating any term yields the value of
    the leftmost leaf variable. -/
theorem leftZero_eval_eq_leftmostVar (t : MagmaTerm) (f : Nat → α) :
    t.eval f leftZeroOp = f t.leftmostVar := by
  induction t with
  | var n => rfl
  | op l _r ih_l _ih_r =>
    simp only [MagmaTerm.eval, leftZeroOp, MagmaTerm.leftmostVar]
    exact ih_l

/-- Left-zero satisfies any equation `x = t` where `t` has leftmost leaf `x`. -/
theorem leftZero_satisfies_of_leftmostVar_eq (eq : MagmaEq)
    (h : eq.rhs.leftmostVar = eq.lhsVar) :
    eq.holds α leftZeroOp := by
  intro f
  rw [leftZero_eval_eq_leftmostVar]
  exact congrArg f h.symm

/-- Left-zero satisfies any pure left-spine equation. -/
theorem leftZero_satisfies_leftSpine {x n : Nat} {t : MagmaTerm}
    (h : IsLeftSpine x n t) :
    (MagmaEq.mk x t).holds α leftZeroOp := by
  apply leftZero_satisfies_of_leftmostVar_eq
  exact h.leftmostVar_eq

/-- In the left-zero magma on `Bool`, any term whose leftmost leaf is NOT `x`
    has an assignment where it evaluates to a value ≠ `f(x)`. -/
theorem leftZero_separates_Bool (eq₂ : MagmaEq)
    (hne : eq₂.rhs.leftmostVar ≠ eq₂.lhsVar) :
    ∃ f : Nat → Bool, f eq₂.lhsVar ≠ eq₂.rhs.eval f leftZeroOp := by
  -- Define f(lhsVar) = true, f(everything else) = false
  refine ⟨fun n => n == eq₂.lhsVar, ?_⟩
  rw [leftZero_eval_eq_leftmostVar]
  simp [beq_iff_eq, hne]

/-- **Spine Isolation, Parts (b)+(c).**
    If `e₁` is a pure left-spine equation and `e₂` has its RHS leftmost leaf
    different from its LHS variable, then `e₁` does not imply `e₂`.

    This covers:
    - Part (b): `e₂` is a pure right-spine equation (leftmost leaf ≠ LHS var)
    - Part (c): `e₂` is a mixed-spine equation (leftmost leaf ≠ LHS var) -/
theorem leftSpine_notImplies_nonLeftSpine {x n : Nat} {t₁ : MagmaTerm}
    (h₁ : IsLeftSpine x n t₁) (e₂ : MagmaEq)
    (hne : e₂.rhs.leftmostVar ≠ e₂.lhsVar) :
    MagmaEq.notImplies (MagmaEq.mk x t₁) e₂ := by
  refine ⟨Bool, leftZeroOp, ?_, ?_⟩
  · -- Left-zero satisfies e₁
    intro f
    rw [leftZero_eval_eq_leftmostVar, h₁.leftmostVar_eq]
  · -- Left-zero fails e₂
    exact leftZero_separates_Bool e₂ hne

end SpineIsolation
