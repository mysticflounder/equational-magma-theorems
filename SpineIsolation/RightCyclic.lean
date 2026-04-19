/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpineIsolation.Defs

/-!
# Right-Cyclic Magma Separation

The right-cyclic magma on `Fin n` with operation `a ◇ b = (b + 1) mod n`
separates right-spine equations of non-divisible depths, giving a direct
proof of the Right-Spine Isolation corollary without passing through the
opposite-magma construction.

This file mirrors `SpineIsolation/Cyclic.lean`; the two differ only in
whether the operation advances the left or the right operand.

## Main results

* `rightCyclic_eval`: in the right-cyclic magma, evaluating any term `t`
  yields `(f(rightmostVar t) + rightSpineDepth t) mod n`.
* `rightSpine_depth_notImplies`: a right-spine equation of depth `n` cannot
  imply one of depth `m` when `n ∤ m`.
-/

namespace SpineIsolation

/-- `(a % n + b) % n = (a + b) % n` for `n > 0`. -/
private theorem Nat.mod_add (a b n : Nat) (hn : 0 < n) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_eq_of_lt (Nat.mod_lt a hn), ← Nat.add_mod a b n]

/-- The right-cyclic magma operation on `Fin n`:
    `a ◇ b = ⟨(b.val + 1) % n, ...⟩`. -/
def rightCyclicOp {n : Nat} (hn : 0 < n) (_a b : Fin n) : Fin n :=
  ⟨(b.val + 1) % n, Nat.mod_lt _ hn⟩

/-- In the right-cyclic magma on `Fin n`, evaluating any term `t` yields
    `⟨(f(rightmostVar t).val + rightSpineDepth t) % n, ...⟩`. -/
theorem rightCyclic_eval {n : Nat} (hn : 0 < n) (t : MagmaTerm) (f : Nat → Fin n) :
    (t.eval f (rightCyclicOp hn)).val =
      ((f t.rightmostVar).val + t.rightSpineDepth) % n := by
  induction t with
  | var v =>
    simp [MagmaTerm.eval, MagmaTerm.rightmostVar, MagmaTerm.rightSpineDepth,
          Nat.mod_eq_of_lt (f v).isLt]
  | op _l r _ih_l ih_r =>
    simp only [MagmaTerm.eval, rightCyclicOp, MagmaTerm.rightmostVar,
               MagmaTerm.rightSpineDepth]
    rw [ih_r, Nat.mod_add _ 1 n hn, Nat.add_assoc]

/-- In the right-cyclic magma, evaluating a right-spine term of depth `k`
    at variable `x` yields `(f(x) + k) % n`. -/
theorem rightCyclic_eval_rightSpine {n : Nat} (hn : 0 < n) {x k : Nat} {t : MagmaTerm}
    (h : IsRightSpine x k t) (f : Nat → Fin n) :
    (t.eval f (rightCyclicOp hn)).val = ((f x).val + k) % n := by
  rw [rightCyclic_eval hn, h.rightmostVar_eq, h.rightSpineDepth_eq]

/-- The right-cyclic magma on `Fin n` satisfies any right-spine equation of
    depth `n` (since `(a + n) % n = a` for `a < n`). -/
theorem rightCyclic_satisfies_depth_n {n : Nat} (hn : 0 < n) {x : Nat} {t : MagmaTerm}
    (h : IsRightSpine x n t) :
    (MagmaEq.mk x t).holds (Fin n) (rightCyclicOp hn) := by
  intro f
  apply Fin.ext
  rw [rightCyclic_eval_rightSpine hn h]
  simp [Nat.add_mod_right, Nat.mod_eq_of_lt (f x).isLt]

/-- The right-cyclic magma on `Fin n` fails a right-spine equation of depth
    `m` when `¬(n ∣ m)`. Witness: the constant-zero assignment. -/
theorem rightCyclic_fails_depth_m {n : Nat} (hn : 0 < n) {x m : Nat} {t : MagmaTerm}
    (h : IsRightSpine x m t) (hndvd : ¬(n ∣ m)) :
    ∃ f : Nat → Fin n, f x ≠ t.eval f (rightCyclicOp hn) := by
  refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
  intro heq
  apply hndvd
  have hval : (⟨0, hn⟩ : Fin n).val =
      (t.eval (fun _ => ⟨0, hn⟩) (rightCyclicOp hn)).val :=
    congrArg Fin.val heq
  rw [rightCyclic_eval_rightSpine hn h] at hval
  simp at hval
  exact Nat.dvd_of_mod_eq_zero hval.symm

/-- **Right-Spine Isolation.**
    A right-spine equation of depth `n` cannot imply a right-spine equation
    of depth `m` when `n ∤ m` (and `n ≥ 1`). -/
theorem rightSpine_depth_notImplies {x₁ x₂ n m : Nat} {t₁ t₂ : MagmaTerm}
    (hn : 0 < n) (h₁ : IsRightSpine x₁ n t₁) (h₂ : IsRightSpine x₂ m t₂)
    (hndvd : ¬(n ∣ m)) :
    MagmaEq.notImplies (MagmaEq.mk x₁ t₁) (MagmaEq.mk x₂ t₂) := by
  refine ⟨Fin n, rightCyclicOp hn, ?_, ?_⟩
  · exact rightCyclic_satisfies_depth_n hn h₁
  · exact rightCyclic_fails_depth_m hn h₂ hndvd

end SpineIsolation
