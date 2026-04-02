/-
Copyright (c) 2026 Adam Flounder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpineIsolation.Defs

/-!
# Cyclic Magma Separation

The cyclic (successor) magma on `Fin n` with operation `a ◇ b = (a + 1) mod n`
separates left-spine equations of non-divisible depths.

This proves Part (a) of the Left-Spine Isolation Theorem.

## Main results

* `cyclic_eval`: In the cyclic magma, evaluating any term `t` yields
  `(f(leftmostVar t) + leftSpineDepth t) mod n`.
* `leftSpine_depth_notImplies`: A left-spine equation of depth `n` cannot
  imply one of depth `m` when `n ∤ m`.
-/

namespace SpineIsolation

/-- `(a % n + b) % n = (a + b) % n` for `n > 0`. -/
private theorem Nat.mod_add (a b n : Nat) (hn : 0 < n) :
    (a % n + b) % n = (a + b) % n := by
  rw [Nat.add_mod (a % n) b n, Nat.mod_eq_of_lt (Nat.mod_lt a hn), ← Nat.add_mod a b n]

/-- The cyclic (successor) magma operation on `Fin n`:
    `a ◇ b = ⟨(a.val + 1) % n, ...⟩`. -/
def cyclicOp {n : Nat} (hn : 0 < n) (a _b : Fin n) : Fin n :=
  ⟨(a.val + 1) % n, Nat.mod_lt _ hn⟩

/-- In the cyclic magma on `Fin n`, evaluating any term `t` yields
    `⟨(f(leftmostVar t).val + leftSpineDepth t) % n, ...⟩`. -/
theorem cyclic_eval {n : Nat} (hn : 0 < n) (t : MagmaTerm) (f : Nat → Fin n) :
    (t.eval f (cyclicOp hn)).val = ((f t.leftmostVar).val + t.leftSpineDepth) % n := by
  induction t with
  | var v =>
    simp [MagmaTerm.eval, MagmaTerm.leftmostVar, MagmaTerm.leftSpineDepth,
          Nat.mod_eq_of_lt (f v).isLt]
  | op l _r ih_l _ =>
    simp only [MagmaTerm.eval, cyclicOp, MagmaTerm.leftmostVar, MagmaTerm.leftSpineDepth]
    -- Goal: ((eval l).val + 1) % n = ((f l.leftmostVar).val + (l.leftSpineDepth + 1)) % n
    rw [ih_l, Nat.mod_add _ 1 n hn, Nat.add_assoc]

/-- In the cyclic magma, evaluating a left-spine term of depth `k` at
    variable `x` yields `(f(x) + k) % n`. -/
theorem cyclic_eval_leftSpine {n : Nat} (hn : 0 < n) {x k : Nat} {t : MagmaTerm}
    (h : IsLeftSpine x k t) (f : Nat → Fin n) :
    (t.eval f (cyclicOp hn)).val = ((f x).val + k) % n := by
  rw [cyclic_eval hn, h.leftmostVar_eq, h.leftSpineDepth_eq]

/-- The cyclic magma on `Fin n` satisfies any left-spine equation of depth `n`
    (since `(a + n) % n = a` for `a < n`). -/
theorem cyclic_satisfies_depth_n {n : Nat} (hn : 0 < n) {x : Nat} {t : MagmaTerm}
    (h : IsLeftSpine x n t) :
    (MagmaEq.mk x t).holds (Fin n) (cyclicOp hn) := by
  intro f
  apply Fin.ext
  rw [cyclic_eval_leftSpine hn h]
  simp [Nat.add_mod_right, Nat.mod_eq_of_lt (f x).isLt]

/-- The cyclic magma on `Fin n` fails a left-spine equation of depth `m`
    when `¬(n ∣ m)`. We exhibit `f = fun _ => ⟨0, hn⟩` as a witness. -/
theorem cyclic_fails_depth_m {n : Nat} (hn : 0 < n) {x m : Nat} {t : MagmaTerm}
    (h : IsLeftSpine x m t) (hndvd : ¬(n ∣ m)) :
    ∃ f : Nat → Fin n, f x ≠ t.eval f (cyclicOp hn) := by
  refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
  intro heq
  apply hndvd
  have hval : (⟨0, hn⟩ : Fin n).val = (t.eval (fun _ => ⟨0, hn⟩) (cyclicOp hn)).val :=
    congrArg Fin.val heq
  rw [cyclic_eval_leftSpine hn h] at hval
  simp at hval
  exact Nat.dvd_of_mod_eq_zero hval.symm

/-- **Left-Spine Isolation, Part (a).**
    A left-spine equation of depth `n` cannot imply a left-spine equation
    of depth `m` when `n ∤ m` (and `n ≥ 1`). -/
theorem leftSpine_depth_notImplies {x₁ x₂ n m : Nat} {t₁ t₂ : MagmaTerm}
    (hn : 0 < n) (h₁ : IsLeftSpine x₁ n t₁) (h₂ : IsLeftSpine x₂ m t₂)
    (hndvd : ¬(n ∣ m)) :
    MagmaEq.notImplies (MagmaEq.mk x₁ t₁) (MagmaEq.mk x₂ t₂) := by
  refine ⟨Fin n, cyclicOp hn, ?_, ?_⟩
  · exact cyclic_satisfies_depth_n hn h₁
  · exact cyclic_fails_depth_m hn h₂ hndvd

end SpineIsolation
