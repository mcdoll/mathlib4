/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.Matrix.Basic

/-!
# Matrices of dual numbers are isomorphic to dual numbers over matrices

Showing this for the more general case of `TrivSqZeroExt R M` would require an action between
`Matrix n n R` and `Matrix n n M`, which would risk causing diamonds.
-/

@[expose] public section


variable {R n : Type} [CommSemiring R] [Fintype n] [DecidableEq n]

open Matrix TrivSqZeroExt

set_option backward.isDefEq.respectTransparency.types false in
/-- Matrices over dual numbers and dual numbers over matrices are isomorphic. -/
@[simps]
def Matrix.dualNumberEquiv : Matrix n n (DualNumber R) ≃ₐ[R] DualNumber (Matrix n n R) where
  toFun A := ⟨of fun i j => (A i j).fst, of fun i j => (A i j).snd⟩
  invFun d := of fun i j => (d.fst i j, d.snd i j)
  map_mul' A B := by
    ext
    · simp [Matrix.mul_apply, fst_sum]
    · simp [snd_mul, smul_eq_mul, Matrix.mul_apply, snd_sum, ← Finset.sum_add_distrib, of_apply]
  map_add' _ _ := TrivSqZeroExt.ext rfl rfl
  commutes' r := by
    simp_rw [algebraMap_eq_inl', algebraMap_eq_diagonal, Pi.algebraMap_def,
      Algebra.algebraMap_self_apply, algebraMap_eq_inl, ← diagonal_map (inl_zero R), map_apply,
      fst_inl, snd_inl]
    rfl
