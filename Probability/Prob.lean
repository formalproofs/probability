import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.NNReal.Basic

import Mathlib.Logic.Function.Defs

import Mathlib.Data.Set.Basic

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Image

import Mathlib.Algebra.Group.Pi.Basic -- for Pi.single

--import Mathlib.Tactic.Explode
-- Adding a comment
open NNReal

variable {τ : Type}

section Indicator

/-- states that p is a valid probability value -/
@[simp]
abbrev Prob (p : ℚ) : Prop := 0 ≤ p ∧ p ≤ 1

namespace Prob

variable {p x y : ℚ} --creating variables

@[simp]
theorem of_complement ( hp : Prob p) : Prob (1-p) := by
        simp_all only [ Prob, sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right, and_self]

@[simp]
theorem complement_inv_nneg (hp : Prob p) : 0 ≤ (1-p)⁻¹ := by simp_all only [Prob, inv_nonneg, sub_nonneg]

theorem lower_bound_fst (hp : Prob p) (h : x ≤ y) : x ≤ p * x + (1-p) * y := by
        have h2 : (1-p) * x ≤ (1-p) * y := mul_le_mul_of_nonneg_left h hp.of_complement.1
        linarith

theorem lower_bound_snd (hp : Prob p) (h : y ≤ x) : y ≤ p * x + (1-p) * y := by
        have h2 : p * y ≤ p * x := mul_le_mul_of_nonneg_left h hp.1
        linarith

theorem upper_bound_fst (hp : Prob p) (h : y ≤ x) : p * x + (1-p) * y ≤ x := by
        have h2 : (1-p) * y ≤ (1-p) * x := mul_le_mul_of_nonneg_left h hp.of_complement.1
        linarith

theorem upper_bound_snd (hp : Prob p) (h : x ≤ y) : p * x + (1-p) * y ≤ y := by
        have h2 : p * x ≤ p * y := mul_le_mul_of_nonneg_left h hp.1
        linarith

end Prob
