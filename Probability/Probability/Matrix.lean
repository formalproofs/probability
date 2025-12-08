import Probability.Probability.Prelude

import Probability.Probability.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace Matrix

structure ProbabilityMatrix (n : ℕ) : Type where
    --(n x n) Matrix where each row is a probability distribution
    P : (Matrix (Fin n) (Fin n) ℚ)
    row_sum : P *ᵥ 1 = 1
    nneg : ∀ i j : Fin n, P i j ≥ 0

variable (n : ℕ) (Prob : ProbabilityMatrix n) (μ : Findist n)


theorem dist_prob_product_nneg : μ.p ᵥ* (Prob.P) ≥ 0 := by
    unfold vecMul
    intro j
    apply dotProduct_nonneg_of_nonneg
    exact μ.nneg
    exact fun i => Prob.nneg i j

theorem dist_prob_product_sum : μ.p ᵥ* (Prob.P) ⬝ᵥ 1 = 1 := by
    rw [← dotProduct_mulVec]
    calc μ.p ⬝ᵥ Prob.P *ᵥ 1 = μ.p ⬝ᵥ 1 := by rw[Prob.row_sum]
        _ = 1 ⬝ᵥ μ.p := by rw[dotProduct_comm]
        _ = 1 := by rw[μ.prob]
