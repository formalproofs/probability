import Probability.Probability.Defs

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
  # Basic properties for probability spaces and expectations

  The main results:
  - LOTUS: The law of the unconscious statistician 
  - The law of total expectations
  - The law of total probabilities
-/

namespace Findist

variable {n : ℕ} {P : Findist n} {B : FinRV n Bool}

theorem ge_zero : 0 ≤ ℙ[B // P] := 
    by rw [prob_eq_exp_ind]
       calc 0 = 𝔼[0 // P] := exp_const.symm 
            _ ≤ 𝔼[𝕀 ∘ B//P] := exp_monotone ind_nneg
       

theorem le_one : ℙ[B // P] ≤ 1 := 
    by rw [prob_eq_exp_ind]
       calc 𝔼[𝕀 ∘ B//P] ≤ 𝔼[1 // P] := exp_monotone ind_le_one 
            _ = 1 := exp_const 

theorem in_prob (P : Findist n) : Prob ℙ[B // P] := ⟨ge_zero, le_one⟩

end Findist

------------------------------ Probability ---------------------------

variable {n : ℕ} {P : Findist n} {B C : FinRV n Bool}

theorem prob_compl_sums_to_one : ℙ[B // P] + ℙ[¬ᵣB // P] = 1 := 
    by rw [prob_eq_exp_ind, prob_eq_exp_ind, ←exp_dists_add, one_of_ind_bool_or_not]
       exact exp_one 

theorem prob_compl_one_minus : ℙ[¬ᵣB // P] = 1 - ℙ[B // P] :=
    by rw [←prob_compl_sums_to_one (P:=P) (B:=B)]; ring 


------------------------------ Expectation ---------------------------

section Expectation 

variable {n : ℕ} {P : Findist n}
variable {k : ℕ} {X : FinRV n ℚ} {B : FinRV n Bool} {L : FinRV n (Fin k)}
variable  (g : Fin k → ℚ)

/-- LOTUS: The law of the unconscious statistician (or similar) -/
theorem LOTUS : 𝔼[g ∘ L // P ] = ∑ i, ℙ[L =ᵣ i // P] * (g i) :=
  by rewrite [exp_decompose (X := g ∘ L) (L := L) ]
     apply Fintype.sum_congr
     intro i
     rewrite [←indi_eq_indr]
     rewrite [←exp_cond_eq_def (X := g ∘ L) ]
     by_cases! h : ℙ[L =ᵣ i // P] = 0 
     · rw [h];  simp only [mul_zero, zero_mul]
     · rw [exp_cond_const i h ]
       ring 

theorem law_total_exp : 𝔼[𝔼[X |ᵣ L // P] // P] = 𝔼[X // P] :=
  let g i := 𝔼[X | L =ᵣ i // P]
  calc
    𝔼[𝔼[X |ᵣ L // P] // P ] = ∑ i , ℙ[ L =ᵣ i // P] * 𝔼[ X | L =ᵣ i // P ] := LOTUS g
    _ =  ∑ i , 𝔼[ X | L =ᵣ i // P ] * ℙ[ L =ᵣ i // P] := by apply Fintype.sum_congr; intro i; ring 
    _ =  ∑ i : Fin k, 𝔼[X * (𝕀 ∘ (L =ᵣ i)) // P] := by apply Fintype.sum_congr; exact fun a  ↦ exp_cond_eq_def
    _ =  ∑ i : Fin k, 𝔼[X * (L =ᵢ i) // P] := by apply Fintype.sum_congr; intro i; apply exp_congr; rw[indi_eq_indr] 
    _ = 𝔼[X // P]  := by rw [←exp_decompose]

end Expectation 

section Probability 

variable {k : ℕ}  {L : FinRV n (Fin k)}

/-- The law of total probabilities -/
theorem law_of_total_probs : ℙ[B // P] =  ∑ i, ℙ[B * (L =ᵣ i) // P]  := 
  by rewrite [prob_eq_exp_ind, rv_decompose (𝕀∘B) L, exp_additive]
     apply Fintype.sum_congr
     intro i 
     rewrite [prob_eq_exp_ind] 
     apply exp_congr
     ext ω
     by_cases h1 : L ω = i 
     repeat by_cases h2 : B ω; repeat simp [h1, h2, 𝕀, indicator ]


end Probability 

#lint 
