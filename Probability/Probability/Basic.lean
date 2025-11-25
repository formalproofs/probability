import Probability.Probability.Defs

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
  # Basic properties for probability spaces and expectations

  The main results:
  - Correspondence between expectations and probabilities (indicator functions)
  - Arithmetic manipulations of random variables
  - The law of total probabilities
  - The law of total expectations
-/

namespace Findist

variable {n : ℕ} {P : Findist n} {B : FinRV n Bool}


theorem ge_zero : 0 ≤ ℙ[ B // P ] :=
    by rw [Ex.prob_eq_exp_ind]
       have h : (0 : FinRV n ℚ) ≤ 𝕀∘B := ind_nneg
       calc 0 = 𝔼[0 // P] := exp_const.symm
            _ ≤ 𝔼[𝕀 ∘ B//P] := exp_monotone h


theorem le_one : ℙ[B // P] ≤ 1 :=
    by rw [Ex.prob_eq_exp_ind]
       have h : 𝕀∘B ≤ (1 : FinRV n ℚ) := ind_le_one
       calc 𝔼[𝕀 ∘ B//P] ≤ 𝔼[1 // P] := exp_monotone h
            _ = 1 := exp_const

theorem in_prob (P : Findist n) : Prob ℙ[B // P] := ⟨ge_zero, le_one⟩

end Findist

------------------------------ Probability ---------------------------

namespace Pr

variable {n : ℕ} {P : Findist n} {B C : FinRV n Bool}


theorem prob_compl_sums_to_one : ℙ[B // P] + ℙ[¬ᵣB // P] = 1 :=
    by rw [Ex.prob_eq_exp_ind, Ex.prob_eq_exp_ind]
       rw [←exp_dists_add]
       rw [one_of_ind_bool_or_not]
       exact exp_one



theorem prob_compl_one_minus : ℙ[¬ᵣB // P] = 1 - ℙ[B // P] :=
    by have := prob_compl_sums_to_one (P:=P) (B:=B)
       linarith


-- TODO: I think that we can show the following results from the law of total expectations

--TODO: theorem law_of_total_probs_bool : ℙ[B // P] = ℙ[B * C // P] + ℙ[B * (¬ᵣC) // P] :=
/-  by
    unfold probability
    have h : ∀ i : Fin n, (𝕀 (B i)) = (𝕀 (B i * C i)) + (𝕀 (B i * (¬ᵣ C) i)) :=
      by
        intro i
        by_cases hB : B i
        · by_cases hC : C i
          · simp [hB, hC, FinRV.not, indicator]
          · simp [hB, hC, FinRV.not, indicator]
        · by_cases hC : C i
          · simp [hB, hC, FinRV.not, indicator]
          · simp [hB, hC, FinRV.not, indicator]
    sorry ---I tried to do this proof but got stuck, feel free to delete my work
-/

--TODO: theorem conditional_total (h : 0 < ℙ[C // P]) : ℙ[B * C // P] =  ℙ[B | C // P] * ℙ[C // P] :=
  -- by simp [probability_cnd] at ⊢ h
  --    have : P.ℙ.iprodb C * (P.ℙ.iprodb C)⁻¹ = 1 :=
  --           Rat.mul_inv_cancel (P.ℙ.iprodb C) (Ne.symm (ne_of_lt h))
  --    calc
  --       P.ℙ.iprodb (B ∧ᵣC) = P.ℙ.iprodb (B ∧ᵣC) * 1 := by ring
  --       _ = P.ℙ.iprodb (B ∧ᵣC) * (P.ℙ.iprodb C * (P.ℙ.iprodb C)⁻¹) := by rw [←this]
  --       _ = P.ℙ.iprodb (B ∧ᵣ C) / P.ℙ.iprodb C * P.ℙ.iprodb C := by ring


--TODO: theorem law_total_prbs_cnd  (h1 : 0 < ℙ[C // P]) (h2 : ℙ[C // P] < 1)
--: ℙ[B // P] = ℙ[B | C // P] * ℙ[ C // P] + ℙ[B | ¬ᵣC // P] * ℙ[¬ᵣC // P] :=
--        by have h2' : 0 < ℙ[¬ᵣC // P] := by rw [prob_compl_one_minus]; linarith
--           rw [←conditional_total P B C h1]
--           rw [←conditional_total P B (¬ᵣC) h2']
--           exact law_of_total_probs_bool P B C

variable {k : ℕ}  {L : FinRV n (Fin k)}

-- TODO: we can  prove this from the law for expectations
-- TODO: theorem law_of_total_probs : ∑ i : Fin k, ℙ[B * (L =ᵣ i) // P] = ℙ[B // P] := sorry

end Pr

------------------------------ Expectation ---------------------------

namespace PMF

variable {n : ℕ} {k : ℕ}  {L : FinRV n (Fin k)}
variable {pmf : Fin k → ℚ} {P : Findist n}

theorem pmf_rv_k_ge_1 (h : PMF pmf P L)  : 0 < k :=
  match k with
  | Nat.zero =>   Fin.pos <| L ⟨0,P.nonempty⟩
  | Nat.succ k₂ => Nat.zero_lt_succ k₂

end PMF

------------------------------ Expectation ---------------------------

namespace Ex

variable {n : ℕ} {P : Findist n}
variable {k : ℕ} {X : FinRV n ℚ} {B : FinRV n Bool} {L : FinRV n (Fin k)}

variable {pmf : Fin k → ℚ}

example (f g : Fin k → ℚ) (h : f = g) : ∑ i, f i = ∑ i, g i := by
  let ff := f
  have h2 : ff = f := by unfold ff; rfl
  rw [←h2]
  rw [←h]


-- TODO: The following derivations should be our focus

---- STEP 1:

/-- Pi.single is an indicator for the random variable -/
theorem indicator_eq_single : ∀ ω : Fin n, (fun i ↦ (L =ᵢ i) ω) = Pi.single (L ω) (1:ℚ) :=
  by intro ω
     simp [Pi.single]
     ext i
     simp [Function.update]
     by_cases h : L ω = i
     · simp [h]
     · simp [h]; exact fun a ↦ h a.symm

variable  (g : Fin k → ℚ)

theorem fin_sum_g: ∀ ω, ∑ i, (g i) * (𝕀 ∘ (L =ᵣ i)) ω = g (L ω) := by
  intro ω
  unfold FinRV.eq 𝕀 Function.comp indicator
  simp
  generalize hk : L ω = j
  let f i := g i * (decide (j = i)).rec 0 1
  have h1 (i : Fin k) : j ≠ i → f i = 0 := by intro h; simp_all [f]
  have h2 (i : Fin k ) : j = i → f i = g j := by intro h; simp_all [f]
  have hh : f = (fun i ↦ g i * (decide (j = i)).rec 0 1) :=  by simp [f]
  rw [←hh]
  rw [←h2 j rfl]
  apply Finset.sum_eq_single_of_mem
  · simp only [Finset.mem_univ]
  · intro b _ hneq
    exact h1 b hneq.symm

variable {ρ : Type} [AddCommMonoid ρ]

/-- Linearity of expectation --/
theorem exp_linear {m : ℕ} (Xs : Fin m → FinRV n ℚ) : 𝔼[∑ i : Fin m, Xs i // P] = ∑ i : Fin m, 𝔼[Xs i // P] :=
  by unfold expect
     exact dotProduct_sum P.p Finset.univ Xs

/-- Decompose a random variable to a sum of constant variables with indicators  -/
theorem fin_sum_simple : (g ∘ L) = ∑ i, (fun _ ↦ g i) * (L =ᵢ i) :=
  by ext ω
     simp

theorem idktheorem (P : Findist n) (L : FinRV n (Fin k)) (g : Fin k → ℚ) :
    𝔼[g ∘ L // P] = ∑ i : Fin k, g i * ℙ[L =ᵣ i // P] := by
    rw [fin_sum_simple]
    rw [exp_linear]
    apply Fintype.sum_congr
    intro a
    rw [exp_prod_const_fun]
    rw [prob_eq_exp_ind]
    rw [exp_indi_eq_exp_indr]


-- TODO: just need the expectation of a constant function and then we are done!!!!

-- LOTUS: the law of the unconscious statistician (or similar)
theorem LOTUS {g : Fin k → ℚ} (h : PMF pmf P L):
        𝔼[ g ∘ L // P ] = ∑ i : Fin k, (pmf i) * (g i) :=
  by rw [idktheorem P L g]
     apply Fintype.sum_congr
     intro i
     rw [h i]
     ring

-- this proof will rely on the extensional property of function (functions are the same if they
-- return the same value for the same inputs; for all inputs)
theorem condexp_pmf : 𝔼[ X |ᵣ L  // P] =  (fun i ↦ 𝔼[ X | (L =ᵣ i) // P]) ∘ L :=
  by unfold expect_cnd_rv
     ext ω; simp



theorem expexp : 𝔼[ 𝔼[ X |ᵣ L // P] // P ] = ∑ i : Fin k, 𝔼[ X | L =ᵣ i // P] * ℙ[ L =ᵣ i // P]   := by
  let pmf i := ℙ[ L =ᵣ i // P]
  have h_pmf : PMF pmf P L := fun i ↦ rfl
  rw [condexp_pmf, LOTUS h_pmf]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm]

-- STEP 2:

example (a : ℚ) : a * 0 = 0 := Rat.mul_zero a

theorem exp_prod_μ  : 𝔼[X | B // P] * ℙ[B // P] = 𝔼[X * (𝕀 ∘ B) // P] :=
    by unfold expect_cnd
       by_cases h: ℙ[B//P] = 0
       · rw [h, Rat.mul_zero]
         unfold expect
         rw [dotProd_hadProd_comm, dotProd_hadProd_rotate, prod_zero_of_prob_zero h]
         exact (dotProduct_zero X).symm
       · simp_all

-- STEP 3:

example (Xs : Fin k → FinRV n ℚ) : (fun ω ↦ ∑ i, Xs i ω)  = ∑ i, Xs i := by exact Eq.symm (Finset.sum_fn Finset.univ Xs)

-- proves that μ distributes over the random variables
theorem μ_dist (Xs : Fin k → FinRV n ℚ) : ∑ i : Fin k, 𝔼[X * (Xs i) // P] = 𝔼[X * (fun ω ↦ ∑ i : Fin k, Xs i ω) // P] := by
    rw [←Finset.sum_fn Finset.univ Xs]
    rw [←rv_prod_sum_linear]
    rw [exp_linear]



theorem fin_sum : ∀ ω : Fin n, ∑ i : Fin k, (𝕀 ∘ (L =ᵣ i)) ω = (1:ℚ) :=
    by have := fin_sum_g 1 (L := L)
       simp_all only [Pi.one_apply, Function.comp_apply, FinRV.eq, one_mul, implies_true]

theorem exp_eq_exp_cond_true : 𝔼[X // P] = 𝔼[X * (fun _ ↦ 1 ) // P] := by simp [expect, Pi.mul_def]


example {f g : ℕ → ℚ} {m : ℕ} (h : ∀ n : ℕ, f n = g n) :
    ∑ i : Fin m, f i = ∑ i : Fin m, g i :=
    by apply Finset.sum_congr
       · simp
       · simp_all

-- STEP 4: We now use the results above to prove the law of total expectations
theorem law_total_exp : 𝔼[𝔼[X |ᵣ L // P] // P] = 𝔼[X // P] :=
  calc
    𝔼[𝔼[X |ᵣ L // P] // P ] = ∑ i : Fin k, 𝔼[ X | L =ᵣ i // P ] * ℙ[ L =ᵣ i // P] := expexp
    _ =  ∑ i : Fin k, 𝔼[X * (𝕀 ∘ (L =ᵣ i)) // P] := by
          apply Finset.sum_congr
          · rfl
          · exact fun a _ ↦ exp_prod_μ
    _ = 𝔼[X * (fun ω ↦  ∑ i : Fin k, (𝕀 ∘ (L =ᵣ i)) ω) // P] := μ_dist (fun i ↦ 𝕀 ∘ (L=ᵣi))
    _ = 𝔼[X * (fun ω ↦  1) // P] := by
          unfold expect; conv => lhs; congr; rfl; congr; rfl; intro ω; exact fin_sum ω
    _ = 𝔼[X // P]  := exp_eq_exp_cond_true.symm


end Ex
