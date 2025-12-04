import Probability.Probability.Basic

namespace Risk

open Findist FinRV

variable {n : ℕ}

def cdf (P : Findist n) (X : FinRV n ℚ) (t : ℚ) : ℚ := ℙ[X ≤ᵣ t // P]

theorem cdf_monotone (P : Findist n) (X : FinRV n ℚ) (t1 t2 : ℚ)
  (ht : t1 ≤ t2) : cdf P X t1 ≤ cdf P X t2 := by
  simp [cdf]
  apply exp_monotone
  intro ω
  by_cases h1 : X ω ≤ t1
  · have h2 : X ω ≤ t2 := le_trans h1 ht
    simp [FinRV.leq, 𝕀, indicator, h1, h2]
  · simp [𝕀, indicator, FinRV.leq, h1]
    by_cases h2 : X ω ≤ t2
    · simp [h2]
    · simp [h2] ---these lines seem really unnecessary but idk how to fix it


/-- Finite set of values taken by a random variable X : Fin n → ℚ. -/
def rangeOfRV (X : FinRV n ℚ) : Finset ℚ := Finset.univ.image X

/-- Value-at-Risk of X at level α: VaR_α(X) = min { t ∈ X(Ω) | P[X ≤ t] ≥ α }.
If we assume 0 ≤ α ∧ α ≤ 1, then the "else 0" branch is never used. -/
def VaR (P : Findist n) (X : FinRV n ℚ) (α : ℚ) : ℚ :=
  let S : Finset ℚ := (rangeOfRV X).filter (fun t => cdf P X t ≥ α)
  if h : S.Nonempty then
    S.min' h
  else
    0 --this is illegal i know -- Keith can fix it :)

notation "VaR[" X "//" P ", " α "]" => VaR P X α

--(Emily) I am now thinking of just trying to keep it in Q
--so I wouln't use anything between these lines!
------------------- defined over the reals to prove monotonicity ---------------------------
noncomputable def cdfR (P : Findist n) (X : FinRV n ℝ) (t : ℝ) : ℝ := ℙ[X ≤ᵣ t // P]

theorem cdfR_monotone (P : Findist n) (X : FinRV n ℝ) (t1 t2 : ℝ)
  (ht : t1 ≤ t2) : cdfR P X t1 ≤ cdfR P X t2 := by
  simp [cdfR]
  apply exp_monotone
  intro ω
  by_cases h1 : X ω ≤ t1
  · have h2 : X ω ≤ t2 := le_trans h1 ht
    simp [FinRV.leq, 𝕀, indicator, h1, h2]
  · simp [𝕀, indicator, FinRV.leq, h1]
    by_cases h2 : X ω ≤ t2
    · simp [h2]
    · simp [h2]

/-- Value-at-Risk of X at level α: VaR_α(X) = inf {t:ℝ | P[X ≤ t] ≥ α } -/
noncomputable def VaR_R (P : Findist n) (X : FinRV n ℝ) (α : ℝ) : ℝ :=
  sInf { t : ℝ | cdfR P X t ≥ α }

theorem VaR_monotone (P : Findist n) (X Y : FinRV n ℝ) (α : ℝ)
  (hXY : ∀ ω, X ω ≤ Y ω) : VaR_R P X α ≤ VaR_R P Y α := by
  let Sx : Set ℝ := { t : ℝ | cdfR P X t ≥ α }
  let Sy : Set ℝ := { t : ℝ | cdfR P Y t ≥ α }
  have hx : VaR_R P X α = sInf Sx := rfl
  have hy : VaR_R P Y α = sInf Sy := rfl
  have hsubset : Sy ⊆ Sx := by
    unfold Sy Sx
    intro t ht
    have h_cdf : ∀ t, cdfR P X t ≥ cdfR P Y t := by
      intro t

      sorry
    sorry
  rw [hx, hy]
  sorry

-------------------------------------------------------------------

theorem VaR_translation_invariant (P : Findist n) (X : FinRV n ℚ) (α c : ℚ) :
  VaR P (fun ω => X ω + c) α = VaR P X α + c := sorry

theorem VaR_positive_homog (P : Findist n) (X : FinRV n ℚ) (α c : ℚ)
  (hc : c > 0) : VaR P (fun ω => c * X ω) α = c * VaR P X α := sorry


/-- Tail indicator: 1 if X(ω) > t, else 0. -/
def tailInd (X : FinRV n ℚ) (t : ℚ) : FinRV n ℚ :=
  fun ω => if X ω > t then 1 else 0

/-- Conditional Value-at-Risk (CVaR) of X at level α under P.
CVaR_α(X) =  E[X * I[X > VaR] ] / P[X > VaR]
If the tail probability is zero, CVaR is defined to be 0.
-/
def CVaR (P : Findist n) (X : FinRV n ℚ) (α : ℚ) : ℚ :=
  let v := VaR P X α
  let B : FinRV n ℚ := tailInd X v
  let num := 𝔼[X * B // P]
  let den := ℙ[X >ᵣ v // P]
  if _ : den = 0 then
     0
  else
     num / den

-- NOTE (Marek): The CVaR, as defined above is not convex/concave.
-- See Page 14 at https://www.cs.unh.edu/~mpetrik/pub/tutorials/risk2/dlrl2023.pdf
-- NOTE (Marek): The CVaR above is defined for costs and not rewards

notation "CVaR[" X "//" P ", " α "]" => CVaR P X α

--TODO: prove...
-- monotonicity: (∀ ω, X ω ≤ Y ω) → CVaR[α, X // P] ≤ CVaR[α, Y // P]
-- translation: CVaR[α, (fun ω => X ω + c) // P] = CVaR[α, X // P] + c
-- positive homogeneity: c > 0 → CVaR[α, (fun ω => c * X ω) // P] = c * CVaR[α, X // P]
-- convexity
-- CVaR ≥ VaR: CVaR[α, X // P] ≥ VaR[α, X // P]


end Risk
