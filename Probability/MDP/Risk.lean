import Probability.Probability.Basic
import Mathlib.Data.Finset.Image

namespace Risk


open Findist FinRV
open Classical
variable {n : ℕ}
variable (P : Findist n) (X : FinRV n ℚ) (c : ℚ) (α : ℚ)

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
def translated_RV : FinRV n ℚ := fun i => X i + c
/-- Value-at-Risk of X at level α: VaR_α(X) = min { t ∈ X(Ω) | P[X ≤ t] ≥ α }.
If we assume 0 ≤ α ∧ α ≤ 1, then the "else 0" branch is never used. -/
def VaR (P : Findist n) (X : FinRV n ℚ) (α : ℚ) : ℚ :=
  let S : Finset ℚ := (rangeOfRV X).filter (fun t => cdf P X t ≥ α)
  if h : S.Nonempty then
    S.min' h
  else
    0


theorem cdf_translation (P : Findist n) (X : FinRV n ℚ) (t c : ℚ) :
  cdf P (fun ω => X ω + c) t = cdf P X (t - c) := by
  rw [cdf, cdf]
  apply congr_arg
  ext ω
  simp [FinRV.leq]
  exact le_sub_iff_add_le.symm


theorem VaR_monotone (P : Findist n) (X Y : FinRV n ℚ) (α : ℚ)
  (hXY : ∀ ω, X ω ≤ Y ω) : VaR P X α ≤ VaR P Y α := by
  have hcdf : ∀ t : ℚ, cdf P X t ≤ cdf P Y t := by
    intro t
    have h_ind : (𝕀 ∘ (Y ≤ᵣ t)) ≤ (𝕀 ∘ (X ≤ᵣ t)) := by
      intro ω
      have h1 : Y ω ≤ t → X ω ≤ t := by
        intro hY
        exact le_trans (hXY ω) hY
      by_cases hY : Y ω ≤ t
      · have hX : X ω ≤ t := by exact h1 hY
        simp [𝕀, indicator, FinRV.leq, hY, hX]
      · simp [𝕀, indicator, FinRV.leq, hY]
    sorry
  rw [hx, hy]
  sorry

/-- The minimum of a set shifted by a constant is the minimum plus the constant. -/
lemma finset_min'_image_add_const {A : Finset ℚ} (hA : A.Nonempty) (c : ℚ) :
    (A.image fun t => t + c).min' ((Finset.image_nonempty.mpr hA)) = (A.min' hA) + c := by

  let a_min := A.min' hA -- let a_min be the minimum of A
  -- the goal is to show that a_min + c is the minimum of the shifted set.
  -- show a_min + c is in the shifted set.
  have h_mem : a_min + c ∈ (A.image fun t => t + c) := by
    apply Finset.mem_image.mpr
    exact ⟨a_min, Finset.min'_mem A hA, rfl⟩  -- a_min is the min element, so it must be in A.
  -- show a_min + c is less than or equal to all elements t' in the shifted set.
  have h_le : ∀ t', t' ∈ (A.image fun t => t + c) → a_min + c ≤ t' := by
    intro t' h_t'
    rcases Finset.mem_image.mp h_t' with ⟨t, h_t_mem, rfl⟩ -- t' must be of the form t + c for some t in A.
    have h_a_min_le_t : a_min ≤ t := Finset.min'_le A t h_t_mem -- because a_min is the minimum of A, a_min ≤ t.
    exact add_le_add_right h_a_min_le_t c -- add c to both sides of the inequality.
  apply le_antisymm
  ·
    apply Finset.min'_le -- show that the minimum of the shifted set is less than or equal to a_min + c.
    exact h_mem
  ·
    apply Finset.le_min'-- show that a_min + c is less than or equal to the minimum of the shifted set.
    exact h_le


theorem range_translated_eq_shifted_range : rangeOfRV (translated_RV X c) = (rangeOfRV X).image fun t => t + c := by
  -- Proof: Unfold rangeOfRV, use Finset.image properties, and ext.
  unfold rangeOfRV translated_RV
  simp_rw [Finset.image_image]
  rfl


theorem VaR_set_translated: (rangeOfRV (translated_RV X c)).filter fun t' => cdf P (translated_RV X c) t' ≥ α =
    ((rangeOfRV X).filter fun t => cdf P X t ≥ α).image fun t => t + c := by
  apply Finset.ext
  intro t_prime

  -- The LHS is (range(X+c) ∩ {t' | cdf(X+c, t') ≥ α})
  -- The RHS is {t+c | t ∈ range(X) ∩ {t | cdf(X, t) ≥ α}}

  constructor-- Split into two directions (biconditional)
  · intro h_in_LHS
    -- decompose the filter membership h_in_LHS into its two parts:
    have h_decomp := Finset.mem_filter.mp h_in_LHS
    have h_mem_range_Y : t_prime ∈ rangeOfRV (translated_RV X c) := h_decomp.1
    have h_cdf_Y : cdf P (translated_RV X c) t_prime ≥ α := h_decomp.2

    -- rewrite the range membership to expose the image structure:
    rw [range_translated_eq_shifted_range] at h_mem_range_Y

    -- decompose the image membership to get t ∈ range(X):
    rcases Finset.mem_image.mp h_mem_range_Y with ⟨t, h_t_mem, rfl⟩

    -- 4. Prove t ∈ range(X) AND cdf(X, t) ≥ α (RHS membership via filter)
    unfold translated_RV at h_cdf_Y
    rw [cdf_translation P X (t + c) c] at h_cdf_Y
    ring_nf at h_cdf_Y
    apply Finset.mem_image.mpr
    exact ⟨t, Finset.mem_filter.mpr ⟨h_t_mem, h_cdf_Y⟩, rfl⟩

  · intro h_in_RHS
    rcases Finset.mem_image.mp h_in_RHS with ⟨t, h_t_S_X, rfl⟩
    -- decompose h_t_S_X into its two parts:
    have h_t_decomp := Finset.mem_filter.mp h_t_S_X
    have h_t_mem_range_X : t ∈ rangeOfRV X := h_t_decomp.1
    have h_cdf_X : cdf P X t ≥ α := h_t_decomp.2

    -- prove t+c ∈ range(X+c) AND cdf(X+c, t+c) ≥ α (LHS membership via filter)
    apply Finset.mem_filter.mpr

    constructor
    -- 1. Prove t+c ∈ range(X+c)
    · rw [range_translated_eq_shifted_range]
      exact Finset.mem_image_of_mem (fun x => x + c) h_t_mem_range_X

    -- 2. Prove cdf(X+c, t+c) ≥ α
    · unfold translated_RV
      rw [cdf_translation P X (t + c) c]
      ring_nf
      exact h_cdf_X


theorem VaR_translation_invariance (h_S_nonempty : ((rangeOfRV X).filter fun t => cdf P X t ≥ α).Nonempty) :
    VaR P (translated_RV X c) α = VaR P X α + c := by

  let S_X := (rangeOfRV X).filter fun t => cdf P X t ≥ α
  let S_Y := (rangeOfRV (translated_RV X c)).filter fun t' => cdf P (translated_RV X c) t' ≥ α

  have h_set_eq : S_Y = S_X.image fun t => t + c := VaR_set_translated P X c α
  have h_S_Y_nonempty : S_Y.Nonempty := by -- Show S_Y is also non-empty
    rw [h_set_eq]
    exact Finset.image_nonempty.mpr h_S_nonempty

  unfold VaR
  have h_VaR_X_eq : VaR P X α = S_X.min' h_S_nonempty := by
    simp only [S_X]
    apply dif_pos h_S_nonempty

  have h_VaR_Y_eq : VaR P (translated_RV X c) α = S_Y.min' h_S_Y_nonempty := by
    simp only [S_Y]
    apply dif_pos h_S_Y_nonempty

  calc
    VaR P (translated_RV X c) α
    _ = S_Y.min' h_S_Y_nonempty := by rw [h_VaR_Y_eq]
    _ = (S_X.image fun t => t + c).min' (Finset.image_nonempty.mpr h_S_nonempty) := by exact Finset.min'.congr_simp S_Y (Finset.image (fun t => t + c) S_X) h_set_eq h_S_Y_nonempty
    _ = S_X.min' h_S_nonempty + c := by exact finset_min'_image_add_const h_S_nonempty c
    _ = VaR P X α + c := by rw [←h_VaR_X_eq]


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
