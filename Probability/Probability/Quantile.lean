import Probability.Probability.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Set.Operations

namespace Statistic 

section Definition 

--def UnitI := {α : ℚ // 0 ≤ α ∧ α ≤ 1}

variable {n : ℕ} (P : Findist n) (X Y : FinRV n ℚ) (α : ℚ) (q v : ℚ)

/-- Proof the `q` is an `α`-quantile of `X` --/
def IsQuantile  : Prop := ℙ[X ≤ᵣ q // P ] ≥ α ∧ ℙ[X ≥ᵣ q // P] ≥ 1 - α

/-- Proof that `q` is a lower bound on the `α`-quantile of `X` --/
def IsQuantileLower : Prop := ℙ[ X ≥ᵣ q // P] ≥ 1 - α

/-- Set of quantiles at a level `α`  --/
def Quantile : Set ℚ := { q | IsQuantile P X α q}

/-- Set of lower bounds on a quantile at `α` -/
def QuantileLower : Set ℚ := {q | IsQuantileLower P X α q}

-- TODO: Would it make sense to use Set.preimage in the definitions above?

end Definition

theorem qset_lb : q ∈ Quantile P X α → ℙ[X ≤ᵣ q // P ] ≥ α := by simp_all [Quantile, IsQuantile]

theorem qset_ub : q ∈ Quantile P X α → ℙ[X ≥ᵣ q // P] ≥ 1 - α := by simp_all [Quantile, IsQuantile]

theorem qset_def : q ∈ Quantile P X α ↔ ℙ[X ≤ᵣ q // P ] ≥ α ∧ ℙ[X ≥ᵣ q // P] ≥ 1 - α := by simp_all [Quantile, IsQuantile]

theorem qset_not_def : q ∉ Quantile P X α ↔ ℙ[ X ≤ᵣ q // P ] < α ∨ ℙ[ X ≥ᵣ q // P] < 1 - α := by
    constructor; repeat intro h2; grind [qset_def]

theorem qsetlower_def : q ∈ QuantileLower P X α ↔ ℙ[X ≥ᵣ q // P] ≥ 1 - α := by simp_all [QuantileLower, IsQuantileLower]

theorem qsetlower_def_lt : q ∈ QuantileLower P X α ↔ ℙ[X <ᵣ q // P] ≤ α :=
    by constructor
       · intro h; have := qsetlower_def.mp h; rw [prob_lt_of_ge]; linarith
       · intro h; rw [prob_lt_of_ge] at h;
         suffices  ℙ[X≥ᵣq // P] ≥ 1-α from this
         linarith

theorem qset_ub_lt : q ∈ Quantile P X α → ℙ[ X <ᵣ q // P] ≤ α :=
  by intro h
     have := qset_ub h
     rewrite [prob_ge_of_lt] at this
     linarith

theorem qset_of_cond : ℙ[ X ≤ᵣ q // P ] ≥ α ∧ ℙ[ X ≥ᵣ q // P] ≥ 1 - α → q ∈ Quantile P X α :=
    by intro h; simp_all [Quantile, IsQuantile]

theorem qset_of_cond_lt : ℙ[X ≤ᵣ q // P] ≥ α ∧ ℙ[ X <ᵣ q // P] ≤ α → q ∈ Quantile P X α :=
    by intro h1
       have h2 : ℙ[ X ≥ᵣ q // P] ≥ 1 - α := by rw [prob_ge_of_lt]; linarith
       exact qset_of_cond ⟨h1.1, h2⟩

theorem qsetlower_of_cond : ℙ[X ≤ᵣ q // P] ≥ α ∧ ℙ[ X ≥ᵣ q // P] ≥ 1 - α → q ∈ QuantileLower P X α :=
    by intro h; simp_all [QuantileLower, IsQuantileLower]

theorem qsetlower_of_cond_lt : ℙ[ X ≤ᵣ q // P ] ≥ α ∧ ℙ[ X <ᵣ q // P] ≤ α → q ∈ QuantileLower P X α :=
    by intro h1
       have h2 : ℙ[ X ≥ᵣ q // P] ≥ 1 - α := by rw [prob_ge_of_lt]; linarith
       exact qsetlower_of_cond ⟨h1.1, h2⟩


theorem quantile_implies_quantilelower : IsQuantile P X α v → IsQuantileLower P X α v :=
    by simp[IsQuantile, IsQuantileLower]

theorem quantile_subset_quantilelower : Quantile P X α ⊆ QuantileLower P X α := fun _ => quantile_implies_quantilelower

theorem quantile_le_monotone : X ≤ Y → IsCofinalFor (QuantileLower P X α) (IsQuantileLower P Y α) := by
  intro hle q₁ hvar₁
  have hq₁ := le_refl q₁
  exact ⟨q₁, ⟨le_trans hvar₁ (prob_ge_antitone hle hq₁), hq₁⟩⟩


theorem quantilelower_cashinv : q ∈ QuantileLower P X α ↔ (q+c) ∈ QuantileLower P (X+c•1) α := by
  constructor
  · intro h; rw [qsetlower_def, prob_ge_cashinvar c] at h; exact h
  · intro h; rw [qsetlower_def, prob_ge_cashinvar c]; exact h

/-- Adding a constant to a random variable shifts the quantile -/
theorem quantilelower_cash_image : QuantileLower P (X+c•1) α = (fun x ↦ x+c) '' QuantileLower P X α := by
  apply Set.eq_of_subset_of_subset
  · unfold Set.image
    intro qc hqc
    use qc-c
    constructor
    · generalize hqcq : qc - c = q
      rw [quantilelower_cashinv (c:=c)]
      have hqcq2 : qc = q + c := by rw[←hqcq]; ring
      rw [hqcq2] at hqc
      exact hqc
    · simp
  · unfold Set.image
    intro q hq
    obtain ⟨a, ha⟩ := hq
    rw [quantilelower_cashinv (c:=c)] at ha
    rw [←ha.2]
    exact ha.1

end Statistic  

