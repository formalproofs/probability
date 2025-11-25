import Probability.Probability.Prelude

import Mathlib.Data.Matrix.Mul  -- dot product definitions and results
import Mathlib.Algebra.Notation.Pi.Defs -- operations on functions
import Mathlib.Algebra.Module.PointwisePi -- for smul_pi
import Mathlib.LinearAlgebra.Matrix.DotProduct -- for monotonicity

--------------------------- Findist ---------------------------------------------------------------

section Findist

variable {n : ℕ}

structure Findist (n : ℕ) : Type where
    p : Fin n → ℚ
    prob : 1 ⬝ᵥ p = 1
    nneg : 0 ≤ p

namespace Findist

abbrev Delta : ℕ → Type := Findist
abbrev Δ : ℕ → Type := Delta


def singleton : Findist 1 :=
    {p    := ![1],
     prob := by simp [Matrix.vecHead],
     nneg := by simp [Pi.zero_def, Pi.le_def] }


@[simp]
def length (_ : Findist n) := n

variable {n : ℕ}

theorem nonempty (P : Findist n) : P.length > 0 :=
  by cases n
     · have := P.prob; simp_all only [Matrix.dotProduct_of_isEmpty, zero_ne_one]
     · simp only [length, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]


end Findist

--#synth (OfNat (ℕ → ℕ) 1)
--#check One.toOfNat1
--#synth One (ℕ → ℕ)
--#check Pi.instOne
end Findist

--------------------------- Random Variable -------------------------------------------------------------------

/-!
Random variables are defined as function. The operations on random variables can be performed
using the standard notation:

- X + Y is elementwise addition
- X * Y is elementwise product (Hadamard product)
- f ∘ X is composition
- c • X is scalar multiplication


- L =ᵣ i is a boolean indicator random variable
- L =ᵢ i is a ℚ indicator random variable
- L ≤ᵣ i is a bool indicator random variable

Main results

- Hadamard product is linear:  Y * (∑ i, Xs i) = ∑ i, Y * (Xs i)
-/


section RandomVariable

/-- A finite random variable  -/
abbrev FinRV (n : ℕ) (ρ : Type) := Fin n → ρ

/- construct a random variable -/
-- def rvOf {n : ℕ} {ρ : Type} (f : Fin n → ρ) := f

variable {n : ℕ} {ρ : Type}

namespace FinRV

-- for convenience define operations on bools
instance instBoolMul : Mul Bool where mul a b := Bool.and a b
instance instBoolAdd: Add Bool  where add a b := Bool.or a b
instance instBoolZero : Zero Bool where zero := false
instance instBoolOne : One Bool where one := true

@[simp] lemma bool_mul_tt : (true * true : Bool) = true := rfl
@[simp] lemma bool_mul_tf : (true * false : Bool) = false := rfl
@[simp] lemma bool_mul_ft : (false * true : Bool) = false := rfl
@[simp] lemma bool_mul_ff : (false * false : Bool) = false := rfl


variable {A B : Bool}

@[simp]
theorem one_eq_true : (1:Bool) = true := rfl
@[simp]
theorem zero_eq_false : (0:Bool) = false := rfl

@[simp]
theorem bool_sum_or : A + B = Bool.or A B := rfl

theorem bool_prod_and : A * B = Bool.and A B := rfl

-- #synth Add (Fin n → ℚ)
-- #check Pi.instAdd

@[simp]
def not (B : FinRV n Bool) : FinRV n Bool :=
  fun ω ↦ (B ω).not

prefix:40 "¬ᵣ" => FinRV.not

@[simp]
def eq [DecidableEq ρ] (Y : FinRV n ρ) (y : ρ) : FinRV n Bool :=
  (fun ω ↦ decide (Y ω = y) )

infix:50 "=ᵣ" => FinRV.eq

/-- indicator version of equality -/
@[simp]
def eqi [DecidableEq ρ] (Y : FinRV n ρ) (y : ρ) : FinRV n ℚ :=
  (fun ω ↦ if Y ω = y then 1 else 0)

infix:50 "=ᵢ" => FinRV.eqi

@[simp]
def leq [LE ρ] [DecidableLE ρ] (Y : FinRV n ρ) (y : ρ) : FinRV n Bool :=
  (fun ω ↦ Y ω ≤ y)

infix:50 "≤ᵣ" => FinRV.leq

@[simp]
def gt [LT ρ] [DecidableLT ρ] (Y : FinRV n ρ) (y : ρ) : FinRV n Bool :=
  fun ω ↦ Y ω > y

infix:50 ">ᵣ" => FinRV.gt

example (m n : ℕ) : (m < n) ∨ (m = n) ∨ (m > n) :=  Nat.lt_trichotomy m n

/-- Shows equivalence when extending the random variable to another element. -/
theorem le_of_le_eq (D : FinRV n ℕ) (m : ℕ) : ((D ≤ᵣ m) + (D =ᵣ m.succ)) = (D ≤ᵣ m.succ) := by
  funext x --extensionality principle for functions
  unfold FinRV.leq FinRV.eq instHAdd Add.add Pi.instAdd
  simp [instBoolAdd]
  have := Nat.lt_trichotomy (D x) (m+1)
  grind

/-- Defines a preimage of an RV. This is a set with a decidable membership. -/
def preimage (f : FinRV n ρ) : ρ → Set (Fin n) :=
  fun t => { m : Fin n | f m  = t}

end FinRV

/-- Boolean indicator function -/
def indicator  [OfNat ρ 0] [OfNat ρ 1] (cond : Bool) : ρ := cond.rec 0 1

abbrev 𝕀 [OfNat ρ 0] [OfNat ρ 1] : Bool → ρ := indicator

-- TODO: add the equivalence between 𝕀 ∘ (L =ᵣ i) and L =ᵢ i

variable {k : ℕ} {L : FinRV n (Fin k)}

theorem indi_eq_indr : ∀i : Fin k, (𝕀 ∘ (L =ᵣ i)) = (L =ᵢ i) := by
  intro i
  unfold FinRV.eq FinRV.eqi 𝕀 indicator
  ext ω
  by_cases h: L ω = i
  · simp [h]
  · simp [h]


variable {B : FinRV n Bool}
/-- Indicator is 0 or 1 -/
theorem ind_zero_one  :  ∀ ω, (𝕀∘B) ω = 1 ∨ (𝕀∘B) ω = 0 := by
    intro ω
    by_cases h : B ω
    · left; simp only [Function.comp_apply, h, indicator]
    · right; simp only [Function.comp_apply, h, indicator]

/-- Indicator is 0 or 1 -/
theorem ind_nneg : (0 : FinRV n ℚ) ≤ 𝕀∘B := by
    intro ω
    simp [𝕀, indicator]
    by_cases h : B ω
    · simp [h]
    · simp [h]

theorem ind_le_one : 𝕀∘B ≤ (1 : FinRV n ℚ) :=
    by unfold 𝕀 indicator
       intro ω
       by_cases h : B ω
       · simp [h]
       · simp [h]

theorem one_of_true : 𝕀 ∘ (1 : Fin n → Bool) = (1 : Fin n → ℚ) := by ext; simp [𝕀, indicator]

theorem one_of_bool_or_not : B + (¬ᵣ B) = (1 : FinRV n Bool) := by ext ω; unfold FinRV.not; simp

theorem one_of_ind_bool_or_not : (𝕀∘B) + (𝕀∘(¬ᵣ B)) = (1 : FinRV n ℚ) :=
    by ext ω
       unfold FinRV.not 𝕀 indicator not
       by_cases h : B ω
       · simp [h]
       · simp [h]

variable {X Y: FinRV n ℚ}

theorem rv_le_abs : X ≤ abs ∘ X := by intro i; simp [le_abs_self (X i)]

theorem rv_prod_sum_linear {Xs : Fin k → FinRV n ℚ} : ∑ i, Y * (Xs i) = Y * (∑ i, Xs i) :=
    by ext ω
       simp
       rw [Finset.mul_sum]

end RandomVariable

------------------------------ Probability ---------------------------


variable {n : ℕ} (P : Findist n) (B C : FinRV n Bool)

/-- Probability of B -/
def probability : ℚ :=  P.p ⬝ᵥ (𝕀 ∘ B)

notation "ℙ[" B "//" P "]" => probability P B

-- helps to refold is when needed
lemma probability_def : P.p ⬝ᵥ (𝕀 ∘ B) = ℙ[B // P] := rfl

-- TODO: the sorry in the definition has to do with the decidability of the membership
--theorem prob_iprod_eq_def : ℙ[B // P] = P.measure (B.preimage true) sorry := sorry

/-- Conditional probability of B -/
def probability_cnd : ℚ := ℙ[B * C // P] / ℙ[ C // P ]


---- conditional probability
notation "ℙ[" B "|" C "//" P "]" => probability_cnd P B C


theorem prob_one_of_true : ℙ[1 // P] = 1 :=
    by unfold probability
       rw[one_of_true]
       rw [dotProduct_comm]
       exact P.prob

example {a b : ℚ} (h : 0 ≤ a) (h2 : 0 ≤ b) : 0 ≤ a * b :=  Rat.mul_nonneg h h2

variable {P : Findist n} {B : FinRV n Bool}

theorem prod_zero_of_prob_zero : ℙ[B // P] = 0 → (P.p * (𝕀∘B) = 0) := by
    intro h; exact prod_eq_zero_of_nneg_dp_zero P.nneg ind_nneg h


------------------------------ PMF ---------------------------

/-- Proof that p is a the PMF of X on probability space P -/
def PMF {K : ℕ} (pmf : Fin K → ℚ) (P : Findist n) (L : FinRV n (Fin K)) :=
    ∀ k : Fin K, pmf k = ℙ[ L =ᵣ k // P]

namespace PMF


end PMF

------------------------------ Expectation ----------------------

namespace Ex


variable {n : ℕ} (P : Findist n) (X Y Z: FinRV n ℚ) (B : FinRV n Bool)

def expect : ℚ := P.p ⬝ᵥ X

notation "𝔼[" X "//" P "]" => expect P X

-- expectation for a joint probability space and random variable
notation "𝔼[" PX "]" => expect PX.1 PX.2

--theorem exp_eq_correct : 𝔼[X // P] = ∑ v ∈ ((List.finRange P.length).map X).toFinset, v * ℙ[ X =ᵣ v // P]

@[simp]
theorem prob_eq_exp_ind : ℙ[B // P] = 𝔼[𝕀 ∘ B // P] :=
    by simp only [expect, probability]


/-- Conditional expectation -/
def expect_cnd : ℚ := 𝔼[ X * (𝕀 ∘ B) // P] / ℙ[ B // P]

notation "𝔼[" X "|" B "//" P "]" => expect_cnd P X B

-- expectation for a joint probability space and random variable
notation "𝔼[" PX "|" B "]" => expect_cnd PX.1 PX.2 B

variable {k : ℕ} (L : FinRV n (Fin k))

-- creates a random variable
def expect_cnd_rv : Fin n → ℚ := fun i ↦ 𝔼[ X | L =ᵣ (L i) // P ]

notation "𝔼[" X "|ᵣ" L "//" P "]" => expect_cnd_rv P X L

end Ex
--- some basic properties

section Expectation_properties
variable {P : Findist n} {X Y Z: FinRV n ℚ} {B : FinRV n Bool}

theorem exp_congr : (X = Y) → 𝔼[X // P] = 𝔼[Y // P] :=
  by intro h
     unfold Ex.expect dotProduct
     apply Fintype.sum_congr
     simp_all

theorem exp_dists_add : 𝔼[X + Y // P] = 𝔼[X // P] + 𝔼[Y // P] := by simp [Ex.expect]

theorem exp_mul_comm : 𝔼[X * Y // P] = 𝔼[Y * X // P] := by unfold Ex.expect; exact dotProd_hadProd_comm

variable {c : ℚ} {p : Fin n → ℚ}

theorem const_fun_to_one : (fun _ ↦ c : FinRV n ℚ)  = c • 1 := by ext; simp;

theorem exp_const : 𝔼[(fun _ ↦ c) // P] = c :=
    by unfold Ex.expect
       rw [const_fun_to_one]
       simp only [dotProduct_smul, smul_eq_mul]
       rw [dotProduct_comm, P.prob]
       simp

theorem exp_one : 𝔼[ 1 // P] = 1 :=
    by calc 𝔼[ 1 // P] = 𝔼[ (fun _ ↦ 1) // P] := rfl
       _ = 1 := exp_const

theorem exp_prod_const : 𝔼[c • X // P] = c * 𝔼[X // P] := by simp only [Ex.expect, dotProduct_smul, smul_eq_mul]

lemma constant_mul_eq_smul : (fun ω ↦ c * X ω) = c • X := rfl

theorem exp_prod_const_fun : 𝔼[(λ _ ↦ c) * X // P] = c * 𝔼[X // P] :=
  by simp only [Ex.expect, Pi.mul_def, constant_mul_eq_smul, dotProduct_smul, smul_eq_mul]

theorem exp_indi_eq_exp_indr : ∀i : Fin k, 𝔼[L =ᵢ i // P] = 𝔼[𝕀 ∘ (L =ᵣ i) // P] := by
  intro i
  rw [indi_eq_indr]

theorem exp_monotone (h: X ≤ Y)  : 𝔼[X // P] ≤ 𝔼[Y // P] :=  dotProduct_le_dotProduct_of_nonneg_left h P.nneg

end Expectation_properties
