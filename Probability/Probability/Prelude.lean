import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Tactic

import Mathlib.Logic.Function.Defs

/-- states that p is a valid probability value -/
@[simp]
abbrev Prob (p : ℚ) : Prop := 0 ≤ p ∧ p ≤ 1


----------------- Section: Basic Probability -----------------------------------------------

namespace Prob

variable {p x y : ℚ} 

@[simp]
theorem of_complement ( hp : Prob p) : Prob (1-p) := by
        simp_all only [ Prob, sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right, and_self]

@[simp]
theorem complement_inv_nneg (hp : Prob p) : 0 ≤ (1-p)⁻¹ := by 
        simp_all only [Prob, inv_nonneg, sub_nonneg]

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

------------------- Section: List operations -----------------------------------------------


namespace List

variable {L : List ℚ} {c : ℚ}

def scale (L : List ℚ) (c : ℚ) : List ℚ := (L.map fun x↦x*c)

@[simp]
theorem scale_sum : (L.scale c).sum = c * L.sum :=
  by induction L
     · simp [scale]
     · simp_all [scale]
       ring

@[simp]
theorem scale_length : (L.scale c).length = L.length := by simp [scale]

theorem scale_nneg_of_nneg (h : ∀l ∈ L, 0 ≤ l) (h1 : 0 ≤ c) : (∀l ∈ L.scale c, 0 ≤ l) :=
  by induction L
     · simp [List.scale]
     · simp_all [List.scale]
       exact Left.mul_nonneg h.1 h1

theorem append_nneg_of_nneg (h : ∀l ∈ L, 0 ≤ l) (h1 : 0 ≤ p) : (∀l ∈ p::L, 0 ≤ l) :=
  by aesop

/-- adds a new probability to a list and renormalizes the rest --/
def grow (L : List ℚ) (p : ℚ) : List ℚ := p :: (L.scale (1-p))

theorem grow_sum : (L.grow p).sum = L.sum * (1-p) + p :=
  by induction L
     · simp [List.grow, List.scale]
     · simp [List.grow, List.scale_sum]
       ring


/-- Removes head and rescales -/
def shrink : List ℚ → List ℚ
    | nil => nil
    | head :: tail => tail.scale (1-head)⁻¹


@[simp]
theorem shrink_length : L.shrink.length = L.tail.length :=
  by cases L; simp [List.shrink]; simp[List.shrink, List.scale]

theorem shrink_length_less_one : L.shrink.length = L.length - 1 :=
    by simp only [shrink_length, length_tail]


@[simp]
theorem shrink_sum (npt: L ≠ []) (h : L.head npt < 1) :
        (L.shrink).sum = (L.tail).sum / (1 - L.head npt)  :=
        by cases L; contradiction; simp_all [List.shrink, List.scale_sum]; ring

theorem shrink_ge0 (h1 : ∀l ∈ L, Prob l) : ∀l ∈ (L.shrink), 0 ≤ l :=
    by simp [List.shrink]
       cases L with
       | nil => simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
       | cons head tail =>
           simp_all only [List.mem_cons, Prob, forall_eq_or_imp]
           have hh : 0 ≤ (1-head)⁻¹ := Prob.complement_inv_nneg h1.1
           exact List.scale_nneg_of_nneg (L:=tail) (c:=(1-head)⁻¹) (fun l a ↦ (h1.2 l a).1) hh


/-- Used to define a probability of a random variable -/
def iprodb (ℙ : List ℚ) (B : ℕ → Bool) : ℚ :=
    match ℙ with
    | [] => 0
    | head :: tail =>  (B tail.length).rec 0 head + tail.iprodb B


/-- Used to define an expectation of a random variable -/
def iprod (ℙ : List ℚ) (X : ℕ → ℚ) : ℚ :=
    match ℙ with
    | [] => 0
    | head :: tail =>  head * (X tail.length) + tail.iprod X


variable (B : ℕ → Bool)

theorem scale_innerprod  (x : ℚ) : (L.scale x).iprodb B = x * (L.iprodb B) :=
  by induction L with
     | nil => simp_all [List.scale, List.iprodb]
     | cons head tail =>
            simp_all [List.iprodb, List.scale]
            cases B tail.length
            · simp_all
            · simp_all
              ring

theorem decompose_supp (h : L ≠ []) (ne1 : L.head h ≠ 1):
    L.iprodb B = (B (L.length - 1)).rec 0 (L.head h) + (1-L.head h) * (L.shrink.iprodb B)  :=
    by conv => lhs; unfold iprodb
       cases L with
       | nil => simp at h
       | cons head tail =>
        simp [List.shrink]
        have := tail.scale_innerprod B (1-head)⁻¹
        simp_all
        have hnz : 1 - head ≠ 0 :=
          by by_contra; have : head = 1 := by linarith;
             contradiction
        calc
          tail.iprodb B = 1 * tail.iprodb B := by ring
          _ = (1 - head) * (1 - head)⁻¹ * tail.iprodb B  :=
              by rw [Rat.mul_inv_cancel (1-head) hnz]
          _ = (1 - head) * ((1 - head)⁻¹ * tail.iprodb B ) := by ring

theorem iprod_eq_zero_of_zeros (hz : ∀ p ∈ L, p = 0) : L.iprodb B = 0 :=
  by induction L with
     | nil => simp [iprodb]
     | cons head tail => simp_all [iprodb]; cases B tail.length; simp; simp

-- if all but head are zero, then the inner product is the just the value of head
theorem iprod_first_of_tail_zero  (hn : L ≠ []) (hz : ∀ p ∈ L.tail, p = 0) :
   L.iprodb B = (B L.tail.length).rec 0 (L.head hn)  :=
   by unfold iprodb
      cases L with
        | nil =>  contradiction
        | cons head tail =>
          simp; simp at hz; 
          exact iprod_eq_zero_of_zeros B hz

lemma iprodb_true_sum : L.iprodb (fun _ ↦ true) = L.sum :=
    by induction L
       · simp only  [iprodb, sum_nil]
       · simp_all only [iprodb, sum_cons]




end List


------------------------------ Section LSimplex --------------------------------------------


/-- Self-normalizing list of probabilities  --/
structure LSimplex (L : List ℚ) : Prop where
  nneg : ∀p ∈ L, 0 ≤ p               -- separate for convenience
  normalized : L.sum = 1             -- sums to 1

namespace LSimplex

def singleton : LSimplex [1] :=
  ⟨fun p a => by simp_all only [List.mem_cons, List.not_mem_nil, or_false, zero_le_one],
    List.sum_singleton⟩

variable {p : ℚ} {L : List ℚ}  {c : ℚ}
variable (S : LSimplex L)

/-- cannot define a simplex on an empty set. -/
@[simp]
theorem nonempty (S : LSimplex L) : L ≠ [] :=
        fun a => by have := S.normalized; simp_all

@[simp]
abbrev npt : LSimplex L → L ≠ [] := LSimplex.nonempty

def phead (h : LSimplex L) : ℚ := L.head h.nonempty

/-- all probability in the head element -/
def degenerate (S : LSimplex L) : Bool := S.phead  == 1

@[reducible]
def supported  : Bool := ¬S.degenerate

@[simp]
theorem mem_prob (S : LSimplex L) : ∀ p ∈ L, Prob p :=
  fun p a => ⟨ S.nneg p a,
               S.normalized ▸ List.single_le_sum S.nneg p a⟩

theorem phead_inpr  : S.phead ∈ L := List.head_mem S.nonempty

@[simp]
theorem phead_prob  : Prob S.phead := S.mem_prob S.phead S.phead_inpr

theorem phead_supp  (supp : S.supported) : S.phead  < 1 :=
  by simp [degenerate] at supp
     exact lt_of_le_of_ne S.phead_prob.2 supp

theorem supported_head_lt_one  (supp : S.supported) : L.head S.npt < 1 :=
    by have prob := LSimplex.mem_prob S (L.head S.npt) (List.head_mem (LSimplex.npt S))
       simp [LSimplex.degenerate] at supp
       simp [Prob] at prob
       exact lt_of_le_of_ne prob.2 supp

@[simp]
theorem List.grow_ge0 (h1 : ∀l ∈ L, 0 ≤ l) (h2 : Prob p) :  ∀ l ∈ (L.grow p), 0 ≤ l :=
    by simp [List.grow]
       constructor
       · exact h2.1
       · intro l a
         exact List.scale_nneg_of_nneg
               (L := L) (c := (1-p)) h1 (Prob.of_complement h2).1 l a

-- grows the simplex to also incude the probability p
@[simp]
theorem grow (S : LSimplex L) {p : ℚ} (prob : Prob p) : LSimplex (L.grow p) :=
  {nneg := List.grow_ge0 S.nneg prob,
   normalized := by simp [List.grow_sum, S.normalized]}

lemma false_of_p_comp1_zero_p_less_one (h1 : 1 - p = 0) (h2 : p < 1) : False := by linarith

@[simp]
theorem tail_sum (S : LSimplex L) : L.tail.sum = (1 - L.head S.npt) :=
  by cases L; have := S.npt; contradiction; have := S.normalized; simp at this ⊢; linarith

theorem degenerate_tail_zero (degen : S.degenerate) : ∀ p ∈ L.tail, p = 0 :=
  by simp [LSimplex.degenerate, LSimplex.phead] at degen
     have ts := S.tail_sum
     rw [degen] at ts; simp at ts
     have nneg := fun p a ↦ S.nneg p (List.mem_of_mem_tail a)
     have lez := fun p a ↦ List.single_le_sum nneg p a
     rw [ts] at lez
     intro p a
     have hl := nneg p a
     have hu := lez p a
     linarith

theorem shrink (S : LSimplex L) (supp : S.supported) : LSimplex (L.shrink) :=
  {nneg := List.shrink_ge0 (LSimplex.mem_prob S),
   normalized :=
     by have npt := S.npt
        have hh := LSimplex.supported_head_lt_one S supp
        have hh1 := S.tail_sum
        have hh2 : (1 - L.head npt) ≠ 0 := by linarith
        rw[List.shrink_sum S.npt hh]
        exact (div_eq_one_iff_eq hh2).mpr hh1}

theorem grow_of_shrink_list (supp : S.supported) : L = (L.shrink).grow (S.phead) :=
   by induction L with
      | nil => have := S.nonempty; contradiction
      | cons head tail =>
             let h : (1-head) ≠ 0 :=
               fun a => false_of_p_comp1_zero_p_less_one a (S.phead_supp supp)
             simp_all [List.grow, List.shrink, List.scale, LSimplex.phead]

-- all props of the same type are equal
theorem grow_of_shrink (supp : S.supported) :
        S = (S.grow_of_shrink_list supp) ▸ (S.shrink supp).grow S.phead_prob := rfl

end LSimplex
