import Probability.List

section LSimplex

variable {p : ℚ}

/-- Self-normalizing list of probabilities  --/
structure LSimplex (L : List ℚ) : Prop where
  nneg : ∀p ∈ L, 0 ≤ p               -- separate for convenience
  normalized : L.sum = 1             -- sums to 1

namespace LSimplex

def singleton : LSimplex [1] :=
  ⟨fun p a => by simp_all only [List.mem_cons, List.not_mem_nil, or_false, zero_le_one],
    List.sum_singleton⟩

variable {L : List ℚ}  {c : ℚ}
variable (S : LSimplex L)

/-- cannot define a simplex on an empty set -/
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
end LSimplex
