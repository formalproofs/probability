import Probability.Prob
--import Mathlib.Tactic.Explode
-- Adding a comment

section List
namespace List

variable {L : List ℚ}

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

end List
end List
