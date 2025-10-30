import Probability.LSimplex

/-- Finite probability distribution on a set-like list (non-duplicates) -/
structure Findist (N : ℕ)  : Type where
  ℙ : List ℚ                      -- probabilities
  simplex : LSimplex ℙ            -- proof of a measure
  lmatch : ℙ.length = N           -- correct length of probability

namespace Findist

abbrev Delta : ℕ → Type := Findist
abbrev Δ : ℕ → Type := Delta

variable {N : ℕ} (F : Findist N)

abbrev degenerate : Bool := F.simplex.degenerate
abbrev supported : Bool := F.simplex.supported

theorem supp_not_degen (supp : F.supported) : ¬ F.degenerate :=
        by simp_all [supported, degenerate]

@[simp]
theorem nonempty (F : Findist N) : N ≥ 1 :=
  F.lmatch ▸ List.length_pos_iff.mpr F.simplex.npt

@[simp]
theorem nonempty_P : F.ℙ ≠ [] :=
  by have := F.simplex.npt
     intro a; contradiction


/-- add a new head -/
def grow {p : ℚ} (prob : Prob p) : Findist (N + 1)  :=
    {ℙ       := F.ℙ.grow p,
     simplex := F.simplex.grow prob,
     lmatch  := by simp [List.grow, List.scale_length, F.lmatch]}

/-- if nondegenenrate then construct a tail distribution -/
def shrink  (supp : F.supported) : Findist (N - 1)  :=
    -- see: https://lean-lang.org/theorem_proving_in_lean4/The-Conversion-Tactic-Mode/
    let hh :  F.ℙ.shrink.length = N - 1 :=
      calc
        F.ℙ.shrink.length = F.ℙ.length - 1 := List.shrink_length_less_one
        _ = N - 1 := by conv => lhs; rw [F.lmatch]
    {ℙ := F.ℙ.shrink
     simplex := F.simplex.shrink supp
     lmatch := hh} --List.shrink_length_less_one (Findist.nonempty_P F)}


def singleton : Findist 1 :=
    {ℙ := [1]
     simplex := LSimplex.singleton,
     lmatch := by simp_all only [List.length_cons, List.length_nil, zero_add]}


abbrev phead := F.simplex.phead

--example (a : Prop) (b : Prop) : ¬(a ∧ b) = (¬ a) ∨ (¬b) :=

@[simp]
theorem phead_inpr : F.phead ∈ F.ℙ := List.head_mem F.nonempty_P

@[simp]
theorem phead_prob : Prob F.phead := F.simplex.mem_prob F.phead F.phead_inpr

theorem nondegenerate_head (supp : F.supported) : F.phead < 1 :=
  by have h1 := Findist.phead_prob F
     simp_all only [supported, LSimplex.supported, LSimplex.degenerate,
                    LSimplex.phead, beq_iff_eq, phead, gt_iff_lt]
     simp! only [decide_not, Bool.not_eq_eq_eq_not, not, decide_eq_false_iff_not] at supp
     simp [Prob] at h1
     exact lt_of_le_of_ne h1.2 supp


-- For the use of ▸ see: https://proofassistants.stackexchange.com/questions/1380/how-do-i-convince-the-lean-4-type-checker-that-addition-is-commutative

theorem grow_shrink_type (_ : F.supported) : Findist (N - 1 + 1) = Findist N :=
        (Nat.sub_add_cancel F.nonempty) ▸ rfl

def growshrink (supp : F.supported) : Findist (N-1+1) :=
   (F.shrink supp).grow F.phead_prob

-- TODO: can we incorporate this example in the theorem below?
example (supp : F.supported) : ((F.shrink supp).grow F.phead_prob).ℙ = F.ℙ :=
    by have h1 : F.supported := by simp_all only
       simp [Findist.shrink, Findist.grow, Findist.phead]
       rw [←LSimplex.grow_of_shrink_list F.simplex h1]


theorem grow_of_shrink_2 (supp : F.supported) :
  F.growshrink supp = ((F.grow_shrink_type supp).mpr F) :=
    by have h1 : F.supported := by simp_all only
       simp [Findist.growshrink, Findist.shrink, Findist.grow, Findist.phead]
       rw [Findist.mk.injEq]
       rw [←LSimplex.grow_of_shrink_list F.simplex h1]
       congr; --TODO: here to deal with casts; need to understand them better (see example below)
         symm; exact Nat.sub_add_cancel F.nonempty;
         simp_all only [heq_cast_iff_heq, heq_eq_eq]

end Findist
