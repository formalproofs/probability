/-
The file defines concepts that we need to define induction for probability spaces
-/

import Probability.Probability.Defs

open Findist

namespace Findist

variable {N : ℕ} (F : Findist N)

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

-- Info: For the use of ▸ see: https://proofassistants.stackexchange.com/questions/1380/how-do-i-convince-the-lean-4-type-checker-that-addition-is-commutative
end Findist 


namespace Finprob

variable (P : Finprob)


def shrink (supp : P.supported) : Finprob :=
  {ℙ := P.ℙ.shrink, prob := P.prob.shrink supp}

theorem shrink_length (supp : P.supported) : (P.shrink supp).length = P.length - 1 :=
    by  have h := Finprob.nonempty P
        simp [List.isEmpty] at h
        simp! [Finprob.shrink, Finprob.length, List.shrink, LSimplex.shrink]

theorem shrink_length_lt (supp : P.supported) : (P.shrink supp).length < P.length :=
    by rw [Finprob.shrink_length P supp]
       exact Nat.sub_one_lt_of_lt (Finprob.length_gt_zero P)

theorem shrink_shorter (supp : P.supported) :
                                 (P.shrink supp).length = P.length - 1 :=
        by simp_all only [length, shrink, List.shrink_length, List.length_tail]

/-- Shows that growing an shrink probability will create the same probability space -/
theorem grow_of_shrink (supp : P.supported) : P = (P.shrink supp).grow P.phead_prob :=
    by rw [Finprob.mk.injEq] -- same fields equivalent to same structures
       simp [Finprob.shrink, Finprob.grow]
       apply LSimplex.grow_of_shrink_list
       simp_all only [decide_not, Bool.decide_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
                Bool.false_eq_true, decide_false, Bool.not_false]
       exact P.prob


/-- induction principle for finite probabilities. Works as "induction P" -/
@[induction_eliminator]
def induction {motive : Finprob → Prop}
        (degenerate :  {fp : Finprob} → (d : fp.degenerate) → motive fp)
        (composite : (tail : Finprob) →  {p : ℚ} → (inP : Prob p) →
                     (motive tail) → motive (tail.grow inP))
        (P : Finprob) : motive P :=
    if b1 : P.ℙ = [] then
      by have := LSimplex.nonempty P.prob; simp_all
    else
      if b2 : P.degenerate then
        degenerate b2
      else
        let indhyp := Finprob.induction  degenerate composite (P.shrink (P.not_degen_supp b2))
        (Finprob.grow_of_shrink P (P.not_degen_supp b2)) ▸
          composite (P.shrink (P.not_degen_supp b2)) P.phead_prob indhyp
    termination_by P.length
    decreasing_by
      simp only [length, shrink, gt_iff_lt]
      exact Finprob.shrink_length_lt P (P.not_degen_supp b2)

end Finprob
