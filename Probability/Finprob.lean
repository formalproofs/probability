import Probability.Findist

/-- Finite probability space. See Finsample for the definition of the sample space. -/
structure Finprob : Type where
  ℙ : List ℚ
  prob : LSimplex ℙ


lemma List.unique_head_notin_tail (L : List τ) (ne : L ≠ []) (nodup : L.Nodup) :
      L.head ne ∉ L.tail :=
  by induction L
     · simp at ne
     · simp [List.head, List.tail]
       simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.nodup_cons]

namespace Finprob

variable (P : Finprob)

@[simp]
def length := P.ℙ.length


def singleton : Finprob :=
   ⟨ [1], LSimplex.singleton ⟩

def grow {p : ℚ} (prob : Prob p) : Finprob :=
  ⟨P.ℙ.grow p, P.prob.grow prob⟩

/-- all probability in the head -/
abbrev degenerate  : Bool := P.prob.degenerate
abbrev supported  : Bool := P.prob.supported

theorem not_degen_supp (supp : ¬P.degenerate) : P.supported :=
  by simp_all [Finprob.degenerate, Finprob.supported]

theorem degen_of_not_supp (notsupp : ¬P.supported) : P.degenerate :=
  by simp_all [Finprob.degenerate, Finprob.supported]

def shrink (supp : P.supported) : Finprob :=
  {ℙ := P.ℙ.shrink, prob := P.prob.shrink supp}


-- Define an induction principle for probability spaces
-- similar to the induction on lists, but also must argue about probability distributions

theorem nonempty : ¬P.ℙ.isEmpty :=
  by intro a;
     simp_all only [LSimplex.nonempty P.prob, List.isEmpty_iff]

--TODO: try to shorten/simplify the theorem below
theorem length_gt_zero : P.length ≥ 1 :=
  by
    simp [Finprob.length]
    have hne : P.ℙ ≠ [] := by
      intro hnil
      have : P.ℙ.isEmpty = true := by simp [List.isEmpty, hnil]
      exact P.nonempty this
    exact Nat.succ_le_of_lt (List.length_pos_iff.mpr hne)

theorem shrink_length (supp : P.supported) : (P.shrink supp).length = P.length - 1 :=
    by  have h := Finprob.nonempty P
        simp [List.isEmpty] at h
        simp! [Finprob.shrink, Finprob.length, List.shrink, LSimplex.shrink]

theorem shrink_length_lt (supp : P.supported) : (P.shrink supp).length < P.length :=
    by rw [Finprob.shrink_length P supp]
       exact Nat.sub_one_lt_of_lt (Finprob.length_gt_zero P)

theorem nonempty_P : P.ℙ ≠ [] := P.prob.nonempty

@[simp]
def phead := P.ℙ.head P.nonempty_P

@[simp]
def ωhead := P.length - 1

theorem phead_inpr : P.phead ∈ P.ℙ := List.head_mem P.nonempty_P

theorem phead_prob : Prob P.phead :=
  P.prob.mem_prob P.phead P.phead_inpr

theorem phead_supp_ne_one (supp : P.supported) : P.phead ≠ 1 :=
        by simp [Finprob.supported, LSimplex.supported, LSimplex.degenerate, LSimplex.phead] at supp
           simp [Finprob.phead]
           exact supp

theorem len_ge_one : P.length ≥ 1 :=
  by simp [Finprob.length]
     have h := P.prob.nonempty
     have : P.ℙ.length ≠ 0 := by simp_all only [ne_eq, List.length_eq_zero_iff, not_false_eq_true]
     exact Nat.one_le_iff_ne_zero.mpr this


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
