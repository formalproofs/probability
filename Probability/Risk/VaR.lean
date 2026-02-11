import Probability.Probability.Basic
import Probability.Probability.Quantile
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Set.Operations


namespace Risk

open Findist FinRV Statistic

variable {n : ℕ}

variable {P : Findist n} {X Y : FinRV n ℚ} {t t₁ t₂ : ℚ}

def IsRiskLevel (α : ℚ) : Prop := 0 ≤ α ∧ α < 1

def RiskLevel := { α : ℚ // IsRiskLevel α}

--instance instCoeRiskUnit : Coe RiskLevel UnitI where
--  coe := fun ⟨v,c⟩ => ⟨v, ⟨c.1, le_of_lt c.2⟩ ⟩


def FinVaR1Set (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) : Finset ℚ :=
  let 𝓧 := Finset.univ.image X
  𝓧.filter (fun t ↦ ℙ[X <ᵣ t // P] ≤ α.val)

theorem FinVar1Set_nonempty (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) : (FinVaR1Set (n := n) P X α).Nonempty :=
  by
    unfold FinVaR1Set
    let 𝓧 := Finset.univ.image X
    apply Finset.filter_nonempty_iff.mpr
    let xmin := (Finset.univ.image X).min' (rv_image_nonempty P X)
    use xmin
    constructor
    · exact Finset.min'_mem 𝓧 (rv_image_nonempty P X)
    · have : ℙ[X <ᵣ xmin // P] = 0 := prob_lt_min_eq_zero
      have := α.2
      unfold IsRiskLevel at this
      linarith

def FinVaR1 (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) : ℚ :=
  let 𝓧 := Finset.univ.image X
  let 𝓢 := 𝓧.filter (fun t ↦ ℙ[X <ᵣ t // P] ≤ α.val)
  have h : 𝓢.Nonempty := FinVar1Set_nonempty P X α
  𝓢.max' h

/- Value-at-Risk of X at level α: VaR_α(X) = min { t ∈ X(Ω) | P[X ≤ t] ≥ α }.
    If we assume 0 ≤ α < 1, then the "else 0" branch is never used. -/

---I redefined it above if we want to pull out the proof tht it is nonempty!

-- def FinVaR1 (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) : ℚ :=
--   let 𝓧 := Finset.univ.image X
--   let 𝓢 := 𝓧.filter (fun t ↦ ℙ[X <ᵣ t // P] ≤ α.val)
--   have h : 𝓢.Nonempty := by
--     apply Finset.filter_nonempty_iff.mpr
--     let xmin := (Finset.univ.image X).min' (rv_image_nonempty P X)
--     use xmin
--     constructor
--     · exact Finset.min'_mem 𝓧 (rv_image_nonempty P X)
--     · have : ℙ[X <ᵣ xmin // P] = 0 := prob_lt_min_eq_zero
--       have := α.2
--       unfold IsRiskLevel at this
--       linarith
--   𝓢.max' h

variable {α : RiskLevel}

theorem var1_prob_lt_var_le_alpha : ℙ[X <ᵣ (FinVaR1 P X α) // P] ≤ α.val := by
    generalize h : (FinVaR1 P X α) = t
    unfold FinVaR1 at h
    extract_lets 𝓧 𝓢 ne𝓢 at h
    have tS : t ∈ 𝓢 := by subst h; exact Finset.max'_mem 𝓢 ne𝓢
    exact (Finset.mem_filter.mp tS).right

theorem var1_prob_le_var_gt_alpha : ℙ[X ≤ᵣ (FinVaR1 P X α) // P] > α.val := by
    generalize h : (FinVaR1 P X α) = t
    unfold FinVaR1 at h
    extract_lets 𝓧 𝓢 ne𝓢 at h
    by_contra! hg
    have tlt : t < (FinRV.max P X) :=
        by by_contra!
           unfold RiskLevel IsRiskLevel at α
           have hh := prob_le_monotone (P := P) (le_refl X) this
           rw [prob_le_eq_one] at hh
           have := α.2.2
           linarith
    obtain ⟨q, hq⟩ := prob_lt_epsi_eq_le_of_lt P X t tlt
    rcases hq with ⟨hqgt, hqp, hqin⟩
    have hqs : q ∈ 𝓢 := by
      apply Finset.mem_filter.mpr
      constructor
      · exact hqin
      · rw [hqp]; exact hg
    have : q ≤ t := by subst h; exact Finset.le_max' 𝓢 q hqs
    linarith

notation "VaR[" X "//" P ", " α "]" => FinVaR1 P X α

variable {n : ℕ} (P : Findist n) (X Y : FinRV n ℚ) (α : RiskLevel) (q v : ℚ)

/-- Value `v` is the Value at Risk at `α` of `X` and probability `P`  -/
def IsVaR : Prop := IsGreatest (Quantile P X α.val) v

/-- A simpler, equivalent definition of Value at Risk  -/
def IsVaR2 : Prop := IsGreatest (QuantileLower P X α.val) v


variable {n : ℕ} {P : Findist n} {X Y : FinRV n ℚ} {α : RiskLevel} {q v q₁ q₂ : ℚ}



theorem var2_prob_cond : IsVaR2 P X α v ↔ (ℙ[X <ᵣ v // P] ≤ α.val ∧ α.val < ℙ[ X ≤ᵣ v // P]) :=
  by constructor
     · intro h
       constructor
       · have h1 : 1 - ℙ[X<ᵣv//P] ≥ 1 - α.val := by simp_all [IsVaR2,IsGreatest,QuantileLower,IsQuantileLower,prob_ge_of_lt]
         linarith
       · by_contra! hc
         obtain ⟨q,hq⟩ := prob_lt_epsi_eq_le P X v
         have h3 : q ∈ QuantileLower P X α.val := by
            rw [←hq.2,prob_lt_of_ge] at hc
            suffices ℙ[X≥ᵣq//P] ≥ 1 - α.val from this
            linarith
         exact false_of_le_gt (h.2 h3) hq.1
     · intro h
       unfold IsVaR2
       constructor
       · exact qsetlower_of_cond_lt ⟨le_of_lt h.2, h.1⟩
       · unfold upperBounds
         by_contra! hc
         simp at hc
         obtain ⟨q, hq⟩ := hc
         have hu : ℙ[X ≤ᵣ v // P] ≤ α.val :=
            calc ℙ[X ≤ᵣ v // P] ≤  ℙ[X <ᵣ q // P] := prob_lt_le_monotone hq.2
                 _ ≤ α.val := qsetlower_def_lt.mp hq.1
         exact false_of_lt_ge h.2 hu

--TODO: should we also show that IsVaR is a singleton? That is, is it unique?

-- This is the main correctness proof
theorem finvar1_correct : IsVaR2 P X α (FinVaR1 P X α) :=
    by rewrite[var2_prob_cond]; exact ⟨var1_prob_lt_var_le_alpha, var1_prob_le_var_gt_alpha⟩

theorem var_is_quantile : IsVaR P X α v → IsQuantile P X α.val v :=
    fun h => by simp_all only [Set.mem_setOf_eq,IsVaR,Quantile,IsGreatest]

theorem var_is_quantilelower : IsVaR P X α v → IsQuantileLower P X α.val v :=
    fun h => by simp_all only [Set.mem_setOf_eq,IsVaR,Quantile,IsGreatest,IsQuantileLower,IsQuantile]

theorem var2_is_quantilelower : IsVaR2 P X α v → IsQuantileLower P X α.val v :=
    fun h => by simp_all only [Set.mem_setOf_eq,IsVaR2,QuantileLower,IsGreatest,Set.mem_setOf_eq]

theorem var2_is_quantile : IsVaR2 P X α v → IsQuantile P X α.val v := by
    intro h
    constructor
    · suffices ℙ[X≤ᵣv//P] > α.val by linarith
      exact (var2_prob_cond.mp h).2
    · exact var2_is_quantilelower h

-- TODO: this should be in Quantile.lean but it depends on VaR
theorem quantile_nonempty : (Quantile P X α.val).Nonempty :=
  Set.nonempty_def.mpr ⟨ VaR[X// P,α], finvar1_correct  |> var2_is_quantile ⟩

theorem isquantilelower_le_isquantile : IsCofinalFor (QuantileLower P X α.val) (Quantile P X α.val) := by
    intro q₁ h
    by_cases h2 : q₁ ∈ Quantile P X α.val
    · exact ⟨q₁, h2, le_refl q₁⟩
    · rewrite [qset_not_def] at h2
      rewrite [qsetlower_def] at h
      cases' h2 with h2l h2r
      · obtain ⟨q₂, hq₂⟩ : (Quantile P X α.val).Nonempty := quantile_nonempty
        use q₂
        constructor
        · exact hq₂
        · by_contra! ine
          exact ge_trans (prob_le_monotone (le_refl X) (le_of_lt ine)) (qset_lb hq₂) |> false_of_lt_ge h2l
      · exfalso; exact false_of_lt_ge h2r h

theorem isquantile_le_isquantilelower : IsCofinalFor (Quantile P X α.val) (QuantileLower P X α.val) :=
    HasSubset.Subset.iscofinalfor quantile_subset_quantilelower

theorem var_eq_var2 : IsVaR P X α v ↔ IsVaR2 P X α v := by
    constructor
    · intro h
      constructor
      · exact var_is_quantilelower h
      · exact (upperBounds_mono_of_isCofinalFor isquantilelower_le_isquantile) h.2
    · intro h
      constructor
      · exact var2_is_quantile h
      · exact (upperBounds_mono_of_isCofinalFor isquantile_le_isquantilelower) h.2

theorem var_prob_cond : IsVaR P X α v ↔ (ℙ[X <ᵣ v // P] ≤ α.val ∧ α.val < ℙ[ X ≤ᵣ v // P]) :=
  by rw[var_eq_var2]; exact var2_prob_cond

----------------------------- Fast VaR computation -------------------------------------------------------

section FasterVaR

theorem tail_monotone (X : Fin (n.succ) → ℚ) (h : Monotone X) : Monotone (Fin.tail X) :=
    by unfold Monotone at h ⊢
       unfold Fin.tail
       intro a b h2
       exact h (Fin.succ_le_succ_iff.mpr h2)

/-- compute a quantile for a (partial) sorted random variable and a partial probability
    used in the induction to eliminate points until we find one that has
    probability greater than α -/
def quantile_srt (n : ℕ) (α : RiskLevel) (p x : Fin n.succ → ℚ)
                 (h1 : Monotone x) (h2 : ∀ω, 0 ≤ p ω) (h3 : α.val < 1 ⬝ᵥ p)
                 (h4 : 0 < 1 ⬝ᵥ p) : Fin n.succ :=
  match n with
  | Nat.zero => 0
  | Nat.succ n' =>
    if h : p 0 ≤ α.val then  -- recursive case: keep going
      let αval':= α.val - p 0
      have bnd_α : IsRiskLevel (α.val - p 0) := by
        unfold IsRiskLevel; subst αval'; specialize h2 0
        constructor
        · grw [←h]; simp
        · grw [←h2]; simpa using α.2.2
      let α' := ⟨αval', bnd_α⟩
      let h1' := (tail_monotone x h1)
      let h2' := (fun ω : Fin n'.succ ↦ h2 ω.succ)
      let h3': αval' < 1 ⬝ᵥ (Fin.tail p) := by
        unfold Fin.tail; subst αval'
        rw [one_dotProduct] at ⊢ h3
        calc α.val - p 0 < ∑ i, p i - p 0 := by linarith
          _  =  (p 0 + ∑ i : Fin n'.succ, p i.succ) - p 0 := by rw [Fin.sum_univ_succ]
          _ = ∑ i : Fin n'.succ, p i.succ := by ring
      let h4' := (lt_of_le_of_lt bnd_α.left h3')
      Fin.succ <| quantile_srt n' α' (Fin.tail p) (Fin.tail x) h1' h2' h3' h4'
    else -- return the value case: p 0 > α
      0

example {p : Fin n.succ → ℚ} : ∑ i ∈ Finset.Icc (0 : Fin n.succ) k, p i = (∑ i ∈ Finset.Ico (0: Fin n.succ) k, p i) + p k
     := sorry

theorem quant_less (n : ℕ) {k : Fin n.succ} (α : RiskLevel) (p x : Fin n.succ → ℚ)
      (h1 : Monotone x) (h2 : ∀ω, 0 ≤ p ω) (h3 : α.val < 1 ⬝ᵥ p)
      (h4 : 0 < 1 ⬝ᵥ p) (h5 : k = quantile_srt n α p x h1 h2 h3 h4) :
      (∑ i ∈ Finset.Ico 0 k, p i ≤ α.val) ∧ ( ∑ i ∈ Finset.Icc 0 k, p i > α.val ) := by
        subst h5
        induction n generalizing α with
        | zero =>
          constructor
          · have h6 : 0 ≤ α.val := α.property.left
            simp [h6]
          · have h7 : (α.val : ℚ) < p 0 := by
              rw [one_dotProduct] at h3
              simpa [Fin.sum_univ_succ] using h3
            simpa [quantile_srt] using h7
        | succ n ih =>
          by_cases h8 : p 0 ≤ α.val
          · unfold quantile_srt
            split_ifs
            · extract_lets αval' _ α' h1' h2' h3' h4'
              set k' := quantile_srt n α' (Fin.tail p) (Fin.tail x) h1' h2' h3' h4'
              specialize ih α' (Fin.tail p) (Fin.tail x) h1' h2' h3' h4'
              simp_all
              constructor
              · have h11 : (Finset.Ico (0:Fin (Nat.succ (Nat.succ n))) (Fin.succ k')) =
                          insert 0 ((Finset.Ico (0:Fin (Nat.succ n)) k').map (Fin.succEmb (n:=n.succ))) :=
                  by
                    ext i
                    simp [Finset.mem_Ico]
                    constructor
                    · intro h12
                      by_cases h13 : i = 0
                      · rw [h13]; simp
                      · simp_all
                        have h15 : 0 < i := by exact (Fin.pos_iff_ne_zero).2 h13
                        have h16 : 1 ≤ i.val := Nat.succ_le_iff.2 (by simpa using h15)
                        exact Fin.le_def.2 h16
                    · intro h12
                      rcases h12 with h0 | h1
                      · subst h0; simp
                      · constructor
                        · have h3 : (i : Nat) < (k' : Nat) := sorry
                          exact Nat.succ_le_of_lt h3

                have h14 : ∑ i ∈ Finset.Ico (0:Fin (Nat.succ n)) k', p i.succ ≤ α'.val := by
                  exact ih.1
                rw [h11]
                simp at h14 ⊢
                sorry
              · sorry
            · contradiction
            --simp [h8]
          · have h9 : p 0 > α.val := lt_of_not_ge h8
            constructor
            · have h0 : 0 ≤ α.val := α.property.left
              simp [quantile_srt, h8, h0]
            · simpa [quantile_srt, h8] using h9


def FinVaR (α : RiskLevel) (P : Findist n) (X : FinRV n ℚ) : ℚ :=
    match n with
    | Nat.zero => 0 -- this case is impossible because n > 0 for Findist
    | Nat.succ n' =>
      let σ := Tuple.sort X
      X <| quantile_srt n' α (P.p ∘ σ) (X ∘ σ)
      (Tuple.monotone_sort X)
      (by intro ω; simpa [Function.comp] using P.nneg (σ ω))
      --h3 : α.val < 1 ⬝ᵥ p
      (by
        have h1 : (1 : Fin (Nat.succ n') → ℚ) ∘ σ ⬝ᵥ P.p ∘ σ = 1 ⬝ᵥ P.p :=
          comp_equiv_dotProduct_comp_equiv (1 : Fin (Nat.succ n') → ℚ) P.p σ
        have h2 : ((1 : Fin (Nat.succ n') → ℚ) ∘ σ) = 1 := by
          funext i
          simp [Function.comp]
        have h3 : (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ P.p := by
          simpa [h2] using h1
        have h4 : (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = 1 := by
          calc
            (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ P.p := h3
            _ = 1 := P.prob
        simpa [h4] using (α.property).right)
      --h4 : 0 < 1 ⬝ᵥ p
      ----this is all the same except for the last line
      ----is there a way to avoid repeating it???
      (by
        have h1 : (1 : Fin (Nat.succ n') → ℚ) ∘ σ ⬝ᵥ P.p ∘ σ = 1 ⬝ᵥ P.p :=
          comp_equiv_dotProduct_comp_equiv (1 : Fin (Nat.succ n') → ℚ) P.p σ
        have h2 : ((1 : Fin (Nat.succ n') → ℚ) ∘ σ) = 1 := by
          funext i
          simp [Function.comp]
        have h3 : (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ P.p := by
          simpa [h2] using h1
        have h4 : (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = 1 := by
          calc
            (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ P.p := h3
            _ = 1 := P.prob
        simp [h4])

end FasterVaR

-------------------- VaR Properties -----------------------------------------------------------------------------


section VaR_properties

variable {P : Findist n} {X Y : FinRV n ℚ} {q q₁ v₁ v₂ c : ℚ} {α : RiskLevel}

theorem var2_monotone : X ≤ Y → IsVaR2 P X α v₁ → IsVaR2 P Y α v₂ → v₁ ≤ v₂ :=
  fun hle hv1 hv2 => upperBounds_mono_of_isCofinalFor (quantile_le_monotone hle) hv2.2 hv1.1

theorem const_monotone_univ : Monotone (fun x ↦ x + c)  := add_left_mono

theorem VaR2_translation_invariant : IsVaR2 P X α v → IsVaR2 P (X+c•1) α (v+c) := by
    intro h
    rw [IsVaR2,quantilelower_cash_image]
    exact MonotoneOn.map_isGreatest (Monotone.monotoneOn add_left_mono
                                    (QuantileLower P X α.val)) h

theorem VaR_translation_invariant : VaR[X + c•1 // P, α] = VaR[X + c•1 // P, α] + c := sorry

theorem VaR_positive_homog (hc : c > 0) : FinVaR1 P (fun ω => c * X ω) α = c * FinVaR1 P X α := sorry

end VaR_properties

end Risk
