/-
In this file we define histories and operations that are related to them.

* Defines an MDP
* Defines a history, which is a sequence of states and actions
* Defines a histories consistent with a partial sequence of states and actions
* A general randomized history-dependent policy
* The reward and probability of the history, which is used to compute the value function
* Value function for a history as the expected reward
-/
import Mathlib.Data.Nat.Basic

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic

--import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Probability.Basic

namespace MDPs

section Definitions

open Findist

/-- Markov decision process -/
structure MDP : Type where
  /-- states -/
  S : ℕ
  S_ne : 0 < S
  /-- actions  -/
  A : ℕ
  A_ne : 0 < A
  /-- transition probability s, a, s' -/
  P : Fin S → Fin A → Δ S
  /-- reward function s, a, s' -/
  r : Fin S → Fin A → Fin S → ℝ

end Definitions

variable (M : MDP)

section Histories

/-- Represents a history. The state is type ℕ and action is type ℕ. -/
inductive Hist (M : MDP)  : Type where
  | init : Fin M.S → Hist M
  | foll : Hist M → Fin M.A → Fin M.S → Hist M

/-- Coerces a state to a history -/
instance : Coe (Fin M.S) (Hist M) where
  coe s := Hist.init s

/-- The length of the history corresponds to the zero-based step of the decision -/
@[reducible] def Hist.length : Hist M → ℕ
  | init _ => 0
  | Hist.foll h _ _ => 1 + length h

/-- Nonempty histories -/
abbrev HistNE (m : MDP) : Type := {h : Hist m // h.length ≥ 1}

/-- Returns the last state of the history -/
def Hist.last : Hist M → Fin M.S
  | init s => s
  | Hist.foll _ _ s => s

/-- Appends the state and action to the history --/
def Hist.append (h : Hist M) (as : Fin M.A × Fin M.S) : Hist M := h.foll as.1 as.2
-- TODO: remove?

def Hist.one (s₀ : Fin M.S) (a : Fin M.A) (s : Fin M.S) : Hist M := (Hist.init s₀).foll a s

/-- Return the prefix of hist of length k -/
def Hist.prefix (k : ℕ)  (h : Hist M) : Hist M :=
    match h with
      | Hist.init s => Hist.init s
      | Hist.foll hp a s =>
        if hp.length + 1 ≤ k then hp.foll a s
        else hp.prefix k





end Histories

end MDPs
