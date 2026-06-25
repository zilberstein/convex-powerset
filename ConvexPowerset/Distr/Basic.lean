import Init.Prelude

import Mathlib.Algebra.CharP.Defs
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Instances.Real.Lemmas

def Distr (α : Type) := PMF (WithBot α)

instance {α : Type} : FunLike (Distr α) (WithBot α) ENNReal where
  coe := Subtype.val
  coe_injective' _ _ h := Subtype.ext h

instance {α : Type} : Nonempty (Distr α) := Nonempty.intro (PMF.pure ⊥)

lemma distr_coe {α : Type} {μ : Distr α} {x : WithBot α} : μ x = μ.val x := rfl

@[ext]
theorem distr_ext {α : Type} {μ ν : Distr α} (h : ∀ x, μ x = ν x) : μ = ν := by {
    apply Subtype.ext; ext x; exact h x
  }

lemma distr_upper_bound {α : Type} (μ : Distr α) (x : WithBot α) :
  μ x ≤ 1 := by {
    rcases μ with ⟨d, hs⟩
    exact (le_hasSum hs x (fun _ _ => bot_le))
  }

lemma prob_bot {α : Type} (d : Distr α) : d ⊥ = 1 - ∑' x : α, d x := by
  rw [← PMF.tsum_coe d]
  conv =>
    rhs; arg 1;
    exact
      ((Equiv.optionEquivSumPUnit.{0} _).symm.tsum_eq _).symm.trans
        (Summable.tsum_sum ENNReal.summable ENNReal.summable)
  simp only [Equiv.optionEquivSumPUnit_symm_inl, Equiv.optionEquivSumPUnit_symm_inr, tsum_fintype,
    Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_const, Finset.card_singleton, one_smul]
  refine (ENNReal.add_sub_cancel_left ?_).symm
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  refine le_of_le_of_eq ?_ (PMF.tsum_coe d)
  exact ENNReal.tsum_comp_le_tsum_of_injective WithBot.coe_injective _

lemma prob_not_bot {α : Type} (d : Distr α) : ∑' x : α, d x = 1 - d ⊥ := by
  rw [prob_bot]; refine Eq.symm (ENNReal.sub_sub_cancel ENNReal.one_ne_top ?_)
  rw [← PMF.tsum_coe d]
  exact Summable.tsum_le_tsum_of_inj some (Option.some_injective _)
    (fun _ _ ↦ bot_le)
    (fun _ ↦ le_refl _)
    ENNReal.summable
    ENNReal.summable

-- Orders on Probability Distributions

instance {α : Type} : LE (Distr α) where
  le d₁ d₂ := ∀ x : α, d₁ x ≤ d₂ x

noncomputable instance {α : Type} : Bot (Distr α) where
  bot := PMF.pure ⊥
noncomputable instance {α : Type} : OrderBot (Distr α) where
  bot_le := by
    intro d x; refine le_of_eq_of_le (PMF.pure_apply_of_ne _ _ ?_) bot_le
    exact WithBot.coe_ne_bot

instance {α : Type} : Preorder (Distr α) where
  le_refl d x := le_refl (d x)
  le_trans :=  by {
    intros d₁ d₂ d₃ h₁ h₂ x
    apply le_trans (h₁ x) (h₂ x)
  }

instance {α : Type} : PartialOrder (Distr α) where
  le_antisymm := by
    intro d₁ d₂ h₁ h₂
    apply PMF.ext
    intro x
    have h (y : α) : d₁ y = d₂ y := le_antisymm (h₁ y) (h₂ y)
    cases x
    · refine (prob_bot d₁).trans (Eq.trans ?_ (prob_bot d₂).symm)
      rw [tsum_congr]
      assumption
    · apply h

theorem prob_ne_top {p : ENNReal} (hp : p ≤ 1) : (p : ENNReal) ≠ ⊤ := by
  apply lt_top_iff_ne_top.mp
  refine lt_of_le_of_lt ?_ (ENNReal.one_lt_top)
  assumption
