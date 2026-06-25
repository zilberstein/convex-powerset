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

lemma total_prob {α : Type} (d : WithBot α → ENNReal) : tsum d = (∑' x : α, d x) + d ⊥ := by
  conv =>
    lhs;
    exact
      ((Equiv.optionEquivSumPUnit.{0} _).symm.tsum_eq _).symm.trans
        (Summable.tsum_sum ENNReal.summable ENNReal.summable)
  simp only [Equiv.optionEquivSumPUnit_symm_inl, Equiv.optionEquivSumPUnit_symm_inr, tsum_fintype,
    Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_const, Finset.card_singleton, one_smul]
  rfl

lemma prob_bot {α : Type} (d : Distr α) : d ⊥ = 1 - ∑' x : α, d x := by
  rw [← PMF.tsum_coe d]
  conv =>
    rhs; arg 1; exact total_prob _
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

theorem prob_ne_top {p : ENNReal} (hp : p ≤ 1) : (p : ENNReal) ≠ ⊤ := by
  apply lt_top_iff_ne_top.mp
  refine lt_of_le_of_lt ?_ (ENNReal.one_lt_top)
  assumption
