import Mathlib.Order.OmegaCompletePartialOrder

import ConvexPowerset.Distr.Monad

-- The Probabilistic Powerdomain of Jones and Plotkin

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

noncomputable instance {α : Type} : Bot (Distr α) where
  bot := PMF.pure ⊥

noncomputable instance {α : Type} : OrderBot (Distr α) where
  bot_le μ x := by
    refine le_of_eq_of_le ?_ (zero_le _)
    exact PMF.pure_apply_of_ne _ _ WithBot.coe_ne_bot

/-- Monotone convergence for `tsum`: for a pointwise-monotone family of `ℝ≥0∞`-valued
functions, the sum of the pointwise suprema is the supremum of the sums. -/
lemma Distr.tsum_iSup_eq_iSup_tsum {α : Type} (f : ℕ → α → ENNReal)
    (hf : ∀ a, Monotone fun i ↦ f i a) :
    ∑' x : α, ⨆ i, f i x = ⨆ i, ∑' x : α, f i x := by
  rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [ENNReal.finsetSum_iSup_of_monotone hf]
  rw [iSup_comm]
  simp_rw [← ENNReal.tsum_eq_iSup_sum]

noncomputable instance {α : Type} : OmegaCompletePartialOrder (Distr α) where
  ωSup c := {
    val x :=
      match x with
      | Option.none => iInf fun i ↦ c i ⊥
      | Option.some x => iSup fun i ↦ c i x
    property := by
      refine ENNReal.summable.hasSum_iff.mpr ?_
      conv => lhs; exact total_prob _
      simp only
      conv => lhs; arg 2; exact iInf_congr fun i ↦ prob_bot (c i)
      rw [Distr.tsum_iSup_eq_iSup_tsum (α := α) (fun i x ↦ (c i) (↑x : WithBot α))
        (fun a i j hij ↦ c.monotone hij a)]
      rw [← ENNReal.sub_iSup ENNReal.one_ne_top]
      refine add_tsub_cancel_of_le (iSup_le fun i ↦ ?_)
      rw [prob_not_bot (c i)]
      exact tsub_le_self
  }
  le_ωSup c _ x := le_iSup (fun j ↦ c j x) _
  ωSup_le c _ h x := iSup_le fun j ↦ h j x

lemma dist_le_bot_ge {α : Type} {μ : Distr α} {ν : Distr α} (hle : μ ≤ ν) : ν ⊥ ≤ μ ⊥ := by {
  rw [prob_bot, prob_bot]; simp only [tsub_le_iff_right]
  have hs := ENNReal.tsum_le_tsum hle
  refine le_trans ?_ (add_le_add_right hs _)
  have hle1 : ∑' (x : α), μ x ≤ 1 := by {
    rcases μ with ⟨d, h⟩; simp only [distr_coe] at *; rw [← HasSum.tsum_eq h]
    exact Summable.tsum_le_tsum_of_inj WithBot.some WithBot.coe_injective (by simp)
      (fun x => le_refl (d ↑x))
      ENNReal.summable
      ENNReal.summable
  }
  rw [ENNReal.sub_add_eq_add_sub hle1, ENNReal.add_sub_cancel_right]
  all_goals { exact ne_top_of_le_ne_top (b := 1) (by simp) hle1 }
}

lemma proper_dist_maximal {α : Type} {μ ν : Distr α} (hbot : μ ⊥ = 0) (hle : μ ≤ ν) :
     μ = ν := by
  have hbot' : ν ⊥ = 0 := by
    refine le_antisymm ?_ bot_le
    rw [← hbot]; exact dist_le_bot_ge hle
  ext x; cases x with
  | bot => exact hbot.trans hbot'.symm
  | coe y =>
    refine (hle _).not_lt_iff_eq.mp fun hc ↦ lt_irrefl (1 : ENNReal) ?_
    nth_rewrite 1 [← μ.property.tsum_eq]
    nth_rewrite 2 [← ν.property.tsum_eq]
    refine ENNReal.tsum_lt_tsum ?_ ?_ hc
    · rw [μ.property.tsum_eq]; exact ENNReal.one_ne_top
    · intro x; cases x with
      | bot => exact le_of_eq (hbot.trans hbot'.symm)
      | coe z => exact hle z
