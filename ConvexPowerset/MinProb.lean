/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Authors: Noam Zilberstein
-/
import ConvexPowerset.Powerdomain

namespace ConvexPowerset

variable {α : Type}

noncomputable def minProb (s : ConvexPowerset α) (E : Set α) : ENNReal :=
  ⨅ μ ∈ s, ∑' x : E, μ (some x)

lemma minProb_monotone (E : Set α) : Monotone (minProb · E) := by
  intro s t hle; apply biInf_mono; exact le_iff_supset.mp hle

open OmegaCompletePartialOrder

/-- Each `some`-coordinate is a continuous function of the distribution, since the topology on
`Distr α` is induced by `distr_inj`. -/
lemma distr_coord_continuous (x : α) : Continuous fun μ : Distr α ↦ μ (some x) := by
  have h : (fun μ : Distr α ↦ μ (some x)) = fun μ ↦ ((distr_inj μ x : NNReal) : ENNReal) :=
    funext fun _ ↦ (ENNReal.coe_toNNReal prob_not_top).symm
  rw [h]
  exact ENNReal.continuous_coe.comp ((continuous_apply x).comp distr_inducing.continuous)

/-- The probability of an event is lower semicontinuous in the distribution, being a sum of
continuous nonnegative functions. -/
lemma prob_lowerSemicontinuous (E : Set α) :
    LowerSemicontinuous fun μ : Distr α ↦ ∑' x : E, μ (some x) :=
  lowerSemicontinuous_tsum fun x ↦ (distr_coord_continuous (x : α)).lowerSemicontinuous

/-- Sublevel sets of the probability of an event are closed. -/
lemma prob_isClosed_le (E : Set α) (t : ENNReal) :
    IsClosed { μ : Distr α | ∑' x : E, μ (some x) ≤ t } :=
  (prob_lowerSemicontinuous E).isClosed_preimage t

/-- The infimum defining `minProb` is attained, since the set is compact and nonempty, and the
probability of an event is lower semicontinuous. -/
lemma minProb_attained (s : ConvexPowerset α) (E : Set α) :
    ∃ μ ∈ s, ∑' x : E, μ (some x) = minProb s E := by
  obtain ⟨μ, hμ, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn s.nonempty s.closed.isCompact
      ((prob_lowerSemicontinuous E).lowerSemicontinuousOn s.set)
  exact ⟨μ, hμ, le_antisymm (le_iInf₂ fun _ hν ↦ hmin hν) (biInf_le _ hμ)⟩

lemma minProb_le_of_mem {s : ConvexPowerset α} {E : Set α} {μ : Distr α} (hμ : μ ∈ s) :
    minProb s E ≤ ∑' x : E, μ (some x) :=
  biInf_le _ hμ

/-- If every element of a chain contains a distribution assigning the event probability at most
`t`, then so does the limit of the chain. This is where compactness is used. -/
lemma chain_level_set_nonempty (c : Chain (ConvexPowerset α)) (E : Set α) {t : ENNReal}
    (h : ∀ i, minProb (c i) E ≤ t) :
    (⋂ i, { μ : Distr α | μ ∈ (c i).set ∧ ∑' x : E, μ (some x) ≤ t }).Nonempty := by
  have hset : (⋂ i, { μ : Distr α | μ ∈ (c i).set ∧ ∑' x : E, μ (some x) ≤ t }) =
      ⋂₀ (Set.range fun i ↦ (c i).set ∩ { μ : Distr α | ∑' x : E, μ (some x) ≤ t }) := by
    rw [Set.sInter_range]; rfl
  rw [hset]
  have hne : Nonempty (Set.range fun i ↦
      (c i).set ∩ { μ : Distr α | ∑' x : E, μ (some x) ≤ t }) := ⟨⟨_, 0, rfl⟩⟩
  refine IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed ?_ ?_ ?_ ?_
  -- The family is directed, since the sets of a chain are decreasing
  · rintro s ⟨i, rfl⟩ u ⟨j, rfl⟩
    refine ⟨_, ⟨max i j, rfl⟩, ?_, ?_⟩ <;>
      refine Set.inter_subset_inter_left _ (le_iff_supset.mp (c.monotone' ?_))
    · exact le_sup_left
    · exact le_sup_right
  -- Each set is nonempty, since the infimum defining `minProb` is attained
  · rintro _ ⟨i, rfl⟩
    obtain ⟨μ, hμ, hval⟩ := minProb_attained (c i) E
    exact ⟨μ, hμ, hval.trans_le (h i)⟩
  -- Each set is compact, being a closed subset of the compact space `Distr α`
  · rintro _ ⟨i, rfl⟩
    exact ((c i).closed.inter (prob_isClosed_le E t)).isCompact
  · rintro _ ⟨i, rfl⟩
    exact (c i).closed.inter (prob_isClosed_le E t)

lemma minProb_ωSup_le (c : Chain (ConvexPowerset α)) (E : Set α) :
    minProb (ωSup c) E ≤ ⨆ i, minProb (c i) E := by
  obtain ⟨μ, hμ⟩ := chain_level_set_nonempty c E (t := ⨆ i, minProb (c i) E)
    (fun i ↦ le_iSup (fun j ↦ minProb (c j) E) i)
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hμ
  refine le_trans (minProb_le_of_mem (s := ωSup c) ?_) (hμ 0).2
  exact mem_ωSup.mpr fun i ↦ (hμ i).1

lemma minProp_ωScottContinuous (E : Set α) : ωScottContinuous (minProb · E) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨minProb_monotone _, ?_⟩
  intro c
  exact le_antisymm (minProb_ωSup_le c E) (iSup_le fun i ↦ minProb_monotone E (le_ωSup c i))

end ConvexPowerset
