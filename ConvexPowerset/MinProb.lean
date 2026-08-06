/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Authors: Noam Zilberstein
-/
import ConvexPowerset.Operations
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
  refine le_trans (biInf_le _  (s := ConvexPowerset.set (ωSup c)) ?_) (hμ 0).2
  exact mem_ωSup.mpr fun i ↦ (hμ i).1

lemma minProb_ωScottContinuous (E : Set α) : ωScottContinuous (minProb · E) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨minProb_monotone _, ?_⟩
  intro c
  exact le_antisymm (minProb_ωSup_le c E) (iSup_le fun i ↦ minProb_monotone E (le_ωSup c i))

/-- The probability of an event under a `PMF.bind` is the average of the probabilities of the
event under the branches. -/
lemma prob_pmf_bind {ι β : Type} {ξ : PMF ι} {k : ι → Distr β} {ν : Distr β}
    (hν : ν = ξ.bind k) (E : Set β) :
    ∑' y : E, ν (some (y : β)) = ∑' i : ι, ξ i * ∑' y : E, k i (some (y : β)) := by
  have h : ∀ y : β, ν (some y) = ∑' i : ι, ξ i * k i (some y) := by
    intro y; rw [hν]; exact PMF.bind_apply _ _ _
  simp only [h]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun z ↦ ENNReal.tsum_mul_left

/-- Specialisation of `prob_pmf_bind` to a bind of distributions, phrased with the `Distr`
coercion. -/
lemma prob_distr_bind {β : Type} {μ : Distr α} {g : WithBot α → Distr β} {ν : Distr β}
    (hν : ν = μ.bind g) (E : Set β) :
    ∑' y : E, ν (some (y : β)) = ∑' z : WithBot α, μ z * ∑' y : E, g z (some (y : β)) := by
  rw [prob_pmf_bind hν E]
  exact tsum_congr fun _ ↦ rfl

/-- The distribution putting all its mass on `⊥` assigns probability zero to every event. -/
lemma prob_bot_distr {β : Type} (E : Set β) :
    ∑' y : E, (PMF.pure (⊥ : WithBot β) : Distr β) (some (y : β)) = 0 := by
  have h : ∀ y : β, (PMF.pure (⊥ : WithBot β) : Distr β) (some y) = 0 :=
    fun y ↦ PMF.pure_apply_of_ne _ _ (by simp)
  simp [h]

/-- Summing the weights `μ x * minProb (f x) E` over the support of `μ` is the same as summing
over all of `α`, since the weights vanish off the support. -/
lemma tsum_support_weights {β : Type} (μ : Distr α) (f : α → ConvexPowerset β) (E : Set β) :
    ∑' x : { x : α | WithBot.some x ∈ μ.support }, μ x * minProb (f x) E =
      ∑' x : α, μ (some x) * minProb (f x) E := by
  refine tsum_subtype_eq_of_support_subset (f := fun x : α ↦ μ (some x) * minProb (f x) E) ?_
  intro x hx
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hx
  exact (PMF.mem_support_iff _ _).mpr hx.1

/-- Given `μ ∈ s`, binding it with minimising distributions for each branch produces an element of
`s >>= f` whose event probability is the average of the branch minima. -/
lemma minProb_bind_le {β : Type} (s : ConvexPowerset α) (f : α → ConvexPowerset β) (E : Set β) :
    minProb (s >>= f) E ≤
    ⨅ μ ∈ s, ∑' x : { x : α | WithBot.some x ∈ μ.support }, μ x * minProb (f x) E := by
  refine le_iInf₂ fun μ hμ ↦ ?_
  choose m hm hval using fun x : α ↦ minProb_attained (f x) E
  let g : WithBot α → Distr β := fun z ↦ z.elim (PMF.pure ⊥) m
  have hmem : μ.bind g ∈ s >>= f := by
    refine mem_bind.mpr ⟨μ, hμ, g, ?_, rfl⟩
    intro z _
    cases z with
    | bot => exact Set.mem_univ _
    | coe x => exact hm x
  refine le_trans (biInf_le _ hmem) ?_
  rw [prob_distr_bind rfl, total_prob, tsum_support_weights]
  have hbot : ∑' y : E, g ⊥ (some (y : β)) = 0 := prob_bot_distr E
  rw [hbot, mul_zero, add_zero]
  exact le_of_eq (tsum_congr fun x ↦ congrArg₂ (· * ·) rfl (hval x))

/-- Every element of `s >>= f` has event probability at least the average, over some `μ ∈ s`, of
the branch minima. -/
lemma le_minProb_bind {β : Type} (s : ConvexPowerset α) (f : α → ConvexPowerset β) (E : Set β) :
    (⨅ μ ∈ s, ∑' x : { x : α | WithBot.some x ∈ μ.support }, μ x * minProb (f x) E) ≤
      minProb (s >>= f) E := by
  refine le_iInf₂ fun ν hν ↦ ?_
  obtain ⟨μ, hμ, g, hg, hbind⟩ := mem_bind.mp hν
  rw [prob_distr_bind hbind]
  refine le_trans (iInf₂_le μ hμ) ?_
  rw [tsum_support_weights]
  refine le_trans ?_ (le_of_eq (total_prob _).symm)
  refine le_trans ?_ le_self_add
  refine ENNReal.tsum_le_tsum fun x ↦ ?_
  by_cases hx : WithBot.some x ∈ μ.support
  · exact mul_le_mul' le_rfl (biInf_le _ (hg (some x) hx))
  · simp only [PMF.mem_support_iff, ne_eq, Decidable.not_not] at hx
    exact le_of_eq_of_le (mul_eq_zero_of_left hx _) bot_le

lemma minProb_bind {β : Type} (s : ConvexPowerset α) (f : α → ConvexPowerset β) (E : Set β) :
    minProb (s >>= f) E =
    ⨅ μ ∈ s, ∑' x : { x : α | WithBot.some x ∈ μ.support }, μ x * minProb (f x) E :=
  le_antisymm (minProb_bind_le s f E) (le_minProb_bind s f E)

lemma minProb_nondet {ι : Type} [Finite ι] [Nonempty ι] (s : ι → ConvexPowerset α) (E : Set α) :
    minProb (nondet s) E = ⨅ i : ι, minProb (s i) E := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun i ↦ ?_
    choose m hm hval using fun j ↦ minProb_attained (s j) E
    refine le_of_le_of_eq (biInf_le _ (i := m i) ?_) (hval i)
    exact mem_nondet.mpr ⟨PMF.pure i, m, fun j _ ↦ hm j, (PMF.pure_bind _ _).symm⟩
  · refine le_iInf₂ fun μ hμ ↦ ?_
    obtain ⟨ξ, k, hk, hbind⟩ := mem_nondet.mp hμ
    rw [prob_pmf_bind hbind]
    calc ⨅ i : ι, minProb (s i) E
        = ∑' i : ι, ξ i * ⨅ j : ι, minProb (s j) E := by
          rw [ENNReal.tsum_mul_right, ξ.tsum_coe, one_mul]
      _ ≤ ∑' i : ι, ξ i * ∑' y : E, k i (some (y : α)) := by
          refine ENNReal.tsum_le_tsum fun i ↦ ?_
          by_cases hi : i ∈ ξ.support
          · exact mul_le_mul' le_rfl
              ((iInf_le (fun j ↦ minProb (s j) E) i).trans (biInf_le _ (hk i hi)))
          · simp only [PMF.mem_support_iff, ne_eq, Decidable.not_not] at hi
            simp [hi]

end ConvexPowerset
