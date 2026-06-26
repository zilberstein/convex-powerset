import ConvexPowerset.Basic

def SmythOrd {α : Type} [LE α] (S T : Set α) :=
  ∀ y ∈ T, ∃ x ∈ S, x ≤ y

instance {α : Type} : LE (ConvexPowerset α) where
  le S T := SmythOrd S.set T.set

lemma le_iff_supset {α : Type} {S T : ConvexPowerset α} :
  S ≤ T ↔ T.set ⊆ S.set := by
    constructor
    · intro h d hd
      have ⟨d', hd', hle⟩ := h d hd
      exact S.upcl hle hd'
    · intro h d hd
      exists d; constructor
      · exact Set.mem_of_subset_of_mem h hd
      · exact le_refl _

instance {α : Type} : OrderBot (ConvexPowerset α) where
  bot_le s := by apply le_iff_supset.mpr; exact Set.subset_univ _

instance {α : Type} : Preorder (ConvexPowerset α) where
  le_refl S := le_iff_supset.mpr (le_refl S.set)
  le_trans S T U h₁ h₂ := by {
    refine le_iff_supset.mpr (le_trans ?_ ?_ (b := T.set)) <;>
      apply le_iff_supset.mp <;> assumption
  }

instance {α : Type} : PartialOrder (ConvexPowerset α) where
  le_antisymm _ _ h₁ h₂ := by
    ext1; exact (le_antisymm (le_iff_supset.mp h₂) (le_iff_supset.mp h₁))

open OmegaCompletePartialOrder

lemma chain_inter_nonempty {α : Type} (c : Chain (ConvexPowerset α)) :
    (Set.iInter fun i ↦ (c i).set).Nonempty := by
  refine IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed ?_ ?_ ?_ ?_
  · rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩; simp only [Set.mem_range, exists_exists_eq_and]
    refine ⟨max i j, ?_, ?_⟩ <;>
      refine le_iff_supset.mp (c.monotone' ?_)
    · exact le_sup_left
    · exact le_sup_right
  · rintro _ ⟨i, rfl⟩; exact (c i).nonempty
  · rintro _ ⟨i, rfl⟩; exact (c i).closed.isCompact
  · rintro _ ⟨i, rfl⟩; exact (c i).closed

lemma chain_inter_convex {α : Type} (c : Chain (ConvexPowerset α)) :
    Convex ENNReal (Subtype.val '' Set.iInter fun i ↦ (c i).set) := by
  convert convex_iInter fun i ↦ (c i).convex
  exact Set.image_val_iInter

instance {α : Type} : OmegaCompletePartialOrder (ConvexPowerset α) where
  ωSup c := {
    set := Set.iInter fun i ↦ (c i).set
    nonempty := chain_inter_nonempty c
    convex := chain_inter_convex c
    closed := isClosed_iInter fun i ↦ (c i).closed
    upcl := isUpperSet_iInter fun i ↦ (c i).upcl
  }
  le_ωSup _ _ := le_iff_supset.mpr (Set.iInter_subset _ _)
  ωSup_le c i h := by
    refine le_iff_supset.mpr ?_
    rintro μ hμ _ ⟨j, rfl⟩
    exact le_iff_supset.mp (h j) hμ
