import ConvexPowerset.Monad.Order
import ConvexPowerset.Powerdomain

namespace ConvexPowerset

lemma convex_sum_mem {α : Type} {s : ConvexPowerset α} {μ ν : Distr α}
    (hμ : μ ∈ s) (hν : ν ∈ s) {p q : ENNReal} (h : p + q = 1) :
    Distr.convex_sum μ ν p q h ∈ s := by
  obtain ⟨_, hmem, heq⟩ :=
    (Set.mem_image _ _ _).mp
      (s.convex
        ((Set.mem_image _ _ _).mpr ⟨_, hμ, rfl⟩)
        ((Set.mem_image _ _ _).mpr ⟨_, hν, rfl⟩)
        bot_le bot_le h)
  convert hmem
  · exact Subtype.ext heq.symm

def singleton {α : Type} (μ : PMF α) : ConvexPowerset α := {
  set := { PMF.to_distr μ }
  nonempty := ⟨_, Set.mem_singleton _⟩
  convex := by
    conv => arg 2; exact Set.image_singleton
    exact convex_singleton _
  closed := isClosed_singleton
  upcl := by
    rintro _ ν hle ⟨_, rfl⟩
    refine Set.mem_singleton_iff.mpr ?_
    symm; exact proper_dist_maximal rfl hle
}

def prob {α ι : Type} (ξ : PMF ι) (s : ι → ConvexPowerset α) : ConvexPowerset α :=
    singleton ξ >>= s

set_option linter.deprecated false in
def bernoulli {α : Type} {p : NNReal} (h : p ≤ 1) (s t : ConvexPowerset α) :
    ConvexPowerset α :=
  prob (PMF.bernoulli p h) fun b ↦ if b then s else t

lemma prob_monotone {α ι : Type} (ξ : PMF ι) : Monotone (@prob α ι ξ) :=
  fun _ _ ↦ bind_monotone (le_refl _)

end ConvexPowerset

-- This really belongs in mathlib, but it doesn't exist
namespace OmegaCompletePartialOrder

def const {α : Type} [Preorder α] (x : α) : Chain α := {
  toFun _ := x
  monotone' _ _ _ := le_refl _
}

lemma ωSup_const {α : Type} [OmegaCompletePartialOrder α] (x : α) :
    ωSup (const x) = x := by
  refine le_antisymm (ωSup_le _ _ ?_) ?_
  · intro _; exact le_refl _
  · refine le_of_eq_of_le ?_ (le_ωSup _ 0); rfl

end OmegaCompletePartialOrder

namespace ConvexPowerset

open OmegaCompletePartialOrder in
lemma prob_continuous {α ι : Type} (ξ : PMF ι) :
    ωScottContinuous (@prob α ι ξ) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨prob_monotone _, fun c ↦ ?_⟩
  unfold prob
  conv => lhs; arg 1; exact (OmegaCompletePartialOrder.ωSup_const (singleton ξ)).symm
  refine (bind_continuous _ _).symm.trans (congrArg _ ?_)
  ext1; ext1 i; rfl

def singleton' {α : Type} (μ : Distr α) : ConvexPowerset α :=
    prob μ fun x ↦ match x with
    | Option.none => ⊥
    | Option.some x => pure x

lemma self_mem_singleton' {α : Type} (μ : Distr α) : μ ∈ singleton' μ := by
  simp only [singleton', prob, Bind.bind, bind, c_bind, Set.image, Set.mem_iUnion, exists_prop,
    Function.uncurry, Prod.exists]
  refine ⟨μ.to_distr, ?_, ⟨_, rfl, rfl, ?_⟩, ?_⟩
  · use fun x ↦ pure
      (match x with
        | Option.none => ⊥
        | Option.some x => x)
  · refine Set.mem_pi.mpr fun x hx ↦ ?_; simp only; cases x with
    | bot => exact Set.mem_univ _
    | coe x => simp only [Option.elim, Function.comp_apply]; cases x with
      | bot => exact Set.mem_univ _
      | coe x => rfl
  · refine (PMF.bind_pure_comp _ _).trans ?_; ext x
    simp only [PMF.to_distr, PMF.map_apply]
    refine (@tsum_eq_single _ _ _ _ _
      (SummationFilter.instLeAtTopUnconditional _) _ (Option.some x) ?_).trans ?_
    · intro y hy; cases y with
      | none => simp only [DFunLike.coe, ite_self]
      | some y =>
        simp only [ite_eq_right_iff]; rintro rfl; contradiction
    · simp only [↓reduceIte, DFunLike.coe]

lemma singleton'_set_eq {α : Type} (μ : Distr α) :
    (singleton' μ).set = { ν | μ ≤ ν } := by
  ext ν; constructor
  · rintro ⟨⟨ν, f⟩, ⟨s, h, hs⟩, ⟨_, rfl, rfl, hf⟩, rfl⟩
    obtain ⟨ξ, rfl⟩ := Set.mem_range.mp h; clear h
    obtain ⟨_, h, h'⟩ := hs
    obtain ⟨rfl, rfl⟩ := Set.mem_range.mp h; clear h
    rcases h' with ⟨rfl, h⟩; simp only [Function.uncurry_apply_pair, Set.mem_setOf_eq]
    intro x; by_cases hx : μ x = 0
    · rw [hx]; exact bot_le
    · conv => rhs; exact PMF.bind_apply _ _ _
      refine le_of_eq_of_le ?_ (ENNReal.le_tsum (some (some x)))
      simp only [DFunLike.coe, PMF.to_distr]
      symm; convert mul_one _ <;> try rfl
      have hx' : some (some x) ∈ (PMF.to_distr μ).support := by
        refine (PMF.mem_support_iff _ _).mpr ?_
        simp only [PMF.to_distr, DFunLike.coe]; exact hx
      have := Set.mem_pi.mp h (some (some x)) hx'
      simp only [Option.elim_some, Function.comp_apply] at this
      have := Set.mem_singleton_iff.mp this
      conv => lhs; arg 1; exact this
      exact PMF.pure_apply_self _
  · intro hle; exact (singleton' _).upcl hle (self_mem_singleton' _)

-- The set of all distributions over a finite type is closed
lemma finite_distrs_closed {ι : Type} [Finite ι] :
    IsClosed (PMF.to_distr '' Set.univ : Set (Distr ι)) := by
  refine distr_inducing.isClosed_iff.mpr ⟨{ f | tsum f = 1 }, ?_, ?_⟩
  · refine isClosed_eq ?_ continuous_const
    have _ := Fintype.ofFinite ι; simp only [tsum_fintype]
    exact continuous_finsetSum _ fun _ _ ↦ continuous_apply _
  · simp only [Set.preimage_setOf_eq, distr_inj, Set.image_univ]; ext μ; constructor
    · intro hsum; refine Set.mem_range.mpr (PMF.to_distr_inv ?_)
      rw [prob_bot]
      suffices h : (∑' (i : ι), μ i) = 1 by rw [h]; exact tsub_self _
      apply ENNReal.coe_inj.mpr at hsum
      refine (Eq.trans ?_ (ENNReal.coe_tsum ?_).symm).trans hsum
      · refine tsum_congr fun i ↦ ?_; simp only [Function.comp_apply]
        refine (ENNReal.coe_toNNReal ?_).symm
        exact ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one _ _)
      · refine ENNReal.summable_toNNReal_of_tsum_ne_top ?_
        refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        rw [← μ.property.tsum_eq, total_prob]; exact le_self_add
    · rintro ⟨μ, rfl⟩
      simp only [DFunLike.coe, Function.comp_def, PMF.to_distr, Set.mem_setOf_eq]
      rw [← ENNReal.tsum_toNNReal_eq, HasSum.tsum_eq μ.property]
      · rfl
      · intro x; exact ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.coe_le_one _ _)

-- Construct a convex powerset as the convex hull of a finite type
def finitely_generated {ι : Type} [Finite ι] [Nonempty ι] : ConvexPowerset ι := {
  set := PMF.to_distr '' Set.univ
  nonempty := by
    let i := Classical.arbitrary ι
    refine ⟨PMF.to_distr (pure i), (Set.mem_image _ _ _).mpr ?_⟩
    exact ⟨PMF.pure i, Set.mem_univ _, rfl⟩
  convex := by
    rintro _ ⟨_ , ⟨μ, _, rfl⟩, rfl⟩
    rintro _ ⟨_ , ⟨ν, _, rfl⟩, rfl⟩
    intro p q _ _ hsum
    refine ⟨Distr.convex_sum (PMF.to_distr μ) (PMF.to_distr ν) p q hsum, ?_, rfl⟩
    refine (Set.mem_image _ _ _).mpr ?_
    simp only [Set.mem_univ, true_and]
    refine PMF.to_distr_inv ?_
    simp only [DFunLike.coe, Distr.convex_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_eq_zero, mul_eq_zero]
    constructor <;> exact Or.inr rfl
  closed := finite_distrs_closed
  upcl := by
    rintro _ ν hle ⟨μ, _, rfl⟩
    refine ⟨μ, Set.mem_univ _, ?_⟩
    exact proper_dist_maximal rfl hle
}

-- Construct the convex hull of a finset. If the set is empty, then it is defined as ⊥
def of_finset {α : Type} (s : Finset α) : ConvexPowerset α :=
  if h : s.Nonempty then @finitely_generated ↑s _ h.coe_sort >>= fun i ↦ pure i.val else ⊥

def nondet {ι α : Type} [Finite ι] [Nonempty ι] (s : ι → ConvexPowerset α) : ConvexPowerset α :=
  finitely_generated >>= s

lemma mem_nondet {ι α : Type} [Finite ι] [Nonempty ι] {s : ι → ConvexPowerset α} {μ : Distr α} :
    μ ∈ nondet s ↔ ∃ ξ : PMF ι, ∃ k ∈ ξ.support.pi (set ∘ s), μ = ξ.bind k := by
  simp only [Membership.mem, Set.Mem, nondet, bind, c_bind, Set.image, finitely_generated,
    Bind.bind, Prod.exists, Function.uncurry_apply_pair]
  constructor
  · rintro ⟨_, f, ⟨_, ⟨ν, rfl⟩, _, ⟨⟨ξ, _, rfl⟩, rfl⟩, rfl, hf⟩, rfl⟩
    refine ⟨ξ, fun x ↦ f x, ?_, ?_⟩
    · refine Set.mem_pi.mpr ?_; intro i hi
      exact Set.mem_pi.mp hf i hi
    · ext x; simp only [DFunLike.coe, PMF.bind, total_prob]
      conv => lhs; arg 2; exact zero_mul _
      rw [add_zero]; rfl
  · rintro ⟨ξ, f, hf, rfl⟩
    refine ⟨PMF.to_distr ξ, with_bot f (β := Distr α), ?_, ?_⟩
    · refine Set.mem_biUnion ?_ ⟨rfl, ?_⟩ (x := PMF.to_distr ξ)
      · exact ⟨ξ, True.intro, rfl⟩
      · refine Set.mem_pi.mpr fun i hi ↦ ?_; cases i with
        | bot => contradiction
        | coe i =>
          simp only [Option.elim, Function.comp_apply, with_bot]
          exact Set.mem_pi.mp hf i hi
    · ext x
      simp only [DFunLike.coe, PMF.bind, PMF.to_distr, total_prob, zero_mul, add_zero, with_bot]

lemma nondet_monotone {ι α : Type} [Finite ι] [Nonempty ι] : Monotone (@nondet ι α _ _) :=
  fun _ _ ↦ bind_monotone (le_refl _)

open OmegaCompletePartialOrder in
lemma nondet_continuous {α ι : Type} [Finite ι] [Nonempty ι] :
    ωScottContinuous (@nondet ι α _ _) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨nondet_monotone, fun c ↦ ?_⟩
  unfold nondet
  conv => lhs; arg 1; exact (OmegaCompletePartialOrder.ωSup_const _).symm
  refine (bind_continuous _ _).symm.trans (congrArg _ ?_)
  ext1; ext1 i; rfl

def nondet₂ {α : Type} (s t : ConvexPowerset α) :=
  nondet fun (b : Bool) ↦ if b then s else t

end ConvexPowerset
