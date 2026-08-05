/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Authors: Noam Zilberstein
-/
import ConvexPowerset.Monad

namespace ConvexPowerset

lemma pure_bind {α β : Type} (x : α) (k : α → ConvexPowerset β) : pure x >>= k = k x := by
  ext d; constructor
  · intro hd; obtain ⟨μ, hμ, f, hf, rfl⟩ := mem_bind.mp hd
    obtain rfl := (mem_pure _).mp hμ
    conv => rhs; exact PMF.pure_bind _ ?_
    refine hf x ?_; exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · intro hd
    have h : ∀ z, ∃ d', (z = x → d' = d) ∧ d' ∈ k z := by
      intro z; by_cases hz : z = x
      · refine ⟨d, fun _ ↦ rfl, ?_⟩; rw [hz]; exact hd
      · have ⟨d', hd⟩ := (k z).nonempty
        exact ⟨d', fun h ↦ False.elim (hz h), hd⟩
    choose f hf using h
    let g z := match z with
      | none => ⊥
      | some z' => f z'
    refine mem_bind.mpr ⟨PMF.pure x, Set.mem_singleton _, g, ?_, ?_⟩
    · apply Set.mem_pi.mpr; intro y hy
      rcases (PMF.mem_support_pure_iff _ _).mp hy with rfl
      simp only [Option.elim, Function.comp_apply, g]
      exact (hf x).2
    · rw [PMF.pure_bind]; simp only [g]; symm; exact (hf x).1 rfl

noncomputable def pmf_with_bot {α β : Type} (f : α → Distr β) (x : WithBot α) : Distr β :=
  match x with
  | ⊥ => ⊥
  | WithBot.some y => f y

lemma with_bot_bind {α β γ : Type} {f : α → Distr β} {g : β → Distr γ} :
    (pmf_with_bot fun x => PMF.bind (f x) (pmf_with_bot g)) =
    fun x => PMF.bind (pmf_with_bot f x) (pmf_with_bot g) := by
  unfold pmf_with_bot; ext x y; cases x with
  | bot => simp [Bot.bot]
  | coe z => simp

lemma pmf_bind_congr {α β : Type} {μ : PMF α} {f g : α → PMF β} (h : ∀ x ∈ μ.support, f x = g x) :
    μ.bind f = μ.bind g := by
  ext y; rw [PMF.bind_apply, PMF.bind_apply]; refine tsum_congr ?_
  intro x; by_cases hx : x ∈ μ.support
  · rw [h _ hx]
  · simp at hx; simp [hx]

-- Lemma B.7 from POPL '25
lemma bind_assoc_convex {α β γ : Type} {μ : Distr α} {ν : WithBot α → Distr β}
    {ξ : WithBot α → WithBot β → Distr γ}
    {g : WithBot β → ConvexPowerset γ}
    (h : ∀ x ∈ PMF.support μ, ∀ y ∈ PMF.support (ν x), ξ x y ∈ g y) :
    ∃ ξ' ∈ (⋃ x ∈ PMF.support μ, PMF.support (ν x)).pi (set ∘ g),
      (PMF.bind μ fun x => PMF.bind (ν x) (ξ x)) = (PMF.bind μ ν).bind ξ' := by
  let p (y : WithBot β) x := μ x * ν x y / PMF.bind μ ν y
  let f y (hy : y ∈ (μ.bind ν).support): Distr α := Subtype.mk (p y) (by {
    unfold p; rw [PMF.bind_apply]; refine (Summable.hasSum_iff ENNReal.summable).mpr ?_
    rw [tsum_congr fun _ ↦ ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
    refine ENNReal.inv_mul_cancel ?_ ?_
    · exact hy
    · intro hc; have h := HasSum.tsum_eq (μ.bind ν).property
      simp only [PMF.bind] at h
      refine False.elim (ne_top_of_le_ne_top ENNReal.one_ne_top ?_ hc); rw [← h]
      exact ENNReal.le_tsum _
  })
  have hf : ∀ y, ∃ ξ', ∀ hy : y ∈ (μ.bind ν).support, ξ' = f y hy := by
    intro y; by_cases hy : y ∈ (μ.bind ν).support
    · exact ⟨f y hy, fun _ ↦ rfl⟩
    · exact ⟨⊥, fun hc ↦ False.elim (hy hc)⟩
  choose ξ' hξ' using hf
  refine ⟨fun y ↦ PMF.bind (ξ' y) fun x ↦ ξ x y, ?_, ?_⟩
  · intro y; simp only [PMF.mem_support_iff, ne_eq, Set.mem_iUnion, exists_prop,
      Function.comp_apply, forall_exists_index, and_imp]; intro x hx hy
    have hy' : y ∈ (μ.bind ν).support := by
      simp only [PMF.support_bind, PMF.mem_support_iff, ne_eq, Set.mem_iUnion, exists_prop]
      exact ⟨x, hx, hy⟩
    refine countably_convex' ?_
    intro x'; rw [hξ' y hy']; unfold f; unfold p; intro hp
    refine h x' ?_ y ?_
    · intro hxx; apply hp; simp only [DFunLike.coe, ENNReal.div_eq_zero_iff, mul_eq_zero]
      left; left; exact hxx
    · intro hy; apply hp; simp only [DFunLike.coe, ENNReal.div_eq_zero_iff, mul_eq_zero]
      left; right; exact hy
  · ext z; simp only [PMF.bind_apply, PMF.bind_bind]
    rw [← tsum_congr (fun _ ↦ ENNReal.tsum_mul_left)]
    rw [← tsum_congr (fun _ ↦ ENNReal.tsum_mul_left)]
    nth_rewrite 2 [ENNReal.tsum_comm]
    nth_rewrite 2 [← tsum_congr (fun _ ↦ tsum_congr fun _ ↦ mul_assoc (G := ENNReal) _ _ _)]
    rw [← tsum_congr (fun _ ↦ tsum_congr fun _ ↦ ENNReal.tsum_mul_left)]
    rw [tsum_congr fun _ ↦ ENNReal.tsum_comm]
    nth_rewrite 2 [ENNReal.tsum_comm]
    refine tsum_congr fun x ↦ tsum_congr fun y ↦ ?_
    have hξeq : ∑' (a : WithBot α), μ a * (ν a) y * ((ξ' y) x * (ξ x y) z) =
                ∑' (a : WithBot α), μ a * (ν a) y * (p y x * (ξ x y) z) := by
      refine tsum_congr fun x' ↦ ?_; by_cases hx' : μ x' = 0
      · simp [hx']
      · by_cases hy' : (ν x') y = 0
        · simp [hy']
        · refine congrArg₂ _ rfl ?_
          have hy' : y ∈ (μ.bind ν).support := by
            simp only [PMF.support_bind, PMF.mem_support_iff, ne_eq, Set.mem_iUnion, exists_prop]
            exact ⟨x', hx', hy'⟩
          rw [hξ' y hy']; unfold f; rfl
    refine Eq.trans ?_ hξeq.symm; unfold p
    rw [ENNReal.tsum_mul_right, ← mul_assoc, ← mul_assoc]; refine congrArg₂ _ ?_ rfl
    by_cases hy : (ν x) y = 0
    · conv => lhs; arg 2; exact hy
      conv => rhs; arg 2; arg 1; arg 2; exact hy
      simp only [mul_zero, PMF.bind_apply, ENNReal.zero_div]
    · rw [ENNReal.mul_div_right_comm, ← mul_assoc]; refine congrArg₂ _ ?_ rfl
      refine Eq.symm (ENNReal.mul_div_cancel' ?_ ?_)
      · intro hz; cases mul_eq_zero.mp (ENNReal.tsum_eq_zero.mp hz x)
        · assumption
        · contradiction
      · intro hc; have h := HasSum.tsum_eq (μ.bind ν).property
        refine False.elim (ne_top_of_le_ne_top ENNReal.one_ne_top ?_ hc); rw [← h]
        simp only [PMF.bind]; exact ENNReal.le_tsum _

lemma bind_union {α β : Type} (s : ConvexPowerset α) (f : α → ConvexPowerset β) :
    set (bind s f) =
    ⋃ μ ∈ s, PMF.bind μ '' (μ.support.pi (Option.elim · Set.univ (set ∘ f))) := by
  simp only [bind, c_bind]; ext ν
  simp only [Set.mem_image, Set.mem_iUnion, exists_prop, Prod.exists, Function.uncurry_apply_pair]
  constructor
  · intro ⟨p, g, ⟨_, hp, rfl, hsupp⟩, hν⟩; subst hν
    exact Set.mem_biUnion hp ((Set.mem_image _ _ _).mpr ⟨g, hsupp, rfl⟩)
  · rintro ⟨t, ht, hν⟩; obtain ⟨μ, rfl⟩ := Set.mem_range.mp ht
    have ⟨hμ, hν⟩ := Set.mem_iUnion.mp hν
    obtain ⟨g, hg, rfl⟩:= (Set.mem_image _ _ _).mp hν
    refine ⟨μ, g, ⟨_, hμ, rfl, hg⟩, rfl⟩

lemma bind_bind_1 {α β γ : Type} (s : ConvexPowerset α) (f : α → ConvexPowerset β)
    (g : β → ConvexPowerset γ) :
    set (s >>= f >>= g) =
    { d | ∃ μ  ∈ s,
          ∃ ν ∈ μ.support.pi (set ∘ with_bot f),
          ∃ ξ ∈ (⋃ x ∈ μ.support, (ν x).support).pi (set ∘ with_bot g),
            d = PMF.bind (PMF.bind μ ν) ξ } := by
  simp only [Bind.bind, bind, c_bind, Set.image, Set.mem_iUnion, exists_prop, Prod.exists,
    Function.uncurry_apply_pair, Set.mem_pi, PMF.mem_support_iff, ne_eq, Function.comp_apply,
    forall_exists_index, and_imp, PMF.bind_bind]
  ext d; constructor
  · rintro ⟨_, g', ⟨_, ⟨μ, f', ⟨_, hμ, rfl, hf⟩, rfl⟩, rfl, hg⟩, rfl⟩
    refine ⟨μ , hμ, f', ?_, g', ?_, PMF.bind_bind _ _ _⟩
    · intro x hx; unfold with_bot; cases x
      · simp only [Bot.bot, Set.mem_univ]
      · exact hf _ hx
    · intro y x hx hxy; unfold with_bot; cases y with
      | bot => simp [Bot.bot]
      | coe y' =>
        refine hg y' ?_
        simp only [PMF.support_bind, PMF.mem_support_iff, ne_eq, Set.mem_iUnion, exists_prop]
        exact ⟨x, hx, hxy⟩
  · rintro ⟨μ, hμ, ν, hf, ξ, hg, rfl⟩
    refine ⟨μ.bind ν, ξ, ⟨μ.bind ν, ⟨μ, ν, ⟨μ, hμ, rfl, ?_⟩, rfl⟩, ?_⟩, PMF.bind_bind _ _ _⟩
    · intro x hx; cases x
      · simp only [Bot.bot, Option.elim_none, Set.mem_univ]
      · exact hf _ hx
    · refine ⟨rfl, ?_⟩; intro y hy
      simp only [PMF.support_bind, PMF.mem_support_iff, ne_eq, Set.mem_iUnion, exists_prop] at hy
      rcases hy with ⟨x, hx, hy⟩
      cases y
      · simp only [Bot.bot, Option.elim_none, Set.mem_univ]
      · exact hg _ x hx hy

lemma bind_bind_2 {α β γ : Type} (s : ConvexPowerset α) (f : α → ConvexPowerset β)
    (g : β → ConvexPowerset γ) :
    (s >>= fun (x : α) => f x >>= g).set =
    { d | ∃ μ  ∈ s,
          ∃ ν ∈ μ.support.pi (set ∘ with_bot f),
          ∃ ξ : WithBot α → WithBot β → Distr γ,
            (∀ x ∈ μ.support, ∀ y ∈ (ν x).support, ξ x y ∈ with_bot g y) ∧
            d = PMF.bind μ fun x ↦ PMF.bind (ν x) (ξ x) } := by
  simp only [Bind.bind, bind, c_bind, Set.image, Set.mem_iUnion, exists_prop, Prod.exists,
    Function.uncurry_apply_pair, Set.mem_pi, PMF.mem_support_iff, ne_eq, Function.comp_apply]
  ext d; constructor
  · rintro ⟨μ, ξ, ⟨_, hμ, rfl, hξ⟩, rfl⟩
    refine ⟨μ, hμ, ?_⟩
    have hν : ∀ x : WithBot α, ∃ ν : Distr β,
        (x ∈ μ.support → ν ∈ with_bot f x) ∧
        ∃ ξ' : WithBot β → Distr γ, x ∈ μ.support →
          ν.bind ξ' = ξ x ∧ ∀ y ∈ ν.support, ξ' y ∈ with_bot g y := by
      intro x; by_cases hx : x ∈ μ.support
      · cases x with
        | bot =>
          refine ⟨⊥, fun _ ↦ Set.mem_univ _, ?_⟩
          have _ (y : WithBot β):= Classical.dec (y = ⊥)
          refine ⟨fun y : WithBot β => if y = ⊥ then ξ ⊥ else ⊥, fun _ ↦ ⟨?_, ?_⟩⟩
          · simp only [Bot.bot, PMF.pure_bind, ↓reduceIte]
          · simp only [Bot.bot, PMF.support_pure, Set.mem_singleton_iff, forall_eq, ↓reduceIte]
            exact Set.mem_univ _
        | coe x =>
          have h := hξ _ hx; simp only [Option.elim, Function.comp_apply, Set.mem_setOf_eq] at h
          obtain ⟨ν, ξ', ⟨_, hν, rfl, hξ'⟩, heq⟩ := h
          refine ⟨ν, fun _ ↦ hν, ξ', fun _ ↦ ⟨heq, ?_⟩⟩
          intro y hy; cases y
          · exact Set.mem_univ _
          · exact hξ' _ hy
      · refine ⟨⊥, fun hc ↦ False.elim (hx hc), ⟨⊥, fun hc ↦ False.elim (hx hc)⟩⟩
    choose ν hνξ using hν
    have hν x := (hνξ x).1
    have hξ x := (hνξ x).2
    choose ξ' hξ using hξ
    refine ⟨ν, hν, ξ', ?_, ?_⟩
    · intro x hx; exact (hξ x hx).2
    · exact pmf_bind_congr fun x hx ↦ Eq.symm (hξ x hx).1
  · rintro ⟨μ, hμ, ν, hν, ξ, hξ, rfl⟩
    refine ⟨μ, fun x ↦ (ν x).bind (ξ x), ⟨_, hμ, rfl, ?_⟩, rfl⟩
    intro x hx; cases x with
    | bot => exact Set.mem_univ _
    | coe x =>
      simp only [Option.elim, Function.comp_apply, Set.mem_setOf_eq]
      refine ⟨ν x, ξ x, ⟨ν x, hν _ hx, rfl, ?_⟩, rfl⟩
      intro y hy; cases y
      · exact Set.mem_univ ?_
      · exact hξ x hx _ hy

lemma bind_assoc {α β γ : Type} (s : ConvexPowerset α)
    (f : α → ConvexPowerset β) (g : β → ConvexPowerset γ) :
    s >>= f >>= g = s >>= fun (x : α) => f x >>= g := by
  ext1; rw [bind_bind_1, bind_bind_2]; ext d
  refine exists_congr fun μ ↦ and_congr_right fun hμ ↦ ?_
  refine exists_congr fun ν ↦ and_congr_right fun hν ↦ ?_
  constructor
  · intro ⟨ξ, hξ, hd⟩; subst hd; refine ⟨fun _ ↦ ξ, ?_, PMF.bind_bind _ _ _⟩
    intro x hx y hy
    simp only [PMF.mem_support_iff, ne_eq, Set.mem_pi, Set.mem_iUnion, exists_prop,
      Function.comp_apply, forall_exists_index, and_imp] at hξ
    exact hξ y x hx hy
  · intro ⟨ξ, hξ, hd⟩; subst hd
    exact bind_assoc_convex hξ

lemma bind_pure {α : Type} (s : ConvexPowerset α) : s >>= pure = s := by
  simp only [Bind.bind, bind, c_bind, Set.image, pure, Set.mem_iUnion, exists_prop, Prod.exists,
    Function.uncurry_apply_pair]
  ext μ; constructor
  · rintro ⟨ν, f, ⟨_, hν, rfl, h⟩, rfl⟩
    refine s.upcl (fun y ↦ ?_) hν
    conv => rhs; exact PMF.bind_apply _ _ _
    refine
      LE.le.trans (b := ν.bind pure y)
        (le_of_eq ?_)
        (ENNReal.summable.tsum_le_tsum ?_ ENNReal.summable)
    · refine DFunLike.congr_fun ν.bind_pure.symm _
    · intro x; by_cases hx : x ∈ ν.support
      · refine mul_le_mul (le_refl _) ?_ bot_le bot_le
        cases x
        · have hpure : pure (α := WithBot α) = PMF.pure := rfl
          rw [hpure, PMF.pure_apply_of_ne]
          · exact bot_le
          · exact Option.some_ne_none _
        · have hf := h _ hx
          simp only [Option.elim, Function.comp_apply, Set.mem_singleton_iff] at hf; rw [hf]
          exact le_of_eq rfl
      · simp only [PMF.mem_support_iff, ne_eq, Decidable.not_not] at hx
        rw [hx]; simp only [zero_mul, Std.le_refl]
  · intro hμ
    refine ⟨μ, PMF.pure, ⟨μ, hμ, rfl, ?_⟩, μ.bind_pure⟩
    intro x hx; cases x
    · exact Set.mem_univ ?_
    · rfl

instance : LawfulMonad ConvexPowerset :=
  LawfulMonad.mk' ConvexPowerset
    (id_map := ConvexPowerset.bind_pure)
    (pure_bind := ConvexPowerset.pure_bind)
    (bind_assoc := ConvexPowerset.bind_assoc)

end ConvexPowerset
