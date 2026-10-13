/-
Copyright (c) 2026 Noam Zilberstein. All rights reserved.
Authors: Noam Zilberstein
-/
import ConvexPowerset.Monad

namespace ConvexPowerset

private lemma bind_apply_dd {α β : Type} (μ : Distr α) (f : WithBot α → Distr β) (y : WithBot β) :
    PMF.bind μ f y = ∑' x, μ x * f x y := PMF.bind_apply μ f y

private lemma bind_apply_dp {α β : Type} (μ : Distr α) (f : WithBot α → PMF (WithBot β))
    (y : WithBot β) : PMF.bind μ f y = ∑' x, μ x * f x y := PMF.bind_apply μ f y

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
    let g : WithBot α → Distr β := fun z => match z with
      | none => ⊥
      | some z' => f z'
    refine mem_bind.mpr ⟨PMF.pure x, Set.mem_singleton _, g, ?_, ?_⟩
    · apply Set.mem_pi.mpr; intro y hy
      rcases (PMF.mem_support_pure_iff _ _).mp hy with rfl
      simp only [Option.elim, Function.comp_apply, g]
      exact (hf x).2
    · refine Eq.symm ((PMF.pure_bind _ g).trans ?_); exact (hf x).1 rfl

noncomputable def pmf_with_bot {α β : Type} (f : α → Distr β) (x : WithBot α) : Distr β :=
  match x with
  | ⊥ => ⊥
  | WithBot.some y => f y

lemma with_bot_bind {α β γ : Type} {f : α → Distr β} {g : β → Distr γ} :
    (pmf_with_bot fun x => PMF.bind (f x) (pmf_with_bot g)) =
    fun x => PMF.bind (pmf_with_bot f x) (pmf_with_bot g) := by
  unfold pmf_with_bot; ext x y; cases x with
  | bot =>
    show (⊥ : Distr γ) y = PMF.bind (PMF.pure (⊥ : WithBot β)) _ y
    refine Eq.symm ((DFunLike.congr_fun (PMF.pure_bind (⊥ : WithBot β) _) y).trans ?_); rfl
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
    unfold p; rw [bind_apply_dd μ ν y]; refine (Summable.hasSum_iff ENNReal.summable).mpr ?_
    rw [tsum_congr fun _ ↦ ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
    refine ENNReal.inv_mul_cancel ?_ ?_
    · exact hy
    · intro hc; have h := HasSum.tsum_eq (μ.bind ν).property
      simp only [PMF.bind] at h
      refine False.elim (ne_top_of_le_ne_top ENNReal.one_ne_top ?_ hc); rw [← h]
      exact ENNReal.le_tsum (f := fun b => ∑' a, μ a * (ν a) b) y
  })
  have hf : ∀ y, ∃ ξ', ∀ hy : y ∈ (μ.bind ν).support, ξ' = f y hy := by
    intro y; by_cases hy : y ∈ (μ.bind ν).support
    · exact ⟨f y hy, fun _ ↦ rfl⟩
    · exact ⟨⊥, fun hc ↦ False.elim (hy hc)⟩
  choose ξ' hξ' using hf
  refine ⟨fun y ↦ PMF.bind (ξ' y) fun x ↦ ξ x y, ?_, ?_⟩
  · intro y; simp only [PMF.mem_support_iff, ne_eq, Set.mem_iUnion, exists_prop,
      Function.comp_apply, forall_exists_index, and_imp]; intro x hx hy
    have hy' : y ∈ (μ.bind ν).support := (PMF.mem_support_bind_iff _ _ _).mpr ⟨x, hx, hy⟩
    refine countably_convex' ?_
    intro x'; rw [hξ' y hy']; unfold f; unfold p; intro hp
    refine h x' ?_ y ?_
    · intro hxx; apply hp; simp only [DFunLike.coe, ENNReal.div_eq_zero_iff, mul_eq_zero]
      left; left; exact hxx
    · intro hy; apply hp; simp only [DFunLike.coe, ENNReal.div_eq_zero_iff, mul_eq_zero]
      left; right; exact hy
  · ext z; rw [PMF.bind_bind μ ν]; simp only [bind_apply_dd, bind_apply_dp, PMF.bind_apply]
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
          have hy' : y ∈ (μ.bind ν).support := (PMF.mem_support_bind_iff _ _ _).mpr ⟨x', hx', hy'⟩
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
        simp only [PMF.bind]; exact ENNReal.le_tsum (f := fun b => ∑' a, μ a * (ν a) b) y

lemma bind_union {α β : Type} (s : ConvexPowerset α) (f : α → ConvexPowerset β) :
    set (bind s f) =
    ⋃ μ ∈ s, PMF.bind μ '' (μ.support.pi (Option.elim · Set.univ (set ∘ f))) := by
  simp only [bind, c_bind]; ext ν
  constructor
  · rintro ⟨⟨p, g⟩, hmem, rfl⟩
    obtain ⟨_, hp, hmem⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨rfl, hsupp⟩ := Set.mem_prod.mp hmem
    exact Set.mem_iUnion₂.mpr ⟨p, hp, ⟨g, hsupp, rfl⟩⟩
  · intro hν
    obtain ⟨μ, hμ, g, hg, rfl⟩ := Set.mem_iUnion₂.mp hν
    exact ⟨(μ, g), Set.mem_iUnion₂.mpr ⟨μ, hμ, Set.mem_prod.mpr ⟨rfl, hg⟩⟩, rfl⟩

lemma bind_bind_1 {α β γ : Type} (s : ConvexPowerset α) (f : α → ConvexPowerset β)
    (g : β → ConvexPowerset γ) :
    set (s >>= f >>= g) =
    { d | ∃ μ  ∈ s,
          ∃ ν ∈ μ.support.pi (set ∘ with_bot f),
          ∃ ξ ∈ (⋃ x ∈ μ.support, (ν x).support).pi (set ∘ with_bot g),
            d = PMF.bind (PMF.bind μ ν) ξ } := by
  ext d; constructor
  · intro hd
    obtain ⟨ν', hν', g', hg, rfl⟩ := mem_bind.mp hd
    obtain ⟨μ, hμ, f', hf, rfl⟩ := mem_bind.mp hν'
    refine ⟨μ, hμ, f', ?_, g', ?_, rfl⟩
    · intro x hx; cases x with
      | bot => exact Set.mem_univ _
      | coe x => exact hf _ hx
    · intro y hy; cases y with
      | bot => exact Set.mem_univ _
      | coe y =>
        obtain ⟨x, hx, hxy⟩ := Set.mem_iUnion₂.mp hy
        exact hg _ ((PMF.mem_support_bind_iff _ _ _).mpr ⟨x, hx, hxy⟩)
  · rintro ⟨μ, hμ, ν, hf, ξ, hg, rfl⟩
    refine mem_bind.mpr ⟨μ.bind ν, mem_bind.mpr ⟨μ, hμ, ν, ?_, rfl⟩, ξ, ?_, rfl⟩
    · intro x hx; cases x with
      | bot => exact Set.mem_univ _
      | coe x => exact hf _ hx
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := (PMF.mem_support_bind_iff _ _ _).mp hy
      cases y with
      | bot => exact Set.mem_univ _
      | coe y => exact hg _ (Set.mem_iUnion₂.mpr ⟨x, hx, hxy⟩)

lemma bind_bind_2 {α β γ : Type} (s : ConvexPowerset α) (f : α → ConvexPowerset β)
    (g : β → ConvexPowerset γ) :
    (s >>= fun (x : α) => f x >>= g).set =
    { d | ∃ μ  ∈ s,
          ∃ ν ∈ μ.support.pi (set ∘ with_bot f),
          ∃ ξ : WithBot α → WithBot β → Distr γ,
            (∀ x ∈ μ.support, ∀ y ∈ (ν x).support, ξ x y ∈ with_bot g y) ∧
            d = PMF.bind μ fun x ↦ PMF.bind (ν x) (ξ x) } := by
  ext d; constructor
  · intro hd
    obtain ⟨μ, hμ, ξ, hξ, rfl⟩ := mem_bind.mp hd
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
          · exact (PMF.pure_bind _ _).trans (if_pos rfl)
          · intro y hy; obtain rfl := (PMF.mem_support_pure_iff _ _).mp hy
            exact Set.mem_univ _
        | coe x =>
          obtain ⟨ν, hν, ξ', hξ', heq⟩ := mem_bind.mp (hξ _ hx)
          refine ⟨ν, fun _ ↦ hν, ξ', fun _ ↦ ⟨heq.symm, ?_⟩⟩
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
    refine mem_bind.mpr ⟨μ, hμ, fun x ↦ (ν x).bind (ξ x), ?_, rfl⟩
    intro x hx; cases x with
    | bot => exact Set.mem_univ _
    | coe x =>
      refine mem_bind.mpr ⟨ν x, hν _ hx, ξ x, ?_, rfl⟩
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
  ext μ; constructor
  · intro hμ'
    obtain ⟨ν, hν, f, h, rfl⟩ := mem_bind.mp hμ'
    refine s.upcl (fun y ↦ ?_) hν
    refine le_of_le_of_eq ?_ (bind_apply_dd ν f y).symm
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
      · replace hx : ν x = 0 := by by_contra hc; exact hx hc
        exact le_of_eq_of_le (mul_eq_zero_of_left hx _) bot_le
  · intro hμ
    refine mem_bind.mpr ⟨μ, hμ, PMF.pure, ?_, μ.bind_pure.symm⟩
    intro x hx; cases x
    · exact Set.mem_univ ?_
    · rfl

instance : LawfulMonad ConvexPowerset :=
  LawfulMonad.mk' ConvexPowerset
    (id_map := ConvexPowerset.bind_pure)
    (pure_bind := ConvexPowerset.pure_bind)
    (bind_assoc := ConvexPowerset.bind_assoc)

end ConvexPowerset
