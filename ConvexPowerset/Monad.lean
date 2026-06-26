import ConvexPowerset.Basic
import ConvexPowerset.Distr.Monad
import ConvexPowerset.Distr.Topology

instance : Pure ConvexPowerset where
  pure x := {
    set := { pure x }
    nonempty := Set.singleton_nonempty _
    convex := by
      conv => arg 2; exact Set.image_singleton
      exact convex_singleton _
    closed := isClosed_singleton
    upcl := by
      intro μ ν hle rfl
      simp only [Set.mem_singleton_iff]; symm; apply proper_dist_maximal _ hle
      refine PMF.pure_apply_of_ne _ _ ?_; symm; exact Option.some_ne_none _
  }

namespace ConvexPowerset

def c_bind {α β : Type} (c : ConvexPowerset α) (k : α → ConvexPowerset β) : Set (Distr β) :=
    Function.uncurry PMF.bind '' ⋃ μ ∈ c, {μ} ×ˢ μ.support.pi (Option.elim · Set.univ (set ∘ k))

lemma c_bind_nonempty {α β : Type} {s : ConvexPowerset α} {k : α → ConvexPowerset β} :
    (s.c_bind k).Nonempty := by
  obtain ⟨μ, hμ⟩ := s.nonempty
  let g t := Option.elim t Set.univ (ConvexPowerset.set ∘ k)
  have hf : (μ.support.pi g).Nonempty := by {
    apply (Set.pi_nonempty_iff (s := μ.support) (t := g)).2
    intro x; match x with
    | ⊥ => use ⊥; intro hb; simp [g, Option.elim]
    | WithBot.some y =>
        have ⟨ν, hν⟩ := (k y).nonempty
        use ν; intro hy; exact hν
  }
  rcases hf with ⟨f, hf⟩; use (PMF.bind μ f)
  refine (Set.mem_image _ _ _).mpr ⟨⟨μ, f⟩, ?_, rfl⟩
  · simp only [Set.mem_iUnion, exists_prop]
    exact ⟨μ, hμ, rfl, hf⟩

-- Lemma B.1 from. POPL '25
lemma countably_convex' {ι α : Type} {s : ConvexPowerset α} {ξ : PMF ι} {f : ι → Distr α}
    (h : ∀ i ∈ ξ.support, f i ∈ s) : PMF.bind ξ f ∈ s := countably_convex h s.convex s.closed

namespace Distr

lemma convex_hassum_1 {α : Type} {d₁ d₂ : α → ENNReal} {p q : ENNReal}
    (h₁ : HasSum d₁ 1) (h₂ : HasSum d₂ 1) (h : p + q = 1) : HasSum (p • d₁ + q • d₂) 1 := by
  have hr (r : ENNReal) : r = r • 1 := by simp
  rw [← h]; refine HasSum.add ?_ ?_
  · nth_rewrite 2 [hr p]; refine (Summable.hasSum_iff ENNReal.summable).mpr ?_
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    rw [ENNReal.tsum_mul_left, HasSum.tsum_eq h₁]; simp only [mul_one]
  · nth_rewrite 2 [hr q]; refine (Summable.hasSum_iff ENNReal.summable).mpr ?_
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    rw [ENNReal.tsum_mul_left, HasSum.tsum_eq h₂]; simp only [mul_one]

noncomputable def convex_sum {α : Type} (μ ν : Distr α) (p q : ENNReal) (h : p + q = 1) : Distr α :=
  ⟨ p • μ.val + q • ν.val, convex_hassum_1 μ.property ν.property h ⟩

lemma convex_sum_0_left {α : Type} {μ ν : Distr α} {q : ENNReal} {h : 0 + q = 1} :
    convex_sum μ ν 0 q h = ν := by
  unfold convex_sum; simp only [zero_add] at h; subst h; simp

lemma convex_sum_0_right {α : Type} {μ ν : Distr α} {p : ENNReal} {h : p + 0 = 1} :
    convex_sum μ ν p 0 h = μ := by
  unfold convex_sum; simp only [add_zero] at h; subst h; simp

end Distr

-- Lemma B.1 from POPL '25
lemma c_bind_convex {α β : Type} {s : ConvexPowerset α} {k : α → ConvexPowerset β} :
    Convex ENNReal (Subtype.val '' s.c_bind k) := by
  simp only [Set.image, c_bind, Set.mem_iUnion, exists_prop, Prod.exists,
    Function.uncurry_apply_pair, Subtype.exists, exists_and_right, exists_eq_right]
  rintro d₁ ⟨hs₁, μ, f, ⟨_, hμ, rfl, hf⟩, heq₁⟩
  rintro d₂ ⟨hs₂, ν, g, ⟨_, hν, rfl, hg⟩, heq₂⟩
  intro p q hp hq hsum
  let ξ := Distr.convex_sum μ ν p q hsum
  have hdsum x (h : x ∈ ξ.support) : (p * μ x / ξ x) + (q * ν x / ξ x) = 1 := by
    simp only [DFunLike.coe, Distr.convex_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ξ]
    rw [← ENNReal.add_div]
    refine ENNReal.div_self h (ne_top_of_le_ne_top ENNReal.one_ne_top ?_)
    nth_rewrite 3 [← hsum]; refine add_le_add ?_ ?_
    · refine LE.le.trans (mul_le_mul (le_refl _) (distr_upper_bound _ _) bot_le bot_le) ?_; simp
    · refine LE.le.trans (mul_le_mul (le_refl _) (distr_upper_bound _ _) bot_le bot_le) ?_; simp
  let d x (h : x ∈ ξ.support) := Distr.convex_sum (f x) (g x) _ _ (hdsum x h)
  have hr x : ∃ d', ∀ h : x ∈ ξ.support, d' = d x h := by
    by_cases hx : x ∈ ξ.support
    · exact ⟨d x hx, fun _ ↦ rfl⟩
    · exact ⟨⊥, fun hc ↦ False.elim (hx hc)⟩
  choose f' hf' using hr
  refine ⟨?_, ξ, f', ⟨ξ, ?_, Set.mem_singleton _, ?_⟩, ?_⟩
  · exact Distr.convex_hassum_1 hs₁ hs₂ hsum
  · have h1 := (Set.mem_image Subtype.val _ _).mpr ⟨μ, hμ, rfl⟩
    have h2 := (Set.mem_image Subtype.val _ _).mpr ⟨ν, hν, rfl⟩
    have h := s.convex h1 h2 hp hq hsum
    obtain ⟨ξ', hξ, heq⟩ := (Set.mem_image Subtype.val s.set ξ.val).mp h
    apply Subtype.ext at heq; subst heq; exact hξ
  · intro x hx; simp only; rw [hf' x hx]; cases x with
    | bot => exact Set.mem_univ _
    | coe x =>
      simp only [Option.elim, Function.comp_apply]
      simp only [Distr.convex_sum, PMF.mem_support_iff, DFunLike.coe, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, ne_eq, add_eq_zero, mul_eq_zero, not_and, not_or, ξ] at hx
      by_cases hμx : μ x = 0
      · unfold d; simp only [hμx, mul_zero, ENNReal.zero_div]
        have hνx := (hx (Or.inr hμx)).2
        rw [Distr.convex_sum_0_left]; exact hg x hνx
      · by_cases hνx : ν x = 0
        · unfold d; simp only [hνx, mul_zero, ENNReal.zero_div]; rw [Distr.convex_sum_0_right]
          exact hf x hμx
        · unfold d; unfold Distr.convex_sum
          have h1 := (Set.mem_image Subtype.val _ _).mpr ⟨f x, hf _ hμx, rfl⟩
          have h2 := (Set.mem_image Subtype.val _ _).mpr ⟨g x, hg _ hνx, rfl⟩
          have h := (k x).convex h1 h2 bot_le bot_le (hdsum x (by {
            simp only [Distr.convex_sum, PMF.mem_support_iff, DFunLike.coe, Pi.add_apply,
              Pi.smul_apply, smul_eq_mul, ne_eq, add_eq_zero, mul_eq_zero, not_and, not_or, ξ]
            exact hx
          }))
          obtain ⟨ξ', hξ, heq⟩ := (Set.mem_image Subtype.val _ _).mp h
          simp_rw [← heq]; exact hξ
  · ext z; refine (PMF.bind_apply _ _ _).trans ?_
    have h1 := congrArg Subtype.val heq₁; simp only at h1; subst h1
    have h2 := congrArg Subtype.val heq₂; simp only at h2; subst h2
    simp only [DFunLike.coe, PMF.bind, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun x ↦ ?_; by_cases hξ : x ∈ ξ.support
    · rw [hf' _ hξ]; simp only [Distr.convex_sum, DFunLike.coe, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, d]
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      rw [mul_assoc, mul_assoc, mul_assoc, ← mul_add, ← mul_assoc]
      rw [ENNReal.mul_inv_cancel]
      · simp [mul_assoc]
      · exact hξ
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top (distr_upper_bound _ _)
    · simp only [PMF.mem_support_iff, ne_eq, Decidable.not_not] at hξ; rw [distr_coe.symm.trans hξ]
      simp only [DFunLike.coe, Distr.convex_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        add_eq_zero, mul_eq_zero, ξ] at hξ
      rcases hξ with ⟨hp | hμx, hq | hνx⟩
      · subst hp; subst hq; simp
      · subst hp; rw [hνx]; simp
      · rw [hμx]; subst hq ; simp
      · rw [hμx, hνx]; simp

-- For some reason, the Mathlib version is only for sums indexed by ℕ
theorem tsum_sub' {ι : Type} {f : ι → ENNReal} {g : ι → ENNReal} (h₁ : ∑' i, g i ≠ ⊤) (h₂ : g ≤ f) :
    ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i :=
  have : ∀ i, f i - g i + g i = f i := fun i => tsub_add_cancel_of_le (h₂ i)
  ENNReal.eq_sub_of_add_eq h₁ <| by simp only [← ENNReal.tsum_add, this]

lemma bind_toReal {α β : Type} {μ : Distr α} {f : WithBot α → Distr β} {y : WithBot β} :
    (μ.bind f y).toReal = ∑' x, (μ x).toReal * (f x y).toReal := by
  rw [PMF.bind_apply]; refine (ENNReal.tsum_toReal_eq ?_).trans ?_
  · intro _; refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    exact mul_le_one₀ (distr_upper_bound _ _) bot_le (distr_upper_bound _ _)
  · refine tsum_congr fun x ↦ ?_; simp only [ENNReal.toReal_mul]; rfl

lemma c_bind_closed {α β : Type} {s : ConvexPowerset α} {k : α → ConvexPowerset β} :
    IsClosed (s.c_bind k) :=
  bind_closed s.closed
    (fun x ↦ (k x).nonempty)
    (fun x ↦ (k x).closed)

lemma c_bind_upcl {α β : Type} {s : ConvexPowerset α} {k : α → ConvexPowerset β} :
    IsUpperSet (s.c_bind k) := by
  simp only [c_bind, Set.image, Set.mem_iUnion, exists_prop, Prod.exists,
    Function.uncurry_apply_pair, isUpperSet_setOf]
  intro ν₁ ν₂ hle
  rintro ⟨μ, f, ⟨_, hμ, rfl, h⟩, rfl⟩
  refine ⟨μ, ?_⟩
  by_cases h0 : μ.bind f ⊥ = 0
  · exact ⟨f, ⟨μ, hμ, rfl, h⟩, proper_dist_maximal h0 hle⟩
  · -- Δ y is the amout of missing probability mass for y, scaled by the amount of unassigned mass
    let Δ (y : β) := (ν₂ y - μ.bind f y) / μ.bind f ⊥
    let g x : Distr β :=
      ⟨ fun y ↦ match y with
        | some y => f x y + f x ⊥ * Δ y
        | none => f x ⊥ * (1 - tsum Δ),
      by sorry
      ⟩
    refine ⟨g, ⟨μ, hμ, rfl, ?_⟩, ?_⟩
    · intro x hx; cases x with
      | bot => exact Set.mem_univ _
      | coe x =>
          refine (k x).upcl ?_ (h x hx)
          intro y; simp only [DFunLike.coe, self_le_add_right, g]
    · sorry

instance : Bind ConvexPowerset where
  bind {α β : Type} (s : ConvexPowerset α) (k : α → ConvexPowerset β) := {
    set := s.c_bind k
    nonempty := c_bind_nonempty
    convex := c_bind_convex
    closed := c_bind_closed
    upcl := c_bind_upcl
  }

instance : Monad ConvexPowerset where

lemma pure_bind {α β : Type} (x : α) (k : α → ConvexPowerset β) : pure x >>= k = k x := by
  simp only [bind, c_bind, pure]
  ext d; constructor
  · rintro ⟨⟨μ, f⟩, ⟨_, ⟨_, rfl⟩, pp, ⟨rfl, rfl⟩, rfl, hf⟩, rfl⟩
    simp only [Function.uncurry, PMF.pure_bind]
    refine hf x ?_
    simp only [PMF.support_pure, Set.mem_singleton_iff]; rfl
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
    simp only [Set.mem_image, Set.mem_iUnion, exists_prop, Prod.exists, Function.uncurry_apply_pair]
    refine ⟨PMF.pure x, g, ⟨_, rfl, rfl, ?_⟩, ?_⟩
    · simp only [PMF.support_pure, Set.singleton_pi, Set.mem_preimage, Function.eval, g]
      exact (hf x).2
    · rw [PMF.pure_bind]; simp only [g]; exact (hf x).1 rfl

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
  simp only [bind, c_bind, Set.image, Set.mem_iUnion, exists_prop, Prod.exists,
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
  simp only [bind, c_bind, Set.image, Set.mem_iUnion, exists_prop, Prod.exists,
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
  simp only [bind, c_bind, Set.image, pure, Set.mem_iUnion, exists_prop, Prod.exists,
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

instance : LawfulMonad ConvexPowerset where
  map_const := by intro α β; simp [Functor.mapConst, Functor.map]
  pure_bind := ConvexPowerset.pure_bind
  bind_assoc := ConvexPowerset.bind_assoc
  id_map := ConvexPowerset.bind_pure
  seqLeft_eq := sorry
  seqRight_eq := sorry
  bind_pure_comp := sorry
  pure_seq := sorry
  bind_map := sorry

end ConvexPowerset
