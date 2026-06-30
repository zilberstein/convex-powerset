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
      by
        have h_tsum_delta : ∑' y, Δ y = ((μ.bind f) ⊥ - ν₂ ⊥) / (μ.bind f) ⊥ := by
          have h_tsum_delta : ∑' y, (ν₂ (some y) - (μ.bind f) (some y)) = (μ.bind f) ⊥ - ν₂ ⊥ := by
            have hkey :
                ∑' y : β, (ν₂ (some y) - (μ.bind f) (some y)) =
                (∑' y : β, ν₂ (some y)) - (∑' y : β, (μ.bind f) (some y)) := by
              apply tsum_sub';
              · have := prob_not_bot ( μ.bind f );
                exact this.symm ▸ ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top);
              · exact fun y => hle y;
            have hkey : ∑' y : β, ν₂ (some y) = 1 - ν₂ ⊥ := prob_not_bot ν₂
            have hkey : ∑' y : β, (μ.bind f) (some y) = 1 - (μ.bind f) ⊥ := prob_not_bot (μ.bind f)
            simp_all only [Set.mem_pi, PMF.mem_support_iff, ne_eq, PMF.bind_apply,
              ENNReal.tsum_eq_zero, mul_eq_zero, not_forall, not_or, tsub_tsub];
            rw [ ENNReal.sub_eq_of_eq_add ];
            · simp only [ne_eq, ENNReal.add_eq_top, ENNReal.sub_eq_top_iff, ENNReal.one_ne_top,
                false_and, or_false];
              exact ne_of_lt ( lt_of_le_of_lt ( distr_upper_bound _ _ ) ( ENNReal.one_lt_top ) );
            · rw [ ← add_assoc, tsub_add_cancel_of_le ];
              · rw [ add_tsub_cancel_of_le ];
                exact distr_upper_bound (μ.bind f) ⊥
              · exact dist_le_bot_ge hle
          convert congr_arg ( · / ( μ.bind f ) ⊥ ) h_tsum_delta using 1;
          simp +decide only [div_eq_mul_inv];
          exact ENNReal.tsum_mul_right
        have h_sum : (∑' y, ((f x) (some y) + (f x) ⊥ * Δ y)) + (f x) ⊥ * (1 - tsum Δ) = 1 := by
          rw [ ENNReal.tsum_add, ENNReal.tsum_mul_left ];
          rw [ h_tsum_delta, ENNReal.mul_sub ];
          · rw [ add_assoc, add_tsub_cancel_of_le ];
            · convert ( f x ).property.tsum_eq using 1;
              rw [ total_prob ] ; aesop;
            · gcongr;
              rw [ ENNReal.div_le_iff_le_mul ] <;> norm_num;
          · exact fun _ _ => ne_of_lt (lt_of_le_of_lt (distr_upper_bound _ _) (ENNReal.one_lt_top));
        convert h_sum using 1;
        constructor <;> intro h;
        · convert h_sum using 1;
        · convert h using 1;
          constructor <;> intro h;
          · convert h_sum using 1;
          · conv => arg 2; exact h.symm
            convert ENNReal.summable.hasSum using 1;
            symm; exact total_prob _
    ⟩
    refine ⟨g, ⟨μ, hμ, rfl, ?_⟩, ?_⟩
    · intro x hx; cases x with
      | bot => exact Set.mem_univ _
      | coe x =>
          refine (k x).upcl ?_ (h x hx)
          intro y; simp only [DFunLike.coe, self_le_add_right, g]
    · -- Prove `htΔ : tsum Δ = (b - ν₂ ⊥) / b`
      have htΔ : tsum Δ = ((μ.bind f) ⊥ - ν₂ ⊥) / (μ.bind f) ⊥ := by
        have htΔ : tsum (fun y : β => ν₂ y - (μ.bind f) y) = (μ.bind f) ⊥ - ν₂ ⊥ := by
          convert tsum_sub' _ _ using 1;
          · rw [ prob_not_bot ν₂ ];
            conv => rhs; arg 2; exact prob_not_bot _
            rw [ tsub_right_comm, ENNReal.sub_sub_cancel ];
            · rfl
            · exact ENNReal.one_ne_top
            · exact distr_upper_bound _ _
          · conv => lhs; exact prob_not_bot _
            exact ne_of_lt ( lt_of_le_of_lt ( tsub_le_self ) ( ENNReal.one_lt_top ) );
          · exact fun y => hle y;
        rw [ ← htΔ, ENNReal.div_eq_inv_mul ];
        rw [ ← ENNReal.tsum_mul_left ] ; exact tsum_congr fun _ => by rw [ ENNReal.div_eq_inv_mul ]
      refine PMF.ext fun x => ?_;
      rcases x with ( _ | x ) <;> simp_all only [Set.mem_pi, PMF.mem_support_iff, ne_eq,
        PMF.bind_apply];
      · -- Substitute htΔ into the expression for the sum.
        have h_sum :
            ∑' a, μ a * (f a) ⊥ * (1 - tsum Δ) =
            (μ.bind f) ⊥ * (1 - ((μ.bind f) ⊥ - ν₂ ⊥) / (μ.bind f) ⊥) := by
          rw [ ENNReal.tsum_mul_right, PMF.bind_apply ];
          rw [ htΔ ];
        convert h_sum using 1;
        · exact tsum_congr fun x => by rw [ mul_assoc ] ; rfl;
        · rw [ ENNReal.mul_sub, mul_one, ENNReal.mul_div_cancel' ];
          · rw [ ENNReal.sub_sub_cancel ];
            · rfl;
            · exact PMF.apply_ne_top (μ.bind f) ⊥
            · exact dist_le_bot_ge hle
          · grind;
          · exact fun h => absurd h ( prob_not_top );
          · exact fun _ _ =>
              ne_of_lt ( lt_of_le_of_lt ( distr_upper_bound _ _ ) ( ENNReal.one_lt_top ) );
      · convert congrArg₂ ( · + · )
            (show ∑' a : WithBot α, μ a * ( f a ) ↑x = ( μ.bind f ) ↑x from ?_)
            (show ∑' a : WithBot α, μ a * ( f a ⊥ * Δ x ) = ν₂ ↑x - ( μ.bind f ) ↑x from ?_) using 1
        · rw [ ← ENNReal.tsum_add ] ; congr ; ext a ; simp only [g] ; ring_nf;
          erw [ mul_add ] ; ring!;
        · exact Eq.symm (add_tsub_cancel_of_le (hle x))
        · rw [ PMF.bind_apply ];
        · convert congrArg ( · * Δ x )
            ( show ∑' a : WithBot α, μ a * ( f a ) ⊥ = ( μ.bind f ) ⊥ from ?_ ) using 1;
          · simp +decide only [← mul_assoc, ENNReal.tsum_mul_right];
          · rw [ ENNReal.mul_div_cancel' ];
            · grind;
            · exact fun h =>
                absurd h (ne_of_lt (lt_of_le_of_lt (distr_upper_bound _ _) (ENNReal.one_lt_top)));
          · rw [ PMF.bind_apply ]

def bind {α β : Type} (s : ConvexPowerset α) (k : α → ConvexPowerset β) : ConvexPowerset β := {
  set := s.c_bind k
  nonempty := c_bind_nonempty
  convex := c_bind_convex
  closed := c_bind_closed
  upcl := c_bind_upcl
}

instance : Bind ConvexPowerset where
  bind := bind

instance : Monad ConvexPowerset where

end ConvexPowerset
