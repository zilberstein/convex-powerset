import ConvexPowerset.Distr.Basic

-- Inject a Distribution into α-dimensional Euclidean Space
def distr_inj {α : Type} (μ : Distr α) : α → NNReal := ENNReal.toNNReal ∘ μ ∘ WithBot.some

lemma distr_inj_injective {α : Type} : @Function.Injective (Distr α) (α → NNReal) distr_inj := by {
  intro μ ν heq
  have h : ∀ x : α, μ x = ν x := by {
    intro x; unfold distr_inj at heq; simp [distr_coe]
    have hnt (ξ : Distr α) : tsum ξ.val ≠ ⊤ := by simp [HasSum.tsum_eq ξ.2]
    have hbot ξ := ENNReal.ne_top_of_tsum_ne_top (hnt ξ) (WithBot.some x)
    apply (ENNReal.toNNReal_eq_toNNReal_iff' (hbot μ) (hbot ν)).1 (congrFun heq x)
  }
  ext x; match x with
  | ⊥ => simp [prob_bot, tsum_congr h]
  | WithBot.some y => exact h y
}

-- Topology on distributions is the product of Euclidean topologies
instance {α : Type} : TopologicalSpace (Distr α) :=
  TopologicalSpace.induced distr_inj Pi.topologicalSpace

lemma distr_inducing {α : Type} : @Topology.IsInducing (Distr α) (α → NNReal) _ _ distr_inj :=
  (Topology.isInducing_iff (@distr_inj α)).2 (by rfl)

instance {α : Type} : T1Space (Distr α) where
  t1 μ := by {
    apply distr_inducing.isClosed_iff.2
    use {distr_inj μ}; constructor
    · exact isClosed_singleton
    · unfold Set.preimage; ext ν; simp
      refine ⟨?_, congrArg _⟩
      intro h; exact distr_inj_injective h
  }

-- Based on Lemma B.4.2 of MM'05, except we use the fact that { x | f x ≤ r } is closed
-- for any continuous function f instead of using projections
lemma closed_finitary_half_space {α : Type} {e : α → NNReal} {r : NNReal} (s : Finset α) :
  IsClosed { d : α → NNReal | (∑ x ∈ s, d x * e x) ≤ r } := by {
    have hcf : Continuous fun (d : α → NNReal) => ∑ x ∈ s, d x * e x :=
      continuous_finset_sum s fun x _ => Continuous.mul (continuous_apply x) continuous_const
    exact isClosed_le hcf continuous_const
  }

-- Infinitary half-space is equal to the intersection of all related finitary half-spaces
lemma infinitary_half_space_fin_approx {α : Type} (e : α → NNReal) (r : NNReal) :
  { d : α → NNReal | Summable (fun x => d x * e x) ∧ ∑' x, d x * e x ≤ r } =
  ⋂ (s : Finset α), { g : α → NNReal | ∑ x ∈ s, g x * e x ≤ r } := by {
    ext d; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    have he :
      Summable (fun x => d x * e x) ∧ ∑' x, d x * e x ≤ r ↔
      (∑' x, (↑(d x * e x) : ENNReal)) ≤ ↑r := by {
      constructor
      · rintro ⟨hs, hb⟩; rw [← ENNReal.coe_tsum hs]; exact ENNReal.coe_le_coe.2 hb
      · intro hb
        have hs :=
          ENNReal.tsum_coe_ne_top_iff_summable.1
            (lt_top_iff_ne_top.1 (lt_of_le_of_lt hb ENNReal.coe_lt_top))
        rw [← ENNReal.coe_tsum hs] at hb; exact ⟨hs, ENNReal.coe_le_coe.1 hb⟩
    }
    rw [he, ENNReal.tsum_eq_iSup_sum, iSup_le_iff]
    apply forall_congr'; intro s; rw [← ENNReal.coe_finset_sum]; exact ENNReal.coe_le_coe
  }

-- Lemma B.4.3 of MM'05
lemma closed_infinitary_half_space {α : Type} (e : α → NNReal) (r : NNReal) :
  IsClosed { d : α → NNReal | Summable (fun x => d x * e x) ∧ ∑' x, d x * e x ≤ r } := by
    rw [infinitary_half_space_fin_approx]; exact isClosed_iInter closed_finitary_half_space

noncomputable def to_distr {α : Type} (f : α → NNReal) : WithBot α → ENNReal :=
  fun x => match x with
    | none => ↑(1 - ∑' y : α, f y)
    | some y => ↑(f y)

lemma to_distr_sum {α : Type} {f : α → NNReal} (h : Summable f) (h' : tsum f ≤ 1) :
  HasSum (to_distr f) 1 := by {
    rcases h with ⟨r, hr⟩
    let g : α ⊕ PUnit.{1} → ENNReal := to_distr f ∘ (Equiv.optionEquivSumPUnit α).invFun
    have hs : HasSum (g ∘ Sum.inl) r := by {
      have h : g ∘ Sum.inl = (↑) ∘ f := by ext x; simp [to_distr, g]
      rw [h]; exact ENNReal.hasSum_coe.2 hr
    }
    have ht : tsum f = r := (Summable.hasSum_iff ⟨r, hr⟩).1 hr
    have hn : HasSum (g ∘ Sum.inr) (1 - r) := by {
      have h : g ∘ Sum.inr = fun _ => ↑(1 - r) := by ext x; simp [g, to_distr, ht]
      rw [h]; apply hasSum_unique
    }
    have hh := HasSum.sum hs hn
    rw [add_comm,
        ENNReal.sub_add_eq_add_sub _ ENNReal.coe_ne_top,
        ENNReal.add_sub_cancel_right ENNReal.coe_ne_top] at hh
    · simp only [Equiv.invFun_as_coe, g] at hh
      exact (Equiv.hasSum_iff (Equiv.optionEquivSumPUnit α).symm).1 hh
    · rw [← HasSum.tsum_eq hr]; exact ENNReal.coe_le_coe_of_le h'
  }

lemma dist_inj_sum_le_1 {α : Type} {μ : Distr α} :
    Summable (distr_inj μ) ∧ tsum (distr_inj μ) ≤ 1 := by
  rcases μ with ⟨d, hs⟩; simp only [distr_inj]
  have hnt : tsum d ≠ ⊤ := by simp [HasSum.tsum_eq hs]
  have hs₁ : HasSum (ENNReal.toNNReal ∘ d) 1 := by {
    apply (Summable.hasSum_iff (ENNReal.summable_toNNReal_of_tsum_ne_top hnt)).2
    simp only [Function.comp_apply]
    rw [← ENNReal.tsum_toNNReal_eq (ENNReal.ne_top_of_tsum_ne_top hnt)]
    exact (ENNReal.toNNReal_eq_one_iff _).2 (HasSum.tsum_eq hs)
  }
  have hsm : Summable (distr_inj ⟨d, hs⟩) := by {
    apply NNReal.summable_coe.1
    have hs₂ : HasSum (NNReal.toReal ∘ ENNReal.toNNReal ∘ d) 1 := by
      rw [← NNReal.coe_one]; exact NNReal.hasSum_coe.2 hs₁
    apply Summable.comp_injective ⟨1, hs₂⟩ WithBot.coe_injective
  }
  constructor
  · exact hsm
  · rw [← Function.comp_assoc, ← HasSum.tsum_eq hs₁]
    apply Summable.tsum_le_tsum_of_inj some (Option.some_injective α) (by simp) _ hsm ⟨1, hs₁⟩
    simp only [distr_inj, Function.comp_apply]; intro x
    have hx := ENNReal.ne_top_of_tsum_ne_top hnt (WithBot.some x)
    exact (ENNReal.toNNReal_le_toNNReal hx hx).2 (le_refl _)

lemma dist_invert {α : Type} {f : α → NNReal} (h : Summable f) (h' : tsum f ≤ 1) :
    ∃ μ : Distr α, distr_inj μ = f := by
  have hl (x : WithBot α) : 0 ≤ to_distr f x := bot_le
  let μ : Distr α := Subtype.mk (to_distr f) (to_distr_sum h h')
  use μ; ext x; simp [μ, distr_inj, to_distr, distr_coe]

-- The space of distributions can be decomposed as follows:
--   Distr α = [0, 1]^α ∩ { f : α → NNReal | tsum f ≤ 1 }
lemma dist_decomp {α : Type} :
  let e (_ : α): NNReal := 1
  Set.range distr_inj =
  { f : α → NNReal | ∀ x, f x ∈ Set.Icc 0 1 } ∩
  { f : α → NNReal | Summable (fun x => f x * e x) ∧ ∑' x, f x * e x ≤ 1 } := by {
    ext f; constructor
    · rintro ⟨μ, hf⟩; constructor
      · intro x; rw [← hf, distr_inj]; simp only [Function.comp_apply, Set.mem_Icc, zero_le,
          true_and]
        rw [← ENNReal.toNNReal_coe 1]
        apply (ENNReal.toNNReal_le_toNNReal _ _).2
        · exact distr_upper_bound μ x
        · exact ne_top_of_le_ne_top (by simp) (distr_upper_bound μ x)
        · simp
      · simp only [mul_one, ← hf, Set.mem_setOf_eq]; exact dist_inj_sum_le_1
    · simp only [Set.mem_Icc, zero_le, true_and, mul_one, Set.mem_inter_iff, Set.mem_setOf_eq,
        Set.mem_range, distr_inj, and_imp]; intro hlu hs hb; exact dist_invert hs hb
  }

-- Lemma B.4.4 of MM'05
instance {α : Type} : CompactSpace (Distr α) := {
  isCompact_univ := by {
    apply distr_inducing.isCompact_iff.2
    -- Distr α = [0, 1]^α ∩ { f : α → NNReal | tsum f ≤ 1 }
    simp only [Set.image_univ]; rw [dist_decomp]
    -- The set above is the intersection of a compact set and a closed set, so it is compact
    apply IsCompact.inter_right
      -- [0, 1]^α is compact by Tychonoff's Theorem
    · exact isCompact_pi_infinite fun _ => isCompact_Icc
      -- Infinitary half-space is closed
    · exact closed_infinitary_half_space _ 1
  }
}

lemma prob_not_top {α : Type} {μ : Distr α} {x : WithBot α} : μ x ≠ ⊤ := by {
  rw [distr_coe]; apply ENNReal.ne_top_of_tsum_ne_top; simp [HasSum.tsum_eq μ.2]
}

noncomputable def distr_bind {α β : Type} (s : Set (Distr α)) (k : α → Set (Distr β)) :
    Set (Distr β) :=
  Function.uncurry PMF.bind '' ⋃ μ ∈ s, {μ} ×ˢ μ.support.pi (Option.elim · Set.univ k)
--  { f : WithBot α → Distr β | ∀ x : α, ↑x ∈ μ.support → f x ∈ k x },

-- The image of PMF.bind is the same over the following two sets:
--   { (μ, f) | μ ∈ s ∧ ∀ x ∈ μ.support, f x ∈ k x }
--   AND
--   s × { f | ∀ x, f x ∈ k x }
-- Which is useful, since the latter set is compact
lemma distr_bind_image {α β : Type} {s : Set (Distr α)} {k : α → Set (Distr β)}
    (hne : ∀ x, (k x).Nonempty) :
    distr_bind s k =
    Function.uncurry PMF.bind '' (s ×ˢ Set.univ.pi (Option.elim · Set.univ k)) := by
  ext ν; constructor
  · rintro ⟨⟨μ, f⟩, hmem, rfl⟩
    obtain ⟨_, hμ, hmem⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨rfl, hf⟩ := Set.mem_prod.mp hmem; simp only at *; clear hmem
    have h : ∀ (x : WithBot α), ∃ y,
        y ∈ (Option.elim · Set.univ k) x ∧ (x ∈ μ.support → y = f x) := by
      intro x; by_cases h : x ∈ μ.support
      · exact ⟨f x, hf x h, fun _ => rfl⟩
      · match x with
        | ⊥ => refine ⟨PMF.pure ⊥, by simp [Option.elim], fun hc => False.elim (h hc)⟩
        | WithBot.some z =>
          rcases (hne z) with ⟨y, hy⟩
          refine ⟨y, ?_, fun hc => False.elim (h hc)⟩
          simp only [Option.elim]; exact hy
    choose g hg using h
    refine (Set.mem_image _ _ _).mpr ⟨⟨μ, g⟩, ?_, ?_⟩
    · refine Set.mem_prod.mpr ⟨hμ, ?_⟩
      refine Set.mem_pi.mpr ?_; intro x _; exact (hg x).1
    · unfold PMF.bind; ext z; simp only [Function.uncurry_apply_pair, distr_coe]
      refine tsum_congr ?_
      intro x; by_cases hx : x ∈ μ.support
      · rw [(hg x).2 hx]
      · simp only [PMF.mem_support_iff, ne_eq, Decidable.not_not] at hx
        rw [hx]; simp only [zero_mul]
  -- The reverse direction is immediate
  · rintro ⟨⟨μ, f⟩, hmem, rfl⟩
    have ⟨hμ, hf⟩ := Set.mem_prod.mp hmem; simp only at *
    simp only [distr_bind, Set.mem_image, Set.mem_iUnion, exists_prop, Prod.exists,
      Function.uncurry_apply_pair]
    refine ⟨μ, f, ⟨μ, hμ, ?_⟩, rfl⟩
    · refine Set.mem_prod.mpr ⟨Set.mem_singleton _, ?_⟩
      intro x _; exact hf x (Set.mem_univ _)

instance {α : Type} : T2Space (Distr α) where
  t2 := by
      -- Since the distributions are injective, their images under the continuous function distr_inj
      -- are distinct. Therefore, there exist open sets u' and v' in the range of distr_inj such
      -- that x' ∈ u' and y' ∈ v', and u' and v' are disjoint.
    have h_distinct :
        ∀ x y : Distr α, x ≠ y →
        ∃ u' v' : Set (α → NNReal),
        IsOpen u' ∧ IsOpen v' ∧ distr_inj x ∈ u' ∧ distr_inj y ∈ v' ∧ Disjoint u' v' := by
      intros x y hxy
      have h_distinct : distr_inj x ≠ distr_inj y := by
        exact fun h => hxy <| distr_inj_injective h
      rcases t2_separation h_distinct with ⟨ u', v', hu', hv', hxu', hyv', huv' ⟩
      exact ⟨ u', v', hu', hv', hxu', hyv', huv' ⟩
    -- By definition of induced topology, if u' and v' are open in the range of distr_inj, then
    -- their preimages under distr_inj are open in Distr α.
    intros x y hxy
    obtain ⟨u', v', hu', hv', hx', hy', huv'⟩ := h_distinct x y hxy
    use distr_inj ⁻¹' u', distr_inj ⁻¹' v';
    exact ⟨ IsOpen.preimage (continuous_iff_le_induced.mpr fun U a ↦ a) hu',
            IsOpen.preimage (continuous_iff_le_induced.mpr fun U a ↦ a) hv',
            hx',
            hy',
            Set.disjoint_left.mpr fun z hzu hzv => huv'.le_bot ⟨ hzu, hzv ⟩ ⟩


-- Lemma B.3 of Zilberstein et al. POPL'25
lemma bind_closed {α β : Type} {s : Set (Distr α)} {k : α → Set (Distr β)}
  (hcs : IsClosed s)
  (hne : ∀ x : α , (k x).Nonempty)
  (h : ∀ x : α , IsClosed (k x)) :
    IsClosed (distr_bind s k) := by
  -- Move into the product topology NNReal^α
  -- refine distr_inducing.isClosed_iff.2 ⟨distr_inj '' distr_bind s k, ?_⟩
  -- refine ⟨?_, Function.Injective.preimage_image distr_inj_injective _⟩
  rw [distr_bind_image hne] --, ← Set.image_comp]
  -- Any compact set is closed, since we are working in a compact space
  have hx (x : WithBot α) : IsClosed (Option.elim x Set.univ k) := by {
    match x with
    | ⊥ => simp [Option.elim]
    | WithBot.some y => simp only [Option.elim]; exact h y
  }
  have hc : IsCompact (Set.prod s (Set.univ.pi (Option.elim · Set.univ k))) :=
    IsClosed.isCompact (IsClosed.prod hcs (isClosed_set_pi fun x _ => hx x))
  -- The image of a continuous function in a Hausdorff space is closed
  refine IsCompact.isClosed (hc.image ?_)
  sorry

lemma countably_convex {ι α : Type} {s : Set (Distr α)} {ξ : PMF ι} {f : ι → Distr α}
    (h : ∀ i ∈ ξ.support, f i ∈ s)
    (hcv : Convex ENNReal (Subtype.val '' s))
    (hcl : IsClosed s) : PMF.bind ξ f ∈ s := by
  sorry
