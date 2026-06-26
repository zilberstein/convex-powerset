import Mathlib.Algebra.BigOperators.Field

import ConvexPowerset.Distr.Basic

-- Inject a Distribution into α-dimensional Euclidean Space
def distr_inj {α : Type} (μ : Distr α) : α → NNReal := ENNReal.toNNReal ∘ μ ∘ WithBot.some

lemma distr_inj_injective {α : Type} : @Function.Injective (Distr α) (α → NNReal) distr_inj := by {
  intro μ ν heq
  have h : ∀ x : α, μ x = ν x := by {
    intro x; unfold distr_inj at heq; simp only [distr_coe]
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
    · unfold Set.preimage; ext ν; simp only [Set.mem_singleton_iff, Set.mem_setOf_eq]
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

open Filter Topology in
/-- General topology: if `ν` is a cluster point of the image of a compact set `K` under any map
`Φ`, then there is an ultrafilter `W` and a point `p ∈ K` with `W → p` and `Φ` tending to `ν`
along `W`.  (`Φ` need not be continuous.) -/
lemma exists_ultrafilter_of_clusterPt_image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (Φ : X → Y) (K : Set X) (hcK : IsCompact K) (ν : Y)
    (hν : ClusterPt ν (𝓟 (Φ '' K))) :
    ∃ (W : Ultrafilter X) (p : X), p ∈ K ∧ ↑W ≤ 𝓝 p ∧ Tendsto Φ W (𝓝 ν) := by
  have hne : (𝓝 ν ⊓ 𝓟 (Φ '' K)).NeBot := hν
  set u : Ultrafilter Y := Ultrafilter.of (𝓝 ν ⊓ 𝓟 (Φ '' K))
  have hule : ↑u ≤ 𝓝 ν ⊓ 𝓟 (Φ '' K) := Ultrafilter.of_le _
  have huC : Φ '' K ∈ u := hule.trans inf_le_right (by simp)
  have huν : ↑u ≤ 𝓝 ν := hule.trans inf_le_left
  have hGne : (Filter.comap Φ ↑u ⊓ 𝓟 K).NeBot :=
    Ultrafilter.comap_inf_principal_neBot_of_image_mem huC
  obtain ⟨p, hpK, hcp⟩ := hcK (f := Filter.comap Φ ↑u ⊓ 𝓟 K) inf_le_right
  haveI hcp' : (𝓝 p ⊓ (Filter.comap Φ ↑u ⊓ 𝓟 K)).NeBot := hcp
  set W : Ultrafilter X := Ultrafilter.of (𝓝 p ⊓ (Filter.comap Φ ↑u ⊓ 𝓟 K))
  have hWle : ↑W ≤ 𝓝 p ⊓ (Filter.comap Φ ↑u ⊓ 𝓟 K) := Ultrafilter.of_le _
  refine ⟨W, p, hpK, hWle.trans inf_le_left, ?_⟩
  have hWcomap : ↑W ≤ Filter.comap Φ ↑u := hWle.trans (le_trans inf_le_right inf_le_left)
  calc map Φ ↑W ≤ map Φ (Filter.comap Φ ↑u) := map_mono hWcomap
    _ ≤ ↑u := map_comap_le
    _ ≤ 𝓝 ν := huν

open Filter Topology in
/-- If a family of distributions `d w` converges to `D` in the (induced/weak) topology, then each
`some`-coordinate converges in `ℝ≥0∞`. -/
lemma distr_tendsto_coord {Ω γ : Type} {l : Filter Ω} {d : Ω → Distr γ} {D : Distr γ}
    (hd : Tendsto d l (𝓝 D)) (y : γ) :
    Tendsto (fun w => (d w) (some y)) l (𝓝 (D (some y))) := by
  convert
    (ENNReal.continuous_coe.tendsto ( D ( some y ) |> ENNReal.toNNReal)).comp
      ?_ (f := fun w => ( d w ) ( some y ) |> ENNReal.toNNReal)
  · simp only [Function.comp_apply, ENNReal.coe_toNNReal prob_not_top]
  · symm; exact ENNReal.coe_toNNReal prob_not_top
  · convert Tendsto.comp ( continuous_apply y |> Continuous.tendsto <| _ )
      ( distr_inducing.continuous.tendsto _ |> Filter.Tendsto.comp <| hd ) using 1;

open Filter Topology in
/-- `some`-coordinate lower bound for the limit of a bind: the non-escaping contribution `P` is
dominated by `ν` on every `some` coordinate. -/
lemma bind_limit_some {α β Ω : Type} {l : Filter Ω} [l.NeBot]
    {F : Ω → Distr α} {G : Ω → WithBot α → Distr β} {μ : Distr α}
    {g : WithBot α → Distr β} {ν : Distr β}
    (hμ : ∀ a : α, Tendsto (fun w => (F w) (some a)) l (𝓝 (μ (some a))))
    (hg : ∀ (a : α) (y : β), Tendsto (fun w => (G w (some a)) (some y)) l (𝓝 (g (some a) (some y))))
    (hbind : ∀ y : β, Tendsto (fun w => (PMF.bind (F w) (G w)) (some y)) l (𝓝 (ν (some y))))
    (y : β) :
    (∑' a : α, μ (some a) * g (some a) (some y)) ≤ ν (some y) := by
  rw [ ENNReal.tsum_eq_iSup_sum ];
  refine ciSup_le ?_;
  intro T
  have h_sum_le :
      ∀ w, ∑ a ∈ T, (F w) (some a) * (G w (some a)) (some y) ≤ (PMF.bind (F w) (G w)) (some y) := by
    intro w
    have h_le :
        ∑ a ∈ T, (F w) (some a) * (G w (some a)) (some y) ≤ ∑' a, (F w) a * (G w a) (some y) := by
      refine le_trans ?_ ( ENNReal.sum_le_tsum ?_ ); swap
      · exact T.map ( Function.Embedding.some );
      · simp only [Finset.sum_map]; rfl;
    convert h_le using 1;
  refine le_of_tendsto_of_tendsto' ( tendsto_finset_sum _ fun a _ =>
    ENNReal.Tendsto.mul ( hμ a ) ?_ ( hg a y ) ?_ ) ( hbind y ) h_sum_le;
  all_goals exact Or.inr ( prob_not_top )
/-
Tail bound: if `c ≤ b` pointwise and `∑' b` is finite, the whole sum of `c` is at most its
finite partial sum over `S` plus the `b`-tail `∑' b - ∑_S b`.
-/
lemma tsum_le_sum_add_tail {ι : Type} {b c : ι → ENNReal} (S : Finset ι)
    (hbc : ∀ a, c a ≤ b a) (hb : (∑' a, b a) ≠ ⊤) :
    (∑' a, c a) ≤ (∑ a ∈ S, c a) + ((∑' a, b a) - ∑ a ∈ S, b a) := by
  have h_split : (∑' a, c a) = (∑ a ∈ S, c a) + (∑' a : {a : ι | a ∉ S}, c a) := by
    rw [ ← ENNReal.summable.tsum_add_tsum_compl ];
    any_goals exact SetLike.coe S;
    · simp +decide only [SetLike.coe_sort_coe, tsum_fintype, Finset.univ_eq_attach, Set.coe_setOf,
       Set.mem_setOf_eq];
      refine congrArg₂ ( · + · ) ?_ ?_;
      · conv_rhs => rw [ ← Finset.sum_attach ] ;
      · convert rfl;
    · simp +zetaDelta at *;
  have h_tail_le : (∑' a : {a : ι | a ∉ S}, c a) ≤ (∑' a : {a : ι | a ∉ S}, b a) := by
    exact ENNReal.tsum_le_tsum fun x => hbc _;
  have h_tail_sum : (∑' a, b a) = (∑ a ∈ S, b a) + (∑' a : {a : ι | a ∉ S}, b a) := by
    rw [ ← ENNReal.sum_add_tsum_compl ];
    congr! 2;
  rw [ h_split, h_tail_sum, ENNReal.add_sub_cancel_left ];
  · gcongr;
  · exact ne_of_lt ( lt_of_le_of_lt ( ENNReal.sum_le_tsum _ ) ( lt_top_iff_ne_top.mpr hb ) )

open Filter Topology in
/-- Escaping-mass bound: the total `some`-mass of `ν` exceeds the non-escaping `some`-mass by at
most `μ ⊥` (the mass that escapes to `⊥` in the source).  Proven by a double finite-subset
argument, bounding the escaping tail by the omitted source mass (each `G w x` is a probability). -/
lemma bind_limit_sumR {α β Ω : Type} {l : Filter Ω} [l.NeBot]
    {F : Ω → Distr α} {G : Ω → WithBot α → Distr β} {μ : Distr α}
    {g : WithBot α → Distr β} {ν : Distr β}
    (hμ : ∀ a : α, Tendsto (fun w => (F w) (some a)) l (𝓝 (μ (some a))))
    (hg : ∀ (a : α) (y : β), Tendsto (fun w => (G w (some a)) (some y)) l (𝓝 (g (some a) (some y))))
    (hbind : ∀ y : β, Tendsto (fun w => (PMF.bind (F w) (G w)) (some y)) l (𝓝 (ν (some y)))) :
    (∑' y : β, ν (some y)) ≤ μ ⊥ + ∑' y : β, (∑' a : α, μ (some a) * g (some a) (some y)) := by
  have h_tsum :
      ∀ (Tβ : Finset β), (∑ y ∈ Tβ, ν (some y)) ≤ μ ⊥ +
        ∑' a, μ (some a) * (∑ y ∈ Tβ, g (some a) (some y)) := by
    intro Tβ
    have h_finite :
        ∀ (Tα : Finset α), ∑ y ∈ Tβ, ν (some y) ≤
          (1 - ∑ a ∈ Tα, μ (some a)) +
            ∑ a ∈ Tα, μ (some a) * (∑ y ∈ Tβ, (g (some a)) (some y)) := by
      intro Tα
      have h_finite :
          ∀ w, ∑ y ∈ Tβ, (PMF.bind (F w) (G w)) (some y) ≤
            (∑ a ∈ Tα, (F w) (some a) * (∑ y ∈ Tβ, (G w (some a)) (some y))) +
              (1 - ∑ a ∈ Tα, (F w) (some a)) := by
        intro w;
        have h_tail_bound :
            ∑ y ∈ Tβ, (PMF.bind (F w) (G w)) (some y) =
            ∑' a, (F w) a * (∑ y ∈ Tβ, (G w a) (some y)) := by
          simp only [PMF.bind_apply, Finset.mul_sum _ _ _];
          symm; exact Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable
        convert tsum_le_sum_add_tail ( Tα.map ( Function.Embedding.some ) ) _ _ using 1 <;>
          norm_num [ Finset.sum_map ];
        rotate_left;
        · use fun a => ( F w ) a;
        · intro a
          have h_sum_le_one : ∑ y ∈ Tβ, (G w a) (some y) ≤ 1 := by
            have := ( G w a ).2;
            convert sum_le_hasSum _ _ this using 1;
            rotate_left;
            · exact Tβ.map ( Function.Embedding.some );
            · exact fun _ _ => zero_le _;
            · simp +decide [ Finset.sum_map ];
              rfl
          exact mul_le_of_le_one_right (by
          exact zero_le _) h_sum_le_one;
        · exact HasSum.tsum_eq ( F w |>.2 ) ▸ by norm_num;
        · rw [ show ( ∑' a : Option α, ( F w ) a ) = 1 from ?_ ];
          convert HasSum.tsum_eq ( F w |>.2 ) using 1
      generalize_proofs at *; (
      have h_limit :
          Filter.Tendsto (fun w => ∑ y ∈ Tβ, (PMF.bind (F w) (G w)) (some y)) l
            (𝓝 (∑ y ∈ Tβ, ν (some y))) := by
        exact tendsto_finset_sum _ fun y hy => hbind y
      generalize_proofs at *; (
      have h_limit :
          Filter.Tendsto (fun w => ∑ a ∈ Tα, (F w) (some a) * (∑ y ∈ Tβ, (G w (some a)) (some y))) l
            (𝓝 (∑ a ∈ Tα, μ (some a) * (∑ y ∈ Tβ, (g (some a)) (some y)))) := by
        refine tendsto_finset_sum _ fun a ha => ?_;
        refine ENNReal.Tendsto.mul ?_ ?_ ?_ ?_ <;> norm_num [ hμ, hg ];
        · exact Or.inr fun x hx => prob_not_top;
        · exact tendsto_finset_sum _ fun y hy => hg a y;
        · exact Or.inr ( prob_not_top )
      generalize_proofs at *; (
      have h_limit :
          Filter.Tendsto (fun w => 1 - ∑ a ∈ Tα, (F w) (some a)) l
            (𝓝 (1 - ∑ a ∈ Tα, μ (some a))) := by
        convert ENNReal.Tendsto.sub tendsto_const_nhds ( tendsto_finset_sum _ fun a _ => hμ a ) _
          using 1 ; norm_num
      generalize_proofs at *; (
      exact le_of_tendsto_of_tendsto' ‹_›
        ( by simpa only [ add_comm ] using Filter.Tendsto.add ‹Tendsto
          ( fun w => ∑ a ∈ Tα, ( F w ) ( some a ) * ∑ y ∈ Tβ, ( G w ( some a ) ) ( some y ) ) l
          ( 𝓝 ( ∑ a ∈ Tα, μ ( some a ) * ∑ y ∈ Tβ, ( g ( some a ) ) ( some y ) ) ) › h_limit )
            fun w => h_finite w))))
    generalize_proofs at *; (
    have h_limit :
        Filter.Tendsto (fun Tα : Finset α => 1 - ∑ a ∈ Tα, μ (some a)
          + ∑ a ∈ Tα, μ (some a) * (∑ y ∈ Tβ, (g (some a)) (some y)))
            Filter.atTop (nhds (1 - ∑' a, μ (some a)
              + ∑' a, μ (some a) * (∑ y ∈ Tβ, (g (some a)) (some y)))) := by
      refine Filter.Tendsto.add ?_ ?_;
      · refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ ?_ <;> norm_num +zetaDelta at *;
        convert ENNReal.summable.hasSum using 1;
      · refine ENNReal.summable.hasSum.comp ?_;
        exact Filter.tendsto_id
    generalize_proofs at *; (
    convert le_of_tendsto_of_tendsto' tendsto_const_nhds h_limit h_finite using 1; rw [ prob_bot ];
    ring!;))
  generalize_proofs at *; (
  refine le_of_tendsto_of_tendsto' ( ENNReal.summable.hasSum ) tendsto_const_nhds fun Tβ => ?_;
  refine le_trans ( h_tsum Tβ ) ?_;
  have h_sum_le :
      ∑' y, ∑' a, μ (some a) * (g (some a)) (some y) =
      ∑' a, ∑' y, μ (some a) * (g (some a)) (some y) := by
    rw [ ENNReal.tsum_comm ];
  simp_all +decide only [PMF.bind_apply, ENNReal.tsum_mul_left, ge_iff_le];
  gcongr;
  exact ENNReal.sum_le_tsum _)
/-
The total mass of the non-escaping contribution `P z = ∑' a, μ (some a) * g (some a) z`
(summed over all `z`) equals `1 - μ ⊥`.
-/
lemma P_tsum_eq {α β : Type} {μ : Distr α} {g : WithBot α → Distr β} :
    (∑' z : WithBot β, ∑' a : α, μ (some a) * g (some a) z) = 1 - μ ⊥ := by
  rw [ ← prob_not_bot, ← ENNReal.tsum_comm ];
  -- By definition of probability mass function, we know that $\sum_{z} g(a, z) = 1$ for each $a$.
  have h_sum_g : ∀ a : α, ∑' z : WithBot β, (g (some a)) z = 1 := by
    exact fun a => PMF.tsum_coe _;
  simp +decide [ ENNReal.tsum_mul_left, h_sum_g ];
  rfl
/-
The `⊥`-coordinate version of `bind_limit_some`, deduced from the escaping-mass bound
`bind_limit_sumR` and the total-mass identity `P_tsum_eq`.
-/
lemma bind_limit_bot {α β : Type} {μ : Distr α} {g : WithBot α → Distr β} {ν : Distr β}
    (hsumR : (∑' y : β, ν (some y)) ≤ μ ⊥ + ∑' y : β, (∑' a : α, μ (some a) * g (some a) (some y)))
    (hPtot : (∑' z : WithBot β, ∑' a : α, μ (some a) * g (some a) z) = 1 - μ ⊥) :
    (∑' a : α, μ (some a) * g (some a) ⊥) ≤ ν ⊥ := by
  have hPb :
      ∑' a : α, μ (some a) * g (some a) ⊥ =
      (1 - μ ⊥) - ∑' y : β, ∑' a : α, μ (some a) * g (some a) (some y) := by
    have hPb :
        ∑' z : WithBot β, ∑' a : α, μ (some a) * g (some a) z =
        (∑' a : α, μ (some a) * g (some a) ⊥) +
          (∑' y : β, ∑' a : α, μ (some a) * g (some a) (some y)) := by
      convert total_prob _ using 1;
      exact add_comm _ _
    generalize_proofs at *; (
    rw [ ← hPtot, hPb, ENNReal.add_sub_cancel_right ];
    contrapose! hPtot; refine ne_of_gt ( lt_of_le_of_lt tsub_le_self ?_ ))
    simp_all only [add_top, le_top, ENNReal.one_lt_top]
  rw [ hPb, prob_bot ];
  convert tsub_le_tsub_left hsumR ( 1 : ENNReal ) using 1
  · rw [ prob_bot, tsub_tsub, add_comm ]
  · convert prob_bot ν using 1

/-
Reconstruction: given the pointwise bound `P ≤ ν` and the total-mass identity, the limit `ν`
is realised as `PMF.bind μ g'` for a choice function `g'` agreeing with `g` on `some` and using a
suitable distribution `gbot` at `⊥` (which absorbs the escaped mass).
-/
lemma bind_reconstruct {α β : Type} {μ : Distr α} {g : WithBot α → Distr β} {ν : Distr β}
    (hPle : ∀ z : WithBot β, (∑' a : α, μ (some a) * g (some a) z) ≤ ν z)
    (hPtot : (∑' z : WithBot β, ∑' a : α, μ (some a) * g (some a) z) = 1 - μ ⊥) :
    ∃ gbot : Distr β,
      PMF.bind μ (fun x => Option.elim x gbot (fun a => g (some a))) = ν := by
  -- Let `R z := ν z - P z` (so `R z ≥ 0` by `hPle`, and `P z + R z = ν z` by
  -- `add_tsub_cancel_of_le (hPle z)`).
  set R : WithBot β → ENNReal := fun z => ν z - ∑' a, μ (some a) * (g (some a)) z
  have hR_nonneg : ∀ z, 0 ≤ R z := by
    exact fun z => zero_le _
  have hR_eq : ∀ z, ν z = ∑' a, μ (some a) * (g (some a)) z + R z := by
    exact fun z => by rw [ add_tsub_cancel_of_le ( hPle z ) ] ;
  -- Now case on whether `μ ⊥ = 0`:
  by_cases hμbot : μ ⊥ = 0;
  · -- If `μ ⊥ = 0`, then `∑' z, R z = 0`, so by `ENNReal.tsum_eq_zero` every `R z = 0`,
    -- i.e. `ν z = P z` for all `z`.
    have hR_zero : ∀ z, R z = 0 := by
      have hR_zero : ∑' z, R z = 0 := by
        convert ENNReal.tsum_sub _ _ using 1;
        rotate_left;
        rotate_left;
        · use fun _ => 0;
        · use fun _ => 0;
        · norm_num;
        · exact fun _ => le_rfl;
        · have hR_zero : ∑' z, R z = (∑' z, ν z) - (∑' z, ∑' a, μ (some a) * (g (some a)) z) := by
            have h_sum_eq : ∑' z, ν z = ∑' z, (∑' a, μ (some a) * (g (some a)) z + R z) := by
              exact tsum_congr hR_eq
            rw [ h_sum_eq, ENNReal.tsum_add ];
            rw [ hPtot ] ; norm_num [ hμbot ];
          simp only [hR_zero, hPtot, hμbot, tsub_zero, tsub_self, tsum_zero];
          rw [ show ∑' z : WithBot β, ν z = 1 from ?_, tsub_self ];
          exact HasSum.tsum_eq ( ν.2 );
        · simp only [tsum_zero, tsub_self]
      exact fun z => le_antisymm ( le_trans ( Summable.le_tsum
        ( show Summable R from by
          exact ENNReal.summable ) z ( fun _ _ => hR_nonneg _ ) ) hR_zero.le ) ( hR_nonneg _ );
    refine ⟨ PMF.pure ⊥, ?_ ⟩;
    ext z
    conv => rhs; exact hR_eq z
    rw [ hR_zero z, add_zero, PMF.bind_apply, total_prob ];
    conv => lhs; arg 2; arg 1; exact hμbot
    simp only [zero_mul, add_zero]; refine congrArg tsum ?_; ext x; rfl
  · -- Define `gbot : Distr β := ⟨fun z => R z / μ ⊥, _⟩`, where the `HasSum _ 1` proof comes from
    -- `∑' z, R z / μ ⊥ = (∑' z, R z) / μ ⊥ = μ ⊥ / μ ⊥ = 1`
    -- (use `ENNReal.tsum_mul_right` with `R z / μ ⊥ = R z * (μ ⊥)⁻¹`,
    -- then `ENNReal.mul_inv_cancel`).
    have hR_sum : ∑' z, R z = μ ⊥ := by
      have hR_sum : ∑' z, ν z = 1 := by
        exact HasSum.tsum_eq ( ν.2 );
      have hR_sum : ∑' z, ν z = ∑' z, (∑' a, μ (some a) * (g (some a)) z) + ∑' z, R z := by
        rw [ ← ENNReal.tsum_add ] ; exact tsum_congr fun z => hR_eq z;
      generalize_proofs at *; (
      rw [ hPtot ] at hR_sum;
      rw [ eq_comm, ← ENNReal.add_right_inj ];
      · rw [ ← hR_sum, ‹∑' z, ν z = 1›, tsub_add_cancel_of_le ];
        grind +suggestions;
      · simp +decide [ ENNReal.sub_eq_top_iff ])
    -- Define `gbot : Distr β := ⟨fun z => R z / μ ⊥, _⟩`.
    obtain ⟨gbot, hgbot⟩ : ∃ gbot : Distr β, ∀ z, gbot z = R z / μ ⊥ := by
      have hR_sum_div : ∑' z, R z / μ ⊥ = 1 := by
        simp only [div_eq_mul_inv, ENNReal.tsum_mul_right, hR_sum];
        exact ENNReal.mul_inv_cancel hμbot ( prob_not_top );
      exact ⟨ ⟨ fun z => R z / μ ⊥, by
        convert ENNReal.summable.hasSum using 1;
        exact hR_sum_div.symm ⟩, fun z => rfl ⟩
    use gbot
    ext z
    simp only [PMF.bind_apply, total_prob, Option.elim];
    conv => lhs; arg 2; arg 2; exact hgbot z
    conv =>
      lhs; arg 2;
      exact ENNReal.mul_div_cancel'
        (fun hc ↦ False.elim (hμbot hc))
        (fun hc ↦ False.elim (prob_not_top hc))
    symm; exact hR_eq _

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
  -- IMPORTANT: `Function.uncurry PMF.bind` is NOT continuous in this weak topology (probability
  -- mass can escape to `⊥`), so the image of the compact set `hc` cannot be shown closed by the
  -- naive continuity argument.  Instead we extract an ultrafilter cluster point and reconstruct the
  -- limit distribution explicitly, letting the unconstrained choice at `⊥` absorb the escaped mass.
  rw [isClosed_iff_clusterPt]
  intro ν hν
  obtain ⟨W, ⟨μ, g⟩, hpK, hWp, hΦν⟩ :=
    exists_ultrafilter_of_clusterPt_image
      (X := Distr α × (WithBot α → Distr β)) (Y := Distr β) (Function.uncurry PMF.bind)
      (s ×ˢ Set.univ.pi (Option.elim · Set.univ k)) hc ν hν
  obtain ⟨hμs, hgpi⟩ := Set.mem_prod.mp hpK
  -- Component limits along the ultrafilter `W`.
  have hfst : Filter.Tendsto (fun w : Distr α × (WithBot α → Distr β) => w.1) ↑W (nhds μ) :=
    (continuous_fst.tendsto _).mono_left hWp
  have hsnd : Filter.Tendsto (fun w : Distr α × (WithBot α → Distr β) => w.2) ↑W (nhds g) :=
    (continuous_snd.tendsto _).mono_left hWp
  have hμc : ∀ a : α, Filter.Tendsto (fun w : Distr α × (WithBot α → Distr β) => (w.1) (some a))
      ↑W (nhds (μ (some a))) := fun a => distr_tendsto_coord hfst a
  have hgc : ∀ (a : α) (y : β),
      Filter.Tendsto (fun w : Distr α × (WithBot α → Distr β) => (w.2 (some a)) (some y))
        ↑W (nhds (g (some a) (some y))) :=
    fun a y => distr_tendsto_coord (((continuous_apply (some a)).tendsto g).comp hsnd) y
  have hbindc : ∀ y : β,
      Filter.Tendsto (fun w : Distr α × (WithBot α → Distr β) => (PMF.bind w.1 w.2) (some y))
        ↑W (nhds (ν (some y))) := by
    intro y
    have hco := distr_tendsto_coord hΦν y
    simpa only [Function.uncurry] using hco
  -- The pointwise lower bound `P ≤ ν`.
  have hPtot : (∑' z : WithBot β, ∑' a : α, μ (some a) * g (some a) z) = 1 - μ ⊥ := P_tsum_eq
  have hPle : ∀ z : WithBot β, (∑' a : α, μ (some a) * g (some a) z) ≤ ν z := by
    intro z
    match z with
    | some y => exact bind_limit_some hμc hgc hbindc y
    | ⊥ => exact bind_limit_bot (bind_limit_sumR hμc hgc hbindc) hPtot
  -- Reconstruct `ν` as a bind with a choice function `g'` that lies in the relevant set.
  obtain ⟨gbot, hgbot⟩ := bind_reconstruct hPle hPtot
  refine ⟨(μ, fun x => Option.elim x gbot (fun a => g (some a))), Set.mem_prod.mpr ⟨hμs, ?_⟩, hgbot⟩
  intro x _
  cases x with
  | none => exact Set.mem_univ _
  | some a =>
      have hgi := Set.mem_pi.mp hgpi (some a) (Set.mem_univ _)
      simpa only [Option.elim] using hgi

/-
Finite convex combinations stay in an `ENNReal`-convex set.  `Convex.sum_mem` from Mathlib
requires the scalar ring to be a field, which `ENNReal` is not, so we prove the version we need
directly by induction.  We only require membership for indices carrying nonzero weight.
-/
lemma ennreal_convex_finset_mem {ι' E : Type*} [AddCommMonoid E] [Module ENNReal E] {C : Set E}
    (hC : Convex ENNReal C) {t : Finset ι'} {w : ι' → ENNReal} {z : ι' → E}
    (hw : ∑ i ∈ t, w i = 1) (hz : ∀ i ∈ t, w i ≠ 0 → z i ∈ C) :
    ∑ i ∈ t, w i • z i ∈ C := by
  classical
  induction t using Finset.induction generalizing w z with
  | empty => simp only [Finset.sum_empty, zero_ne_one] at hw
  | insert i t hi ih =>
    by_cases hi' : w i = 0 <;> by_cases ht' : ∑ i ∈ t, w i = 0
    · simp_all only [ne_eq, not_false_eq_true, Finset.sum_insert, add_zero, zero_ne_one]
    · simp_all only [ne_eq, not_false_eq_true, Finset.sum_insert, zero_add, Finset.mem_insert,
        forall_eq_or_imp, not_true_eq_false, IsEmpty.forall_iff, true_and, one_ne_zero, zero_smul,
        implies_true]
    · simp_all only [ne_eq, not_false_eq_true, Finset.sum_insert, add_zero, Finset.mem_insert,
        forall_eq_or_imp, one_ne_zero, forall_const, Finset.sum_eq_zero_iff, one_smul, zero_smul,
        Finset.sum_const_zero]
    have h_div : ∑ i ∈ t, (w i / (∑ i ∈ t, w i)) • z i ∈ C := by
      refine ih ?_ ?_ <;>
        simp_all only [ne_eq, not_false_eq_true, Finset.sum_insert];
      · simp only [ENNReal.div_eq_inv_mul, ← Finset.mul_sum]
        refine ENNReal.inv_mul_cancel ht' ?_
        simp only [Finset.sum_eq_zero_iff, not_forall] at ht'
        have ⟨x, hx, hxw⟩ := ht'
        symm; refine ne_of_gt (lt_of_le_of_lt (le_of_le_of_eq ?_ hw) ?_)
        · exact self_le_add_left _ _
        · exact ENNReal.one_lt_top
      · intro x hx h; refine hz ?_ ?_ ?_
        · exact Finset.mem_insert.mpr (Or.inr hx)
        · exact left_ne_zero_of_mul h
    simp only [Finset.mem_insert, ne_eq, forall_eq_or_imp] at hz
    convert hC (hz.1 hi') h_div ( show 0 ≤ w i from zero_le _ )
      ( show 0 ≤ ∑ i ∈ t, w i from zero_le _ ) _ using 1;
    · conv => lhs; exact Finset.sum_insert hi
      refine congrArg₂ _ rfl ?_
      simp only [Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl ?_; intro x hx
      refine congrArg₂ _ (ENNReal.mul_div_cancel' ?_ ?_).symm rfl
      · intro h; exact Finset.sum_eq_zero_iff.mp h x hx
      · intro hc
        simp_all only [ne_eq, not_false_eq_true, Finset.sum_insert, add_top, ENNReal.top_ne_one]
    · simp_all only [ne_eq, not_false_eq_true, Finset.sum_insert, Finset.sum_eq_zero_iff,
       not_forall, forall_const]

-- The finite truncation of the barycenter `PMF.bind ξ f`, where the missing mass
-- `1 - ∑_{i ∈ F} ξ i` is placed on a fixed support point `i₀`, is a genuine convex combination of
-- points of `s`, hence lies in `Subtype.val '' s`.
lemma cc_approx_mem {ι α : Type} {s : Set (Distr α)} {ξ : PMF ι} {f : ι → Distr α}
    (h : ∀ i ∈ ξ.support, f i ∈ s) (hcv : Convex ENNReal (Subtype.val '' s))
    {i₀ : ι} (hi₀ : i₀ ∈ ξ.support) (F : Finset ι) (hF : i₀ ∈ F) :
    (∑ i ∈ F, ξ i • (f i).val + (1 - ∑ i ∈ F, ξ i) • (f i₀).val) ∈ Subtype.val '' s := by
  classical
  have hsum_le : ∑ i ∈ F, ξ i ≤ 1 := by
    refine le_trans (ENNReal.sum_le_tsum F) ?_
    rw [ξ.tsum_coe]
  set c : ENNReal := 1 - ∑ i ∈ F, ξ i with hc
  set w : ι → ENNReal := fun i => ξ i + (if i = i₀ then c else 0) with hw
  -- Rewrite the truncation as a single weighted sum over `F`.
  have hA : (∑ i ∈ F, ξ i • (f i).val + c • (f i₀).val) = ∑ i ∈ F, w i • (f i).val := by
    have hsplit : ∑ i ∈ F, w i • (f i).val
        = ∑ i ∈ F, ξ i • (f i).val + ∑ i ∈ F, (if i = i₀ then c else 0) • (f i).val := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by rw [hw, add_smul])
    rw [hsplit]
    congr 1
    have hcollapse : ∑ i ∈ F, (if i = i₀ then c else 0) • (f i).val
        = ∑ i ∈ F, (if i = i₀ then c • (f i).val else 0) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [ite_smul, zero_smul]
    rw [hcollapse, Finset.sum_ite_eq' F i₀ (fun i => c • (f i).val), if_pos hF]
  rw [hA]
  apply ennreal_convex_finset_mem hcv
  · -- weights sum to one
    have : ∑ i ∈ F, w i = ∑ i ∈ F, ξ i + ∑ i ∈ F, (if i = i₀ then c else 0) := by
      rw [← Finset.sum_add_distrib]
    rw [this, Finset.sum_ite_eq' F i₀ (fun _ => c), if_pos hF, hc, add_tsub_cancel_of_le hsum_le]
  · -- nonzero-weight points lie in `s`
    intro i hiF hwi
    by_cases hii : i = i₀
    · subst hii; exact ⟨f i, h i hi₀, rfl⟩
    · rw [hw] at hwi
      simp only [hii, if_false, add_zero] at hwi
      exact ⟨f i, h i ((ξ.mem_support_iff i).mpr hwi), rfl⟩
/-
Each Euclidean coordinate of the finite truncation converges to the corresponding coordinate of
the barycenter `PMF.bind ξ f`.
-/
lemma cc_coord_tendsto {ι α : Type} {ξ : PMF ι} {f : ι → Distr α} {i₀ : ι} (a : α) :
    Filter.Tendsto
      (fun F : Finset ι =>
        (∑ i ∈ F, ξ i * (f i).val (some a)
          + (1 - ∑ i ∈ F, ξ i) * (f i₀).val (some a)).toNNReal)
      Filter.atTop (nhds (((ξ.bind f).val (some a)).toNNReal)) := by
  refine ENNReal.tendsto_toNNReal ?_ |> fun h => h.comp ?_;
  · exact ne_of_lt ( lt_of_le_of_lt ( distr_upper_bound _ _ ) ENNReal.one_lt_top );
  · have h_sum :
        Filter.Tendsto (fun F : Finset ι => ∑ i ∈ F, ξ i * (f i).val (some a))
          Filter.atTop (nhds (ξ.bind f |>.1 (some a))) := by
      have h_sum : ∑' i, ξ i * (f i).val (some a) = (ξ.bind f).val (some a) := by
        convert ξ.bind_apply ( f := f ) ( some a ) |> Eq.symm using 1;
      convert h_sum ▸ ENNReal.summable.hasSum;
    convert h_sum.add
      ( ENNReal.Tendsto.mul_const ( ENNReal.Tendsto.sub tendsto_const_nhds ( ξ.2 ) _ ) _ )
        using 2 <;> norm_num;
    exact prob_not_top

lemma countably_convex {ι α : Type} {s : Set (Distr α)} {ξ : PMF ι} {f : ι → Distr α}
    (h : ∀ i ∈ ξ.support, f i ∈ s)
    (hcv : Convex ENNReal (Subtype.val '' s))
    (hcl : IsClosed s) : PMF.bind ξ f ∈ s := by
  classical
  obtain ⟨i₀, hi₀⟩ := ξ.support_nonempty
  set δ : Distr α := ξ.bind f with hδ
  -- membership of the finite truncations
  have hmem : ∀ F : Finset ι, i₀ ∈ F →
      (∑ i ∈ F, ξ i • (f i).val + (1 - ∑ i ∈ F, ξ i) • (f i₀).val) ∈ Subtype.val '' s :=
    fun F hF => cc_approx_mem h hcv hi₀ F hF
  -- pick distributions realizing these truncations
  let dd : Finset ι → Distr α := fun F =>
    if hF : i₀ ∈ F then (hmem F hF).choose else f i₀
  have hdd_mem : ∀ F : Finset ι, i₀ ∈ F → dd F ∈ s := by
    intro F hF; simp only [dd, dif_pos hF]; exact (hmem F hF).choose_spec.1
  have hdd_val : ∀ F : Finset ι, i₀ ∈ F →
      (dd F).val = (∑ i ∈ F, ξ i • (f i).val + (1 - ∑ i ∈ F, ξ i) • (f i₀).val) := by
    intro F hF; simp only [dd, dif_pos hF]; exact (hmem F hF).choose_spec.2
  -- the truncations converge to δ in the (induced) topology on `Distr α`
  have htend : Filter.Tendsto dd Filter.atTop (nhds δ) := by
    rw [distr_inducing.tendsto_nhds_iff, tendsto_pi_nhds]
    intro a
    refine (cc_coord_tendsto (i₀ := i₀) a).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({i₀} : Finset ι)] with F hF
    have hF' : i₀ ∈ F := by simpa using hF
    change (∑ i ∈ F, ξ i * (f i).val (some a)
           + (1 - ∑ i ∈ F, ξ i) * (f i₀).val (some a)).toNNReal = (distr_inj ∘ dd) F a
    rw [Function.comp_apply, distr_inj, Function.comp_apply, Function.comp_apply]
    congr 1
    rw [distr_coe, hdd_val F hF']
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, WithBot.some_eq_coe]
  -- conclude by closedness of `s`
  refine hcl.mem_of_tendsto htend ?_
  filter_upwards [Filter.eventually_ge_atTop ({i₀} : Finset ι)] with F hF
  exact hdd_mem F (by simpa using hF)
