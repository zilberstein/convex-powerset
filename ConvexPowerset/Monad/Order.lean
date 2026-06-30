import ConvexPowerset.Monad
import ConvexPowerset.Powerdomain

namespace ConvexPowerset

lemma bind_monotone {α β : Type}
    {s t : ConvexPowerset α} {f g : α → ConvexPowerset β}
    (h : s ≤ t) (h' : f ≤ g) : s.bind f ≤ t.bind g := by
  apply le_iff_supset.mp at h
  have h' x := le_iff_supset.mp (h' x)
  refine le_iff_supset.mpr ?_
  simp only [bind, c_bind, Set.image, Set.mem_iUnion, exists_prop, Function.uncurry, Prod.exists,
    Set.setOf_subset_setOf, forall_exists_index, and_imp]
  intro _ μ f' _ hμ ⟨rfl, hf⟩ rfl
  refine ⟨μ, f', ⟨μ, h hμ, rfl, ?_⟩, rfl⟩
  refine Set.mem_pi.mpr fun x hx ↦ ?_
  cases x with
  | bot => exact Set.mem_univ _
  | coe x => exact h' x (hf x hx)

end ConvexPowerset

namespace OmegaCompletePartialOrder
namespace Chain

def bind {α β : Type}
    (c : Chain (ConvexPowerset α))
    (cf : Chain (α → ConvexPowerset β)) :
    Chain (ConvexPowerset β) := {
  toFun i := (c i).bind (cf i)
  monotone' := by
    intro _ _ hle; apply ConvexPowerset.bind_monotone
    · exact c.monotone' hle
    · exact cf.monotone' hle
}

end Chain
end OmegaCompletePartialOrder

namespace ConvexPowerset
open OmegaCompletePartialOrder

open Filter Topology in
/-- Extraction of the reconstruction step of `bind_closed`: if an ultrafilter `W` on the product
space converges to `(μ, g)` and `Function.uncurry PMF.bind` tends to `ν` along `W`, then `ν` is a
`PMF.bind` of `μ` with a choice function agreeing with `g` on `some` (the `⊥`-component `gbot`
absorbs the escaped mass). -/
lemma bind_reconstruct_of_ultrafilter {α β : Type}
    {μ : Distr α} {g : WithBot α → Distr β} {ν : Distr β}
    (W : Ultrafilter (Distr α × (WithBot α → Distr β)))
    (hWp : ↑W ≤ 𝓝 (μ, g))
    (hΦν : Tendsto (Function.uncurry PMF.bind :
        Distr α × (WithBot α → Distr β) → Distr β) ↑W (𝓝 ν)) :
    ∃ gbot : Distr β,
      PMF.bind μ (fun x => Option.elim x gbot (fun a => g (some a))) = ν := by
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
    exact distr_tendsto_coord hΦν
  have hPtot : (∑' z : WithBot β, ∑' a : α, μ (some a) * g (some a) z) = 1 - μ ⊥ := P_tsum_eq
  have hPle : ∀ z : WithBot β, (∑' a : α, μ (some a) * g (some a) z) ≤ ν z := by
    intro z
    match z with
    | some y => exact bind_limit_some hμc hgc hbindc y
    | ⊥ => exact bind_limit_bot (bind_limit_sumR hμc hgc hbindc) hPtot
  exact bind_reconstruct hPle hPtot

open Filter Topology in
/-- Scott-continuity core for `distr_bind`: for antitone families of closed sets `A i` and
closed nonempty sets `K i x`, an element of every `distr_bind (A i) (K i)` is realised as a
`distr_bind` over the intersections.  The map `Function.uncurry PMF.bind` is *not* continuous in
the weak topology (mass can escape to `⊥`), so this is proven by extracting an ultrafilter limit
of a sequence of witnesses and reconstructing the limit distribution explicitly, exactly as in
`bind_closed`. -/
lemma distr_bind_iInter_subset {α β : Type}
    {A : ℕ → Set (Distr α)} {K : ℕ → α → Set (Distr β)}
    (hAcl : ∀ i, IsClosed (A i)) (hAanti : Antitone A)
    (hKcl : ∀ i x, IsClosed (K i x)) (hKne : ∀ i x, (K i x).Nonempty)
    (hKanti : ∀ x, Antitone fun i => K i x) :
    (⋂ i, distr_bind (A i) (K i)) ⊆ distr_bind (⋂ i, A i) (fun x => ⋂ i, K i x) := by
  intro ν hν;
  obtain ⟨p, hpC, hpΦ⟩ :
      ∃ p : ℕ → Distr α × (WithBot α → Distr β),
        (∀ i, p i ∈ (A i) ×ˢ Set.univ.pi (Option.elim · Set.univ (K i))) ∧
        (∀ i, (Function.uncurry PMF.bind) (p i) = ν) := by
    simp_all only [implies_true, distr_bind_image, Set.mem_iInter];
    choose a ha hb using hν; exact ⟨a, ha, hb⟩
  obtain ⟨U, hU⟩ : ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ Filter.atTop :=
    Ultrafilter.exists_le _
  obtain ⟨q, hq⟩ :
      ∃ q : Distr α × (WithBot α → Distr β),
        q ∈ (A 0) ×ˢ Set.univ.pi (Option.elim · Set.univ (K 0)) ∧
        (U.map p : Filter (Distr α × (WithBot α → Distr β))) ≤ nhds q := by
    apply IsCompact.ultrafilter_le_nhds;
    · refine IsCompact.prod ?_ ?_;
      · exact IsClosed.isCompact ( hAcl 0 );
      · refine isCompact_univ_pi fun x => ?_
        cases x <;> [
          exact isCompact_univ;
          exact IsCompact.of_isClosed_subset ( isCompact_univ ) ( hKcl 0 _ ) ( Set.subset_univ _ )
        ] ;
    · intro x hx;
      simp_all only [Set.mem_iInter, mem_principal, Ultrafilter.coe_map, mem_map,
        Ultrafilter.mem_coe];
      refine Filter.mem_of_superset ( hU <| Filter.Ici_mem_atTop 0 ) fun i hi => hx <| ?_
      exact ⟨ hAanti hi <| hpC i |>.1, fun x => hpC i |>.2 x |> fun hx => by cases x <;> aesop ⟩
  have hq_mem : ∀ i, q ∈ (A i) ×ˢ Set.univ.pi (Option.elim · Set.univ (K i)) := by
    intro i
    have hq_mem_i :
        (A i) ×ˢ Set.univ.pi (Option.elim · Set.univ (K i)) ∈
        (U.map p : Filter (Distr α × (WithBot α → Distr β))) := by
      have hq_mem_i : {j | p j ∈ (A i) ×ˢ Set.univ.pi (Option.elim · Set.univ (K i))} ∈ U := by
        refine Filter.mem_of_superset ( hU <| Filter.Ici_mem_atTop i ) fun j hj => ?_
        refine ⟨ hAanti hj <| hpC j |>.1, fun x hx => ?_ ⟩
        cases x <;> [ exact Set.mem_univ _ ; exact hKanti _ hj <| hpC j |>.2 _ hx ]
      exact Filter.mem_map.mpr ( Filter.mem_of_superset hq_mem_i fun x hx => hx );
    have hq_mem_i : IsClosed ((A i) ×ˢ Set.univ.pi (Option.elim · Set.univ (K i))) := by
      refine IsClosed.prod ( hAcl i ) ?_;
      exact isClosed_set_pi fun x _ => by cases x <;> [ exact isClosed_univ; exact hKcl i _ ] ;
    exact hq_mem_i.mem_of_tendsto hq.2 ‹_›;
  obtain ⟨gbot, hgbot⟩ :
      ∃ gbot : Distr β, PMF.bind q.1 (fun x => Option.elim x gbot (fun a => q.2 (some a))) = ν := by
    refine bind_reconstruct_of_ultrafilter (U.map p) ?_ ?_
    · exact hq.2;
    · intro s hs; refine mem_map.mpr ?_
      refine Ultrafilter.mem_map.mpr ?_
      simp only [Set.preimage, Set.mem_setOf_eq]; convert U.univ_sets
      · rfl
      · ext i; constructor <;> intro _
        · exact Set.mem_univ _
        · simp only [Set.mem_setOf_eq]; conv => rhs; exact hpΦ i
          exact mem_of_mem_nhds hs
  refine ⟨ ?_, ?_, ?_ ⟩;
  · exact ⟨ q.1, fun x => Option.elim x gbot fun a => q.2 ( some a ) ⟩;
  · simp_all only [Set.mem_iInter, Ultrafilter.coe_map, true_and, Set.mem_iUnion,
    exists_prop];
    refine ⟨q.1, ?_, rfl, ?_⟩
    · intro i; exact (hq_mem i).1
    · simp only [Set.mem_pi, PMF.mem_support_iff, ne_eq]; intro i hi
      cases i with
      | bot => exact Set.mem_univ _
      |coe x =>
        refine Set.mem_iInter.mpr fun j ↦ ?_
        exact hq_mem j |>.2 (some x) (Set.mem_univ _)
  · exact hgbot

lemma bind_continuous {α β : Type}
    (c : Chain (ConvexPowerset α))
    (cf : Chain (α → ConvexPowerset β)) :
    ωSup (c.bind cf)  = (ωSup c).bind (ωSup cf) := by
  refine le_antisymm ?_ ?_
  · refine ωSup_le _ _ fun i ↦ ?_
    refine bind_monotone ?_ ?_ <;> exact le_ωSup _ _
  · refine le_iff_supset.mpr ?_
    -- Reduce to the `distr_bind` statement on underlying sets.
    refine distr_bind_iInter_subset (A := fun i => (c i).set)
      (K := fun i x => (cf i x).set) ?_ ?_ ?_ ?_ ?_
    · exact fun i => (c i).closed
    · intro i j hij; exact le_iff_supset.mp (c.monotone' hij)
    · exact fun i x => (cf i x).closed
    · exact fun i x => (cf i x).nonempty
    · intro x i j hij; exact le_iff_supset.mp (cf.monotone' hij x)

end ConvexPowerset
