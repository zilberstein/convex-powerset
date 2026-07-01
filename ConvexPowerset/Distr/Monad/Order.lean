import ConvexPowerset.Distr.Monad
import ConvexPowerset.Distr.Powerdomain

namespace Distr

lemma bind_monotone {α β : Type u} {μ ν : Distr α} {f g : α → Distr β}
    (h : μ ≤ ν) (h' : f ≤ g) : (μ >>= f) ≤ (ν >>= g) := by
  intro y;
  conv => lhs; exact total_prob _
  conv => rhs; exact total_prob _
  refine add_le_add ?_ ?_
  · refine ENNReal.tsum_le_tsum fun x ↦ mul_le_mul (h _) (h' _ _) ?_ ?_<;> exact zero_le
  · simp only [PMF.pure_apply, WithBot.coe_ne_bot, ↓reduceIte, mul_zero, Std.le_refl]

open OmegaCompletePartialOrder

namespace Chain

noncomputable def bind {α β : Type u}
    (c : Chain (Distr α))
    (cf : Chain (α → Distr β)) :
    Chain (Distr β) := {
  toFun i := (c i) >>= (cf i)
  monotone' := by
    intro _ _ hle; apply Distr.bind_monotone
    · exact c.monotone' hle
    · exact cf.monotone' hle
}

end Chain

/-- For monotone sequences of extended non-negative reals, the product of the two
suprema equals the supremum of the pointwise products. -/
lemma iSup_mul_iSup_of_monotone {f g : ℕ → ENNReal} (hf : Monotone f) (hg : Monotone g) :
    (⨆ i, f i) * (⨆ j, g j) = ⨆ k, f k * g k := by
  rw [ENNReal.iSup_mul]
  simp_rw [ENNReal.mul_iSup]
  apply le_antisymm
  · refine iSup_le fun i => iSup_le fun j => ?_
    refine le_iSup_of_le (max i j) ?_
    exact mul_le_mul (hf (le_max_left i j)) (hg (le_max_right i j)) zero_le zero_le
  · exact iSup_le fun k => le_iSup_of_le k (le_iSup_of_le k (le_refl _))

lemma bind_continuous {α β : Type u}
    (c : Chain (Distr α))
    (cf : Chain (α → Distr β)) :
    ωSup (Chain.bind c cf)  = (ωSup c) >>= (ωSup cf) := by
  refine le_antisymm ?_ ?_
  · refine ωSup_le _ _ fun i ↦ ?_
    refine bind_monotone ?_ ?_ <;> exact le_ωSup _ _
  · intro y
    conv => lhs; exact (PMF.bind_apply _ _ _).trans (total_prob _)
    dsimp only
    have hp : (PMF.pure (⊥ : WithBot β)) (↑y : WithBot β) = 0 := by
      simp [PMF.pure_apply, eq_comm]
    rw [hp, mul_zero, add_zero]
    -- pointwise values of the suprema
    have hc : ∀ x : α, (ωSup c) (↑x : WithBot α) = ⨆ i, (c i) (↑x : WithBot α) := fun _ => rfl
    have hcf : ∀ x : α, (ωSup cf) x (↑y : WithBot β) = ⨆ i, (cf i) x (↑y : WithBot β) :=
      fun _ => rfl
    -- monotonicity of the two families
    have hmc : ∀ x : α, Monotone (fun i => (c i) (↑x : WithBot α)) :=
      fun x _ _ hij => c.monotone hij x
    have hmcf : ∀ x : α, Monotone (fun i => (cf i) x (↑y : WithBot β)) :=
      fun x _ _ hij => cf.monotone hij x y
    -- value of the bind on the right
    have hbind : ∀ i, ((Chain.bind c cf) i) (↑y : WithBot β)
        = ∑' x : α, (c i) (↑x : WithBot α) * (cf i) x (↑y : WithBot β) := by
      intro i
      conv => lhs; exact (PMF.bind_apply _ _ _).trans (total_prob _)
      dsimp only
      rw [hp, mul_zero, add_zero]; rfl
    have hRHS : (ωSup (Chain.bind c cf)) (↑y : WithBot β)
        = ⨆ i, ∑' x : α, (c i) (↑x : WithBot α) * (cf i) x (↑y : WithBot β) :=
      iSup_congr hbind
    rw [hRHS]
    refine le_of_eq ?_
    --simp_rw [hc, hcf]
    conv => lhs; exact tsum_congr fun x => iSup_mul_iSup_of_monotone (hmc x) (hmcf x)
    exact Distr.tsum_iSup_eq_iSup_tsum
      (fun (k : ℕ) (x : α) => (c k) (↑x : WithBot α) * (cf k) x (↑y : WithBot β))
      (fun (x : α) _ _ hij => mul_le_mul (hmc x hij) (hmcf x hij) zero_le zero_le)

end Distr
