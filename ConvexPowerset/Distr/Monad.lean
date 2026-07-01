import Mathlib.Probability.ProbabilityMassFunction.Constructions

import ConvexPowerset.Distr.Basic

noncomputable instance : Pure Distr where
  pure x := PMF.pure (some x)

noncomputable instance : Bind Distr where
  bind d f := PMF.bind d fun x => match x with
  | Option.none => PMF.pure ⊥
  | Option.some y => f y

noncomputable instance : Monad Distr where

instance : LawfulMonad Distr := LawfulMonad.mk' Distr
  (id_map := by
    intro α μ; ext x; refine (tsum_eq_single x ?_).trans ?_
    · intro y hne; cases y with
      | bot =>
        simp only [PMF.pure_apply, mul_ite, mul_one, mul_zero, ite_eq_right_iff]
        intro rfl; contradiction
      | coe y =>
        simp only [Function.comp_apply, id_eq, mul_eq_zero]
        right; exact PMF.pure_apply_of_ne _ _ (Ne.symm hne)
    · cases x with
      | bot => simp only [PMF.pure_apply, ↓reduceIte, mul_one]; rfl
      | coe x =>
        simp only [Function.comp_apply, id_eq]
        conv => lhs; arg 2; exact PMF.pure_apply_self _
        exact mul_one _
    )
  (pure_bind := fun _ _ ↦ PMF.pure_bind _ _)
  (bind_assoc := by
    intro α β γ μ f g;
    conv => lhs; exact PMF.bind_bind _ _ _
    refine congrArg₂ _ rfl ?_; ext1 x; cases x with
    | bot => exact PMF.pure_bind _ _
    | coe x => rfl)
