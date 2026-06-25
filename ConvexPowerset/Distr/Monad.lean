import Mathlib.Probability.ProbabilityMassFunction.Constructions

import ConvexPowerset.Distr.Basic

noncomputable instance : Functor Distr where
  map f := PMF.map (Option.map f)

-- instance : LawfulFunctor Distr where
--   map_const := by
--     intro α β; ext x d y
--     refine (@LawfulFunctor.map_const PMF _ _).trans ?_

noncomputable instance : Pure Distr where
  pure x := PMF.pure (some x)

noncomputable instance : Bind Distr where
  bind d f := PMF.bind d fun x => match x with
  | Option.none => PMF.pure ⊥
  | Option.some y => f y
