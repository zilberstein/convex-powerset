import Mathlib.Probability.ProbabilityMassFunction.Constructions

import ConvexPowerset.Distr.Basic

-- Monad structure on `WithBot`, reused for the `Distr` monad below.
instance instMonadWithBot : Monad WithBot := inferInstanceAs (Monad (OptionT Id))

instance instLawfulMonadWithBot : LawfulMonad WithBot := inferInstanceAs (LawfulMonad (OptionT Id))

noncomputable instance instFunctorDistr : Functor Distr :=
{
  map := λ f a => PMF.map (WithBot.map f) a
}

noncomputable instance instApplicativeDistr : Applicative Distr :=
{
  pure := λ x => PMF.pure (pure x)
  seq := λ mf mx =>
    PMF.bind mf (λ wf => PMF.map (λ wx => wf <*> wx) (mx ()))
}

noncomputable instance instMonadDistr : Monad Distr :=
{
  pure := λ x => PMF.pure (pure x),
  bind := λ {α β} (m : Distr α) (f : α → Distr β) =>
    PMF.bind m (λ wb =>
      match wb with
      | ⊥ => pure ⊥
      | some a => f a
    )
}

-- This is nontrivial: PMF (M a)
-- PMFT = M (PMF a)
instance instLawfulMonadDistr : LawfulMonad Distr where
  map_const := by {
    intros α β; simp [Functor.mapConst, Functor.map]
  }
  id_map := by {
    intros α da
    show PMF.map (WithBot.map id) da = da
    rw [WithBot.map_id]; exact PMF.map_id da
  }
  seqLeft_eq := by {
    intros α β x y; simp [Functor.map]; simp [SeqLeft.seqLeft]; solve_by_elim
  }
  seqRight_eq := by {
    intros α β x y; simp [Functor.map]; simp [SeqRight.seqRight]; solve_by_elim
  }
  pure_seq := by {
    intros α β g x; simp only [Functor.map, pure]
    dsimp [Seq.seq]
    rw [PMF.pure_bind]; congr
  }
  bind_pure_comp := by {
    intros α β f x
    dsimp [Functor.map, pure, bind, PMF.map]; congr
    funext y
    dsimp [WithBot.map, Option.map]
    cases y <;> rfl
  }
  bind_map := by {
    intros α β f x
    dsimp [Functor.map, bind, Seq.seq, PMF.map]; congr
    funext y
    cases y <;> simp <;> congr
    show PMF.pure (⊥ : WithBot β) = PMF.map (Function.const (WithBot α) (⊥ : WithBot β)) x
    rw [PMF.map_const]
  }
  pure_bind := by {
    intros α β x f
    dsimp [pure, bind]
    simp only [PMF.pure_bind]
    rfl
  }
  bind_assoc := by {
    intros α β γ x f g
    dsimp [bind] ; simp ; congr
    funext wb; cases wb <;> simp
    simp [pure, PMF.pure_bind]
  }
