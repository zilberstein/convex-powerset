import ConvexPowerset.Distr.Powerdomain
import ConvexPowerset.Distr.Topology

@[ext]
structure ConvexPowerset (α : Type) where
  set : Set (Distr α)
  nonempty : set.Nonempty
  convex : Convex ENNReal (Subtype.val '' set)
  closed : IsClosed set
  upcl : IsUpperSet set

instance {α : Type} : Membership (Distr α) (ConvexPowerset α) where
  mem s d := d ∈ s.set

lemma hassum_1_convex {α : Type} : Convex ENNReal { d : WithBot α → ENNReal | HasSum d 1} := by
  refine convex_iff_forall_pos.mpr ?_; simp only [Set.mem_setOf_eq]
  intro d hd d' hd' p q hp hq hpq
  have heq (r : ENNReal) (e : WithBot α → ENNReal) : r • e = fun x => r • e x := rfl
  have hr (r : ENNReal) : r = r • 1 := by simp
  rw [← hpq, heq p d, heq q d']; refine HasSum.add ?_ ?_
  · nth_rewrite 2 [hr p]; refine (Summable.hasSum_iff ENNReal.summable).mpr ?_
    rw [ENNReal.tsum_const_smul p, HasSum.tsum_eq hd]
  · nth_rewrite 2 [hr q]; refine (Summable.hasSum_iff ENNReal.summable).mpr ?_
    rw [ENNReal.tsum_const_smul q, HasSum.tsum_eq hd']

instance {α : Type} : Bot (ConvexPowerset α) where
  bot := {
    set := Set.univ
    nonempty := Set.univ_nonempty
    convex := by
      convert hassum_1_convex; ext d; simp only [Set.mem_image, Subtype.exists, exists_and_right,
        exists_eq_right, Set.mem_setOf_eq]
      constructor
      · intro ⟨hs, _⟩; exact hs
      · intro hs; exact ⟨hs, True.intro⟩
    closed := isClosed_univ
    upcl _ _ _ _ := Set.mem_univ _
}

def with_bot {α β : Type} (f : α → ConvexPowerset β) (x : WithBot α) : ConvexPowerset β :=
  match x with
  | ⊥ => ⊥
  | WithBot.some y => f y
