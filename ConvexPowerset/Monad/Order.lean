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
