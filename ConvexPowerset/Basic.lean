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
