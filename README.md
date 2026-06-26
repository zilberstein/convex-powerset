# Lean Formalization of the Convex Powerdomain

The Convex Powerdomain is a semantic structure used to encode the mixture of probabilistic and nondeterministic and nondeterminism computation. At its core, the convex powerdomain is a set of probability distributions, with the following properties:

* **Nonemptiness:** Each set must be nonempty, to signify that the semantics is not vacuous;
* **Convexity:** Each set is convex, in order to ensure a proper monad structure;
* **Closedness:** Each set must be closed, which ensures that suprema of chains exist;
* **Up-Closed:** Each set must be up-closed to ensure that the Smyth powerdomain is well-defined

The library here defines the monad and omega complete partial order structure for the convex powerdomain. The construction is based on the work of:

* He et al. 1997: https://doi.org/10.1016/S0167-6423(96)00019-6
* McIver and Morgan 2005: https://doi.org/10.1007/b138392
* Zilberstein et al. 2025: https://doi.org/10.1145/3704855

In particular, the powerdomain definition uses the Smyth construction, which is suitable for total correctness. Other constructions are possible too, but are less useful for the purposes of defining program semantics (refer to Zilberstein et al. 2025 for a discussion).