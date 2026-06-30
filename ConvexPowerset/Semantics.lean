import ConvexPowerset.Operations

abbrev Var := String
abbrev Val := ℚ
abbrev Mem := Var → Val
abbrev Expr := Mem → Val

def literal (v : ℚ) : Expr := fun _ ↦ v
def var (x : Var) : Expr := fun σ ↦ σ x

namespace Mem

def emp : Mem := fun _ ↦ 0

def insert (σ : Mem) (x : Var) (v : Val) : Mem :=
  fun y ↦ if x = y then v else σ y

end Mem

inductive Cmd : Type
  | skip : Cmd
  | seq : Cmd → Cmd → Cmd
  | if_stmt : Expr → Cmd → Cmd → Cmd
  | prob : Expr → Cmd → Cmd → Cmd
  | nondet : Cmd → Cmd → Cmd
  | while_loop : Expr → Cmd → Cmd
  | assign : Var → Expr → Cmd

infixl:10 " ;; " => Cmd.seq
infixl:20 " ::= " => Cmd.assign
infixl:30 " & " => Cmd.nondet
notation c₁ " ⊕[ " p " ] " c₂ => Cmd.prob p c₁ c₂

namespace Cmd

def cond (v : Val) (s₁ s₂ : ConvexPowerset Mem) : ConvexPowerset Mem :=
  if v = 1 then s₁ else if v = 0 then s₂ else ⊥

def Φ (c : Mem → ConvexPowerset Mem) (e : Expr) (f : Mem → ConvexPowerset Mem) (σ : Mem) :
    ConvexPowerset Mem :=
  cond (e σ) (c σ >>= f) (pure σ)

lemma Φ_monotone (c : Mem → ConvexPowerset Mem) (e : Expr) : Monotone (Φ c e) := by
  intro f g hle σ; unfold Φ cond
  by_cases h : e σ = 1 <;> simp only [h, ↓reduceIte]
  · exact ConvexPowerset.bind_monotone (le_refl _) hle
  · by_cases h' : e σ = 0 <;> simp only [h', ↓reduceIte, Std.le_refl]

open OmegaCompletePartialOrder in
lemma Φ_continuous (c : Mem → ConvexPowerset Mem) (e : Expr) : ωScottContinuous (Φ c e) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨Φ_monotone _ _, fun ch ↦ ?_⟩
  ext1 σ; unfold Φ cond
  by_cases h : e σ = 1 <;> simp only [h, ↓reduceIte]
  · conv => lhs; arg 1; exact (OmegaCompletePartialOrder.ωSup_const _).symm
    refine (ConvexPowerset.bind_continuous _ _).symm.trans (congrArg _ ?_)
    ext1; ext1 i; simp only [Chain.coe_map, Pi.evalOrderHom_coe, OrderHom.coe_mk,
      Function.comp_apply, Function.eval, h, ↓reduceIte]; rfl
  · refine (OmegaCompletePartialOrder.ωSup_const _).symm.trans (congrArg _ ?_)
    ext1; ext1 i; simp only [const, Chain.map, OrderHom.comp, Pi.evalOrderHom_coe, OrderHom.coe_mk,
      Chain.coe_toOrderHom, Function.comp_def, Function.eval, h, ↓reduceIte]

def with_prob {α : Type} (v : Val) (f : {p : NNReal} → p ≤ 1 → ConvexPowerset α) :
    ConvexPowerset α :=
  if h : 0 ≤ v ∧ v ≤ 1 then
    f (p := ⟨v, Rat.cast_nonneg.mpr h.1⟩) (by convert (Rat.cast_le (K := Real)).mpr h.2; aesop)
  else ⊥

def sem (c : Cmd) (σ : Mem) : ConvexPowerset Mem :=
  match c with
  | Cmd.skip => pure σ
  | Cmd.seq c₁ c₂ => sem c₁ σ >>= sem c₂
  | Cmd.if_stmt e c₁ c₂ => cond (e σ) (sem c₁ σ) (sem c₂ σ)
  | Cmd.prob e c₁ c₂ =>
      with_prob (e σ) fun hp ↦ ConvexPowerset.bernoulli hp (sem c₁ σ) (sem c₂ σ)
  | Cmd.nondet c₁ c₂ => ConvexPowerset.nondet₂ (sem c₁ σ) (sem c₂ σ)
  | Cmd.while_loop e c =>
      OmegaCompletePartialOrder.lfp (Φ_monotone (sem c) e) σ
  | Cmd.assign x e => pure (σ.insert x (e σ))

-- Example Program

def geo : Cmd :=
  "x" ::= literal 0 ;;
  "b" ::= literal 1 ;;
  Cmd.while_loop (var "b") (
    ("b" ::= 0) ⊕[ literal 0.5 ] ("x" ::= fun σ ↦ σ "x" + 1)
  )

end Cmd
