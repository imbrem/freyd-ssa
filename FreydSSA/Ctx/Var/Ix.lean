import FreydSSA.Ctx.Var
import FreydSSA.Ctx.Var.Fun

variable {ν ν' α β} [DecidableEq ν] [DecidableEq ν'] [DecidableEq α]

structure TCtx (α : Type v) : Type _ where
  arity : ℕ
  ty : Fin arity → α

structure ICtx (ν : Type u) (α : Type v) extends TCtx α : Type (max u v) where
  name : Fin arity → ν

structure IFCtx (ν : Type u) (α : Type v) extends ICtx (WithBot ν) α : Type (max u v) where
  no_shadow : ∀ i j, name i = name j -> name i = ⊥ ∨ i = j

structure ISCtx (ν : Type u) (α : Type v) extends ICtx ν α : Type (max u v) where
  nodup : ∀ i j, name i = name j -> i = j

structure FICtx (ν : Type u) (α : Type v) extends TCtx α : Type (max u v) where
  ix : FCtx ν (Fin arity)
  injective : Function.Injective ix

--TODO: ICtx ≅ Ctx

--TODO: map functions, positional map functions

--TODO: ICtx → (IFCtx, FICtx)

--TODO: FICtx ≅ IFCtx, TCtx equal...

def TCtx.Var {α} (Γ : TCtx α) (A : α) (i : Fin Γ.arity) : Prop := Γ.ty i = A

--TODO: factor out ix for Wk variants? can then use subset types...

structure TCtx.Wk {α} (Γ : TCtx α) (Δ : TCtx α) (ρ : Fin Δ.arity → Fin Γ.arity) : Prop where
  ty_eq : ∀i, Γ.ty (ρ i) = Δ.ty i
  injective : Function.Injective ρ

structure ICtx.Var {ν α} (Γ : ICtx ν α) (x : ν) (A : α) (i : Fin Γ.arity) : Prop where
  ix_name : Γ.name i = x
  ix_ty : Γ.ty i = A
  ix_last : ∀j, Γ.name j = x → j ≤ i

structure IFCtx.Var {ν α} (Γ : IFCtx ν α) (x : ν) (A : α) (i : Fin Γ.arity) : Prop where
  ix_name : Γ.name i = x
  ix_ty : Γ.ty i = A

--TODO: IFCtx.Var ↔ ICtx.Var (using toICtx)

structure FICtx.Var {ν α} (Γ : FICtx ν α) (x : ν) (A : α) (i : Fin Γ.arity) : Prop where
  ix_name : Γ.ix x = i
  ix_ty : Γ.ty i = A

-- *syntactic* weakening, in which shadowed variables are simply ignored
structure ICtx.VWk {ν α} (Γ : ICtx ν α) (Δ : ICtx ν α) where
  ix : Fin Δ.arity → Fin Γ.arity
  var : ∀{x A i}, Δ.Var x A i → Γ.Var x A (ix i)

-- *semantic* weakening, which can be interpreted nicely for affine variables
-- Note that the _names_ of shadowed variables don't matter
structure ICtx.Wk {ν α} (Γ : ICtx ν α) (Δ : ICtx ν α) (ρ : Fin Δ.arity → Fin Γ.arity) extends TCtx.Wk Γ.toTCtx Δ.toTCtx ρ : Prop where
  var : ∀{x A i}, Δ.Var x A i → Γ.Var x A (ρ i)

--TODO: ICtx.Wk --> ICtx.VWk, with equal indices

-- *strict* weakening, which does not swap variables, and respects all variable names
structure ICtx.SWk {ν α} (Γ : ICtx ν α) (Δ : ICtx ν α) (ρ : Fin Δ.arity → Fin Γ.arity) extends Wk Γ Δ ρ : Prop where
  name_eq : ∀i, Γ.name (ρ i) = Δ.name i
  monotone : Monotone ρ

--TODO: Strict weakning ≅ Ctx weakening

--TODO: Weakening _preorder_ on ICtx

--TODO: Connection between FCtx and ICtx


--TODO: ICtx comparability

structure IFCtx.VWk {ν α} (Γ : IFCtx ν α) (Δ : IFCtx ν α) (ρ : Fin Δ.arity → Fin Γ.arity) extends TCtx.Wk Γ.toTCtx Δ.toTCtx ρ : Prop where
  var : ∀{x A i}, Δ.Var x A i → Γ.Var x A (ρ i)

structure IFCtx.Wk {ν α} (Γ : IFCtx ν α) (Δ : IFCtx ν α) (ρ : Fin Δ.arity → Fin Γ.arity) extends TCtx.Wk Γ.toTCtx Δ.toTCtx ρ : Prop where
  name_eq : ∀i, Γ.name (ρ i) = Δ.name i

--TODO: IFCtx.Wk --> IFCtx.VWk

structure FICtx.Wk {ν α} (Γ : FICtx ν α) (Δ : FICtx ν α) (ρ : Fin Δ.arity → Fin Γ.arity) extends TCtx.Wk Γ.toTCtx Δ.toTCtx ρ : Prop where
  name_eq : ∀x, (Δ.ix x).map ρ ⊆ Γ.ix x

--TODO: likewise for IFCtx, FICtx, ISCtx, etc...
