import FreydSSA.Ctx.Label
import FreydSSA.Ctx.Var.Perm

inductive LCtx.LPerm : LCtx ν κ α → LCtx ν κ α → Prop
  | nil : LPerm [] []
  | cons : LPerm L K → LPerm (ℓ::L) (ℓ::K)
  | swap (ℓ ℓ') (L) : ℓ.name ≠ ℓ'.name -> LPerm (ℓ::ℓ'::L) (ℓ'::ℓ::L)
  | trans : LPerm Γ Δ → LPerm Δ Ξ → LPerm Γ Ξ

structure Label.TPerm (ℓ : Label ν κ α) (ℓ' : Label ν κ α) :=
  name : ℓ.name = ℓ'.name
  param : ℓ.param = ℓ'.param
  live : ℓ.live.TPerm ℓ'.live

inductive LCtx.PPerm : LCtx ν κ α → LCtx ν κ α → Prop
  | nil : PPerm [] []
  | cons : ℓ.TPerm ℓ' → PPerm L K → PPerm (ℓ::L) (ℓ'::K)

inductive LCtx.LTPerm : LCtx ν κ α → LCtx ν κ α → Prop
  | nil : LTPerm [] []
  | cons : ℓ.TPerm ℓ' → LTPerm L K → LTPerm (ℓ::L) (ℓ'::K)
  | swap (ℓ ℓ') (L) : ℓ.name ≠ ℓ'.name -> LTPerm (ℓ::ℓ'::L) (ℓ'::ℓ::L)
  | trans : LTPerm Γ Δ → LTPerm Δ Ξ → LTPerm Γ Ξ
