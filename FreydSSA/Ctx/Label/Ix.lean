import FreydSSA.Ctx.Label
import FreydSSA.Ctx.Var.Ix

variable {κ ν α} [DecidableEq κ] [DecidableEq ν] [DecidableEq α]

--NOTE: ordering is κ ν α rather than ν κ α

structure ILabel (κ : Type _) (ν : Type _) (α : Type _) where
  name : κ
  param : α
  live : ICtx ν α

structure ILCtx (κ : Type _) (ν : Type _) (α : Type _) : Type _ where
  arity : ℕ
  elements : Fin arity → ILabel κ ν α

--TODO: as for ICtx, so ILCtx

--TODO: functional ILCtx?
