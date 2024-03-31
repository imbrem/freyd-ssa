import FreydSSA.Ctx.Var.Fun

structure FLCtx (κ : Type _) (ν : Type _) (α : Type _) : Type _ where
  toFun : κ → WithBot (FCtx ν α)
  support : Finset κ
  mem_support_toFun : ∀x, x ∈ support ↔ toFun x ≠ ⊥
