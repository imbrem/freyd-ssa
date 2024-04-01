import FreydSSA.Ctx.Var.Fun

structure FLCtx (κ : Type _) (ν : Type _) (α : Type _) : Type _ where
  toFun : κ → WithBot (FCtx ν α)
  support : Finset κ
  mem_support_toFun : ∀x, x ∈ support ↔ toFun x ≠ ⊥

--TODO: weakening

--TODO: strict weakening

--TODO: comparability

--TODO: strict comparability

--TODO: lattice lore

--TODO: *strict* lattice lore; need a wrapper or smt...
