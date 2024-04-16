import FreydSSA.BasicBlock.Fun.Basic
import FreydSSA.Untyped.FCFG

-- TODO: to bottom map...

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

structure FCtx.WfStep (I : FLCtx κ ν (Ty α)) (g : FCFG φ ν κ) (O : FLCtx κ ν (Ty α)) : Type _
  where
  support_eq : I.support = g.support
  support_typed : ∀ℓ ∈ I.support, True
