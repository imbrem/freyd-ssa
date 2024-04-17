import FreydSSA.BasicBlock.Fun.Basic

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

inductive UCFG.FWfI : FLCtx κ ν (Ty α) → UCFG φ (Ty α) ν κ → FLCtx κ ν (Ty α) → Type _
  | nil : L.Wk K → FWfI L nil K
  | cons (ℓ x A) : FWfI L g (K.cons ℓ Γℓ) → β.FWf 0 (Γℓ.toFCtx x) L → FWfI L (g.cons ℓ x A β) K
