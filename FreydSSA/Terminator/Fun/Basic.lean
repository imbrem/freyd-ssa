import FreydSSA.Term.Fun.Basic
import FreydSSA.Ctx.Label.Fun

variable {φ ν κ α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

inductive UTerminator.FWf : FCtx ν (Ty α) → UTerminator φ ν κ → FLCtx κ ν (Ty α) → Type _
  | br : FLCtx.Wk (FLCtx.singleton ℓ ⟨Γ, A⟩) L → e.FWf p Γ A → (br ℓ e).FWf Γ L
  | ite : e.FWf p Γ Ty.bool → s.FWf Γ L → t.FWf Γ L → (ite e s t).FWf Γ L

inductive UTerminator.FWfM : FCtx ν (Ty α) → UTerminator φ ν κ → FLCtx κ ν (Ty α) → Type _
  | br ℓ : e.FWf p Γ A → (br ℓ e).FWfM Γ (FLCtx.singleton ℓ ⟨Γ, A⟩)
  | ite : e.FWf p Γ Ty.bool → s.FWfM Γ L → t.FWfM Γ K → L.Cmp K → (ite e s t).FWfM Γ (L.lsup K)

--TODO: FWf', factorization, etc...

--TODO: FLCtx "Γ multiplication"...
