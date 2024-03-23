import FreydSSA.Terminator.Extrinsic.Basic
import FreydSSA.Term.Extrinsic.Subst

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

inductive InstSet.USubstL [Φ : InstSet φ (Ty α)] (σ : ν → UTm φ ν)
  : LCtx ν κ (Ty α) → LCtx ν κ (Ty α) → Type _
  | nil : USubstL σ [] []
  | cons : USubst σ Γ Δ → USubstL σ L K → USubstL σ (⟨n, A, Γ⟩ :: L) (⟨n, A, Δ⟩ :: K)
  | skip : USubstL σ L K → ℓ.name ∉ L.labels →  USubstL σ L (ℓ :: K)

-- def UTerminator.Wf.subst {Γ Δ Γ' : Ctx ν (Ty α)} {σ}
--   {t : UTerminator φ ν κ}
--   (hσ : Φ.USubst σ Γ' Γ) : t.Wf Γ L → (t.rewrite σ).Wf Γ' L
--   := sorry
