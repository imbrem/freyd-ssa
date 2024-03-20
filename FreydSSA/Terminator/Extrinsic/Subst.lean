import FreydSSA.Terminator.Extrinsic.Basic
import FreydSSA.Term.Extrinsic.Subst

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

-- inductive InstSet.USubstL [Φ : InstSet φ (Ty α)] (σ : ν → UTm φ ν)
--   : Ctx ν (Ty α) → LCtx ν κ (Ty α) → Type _
--   | nil : USubstL σ Γ []
--   | cons : USubst σ Γ Δ → USubstL σ Γ L → USubstL σ Γ (sorry :: L)

-- def UTerminator.Wf.subst {Γ Δ Γ' : Ctx ν (Ty α)} {σ}
--   {t : UTerminator φ ν κ}
--   (hσ : Φ.USubst σ Γ' Γ) : t.Wf Γ L → (t.rewrite σ).Wf Γ' L
--   := sorry
