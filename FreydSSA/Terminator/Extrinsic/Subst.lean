import FreydSSA.Terminator.Extrinsic.Basic
import FreydSSA.Term.Extrinsic.Subst

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

-- def UTerminator.Wf.subst {Γ Δ Γ' : Ctx ν (Ty α)} {σ}
--   {t : UTerminator φ ν κ}
--   (hσ : Φ.USubst σ Γ' Γ) : t.Wf Γ L → (t.rewrite σ).Wf Γ' L
--   := sorry
