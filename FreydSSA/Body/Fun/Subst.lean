import FreydSSA.Body.Fun.Basic
import FreydSSA.Term.Fun.Subst

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

--TODO: _capture avoiding_ substitution of σ, so as not to change newly bound variables
--TODO: also, try _minimal new substitution_, and so on...
-- def UBody.FWf.Subst {Γ' Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} {σ : ν → UTm φ ν}
--   (hσ : Γ'.Subst σ Γ) (dt : t.FWf p Γ Δ)
--   : (Δ' : FCtx ν (Ty α)) × t.FWf p Γ' Δ' × Δ'.Subst σ Δ
--   := sorry
