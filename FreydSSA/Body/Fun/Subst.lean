import FreydSSA.Body.Fun.Basic
import FreydSSA.Term.Fun.Subst

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

-- def UBody.FWf.subst {Γ' Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} {σ : USubst φ ν}
--   (hσ : Γ'.Subst σ Γ) (dt : t.FWf p Γ Δ)
--   : (Δ' : FCtx ν (Ty α)) × t.FWf p Γ' Δ' × Δ'.Subst (σ.cons_list t.defs) Δ
--   := sorry

-- def UBody.FWf.substEntry {Γ' Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} {σ : USubst φ ν}
--   (hσ : Γ'.Subst σ Γ) (dt : t.FWf p Γ Δ) (hΔ : Δ.support ⊆ t.defs.toFinset)
--   : t.FWf p Γ Δ
--   := sorry

--TODO: minimal UBody lore
