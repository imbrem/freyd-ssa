import Mathlib.Order.Disjoint

import FreydSSA.Body.Fun.Basic
import FreydSSA.Term.Fun.Subst

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

-- TODO: this requires SubstCons for the definition set. Disjoint support merely ensures that.
-- def UBody.FWf.subst {Γ' Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} {σ : USubst φ ν}
--   (hσ : Γ'.Subst σ Γ)
--   (hΓ' : Disjoint Γ'.support t.defs.toFinset)
--   : t.FWf p Γ Δ → (Δ' : FCtx ν (Ty α)) × t.FWf p Γ' Δ' × Δ'.Subst (σ.cons_list t.defs) Δ
--   | nil p w => ⟨Γ', nil p (FCtx.Wk.refl _), hσ.wkExit w⟩
--   | let1 x de dt =>
--     let dt' := dt.subst (hσ.cons _ _ sorry) sorry;
--     sorry
--   | let2 x y de dt => sorry

-- def UBody.FWf.substEntry {Γ' Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} {σ : USubst φ ν}
--   (hσ : Γ'.Subst σ Γ) (dt : t.FWf p Γ Δ) (hΔ : Δ.support ⊆ t.defs.toFinset)
--   : t.FWf p Γ Δ
--   := sorry

--TODO: minimal UBody lore
