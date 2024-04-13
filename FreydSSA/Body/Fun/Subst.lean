import Mathlib.Order.Disjoint

import FreydSSA.Body.Fun.Basic
import FreydSSA.Term.Fun.Subst

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

-- def UBody.FWf.substCons {Γ' Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} {σ : USubst φ ν}
--   (hσ : Γ'.SubstCons σ Γ N)
--   (hN : t.defs.toFinset ⊆ N)
--   : t.FWf p Γ Δ → (Δ' : FCtx ν (Ty α)) × (t.subst σ).FWf p Γ' Δ' × Δ'.SubstCons (σ.cons_list t.defs) Δ N
--   | nil p w => ⟨Γ', nil p (FCtx.Wk.refl _), hσ.wkExit w⟩
--   | let1 x de dt =>
--     let dt' := dt.substCons (hσ.cons _ _ (hN (by simp [defs]))) (Finset.Subset.trans (by simp [defs]) hN);
--     ⟨dt'.1, let1 x (de.subst hσ.toSubst) dt'.2.1, by
--       simp [defs, USubst.cons_cons_list_rev]
--       exact dt'.2.2⟩
--   | let2 x y de dt =>
--     -- TODO: cons₂, insert₂
--     -- let dt' := dt.substCons sorry (Finset.Subset.trans sorry hN);
--     sorry

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
