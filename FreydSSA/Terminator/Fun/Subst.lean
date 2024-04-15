import FreydSSA.Terminator.Fun.Basic
import FreydSSA.Term.Fun.Subst

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

inductive FLCtx.SubstBot
  : WithBot (FLabel ν (Ty α)) → USubst φ ν →  WithBot (FLabel ν (Ty α)) → Type _
  | bot (σ Γ) : SubstBot ⊥ σ Γ
  | subst (hσ : FCtx.Subst Γ σ Δ) (A : Ty α) : SubstBot (↑(FLabel.mk Γ A)) σ (↑(FLabel.mk Δ A))

-- TODO: composition, other such nonsense

def FLCtx.Subst (L : FLCtx κ ν (Ty α)) (σ : USubst φ ν) (K : FLCtx κ ν (Ty α))
  := ∀x, SubstBot (L x) σ (K x)

-- TODO: composition, other such nonsense

inductive FLCtx.PSubstBot
  : WithBot (FLabel ν (Ty α)) → USubst φ ν →  WithBot (FLabel ν (Ty α)) → Type _
  | bot (σ) : PSubstBot ⊥ σ ⊥
  | subst (hσ : FCtx.Subst Γ σ Δ) (A : Ty α) : PSubstBot (↑(FLabel.mk Γ A)) σ (↑(FLabel.mk Δ A))

def FLCtx.PSubstBot.toSubstBot
  {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  : PSubstBot Γ σ Δ → SubstBot Γ σ Δ
  | bot _ => SubstBot.bot _ _
  | subst hσ A => SubstBot.subst hσ A

def FLCtx.PSubst (L : FLCtx κ ν (Ty α)) (σ : USubst φ ν) (K : FLCtx κ ν (Ty α))
  := ∀x, PSubstBot (L x) σ (K x)

def FLCtx.PSubst.toSubst {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) : L.Subst σ K
  := λx => (hσ x).toSubstBot

-- TODO: PSubst for FWfM

-- TODO: refactor to dePSubst, and so on...

-- def UTerminator.FWf.subst {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
--   (hσ : Γ.Subst σ Δ)
--   : t.FWf Δ L → (L' : FLCtx κ ν (Ty α)) × (t.rewrite σ).FWf Γ L' × (L'.Subst σ L)
--   := sorry
