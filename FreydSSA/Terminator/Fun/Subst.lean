import FreydSSA.Terminator.Fun.Basic
import FreydSSA.Term.Fun.Subst

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

inductive FLCtx.SubstBot
  : WithBot (FLabel ν (Ty α)) → USubst φ ν →  WithBot (FLabel ν (Ty α)) → Type _
  | bot (σ Γ) : SubstBot ⊥ σ Γ
  | subst {Γ Δ : FLabel ν (Ty α)} (hσ : FCtx.Subst Γ.live σ Δ.live) (hparam : Γ.param = Δ.param) : SubstBot (↑Γ) σ (↑Δ)

-- TODO: composition, other such nonsense

def FLCtx.Subst (L : FLCtx κ ν (Ty α)) (σ : USubst φ ν) (K : FLCtx κ ν (Ty α))
  := ∀x, SubstBot (L x) σ (K x)

-- TODO: composition, other such nonsense

inductive FLCtx.PSubstBot
  : WithBot (FLabel ν (Ty α)) → USubst φ ν →  WithBot (FLabel ν (Ty α)) → Type _
  | bot (σ) : PSubstBot ⊥ σ ⊥
  | subst {Γ Δ : FLabel ν (Ty α)} (hσ : FCtx.Subst Γ.live σ Δ.live) (hparam : Γ.param = Δ.param) : PSubstBot (↑Γ) σ (↑Δ)

theorem FLCtx.PSubstBot.bot_mp {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstBot Γ σ Δ) : Γ = ⊥ → Δ = ⊥
  := λh => by
    cases hσ with
    | bot => rfl
    | subst => cases h

theorem FLCtx.PSubstBot.bot_mpr {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstBot Γ σ Δ) : Δ = ⊥ → Γ = ⊥
  := λh => by
    cases hσ with
    | bot => rfl
    | subst => cases h

theorem FLCtx.PSubstBot.param_eq {Γ : FLabel ν (Ty α)} {σ : USubst φ ν} {Δ : FLabel ν (Ty α)}
  (hσ : @PSubstBot _ ν α Φ (↑Γ) σ (↑Δ)) : Γ.param = Δ.param
  := by cases hσ; assumption

def FLCtx.PSubstBot.toSubstBot
  {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  : PSubstBot Γ σ Δ → SubstBot Γ σ Δ
  | bot _ => SubstBot.bot _ _
  | subst hσ A => SubstBot.subst hσ A

def FLCtx.PSubst (L : FLCtx κ ν (Ty α)) (σ : USubst φ ν) (K : FLCtx κ ν (Ty α))
  := ∀x, PSubstBot (L x) σ (K x)

theorem FLCtx.PSubst.bot_mp {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : L x = ⊥ → K x = ⊥
  := (hσ x).bot_mp

theorem FLCtx.PSubst.bot_mpr {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : K x = ⊥ → L x = ⊥
  := (hσ x).bot_mpr

-- def FLCtx.PSubst.lsup
--   {L₁ L₂ : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K₁ K₂ : FLCtx κ ν (Ty α)}
--   (hσ₁ : L₁.PSubst σ K₁) (hσ₂ : L₂.PSubst σ K₂) : (L₁.lsup L₂).PSubst σ (K₁.lsup K₂)
--   := λx => by
--     simp only [lsup_app, lsup_bot]
--     split
--     . rename_i he
--       split
--       . exact hσ₂ x
--       . rename_i c
--         exact (c $ hσ₁.bot_mp _ he).elim
--       . rename_i he' _
--         simp [hσ₁.bot_mp _ he] at he'
--     . rename_i he c
--       split
--       . rename_i he'
--         exact (c $ hσ₁.bot_mpr _ he').elim
--       . exact hσ₁ x
--       . rename_i he'
--         simp [hσ₂.bot_mp _ he] at he'
--     . rename_i Γ₁ Γ₂ hLe₁ hLe₂
--       split
--       . rename_i he
--         simp [hσ₁.bot_mpr _ he] at hLe₁
--       . rename_i he _
--         simp [hσ₂.bot_mpr _ he] at hLe₂
--       . rename_i Δ₁ Δ₂ hKe₁ hKe₂
--         let h₁ := hKe₁ ▸ hLe₁ ▸ hσ₁ x;
--         let h₂ := hKe₂ ▸ hLe₂ ▸ hσ₂ x;
--         cases h₁
--         constructor
--         sorry -- TODO: lsup substitution
--         assumption
--         -- apply PSubstBot.subst

-- TODO: PSubst preserves compatibility

def FLCtx.PSubst.toSubst {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) : L.Subst σ K
  := λx => (hσ x).toSubstBot

def FCtx.Subst.toPSingleton {Γ : FCtx ν (Ty α)} {σ : USubst φ ν} {Δ : FCtx ν (Ty α)}
  (x : κ) (hσ : Γ.Subst σ Δ) (param : Ty α) : (Γ.toSingleton x param).PSubst σ (Δ.toSingleton x param)
  := λy => by
    if h : y = x then
      simp only [toSingleton, h, FLCtx.singleton_app, ↓reduceIte]
      constructor
      assumption
      rfl
    else
      simp only [toSingleton, h, FLCtx.singleton_app, ↓reduceIte]
      constructor

-- def UTerminator.FWfM.subst {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
--   (hσ : Γ.Subst σ Δ)
--   : t.FWfM Δ L → (L' : FLCtx κ ν (Ty α)) × (t.rewrite σ).FWfM Γ L' × (L'.PSubst σ L)
--   | br _ de rfl => ⟨_, br _ (de.subst hσ) rfl, hσ.toPSingleton _ _⟩
--   | ite de ds dt h rfl =>
--     let ⟨Ls', ds', σs'⟩ := ds.subst hσ;
--     let ⟨Lt', dt', σt'⟩ := dt.subst hσ;
--     ⟨_, ite (de.subst hσ) ds' dt' sorry rfl, σs'.lsup σt'⟩

-- TODO: PSubst for FWfM

-- TODO: refactor to dePSubst, and so on...

-- def UTerminator.FWf.subst {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
--   (hσ : Γ.Subst σ Δ)
--   : t.FWf Δ L → (L' : FLCtx κ ν (Ty α)) × (t.rewrite σ).FWf Γ L' × (L'.Subst σ L)
--   := sorry
