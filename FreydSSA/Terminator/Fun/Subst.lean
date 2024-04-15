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
  := λh => by cases hσ <;> simp at *

theorem FLCtx.PSubstBot.bot_mpr {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstBot Γ σ Δ) : Δ = ⊥ → Γ = ⊥
  := λh => by cases hσ <;> simp at *

theorem FLCtx.PSubstBot.is_some_mp {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstBot Γ σ Δ) : Γ.isSome → Δ.isSome
  := λh => by cases hσ <;> simp [Option.isSome] at *

theorem FLCtx.PSubstBot.is_some_mpr {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstBot Γ σ Δ) : Δ.isSome → Γ.isSome
  := λh => by cases hσ <;> simp [Option.isSome] at *

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

theorem FLCtx.PSubst.is_some_mp {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : (L x).isSome → (K x).isSome
  := (hσ x).is_some_mp

theorem FLCtx.PSubst.is_some_mpr {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : (K x).isSome → (L x).isSome
  := (hσ x).is_some_mpr

theorem FLCtx.PSubst.some_trg {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) (Γ : FLabel ν (Ty α)) : L x = some Γ → Σ'Δ, K x = some Δ
  := λh => ⟨(K x).get (hσ.is_some_mp x (by simp [h])), by simp⟩

def FLCtx.PSubst.lsup
  {L₁ L₂ : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K₁ K₂ : FLCtx κ ν (Ty α)}
  (hσ₁ : L₁.PSubst σ K₁) (hσ₂ : L₂.PSubst σ K₂) (hL : L₁.Cmp L₂) : (L₁.lsup L₂).PSubst σ (K₁.lsup K₂)
  := λx => by
    simp only [lsup_app, lsup_bot]
    split
    . rename_i he
      split
      . exact hσ₂ x
      . rename_i c
        exact (c $ hσ₁.bot_mp _ he).elim
      . rename_i he' _
        simp [hσ₁.bot_mp _ he] at he'
    . rename_i he c
      split
      . rename_i he'
        exact (c $ hσ₁.bot_mpr _ he').elim
      . exact hσ₁ x
      . rename_i he'
        simp [hσ₂.bot_mp _ he] at he'
    . rename_i Γ₁ Γ₂ hLe₁ hLe₂
      split
      . rename_i he
        simp [hσ₁.bot_mpr _ he] at hLe₁
      . rename_i he _
        simp [hσ₂.bot_mpr _ he] at hLe₂
      . rename_i Δ₁ Δ₂ hKe₁ hKe₂
        let h₁ := hKe₁ ▸ hLe₁ ▸ hσ₁ x;
        let h₂ := hKe₂ ▸ hLe₂ ▸ hσ₂ x;
        have hL := hLe₁ ▸ hLe₂ ▸ hL x
        cases h₁ with
        | subst hσ hparam =>
          cases h₂ with
          | subst hσ' hparam' =>
            constructor
            apply hσ.lsup hσ'
            cases hL with
            | both c => exact c.live
            exact hparam

-- theorem FCtx.Subst.cmp_label {Γ Δ Γ' Δ' : FLabel ν (Ty α)} {σ : USubst φ ν}
--   (hσ : Γ.live.Subst σ Δ.live) (hσ' : Γ'.live.Subst σ Δ'.live) (hΓ : Γ.Cmp Γ') : Δ.Cmp Δ'
--   := ⟨sorry, sorry⟩

theorem FLCtx.PSubstBot.cmp
  {Γ Δ Γ' Δ' : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν}
  (hσ : PSubstBot Γ σ Δ) (hσ' : PSubstBot Γ' σ Δ') (hΓ : FLCtx.CmpBot Γ Γ') : FLCtx.CmpBot Δ Δ'
  := by
    cases hσ with
    | bot => constructor
    | subst hΔ hp => cases hσ' with
      | bot => constructor
      | subst hΔ' hp' =>
        cases hΓ with
        | both hΓ =>
          constructor
          constructor
          exact hΔ.cmp hΔ' hΓ.live
          rw [<-hp, <-hp', hΓ.param]

theorem FLCtx.PSubst.cmp
  {L₁ L₂ : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K₁ K₂ : FLCtx κ ν (Ty α)}
  (hσ₁ : L₁.PSubst σ K₁) (hσ₂ : L₂.PSubst σ K₂) (hL : L₁.Cmp L₂) : K₁.Cmp K₂
  := λx => (hσ₁ x).cmp (hσ₂ x) (hL x)

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

-- TODO: use LEq lore

-- def UTerminator.FWfM.subst {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
--   (hσ : Γ.Subst σ Δ)
--   : t.FWfM Δ L → (L' : FLCtx κ ν (Ty α)) × (t.rewrite σ).FWfM Γ L' × (L'.PSubst σ L)
--   | br _ de rfl => ⟨_, br _ (de.subst hσ) rfl, hσ.toPSingleton _ _⟩
--   | ite de ds dt h rfl =>
--     let ⟨Ls', ds', σs'⟩ := ds.subst hσ;
--     let ⟨Lt', dt', σt'⟩ := dt.subst hσ;
--     ⟨_, ite (de.subst hσ) ds' dt' sorry rfl, σs'.lsup σt'⟩

-- def UTerminator.FWf.subst {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
--   (hσ : Γ.Subst σ Δ)
--   : t.FWf Δ L → (L' : FLCtx κ ν (Ty α)) × (t.rewrite σ).FWf Γ L' × (L'.Subst σ L)
--   := sorry
