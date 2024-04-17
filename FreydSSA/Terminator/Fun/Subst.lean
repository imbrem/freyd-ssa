import FreydSSA.Terminator.Fun.Basic
import FreydSSA.Term.Fun.Subst

-- TODO: label-by-label substitution...

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

theorem FLCtx.PSubstBot.bot_iff {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstBot Γ σ Δ) : Γ = ⊥ ↔ Δ = ⊥
  := ⟨hσ.bot_mp, hσ.bot_mpr⟩

theorem FLCtx.PSubstBot.bot_ne_iff {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstBot Γ σ Δ) : Γ ≠ ⊥ ↔ Δ ≠ ⊥
  := by simp [hσ.bot_iff]

theorem FLCtx.PSubstBot.is_some_mp {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstBot Γ σ Δ) : Γ.isSome → Δ.isSome
  := λh => by cases hσ <;> simp [Option.isSome] at *

theorem FLCtx.PSubstBot.is_some_mpr {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstBot Γ σ Δ) : Δ.isSome → Γ.isSome
  := λh => by cases hσ <;> simp [Option.isSome] at *

theorem FLCtx.PSubstBot.param_eq {Γ : FLabel ν (Ty α)} {σ : USubst φ ν} {Δ : FLabel ν (Ty α)}
  (hσ : @PSubstBot _ ν α Φ (↑Γ) σ (↑Δ)) : Γ.param = Δ.param
  := by cases hσ; assumption

def FLCtx.PSubstBot.wkExit {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ Δ' : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstBot Γ σ Δ) (w : Δ ≤ Δ') : SubstBot Γ σ Δ'
  := match hσ, Δ' with
  | bot _, _ => SubstBot.bot _ _
  | subst hσ hparam, ⊥ => by simp at w
  | subst hσ hparam, some Δ' =>
    have w := FLabel.Wk.of_le_coe w;
    SubstBot.subst (hσ.wkExit w.live) (hparam.trans w.param)

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

theorem FLCtx.PSubst.bot_iff {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : L x = ⊥ ↔ K x = ⊥
  := (hσ x).bot_iff

theorem FLCtx.PSubst.bot_ne_iff {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : L x ≠ ⊥ ↔ K x ≠ ⊥
  := (hσ x).bot_ne_iff

theorem FLCtx.PSubst.mem_support_iff {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : x ∈ L.support ↔ x ∈ K.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubst.mem_support_mp {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : x ∈ L.support → x ∈ K.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubst.mem_support_mpr {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : x ∈ K.support → x ∈ L.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubst.not_mem_support_iff {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : x ∉ L.support ↔ x ∉ K.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubst.not_mem_support_mp {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : x ∉ L.support → x ∉ K.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubst.not_mem_support_mpr {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) (x : κ) : x ∉ K.support → x ∉ L.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubst.support_eq {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubst σ K) : L.support = K.support
  := Finset.ext hσ.mem_support_iff

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

-- BUG: another spurious unused variable warning. Something something "is water part of the essence of bread" something something
theorem FCtx.LWkBot.psubst_cmp₂ {Γ : FCtx ν (Ty α)} {Δ Ξ M M' : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν}
  (hΔ : Γ.LWkBot Δ) (hΞ : Γ.LWkBot Ξ) (_hΔ' : FLCtx.PSubstBot Δ σ M) (_hΞ' : FLCtx.PSubstBot Ξ σ M')
  (hM : FLCtx.CmpBot M M')
  : FLCtx.CmpBot Δ Ξ
  := match hΔ, hΞ with
  | bot, _ => by constructor
  | _, bot => by constructor
  | wk A w, wk A' w' => by
    constructor
    cases M with
    | none => cases _hΔ'
    | some M =>
      cases _hΔ'
      cases _hΞ'
      constructor
      exact w.cmp₂ w'
      cases hM
      rename_i h
      cases h
      aesop

theorem FCtx.LWk.psubst_cmp₂ {L K M M' : FLCtx κ ν (Ty α)} {Γ : FCtx ν (Ty α)} {σ : USubst φ ν}
  (hL : Γ.LWk L) (hK : Γ.LWk K) (hLM : L.PSubst σ M) (hKM : K.PSubst σ M') (hM : M.Cmp M')
  : L.Cmp K
  := λx => (hL x).psubst_cmp₂ (hK x) (hLM x) (hKM x) (hM x)

def UTerminator.FWfM.subst {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
  (hσ : Γ.Subst σ Δ)
  : t.FWfM Δ L → (L' : FLCtx κ ν (Ty α)) × (t.rewrite σ).FWfM Γ L' × (L'.PSubst σ L)
  | br _ de rfl => ⟨_, br _ (de.subst hσ) rfl, hσ.toPSingleton _ _⟩
  | ite de ds dt h rfl =>
    let ⟨_, ds', σs'⟩ := ds.subst hσ;
    let ⟨_, dt', σt'⟩ := dt.subst hσ;
    let ls' := ds'.trgLEq.toLWk;
    let lt' := dt'.trgLEq.toLWk;
    let hc := ls'.psubst_cmp₂ lt' σs' σt' h;
    ⟨_, ite (de.subst hσ) ds' dt' hc rfl, σs'.lsup σt' hc⟩

def FLCtx.PSubst.wkExit {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  {K' : FLCtx κ ν (Ty α)} (hσ : L.PSubst σ K) (w : K.Wk K') : L.Subst σ K'
  := λx => (hσ x).wkExit (w x)

def UTerminator.FWf'.subst {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
  (hσ : Γ.Subst σ Δ) (dt : t.FWf' Δ L) : (L' : FLCtx κ ν (Ty α)) × (t.rewrite σ).FWfM Γ L' × (L'.Subst σ L)
  := let dt' := dt.FWfM.subst hσ; ⟨dt'.1, dt'.2.1, dt'.2.2.wkExit dt.wk⟩

def UTerminator.FWf.subst {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
  (hσ : Γ.Subst σ Δ) (dt : t.FWf Δ L) : (L' : FLCtx κ ν (Ty α)) × (t.rewrite σ).FWfM Γ L' × (L'.Subst σ L)
  := dt.factor.subst hσ

-- TODO: casts to subst, minimization

inductive FLCtx.SubstConsBot
  : WithBot (FLabel ν (Ty α)) → USubst φ ν →  WithBot (FLabel ν (Ty α)) → Finset ν → Type _
  | bot (σ Γ N) : SubstConsBot ⊥ σ Γ N
  | subst {Γ Δ : FLabel ν (Ty α)} (hσ : FCtx.SubstCons Γ.live σ Δ.live N) (hparam : Γ.param = Δ.param) : SubstConsBot (↑Γ) σ (↑Δ) N

-- TODO: composition, other such nonsense

-- Consider: per-κ cons-ness
def FLCtx.SubstCons (L : FLCtx κ ν (Ty α)) (σ : USubst φ ν) (K : FLCtx κ ν (Ty α)) (N : Finset ν)
  := ∀x, SubstConsBot (L x) σ (K x) N

-- TODO: composition, other such nonsense

inductive FLCtx.PSubstConsBot
  : WithBot (FLabel ν (Ty α)) → USubst φ ν →  WithBot (FLabel ν (Ty α)) → Finset ν → Type _
  | bot (σ N) : PSubstConsBot ⊥ σ ⊥ N
  | subst {Γ Δ : FLabel ν (Ty α)} (hσ : FCtx.SubstCons Γ.live σ Δ.live N) (hparam : Γ.param = Δ.param) : PSubstConsBot (↑Γ) σ (↑Δ) N

theorem FLCtx.PSubstConsBot.bot_mp {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstConsBot Γ σ Δ N) : Γ = ⊥ → Δ = ⊥
  := λh => by cases hσ <;> simp at *

theorem FLCtx.PSubstConsBot.bot_mpr {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstConsBot Γ σ Δ N) : Δ = ⊥ → Γ = ⊥
  := λh => by cases hσ <;> simp at *

theorem FLCtx.PSubstConsBot.bot_iff {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstConsBot Γ σ Δ N) : Γ = ⊥ ↔ Δ = ⊥
  := ⟨hσ.bot_mp, hσ.bot_mpr⟩

theorem FLCtx.PSubstConsBot.is_some_mp {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstConsBot Γ σ Δ N) : Γ.isSome → Δ.isSome
  := λh => by cases hσ <;> simp [Option.isSome] at *

theorem FLCtx.PSubstConsBot.is_some_mpr {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstConsBot Γ σ Δ N) : Δ.isSome → Γ.isSome
  := λh => by cases hσ <;> simp [Option.isSome] at *

theorem FLCtx.PSubstConsBot.param_eq {Γ : FLabel ν (Ty α)} {σ : USubst φ ν} {Δ : FLabel ν (Ty α)}
  (hσ : @PSubstConsBot _ ν α Φ _ (↑Γ) σ (↑Δ) N) : Γ.param = Δ.param
  := by cases hσ; assumption

def FLCtx.PSubstConsBot.wkExit {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ Δ' : WithBot (FLabel ν (Ty α))}
  (hσ : PSubstConsBot Γ σ Δ N) (w : Δ ≤ Δ') : SubstConsBot Γ σ Δ' N
  := match hσ, Δ' with
  | bot _ _, _ => SubstConsBot.bot _ _ _
  | subst hσ hparam, ⊥ => by simp at w
  | subst hσ hparam, some Δ' =>
    have w := FLabel.Wk.of_le_coe w;
    SubstConsBot.subst (hσ.wkExit w.live) (hparam.trans w.param)

def FLCtx.PSubstConsBot.toSubstConsBot
  {Γ : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν} {Δ : WithBot (FLabel ν (Ty α))}
  : PSubstConsBot Γ σ Δ N → SubstConsBot Γ σ Δ N
  | bot _ _ => SubstConsBot.bot _ _ _
  | subst hσ A => SubstConsBot.subst hσ A

-- Consider: per-κ cons-ness
def FLCtx.PSubstCons (L : FLCtx κ ν (Ty α)) (σ : USubst φ ν) (K : FLCtx κ ν (Ty α)) (N : Finset ν)
  := ∀x, PSubstConsBot (L x) σ (K x) N

theorem FLCtx.PSubstCons.bot_mp {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) : L x = ⊥ → K x = ⊥
  := (hσ x).bot_mp

theorem FLCtx.PSubstCons.bot_mpr {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) : K x = ⊥ → L x = ⊥
  := (hσ x).bot_mpr

theorem FLCtx.PSubstCons.bot_iff {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) : L x = ⊥ ↔ K x = ⊥
  := (hσ x).bot_iff

theorem FLCtx.PSubstCons.mem_support_iff {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) : x ∈ L.support ↔ x ∈ K.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubstCons.mem_support_mp {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) : x ∈ L.support → x ∈ K.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubstCons.mem_support_mpr {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) : x ∈ K.support → x ∈ L.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubstCons.not_mem_support_iff {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) : x ∉ L.support ↔ x ∉ K.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubstCons.not_mem_support_mp {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) : x ∉ L.support → x ∉ K.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubstCons.not_mem_support_mpr {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) : x ∉ K.support → x ∉ L.support
  := by simp [FLCtx.mem_support, (hσ x).bot_iff]

theorem FLCtx.PSubstCons.is_some_mp {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) : (L x).isSome → (K x).isSome
  := (hσ x).is_some_mp

theorem FLCtx.PSubstCons.is_some_mpr {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) : (K x).isSome → (L x).isSome
  := (hσ x).is_some_mpr

theorem FLCtx.PSubstCons.some_trg {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) (x : κ) (Γ : FLabel ν (Ty α)) : L x = some Γ → Σ'Δ, K x = some Δ
  := λh => ⟨(K x).get (hσ.is_some_mp x (by simp [h])), by simp⟩

def FLCtx.PSubstCons.lsup
  {L₁ L₂ : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K₁ K₂ : FLCtx κ ν (Ty α)}
  (hσ₁ : L₁.PSubstCons σ K₁ N) (hσ₂ : L₂.PSubstCons σ K₂ N) (hL : L₁.Cmp L₂) : (L₁.lsup L₂).PSubstCons σ (K₁.lsup K₂) N
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

theorem FLCtx.PSubstConsBot.cmp
  {Γ Δ Γ' Δ' : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν}
  (hσ : PSubstConsBot Γ σ Δ N) (hσ' : PSubstConsBot Γ' σ Δ' N') (hΓ : FLCtx.CmpBot Γ Γ') : FLCtx.CmpBot Δ Δ'
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

theorem FLCtx.PSubstCons.cmp
  {L₁ L₂ : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K₁ K₂ : FLCtx κ ν (Ty α)}
  (hσ₁ : L₁.PSubstCons σ K₁ N) (hσ₂ : L₂.PSubstCons σ K₂ N') (hL : L₁.Cmp L₂) : K₁.Cmp K₂
  := λx => (hσ₁ x).cmp (hσ₂ x) (hL x)

def FLCtx.PSubstCons.toSubstCons {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  (hσ : L.PSubstCons σ K N) : L.SubstCons σ K N
  := λx => (hσ x).toSubstConsBot

def FCtx.SubstCons.toPSingleton {Γ : FCtx ν (Ty α)} {σ : USubst φ ν} {Δ : FCtx ν (Ty α)}
  (x : κ) (hσ : Γ.SubstCons σ Δ N) (param : Ty α) : (Γ.toSingleton x param).PSubstCons σ (Δ.toSingleton x param) N
  := λy => by
    if h : y = x then
      simp only [toSingleton, h, FLCtx.singleton_app, ↓reduceIte]
      constructor
      assumption
      rfl
    else
      simp only [toSingleton, h, FLCtx.singleton_app, ↓reduceIte]
      constructor

-- BUG: another spurious unused variable warning. Something something "is water part of the essence of bread" something something
theorem FCtx.LWkBot.psubstCons_cmp₂ {Γ : FCtx ν (Ty α)} {Δ Ξ M M' : WithBot (FLabel ν (Ty α))} {σ : USubst φ ν}
  (hΔ : Γ.LWkBot Δ) (hΞ : Γ.LWkBot Ξ) (_hΔ' : FLCtx.PSubstConsBot Δ σ M N) (_hΞ' : FLCtx.PSubstConsBot Ξ σ M' N')
  (hM : FLCtx.CmpBot M M')
  : FLCtx.CmpBot Δ Ξ
  := match hΔ, hΞ with
  | bot, _ => by constructor
  | _, bot => by constructor
  | wk A w, wk A' w' => by
    constructor
    cases M with
    | none => cases _hΔ'
    | some M =>
      cases _hΔ'
      cases _hΞ'
      constructor
      exact w.cmp₂ w'
      cases hM
      rename_i h
      cases h
      aesop

theorem FCtx.LWk.psubstCons_cmp₂ {L K M M' : FLCtx κ ν (Ty α)} {Γ : FCtx ν (Ty α)} {σ : USubst φ ν}
  (hL : Γ.LWk L) (hK : Γ.LWk K) (hLM : L.PSubstCons σ M N) (hKM : K.PSubstCons σ M' N') (hM : M.Cmp M')
  : L.Cmp K
  := λx => (hL x).psubstCons_cmp₂ (hK x) (hLM x) (hKM x) (hM x)

def UTerminator.FWfM.substCons {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
  (hσ : Γ.SubstCons σ Δ N)
  : t.FWfM Δ L → (L' : FLCtx κ ν (Ty α)) × (t.rewrite σ).FWfM Γ L' × (L'.PSubstCons σ L N)
  | br _ de rfl => ⟨_, br _ (de.subst hσ.toSubst) rfl, hσ.toPSingleton _ _⟩
  | ite de ds dt h rfl =>
    let ⟨_, ds', σs'⟩ := ds.substCons hσ;
    let ⟨_, dt', σt'⟩ := dt.substCons hσ;
    let ls' := ds'.trgLEq.toLWk;
    let lt' := dt'.trgLEq.toLWk;
    let hc := ls'.psubstCons_cmp₂ lt' σs' σt' h;
    ⟨_, ite (de.subst hσ.toSubst) ds' dt' hc rfl, σs'.lsup σt' hc⟩

def FLCtx.PSubstCons.wkExit {L : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {K : FLCtx κ ν (Ty α)}
  {K' : FLCtx κ ν (Ty α)} (hσ : L.PSubstCons σ K N) (w : K.Wk K') : L.SubstCons σ K' N
  := λx => (hσ x).wkExit (w x)

def UTerminator.FWf'.substCons {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
  (hσ : Γ.SubstCons σ Δ N) (dt : t.FWf' Δ L) : (L' : FLCtx κ ν (Ty α)) × (t.rewrite σ).FWfM Γ L' × (L'.SubstCons σ L N)
  := let dt' := dt.FWfM.substCons hσ; ⟨dt'.1, dt'.2.1, dt'.2.2.wkExit dt.wk⟩

def UTerminator.FWf.substCons {Γ : FCtx ν (Ty α)} {t : UTerminator φ ν κ}
  (hσ : Γ.SubstCons σ Δ N) (dt : t.FWf Δ L) : (L' : FLCtx κ ν (Ty α)) × (t.rewrite σ).FWfM Γ L' × (L'.SubstCons σ L N)
  := dt.factor.substCons hσ
