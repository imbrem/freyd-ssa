import FreydSSA.Term.Extrinsic.Subst
import FreydSSA.Body.Extrinsic.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

def UBody.Wf.subst {Γ Δ Γ' : Ctx ν (Ty α)} {σ}
  {b : UBody φ ν}
  (hσ : Φ.USubst σ Γ' Γ)
  (hσ' : ∀ x ∈  b.defs, σ x = UTm.var x)
  (hb : b.SSA Γ'.names) :
  b.Wf p Γ Δ → (Δ' : Ctx ν (Ty α)) × (b.rewrite σ).Wf p Γ' Δ' × Φ.USubst σ Δ' Δ
  | nil p w => ⟨Γ', nil p (Ctx.Wk.refl _), hσ.wk_exit w⟩
  | let1 de db =>
    let ⟨Δ', db', hσ'⟩ := db.subst
      (hσ.tensor (λh => hb.1 h (by simp [defs])) (hσ' _ (by simp [defs])))
      (λx hx => hσ' x (hx.tail _))
      (UBody.SSA.of_let1'' hb);
    ⟨Δ', let1 (de.subst hσ) db', hσ'⟩
  | let2 de db =>
    let ⟨Δ', db', hσ'⟩ := db.subst
      ((hσ.tensor
        (λh => hb.1 h (by simp [defs]))
        (hσ' _ (by simp [defs]))).tensor
          (List.not_mem_cons_of_ne_of_not_mem
            (λh => by cases h; simp [SSA, defs] at hb) -- TODO: factor out as lemma
            (λh => hb.1 h (by simp [defs])))
          (hσ' _ (by simp [defs])))
      (λx hx => hσ' x ((hx.tail _).tail _))
      (UBody.SSA.of_let2'' hb);
    ⟨Δ', let2 (de.subst hσ) db', hσ'⟩

def UBody.Wf.subst_wk {Γ Δ Γ' Δ' : Ctx ν (Ty α)} {σ}
  {b : UBody φ ν}
  (hσ : Φ.USubst σ Γ' Γ)
  (hσ' : ∀ x ∈  b.defs, σ x = UTm.var x)
  (hb : b.SSA Γ'.names)
  (db: b.Wf p Γ Δ)
  (dσb : (b.rewrite σ).Wf p Γ' Δ')
  : (db.subst hσ hσ' hb).1.Wk Δ'
  := match b, db, dσb with
  | UBody.nil, nil _ _, nil _ w => w
  | UBody.let1 _x _e _b, let1 de db, let1 de' dσb => by
    cases (de.subst hσ).tyEq de'
    exact subst_wk _ _ _ db dσb
  | UBody.let2 _x _y _e _b, let2 de db, let2 de' dσb => by
    cases (de.subst hσ).tyEq de'
    exact subst_wk _ _ _ db dσb

def UBody.WfM.subst {Γ Δ Γ' : Ctx ν (Ty α)} {σ}
  {b : UBody φ ν}
  (hσ : Φ.USubst σ Γ' Γ)
  (hσ' : ∀ x ∈  b.defs, σ x = UTm.var x)
  (hb : b.SSA Γ'.names) :
  b.WfM p Γ Δ → (Δ' : Ctx ν (Ty α)) × (b.rewrite σ).WfM p Γ' Δ' × Φ.USubst σ Δ' Δ
  | nil p w => ⟨Γ', nil p _, hσ⟩
  | let1 de db =>
    let ⟨Δ', db', hσ'⟩ := db.subst
      (hσ.tensor (λh => hb.1 h (by simp [defs])) (hσ' _ (by simp [defs])))
      (λx hx => hσ' x (hx.tail _))
      (UBody.SSA.of_let1'' hb);
    ⟨Δ', let1 (de.subst hσ) db', hσ'⟩
  | let2 de db =>
    let ⟨Δ', db', hσ'⟩ := db.subst
      ((hσ.tensor
        (λh => hb.1 h (by simp [defs]))
        (hσ' _ (by simp [defs]))).tensor
          (List.not_mem_cons_of_ne_of_not_mem
            (λh => by cases h; simp [SSA, defs] at hb) -- TODO: factor out as lemma
            (λh => hb.1 h (by simp [defs])))
          (hσ' _ (by simp [defs])))
      (λx hx => hσ' x ((hx.tail _).tail _))
      (UBody.SSA.of_let2'' hb);
    ⟨Δ', let2 (de.subst hσ) db', hσ'⟩

--TODO: Wf.subst is WfM.subst; formalize this...
