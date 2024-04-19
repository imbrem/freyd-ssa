import FreydSSA.Term.Fun.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

inductive UBody.FWf : Purity → FCtx ν (Ty α) → UBody φ ν → FCtx ν (Ty α) → Type _
  | nil (p) : Γ.Wk Δ → FWf p Γ nil Δ
  | let1 (x) : e.FWf p Γ A → FWf p (Γ.cons x A) t Δ
    → FWf p Γ (let1 x e t) Δ
  | let2 (x y) : e.FWf p Γ (Ty.pair A B) →
    FWf p ((Γ.cons x A).cons y B) t Δ → FWf p Γ (let2 x y e t) Δ

def UBody.FWf.wkEntry {Γ' Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} (w: Γ'.Wk Γ)
  : FWf p Γ t Δ → FWf p Γ' t Δ
  | nil _ w' => nil _ (w.comp w')
  | let1 x de dt => let1 x (de.wk w) (dt.wkEntry (w.cons x _))
  | let2 x y de dt => let2 x y (de.wk w) (dt.wkEntry ((w.cons x _).cons y _))

def UBody.FWf.wkExit {Γ Δ Δ' : FCtx ν (Ty α)} {t : UBody φ ν} (dt : FWf p Γ t Δ) (w: Δ.Wk Δ')
  : FWf p Γ t Δ' := match dt with
  | nil _ w' => nil _ (w'.comp w)
  | let1 x de dt => let1 x de (dt.wkExit w)
  | let2 x y de dt => let2 x y de (dt.wkExit w)

theorem UBody.FWf.allEq {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} (dt : FWf p Γ t Δ) (dt' : FWf p Γ t Δ)
  : dt = dt' := by induction dt with
  | nil => cases dt'; rfl
  | let1 x de dt I => cases dt' with | let1 x de' dt' =>
    cases de.tyEq de'
    cases de.allEq de'
    rw [I]
  | let2 x y de dt I => cases dt' with | let2 x y de' dt' =>
    cases de.tyEq de'
    cases de.allEq de'
    rw [I]

def UBody.FWf.infTrg {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} : FWf p Γ t Δ → FCtx ν (Ty α)
  | @nil _ _ _ _ _ Γ _ _ _ => Γ
  | let1 _ _ dt => dt.infTrg
  | let2 _ _ _ dt => dt.infTrg

def UBody.FWf.toInf {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} : (dt : FWf p Γ t Δ) → FWf p Γ t dt.infTrg
  | nil _ _ => nil _ (FCtx.Wk.refl _)
  | let1 _ de dt => let1 _ de dt.toInf
  | let2 _ _ de dt => let2 _ _ de dt.toInf

theorem UBody.FWf.infTrg_wk {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} (dt : FWf p Γ t Δ)
  : dt.infTrg.Wk Δ := by induction dt <;> assumption

theorem UBody.FWf.infTrg_eq {Γ Δ Δ' : FCtx ν (Ty α)} {t : UBody φ ν}
  (dt : FWf p Γ t Δ) (dt' : FWf p Γ t Δ')
  : dt.infTrg = dt'.infTrg := by induction dt generalizing Δ' with
  | nil => cases dt'; rfl
  | let1 _ de _ I => cases dt' with | let1 _ de' dt' =>
    cases de.tyEq de'
    simp only [infTrg]; exact I dt'
  | let2 _ _ de _ I => cases dt' with | let2 _ _ de' dt' =>
    cases de.tyEq de'
    simp only [infTrg]; exact I dt'

theorem UBody.FWf.trgCmp {Γ Δ Δ' : FCtx ν (Ty α)} {t : UBody φ ν}
  (dt : FWf p Γ t Δ) (dt' : FWf p Γ t Δ')
  : Δ.Cmp Δ' := dt.infTrg_wk.cmp₂ (dt.infTrg_eq dt' ▸ dt'.infTrg_wk)

theorem UBody.FWf.infTrg_wk' {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} (dt : FWf p Γ t Δ) (dt' : FWf p Γ t Δ')
  : dt.infTrg.Wk Δ' := dt.infTrg_eq dt' ▸ dt'.infTrg_wk

def UBody.trgs (Γ : FCtx ν (Ty α)) (p : Purity) (t : UBody φ ν)
  : Set (FCtx ν (Ty α)) := λΔ => Nonempty (FWf p Γ t Δ)

theorem UBody.FWf.infTrg_is_least {Γ Δ Δ' : FCtx ν (Ty α)} {t : UBody φ ν}
  (dt : FWf p Γ t Δ) : IsLeast (t.trgs Γ p) dt.infTrg := ⟨⟨dt.toInf⟩, λ_ ⟨dt'⟩ => dt.infTrg_wk' dt'⟩

theorem UBody.FWf.infTrg_is_glb {Γ Δ Δ' : FCtx ν (Ty α)} {t : UBody φ ν}
  (dt : FWf p Γ t Δ) : IsGLB (t.trgs Γ p) dt.infTrg := ⟨λ_ ⟨dt'⟩ => dt.infTrg_wk' dt', λ_ hΔ => hΔ ⟨dt.toInf⟩⟩

-- def UBody.FWf.restrict {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} : FWf p Γ t Δ → FWf p (Γ.restrict (t.vars_for Δ.support)) t Δ
--   | @nil _ _ _ _ _ Γ _ _ _ => Γ
--   | let1 _ _ dt => dt.infTrg
--   | let2 _ _ _ dt => dt.infTrg

-- all sources must contain all variables in t.vars_for Δ.support, and in particular must contain all variables in t.vars

def UBody.srcs (p : Purity) (t : UBody φ ν) (Δ : FCtx ν (Ty α))
  : Set (FCtx ν (Ty α)) := λΓ => Nonempty (FWf p Γ t Δ)

-- given Γ, Γ.restrict (t.vars_for Δ.support) is the smallest source _compatible with Γ_

--TODO: FWf.comp

--TODO: inf/sup lore

inductive UBody.FWfM : Purity → FCtx ν (Ty α) → UBody φ ν → FCtx ν (Ty α) → Type _
  | nil (p Γ) : FWfM p Γ nil Γ
  | let1 (x) : e.FWf p Γ A → FWfM p (Γ.cons x A) t Δ
    → FWfM p Γ (let1 x e t) Δ
  | let2 (x y) : e.FWf p Γ (Ty.pair A B) →
    FWfM p ((Γ.cons x A).cons y B) t Δ → FWfM p Γ (let2 x y e t) Δ

-- BUG: spurious unused variable warning
set_option linter.unusedVariables false in
def UBody.FWfM.toFWf {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} : FWfM p Γ t Δ → FWf p Γ t Δ
  | nil _ _ => FWf.nil _ (FCtx.Wk.refl _)
  | let1 x de dt => FWf.let1 x de dt.toFWf
  | let2 x y de dt => FWf.let2 x y de dt.toFWf

def UBody.FWf.toFWfM {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} : (dt : FWf p Γ t Δ) → FWfM p Γ t dt.infTrg
  | FWf.nil _ w => FWfM.nil _ _
  | FWf.let1 x de dt => FWfM.let1 x de dt.toFWfM
  | FWf.let2 x y de dt => FWfM.let2 x y de dt.toFWfM

structure UBody.FWf' (p : Purity) (Γ : FCtx ν (Ty α)) (t : UBody φ ν) (Δ : FCtx ν (Ty α)) :=
  (live : FCtx ν (Ty α))
  (FWfM : FWfM p Γ t live)
  (wk : live.Wk Δ)

def UBody.FWf'.toFWf {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} (dt : UBody.FWf' p Γ t Δ) : FWf p Γ t Δ := dt.FWfM.toFWf.wkExit dt.wk

def UBody.FWf.factor {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} (dt : FWf p Γ t Δ) : UBody.FWf' p Γ t Δ where
  live := dt.infTrg
  FWfM := dt.toFWfM
  wk := dt.infTrg_wk

--TODO: FWf'

--TODO: body composition lore
