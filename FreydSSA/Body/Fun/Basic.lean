import FreydSSA.Term.Fun.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

inductive UBody.FWf : Purity → FCtx ν (Ty α) → UBody φ ν → FCtx ν (Ty α) → Type _
  | nil (p) : Γ.Wk Δ → FWf p Γ nil Δ
  | let1 (x) : e.FWf p Γ A → FWf p (Γ.update x A) t Δ
    → FWf p Γ (let1 x e t) Δ
  | let2 (x y) : e.FWf p Γ (Ty.pair A B) →
    FWf p ((Γ.update x A).update y B) t Δ → FWf p Γ (let2 x y e t) Δ

def UBody.FWf.wkEntry {Γ' Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} (w: Γ'.Wk Γ)
  : FWf p Γ t Δ → FWf p Γ' t Δ
  | nil _ w' => nil _ (w.comp w')
  | let1 x de dt => let1 x (de.wk w) (dt.wkEntry (w.update x _))
  | let2 x y de dt => let2 x y (de.wk w) (dt.wkEntry ((w.update x _).update y _))

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

def UBody.FWf.maxTrg {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} : FWf p Γ t Δ → FCtx ν (Ty α)
  | @nil _ _ _ _ _ Γ _ _ _ => Γ
  | let1 _ _ dt => dt.maxTrg
  | let2 _ _ _ dt => dt.maxTrg

theorem UBody.FWf.maxTrg_wk {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} (dt : FWf p Γ t Δ)
  : dt.maxTrg.Wk Δ := by induction dt <;> assumption

--TODO: cmpTrg lore

--TODO: FWf.comp

--TODO: inf/sup lore

inductive UBody.FWfM : Purity → FCtx ν (Ty α) → UBody φ ν → FCtx ν (Ty α) → Type _
  | nil (p Γ) : FWfM p Γ nil Γ
  | let1 (x) : e.FWf p Γ A → FWfM p (Γ.update x A) t Δ
    → FWfM p Γ (let1 x e t) Δ
  | let2 (x y) : e.FWf p Γ (Ty.pair A B) →
    FWfM p ((Γ.update x A).update y B) t Δ → FWfM p Γ (let2 x y e t) Δ

-- BUG: spurious unused variable warning
set_option linter.unusedVariables false in
def UBody.FWfM.toFWf {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} : FWfM p Γ t Δ → FWf p Γ t Δ
  | nil _ _ => FWf.nil _ (FCtx.Wk.refl _)
  | let1 x de dt => FWf.let1 x de dt.toFWf
  | let2 x y de dt => FWf.let2 x y de dt.toFWf

def UBody.FWf.toFWfM {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} : (dt : FWf p Γ t Δ) → FWfM p Γ t dt.maxTrg
  | FWf.nil _ w => FWfM.nil _ _
  | FWf.let1 x de dt => FWfM.let1 x de dt.toFWfM
  | FWf.let2 x y de dt => FWfM.let2 x y de dt.toFWfM

structure UBody.FWf' (p : Purity) (Γ : FCtx ν (Ty α)) (t : UBody φ ν) (Δ : FCtx ν (Ty α)) :=
  (live : FCtx ν (Ty α))
  (FWfM : FWfM p Γ t live)
  (wk : live.Wk Δ)

def UBody.FWf'.toFWf {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} (dt : UBody.FWf' p Γ t Δ) : FWf p Γ t Δ := dt.FWfM.toFWf.wkExit dt.wk

def UBody.FWf.factor {Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} (dt : FWf p Γ t Δ) : UBody.FWf' p Γ t Δ where
  live := dt.maxTrg
  FWfM := dt.toFWfM
  wk := dt.maxTrg_wk

--TODO: min/max lore, e.g. FWf maxTrg and so on...

--TODO: FWf'
