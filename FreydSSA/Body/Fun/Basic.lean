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

--TODO: cmpTrg lore

--TODO: FWf.comp

--TODO: inf/sup lore

inductive UBody.FWfM : Purity → FCtx ν (Ty α) → UBody φ ν → FCtx ν (Ty α) → Type _
  | nil (p Γ) : FWfM p Γ nil Γ
  | let1 (x) : e.FWf p Γ A → FWfM p (Γ.cons x A) t Δ
    → FWfM p Γ (let1 x e t) Δ
  | let2 (x y) : e.FWf p Γ (Ty.pair A B) →
    FWfM p ((Γ.cons x A).cons y B) t Δ → FWfM p Γ (let2 x y e t) Δ

--TODO: min/max lore, e.g. FWf maxTrg and so on...

--TODO: FWf'
