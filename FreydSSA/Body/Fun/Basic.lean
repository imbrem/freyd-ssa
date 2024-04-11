import FreydSSA.Term.Fun.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

inductive UBody.FWf : FCtx ν (Ty α) → UBody φ ν → FCtx ν (Ty α) → Type _
  | nil {Γ Δ} : Γ.Wk Δ → FWf Γ nil Δ
  | let1 (x) : e.FWf p Γ A → FWf (Γ.cons x A) t Δ → FWf Γ (let1 x e t) Δ
  | let2 (x y)
    : e.FWf p Γ (Ty.pair A B) → FWf ((Γ.cons x A).cons y B) t Δ → FWf Γ (let2 x y e t) Δ

def UBody.FWf.wk_entry {Γ' Γ Δ : FCtx ν (Ty α)} {t : UBody φ ν} (w: Γ'.Wk Γ)
  : FWf Γ t Δ → FWf Γ' t Δ
  | nil w' => nil (w.comp w')
  | let1 x de dt => let1 x (de.wk w) (dt.wk_entry (w.cons x _))
  | let2 x y de dt => let2 x y (de.wk w) (dt.wk_entry ((w.cons x _).cons y _))

def UBody.FWf.wk_exit {Γ Δ Δ' : FCtx ν (Ty α)} {t : UBody φ ν} (dt : FWf Γ t Δ) (w: Δ.Wk Δ')
  : FWf Γ t Δ' := match dt with
  | nil w' => nil (w'.comp w)
  | let1 x de dt => let1 x de (dt.wk_exit w)
  | let2 x y de dt => let2 x y de (dt.wk_exit w)

--TODO: allEq, cmpTrg lore

--TODO: FWf.comp

--TODO: inf/sup lore

--TODO: min/max lore
