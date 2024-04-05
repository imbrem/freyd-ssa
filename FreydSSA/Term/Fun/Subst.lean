import FreydSSA.Term.Fun.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

def FCtx.Subst (Γ : FCtx ν (Ty α)) (σ : ν → UTm φ ν) (Δ : FCtx ν (Ty α)) : Type _
  := ∀ {x}, (h : x ∈ Δ.support) -> (σ x).FWf 1 Γ (Δ.get h)

def FCtx.Subst.refl (Γ : FCtx ν (Ty α)) : FCtx.Subst Γ (@UTm.var φ ν) Γ
  := λ h => UTm.FWf.var 1 (by rw [Γ.get_eq h])

def FCtx.Subst.wk_entry {Γ' Γ Δ : FCtx ν (Ty α)} {σ : ν → UTm φ ν}
  (w : Γ'.Wk Γ) (hσ : FCtx.Subst Γ σ Δ) : Γ'.Subst σ Δ
  := λ h => (hσ h).wk w

def FCtx.Subst.wk_exit {Γ Δ Δ' : FCtx ν (Ty α)} {σ : ν → UTm φ ν}
  (hσ : FCtx.Subst Γ σ Δ) (w : Δ.Wk Δ') : Γ.Subst σ Δ'
  := λ h => w.get_eq h ▸ hσ (w.support_subset h)

def FCtx.Subst.to_ty_eq {Γ Δ : FCtx ν (Ty α)} {σ : ν → UTm φ ν} (hσ : FCtx.Subst Γ σ Δ)
: ∀ {x}, ∀ {a : (Ty α)}, Δ x = a -> (σ x).FWf 1 Γ a
:= λh => Δ.get_var h ▸ hσ (Δ.mem_support_of_var _ _ h)

def UTm.FWf.subst {Γ Δ : FCtx ν (Ty α)} {σ : ν → UTm φ ν} {e : UTm φ ν} (hσ : Γ.Subst σ Δ)
  : e.FWf p Δ A -> (e.rewrite σ).FWf p Γ A
  | var p w => (hσ.to_ty_eq w).of_pure
  | op hf de => op hf (de.subst hσ)
  | pair p dl dr => pair p (dl.subst hσ) (dr.subst hσ)
  | unit p => unit p
  | bool p b => bool p b
