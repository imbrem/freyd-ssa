import FreydSSA.Term.Fun.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

-- TODO: figure out how to bind this correctly...
-- TODO: make into structure or smt?
def FCtx.Subst (Γ : FCtx ν (Ty α)) (σ : USubst φ ν) (Δ : FCtx ν (Ty α)) : Type _
  := ∀ {x}, (h : x ∈ Δ.support) -> (σ x).FWf 1 Γ (Δ.get h)

theorem FCtx.Subst.allEq {Γ : FCtx ν (Ty α)} {σ : USubst φ ν} {Δ : FCtx ν (Ty α)}
  (hσ hσ' : FCtx.Subst Γ σ Δ) : @hσ = @hσ'
  := by funext _ _; apply UTm.FWf.allEq

def FCtx.Subst.refl (Γ : FCtx ν (Ty α)) : FCtx.Subst Γ (USubst.id φ ν) Γ
  := λ h => UTm.FWf.var 1 (by rw [Γ.get_eq h])

def FCtx.Subst.wkEntry {Γ' Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν}
  (w : Γ'.Wk Γ) (hσ : FCtx.Subst Γ σ Δ) : Γ'.Subst σ Δ
  := λ h => (hσ h).wk w

def FCtx.Subst.wkExit {Γ Δ Δ' : FCtx ν (Ty α)} {σ : USubst φ ν}
  (hσ : FCtx.Subst Γ σ Δ) (w : Δ.Wk Δ') : Γ.Subst σ Δ'
  := λ h => w.get_eq h ▸ hσ (w.support_subset h)

def FCtx.Subst.ofWk {Γ Δ : FCtx ν (Ty α)}
  (w : Γ.Wk Δ) : FCtx.Subst Γ (USubst.id φ ν) Δ
  := wkExit (refl Γ) w

def FCtx.Subst.refl_wk {Γ Δ : FCtx ν (Ty α)}
  (hσ : FCtx.Subst Γ (USubst.id φ ν) Δ) : Γ.Wk Δ
  := Wk.of_eq_on (λ x h => by cases hσ h with | var _ h' => rw [h', Δ.get_eq h])

def FCtx.Subst.to_ty_eq {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν} (hσ : FCtx.Subst Γ σ Δ)
: ∀ {x}, ∀ {a : (Ty α)}, Δ x = a -> (σ x).FWf 1 Γ a
:= λh => Δ.get_var h ▸ hσ (Δ.mem_support_of_var _ _ h)

def UTm.FWf.subst {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν} {e : UTm φ ν} (hσ : Γ.Subst σ Δ)
  : e.FWf p Δ A -> (e.rewrite σ).FWf p Γ A
  | var p w => (hσ.to_ty_eq w).of_pure
  | op hf de => op hf (de.subst hσ)
  | pair p dl dr => pair p (dl.subst hσ) (dr.subst hσ)
  | unit p => unit p
  | bool p b => bool p b

def FCtx.Subst.comp {Γ Δ Ξ : FCtx ν (Ty α)} {σ : USubst φ ν} {τ : USubst φ ν}
  (hσ : Γ.Subst σ Δ) (hτ : Δ.Subst τ Ξ) : Γ.Subst (τ.comp σ) Ξ
  := λ h => (hτ h).subst hσ

-- def FCtx.Subst.cons {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν}
--   (x : ν) (A : Ty α) (hσ : Γ.Subst σ Δ) (hx : x ∉ Γ.support) : (Γ.cons x A).Subst (σ.cons x) (Δ.cons x A)
--   := λ{y} h => if p: x = y then
--     σ.cons_eq_left p ▸ UTm.FWf.var 1 (by cases p; rw [Γ.cons_eq _ _ _ rfl, <-get_eq,  Δ.cons_eq _ _ _ rfl])
--   else
--     -- (FCtx.cons_get_ne _ _ _ p _).symm ▸
--       σ.cons_ne p ▸
--         (hσ (cons_mem_support_ne _ _ _ (Ne.symm p) h)).wk (Wk.cons_not_mem _ _ _ hx)
