import FreydSSA.Term.Fun.Basic

variable {φ ν α} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq α]

-- TODO: figure out how to bind this correctly...
-- TODO: make into structure or smt?
-- TODO: should all this be a prop _for FCtx_?
def FCtx.Subst (Γ : FCtx ν (Ty α)) (σ : USubst φ ν) (Δ : FCtx ν (Ty α)) : Type _
  := ∀ x, (h : x ∈ Δ.support) -> (σ x).FWf 1 Γ (Δ.get x h)

theorem FCtx.Subst.allEq {Γ : FCtx ν (Ty α)} {σ : USubst φ ν} {Δ : FCtx ν (Ty α)}
  (hσ hσ' : FCtx.Subst Γ σ Δ) : @hσ = @hσ'
  := by funext _ _; apply UTm.FWf.allEq

def FCtx.Subst.refl (Γ : FCtx ν (Ty α)) : FCtx.Subst Γ (USubst.id φ ν) Γ
  := λ _ h => UTm.FWf.var 1 (by rw [Γ.get_eq h])

def FCtx.Subst.wkEntry {Γ' Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν}
  (w : Γ'.Wk Γ) (hσ : FCtx.Subst Γ σ Δ) : Γ'.Subst σ Δ
  := λ _ h => (hσ _ h).wk w

def FCtx.Subst.wkExit {Γ Δ Δ' : FCtx ν (Ty α)} {σ : USubst φ ν}
  (hσ : FCtx.Subst Γ σ Δ) (w : Δ.Wk Δ') : Γ.Subst σ Δ'
  := λ _ h => w.get_eq h ▸ hσ _ (w.support_subset h)

def FCtx.Subst.ofWk {Γ Δ : FCtx ν (Ty α)}
  (w : Γ.Wk Δ) : FCtx.Subst Γ (USubst.id φ ν) Δ
  := wkExit (refl Γ) w

def FCtx.Subst.refl_wk {Γ Δ : FCtx ν (Ty α)}
  (hσ : FCtx.Subst Γ (USubst.id φ ν) Δ) : Γ.Wk Δ
  := Wk.of_eq_on (λ x h => by cases hσ _ h with | var _ h' => rw [h', Δ.get_eq h])

def FCtx.Subst.to_ty_eq {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν} (hσ : FCtx.Subst Γ σ Δ)
: ∀ x, ∀ a : (Ty α), Δ x = a -> (σ x).FWf 1 Γ a
:= λ_ _ h => Δ.get_var _ _ h ▸ hσ _ (Δ.mem_support_of_var _ _ h)

def UTm.FWf.subst {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν} {e : UTm φ ν} (hσ : Γ.Subst σ Δ)
  : e.FWf p Δ A -> (e.rewrite σ).FWf p Γ A
  | var p w => (hσ.to_ty_eq _ _ w).of_pure
  | op hf de => op hf (de.subst hσ)
  | pair p dl dr => pair p (dl.subst hσ) (dr.subst hσ)
  | unit p => unit p
  | bool p b => bool p b

def FCtx.Subst.comp {Γ Δ Ξ : FCtx ν (Ty α)} {σ : USubst φ ν} {τ : USubst φ ν}
  (hσ : Γ.Subst σ Δ) (hτ : Δ.Subst τ Ξ) : Γ.Subst (τ.comp σ) Ξ
  := λ _ h => (hτ _ h).subst hσ

def FCtx.Subst.vars_sub_support {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν} (hσ : FCtx.Subst Γ σ Δ)
  : σ.vars Δ.support ⊆ Γ.support
  := σ.vars_sub Δ.support Γ.support (λx h => (hσ x h).vars_sub_support)

def FCtx.Subst.restrict {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν}
  (hσ : FCtx.Subst Γ σ Δ) : FCtx.Subst (Γ.restrict (σ.vars Δ.support)) σ Δ
  := λx h => (hσ x h).restrict.wk (FCtx.Wk.restrict_sub _ (σ.sub_vars Δ.support x h))

def FCtx.Subst.unrestrict {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν} {N : Finset ν}
  (hσ : FCtx.Subst (Γ.restrict R) σ Δ) : FCtx.Subst Γ σ Δ
  := hσ.wkEntry (FCtx.Wk.wk_restrict Γ _)

-- def FCtx.Subst.lsupExit {Γ Δ Ξ : FCtx ν (Ty α)} {σ : USubst φ ν}
--   (hσ : Γ.Subst σ Δ) (hσ' : Γ.Subst σ Ξ) : Γ.Subst σ (Δ.lsup Ξ)
--   := sorry

theorem FCtx.Subst.cmp {Γ Δ Γ' Δ' : FCtx ν (Ty α)} {σ : USubst φ ν}
  (hσ : Γ.Subst σ Δ) (hσ' : Γ'.Subst σ Δ') (hΓ : Γ.Cmp Γ') : Δ.Cmp Δ'
  := λx => if hΔ : x ∈ Δ.support then
    if hΔ' : x ∈ Δ'.support then by
      apply Or.inl
      have hΓl := (hσ _ hΔ).lsup (hσ' _ hΔ')
      have hΓr := hΓ.lsup_eq_rsup.symm ▸ (hσ _ hΔ).rsup (hσ' _ hΔ')
      rw [get_eq hΔ, get_eq hΔ', hΓl.tyEq hΓr]
    else by simp [(not_mem_support _).mp hΔ']
    else by simp [(not_mem_support _).mp hΔ]

def FCtx.Subst.lsup {Γ Δ Γ' Δ' : FCtx ν (Ty α)} {σ : USubst φ ν}
  (hσ : Γ.Subst σ Δ) (hσ' : Γ'.Subst σ Δ') (hΓ : Γ.Cmp Γ') : (Γ.lsup Γ').Subst σ (Δ.lsup Δ')
  := λx h => by
    let hΔ : x ∈ Δ.support := by simp only [lsup_support, Finset.mem_inter] at h; exact h.1
    let hΔ' : x ∈ Δ'.support := by simp only [lsup_support, Finset.mem_inter] at h; exact h.2
    have hΔc := hσ.cmp hσ' hΓ
    let hxΓ := hσ x hΔ
    let _hxΓ' := hσ' x hΔ' -- BUG: spurious unused variable warning
    rw [<-hΔc.lsup_wk_left.get_eq h] at hxΓ
    rw [<-hΔc.lsup_wk_right.get_eq h] at _hxΓ'
    exact hxΓ.lsup _hxΓ'

def FCtx.Subst.cons {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν}
  (x : ν) (A : Ty α) (hσ : Γ.Subst σ Δ) (hx : x ∉ Γ.support) : (Γ.cons x A).Subst (σ.cons x) (Δ.cons x A)
  := λy h => if p: x = y then
    σ.cons_eq_left p ▸ UTm.FWf.var 1 (by cases p; rw [Γ.cons_eq _ _ _ rfl, <-get_eq,  Δ.cons_eq _ _ _ rfl])
  else by
    rw [FCtx.cons_get_ne _ _ _ (Ne.symm p) _, σ.cons_ne p]
    exact (hσ _ (cons_mem_support_ne _ _ _ (Ne.symm p) h)).wk (Wk.cons_not_mem _ _ _ hx)

-- TODO: can even do an ordered SubstCons, where you erase everything _over_ a given x, and have everything over bottom
-- But that's pretty over-complicated...
def FCtx.SubstCons (Γ : FCtx ν (Ty α)) (σ : USubst φ ν) (Δ : FCtx ν (Ty α)) (N : Finset ν) : Type _
  := ∀ x, (h : x ∈ Δ.support) -> (σ x).FWf 1 (Γ.sdiff_except N x) (Δ.get _ h)

def FCtx.SubstCons.refl (Γ : FCtx ν (Ty α)) (N : Finset ν) : FCtx.SubstCons Γ (USubst.id φ ν) Γ N
  := λ_ h => UTm.FWf.var 1 (by simp [<-get_eq, sdiff_except, sdiff_app])

def FCtx.SubstCons.wkEntry {Γ' Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν}
  (w : Γ'.Wk Γ) (hσ : FCtx.SubstCons Γ σ Δ N) : Γ'.SubstCons σ Δ N
  := λ_ h => (hσ _ h).wk (w.sdiff _)

def FCtx.SubstCons.wkExit {Γ Δ Δ' : FCtx ν (Ty α)} {σ : USubst φ ν}
  (hσ : FCtx.SubstCons Γ σ Δ N) (w : Δ.Wk Δ') : Γ.SubstCons σ Δ' N
  := λ_ h => w.get_eq h ▸ hσ _ (w.support_subset h)

theorem FCtx.SubstCons.allEq {Γ : FCtx ν (Ty α)} {σ : USubst φ ν} {Δ : FCtx ν (Ty α)} {N : Finset ν}
  (hσ hσ' : FCtx.SubstCons Γ σ Δ N) : @hσ = @hσ'
  := by funext _ _; apply UTm.FWf.allEq

def FCtx.SubstCons.toSubst {Γ : FCtx ν (Ty α)} {σ : USubst φ ν} {Δ : FCtx ν (Ty α)} {N : Finset ν}
  (hσ : FCtx.SubstCons Γ σ Δ N) : FCtx.Subst Γ σ Δ
  := λ_ h => (hσ _ h).wk (FCtx.Wk.sdiff_except Γ N _)

def FCtx.SubstCons.ofSubst {Γ : FCtx ν (Ty α)} {σ : USubst φ ν} {Δ : FCtx ν (Ty α)} {N : Finset ν}
  (hσ : FCtx.Subst Γ σ Δ) (hΓ : Disjoint Γ.support N) : FCtx.SubstCons Γ σ Δ N
  := λ_ h => (Γ.sdiff_except_eq_disjoint _ _ hΓ).symm ▸ hσ _ h

def FCtx.SubstCons.subset {Γ : FCtx ν (Ty α)} {σ : USubst φ ν} {Δ : FCtx ν (Ty α)} {N N' : Finset ν}
  (hσ : FCtx.SubstCons Γ σ Δ N) (hN : N' ⊆ N) : FCtx.SubstCons Γ σ Δ N'
  := λ_ h => (hσ _ h).wk (FCtx.Wk.sdiff_subset _ _ _ (Finset.erase_subset_erase _ hN))

def FCtx.SubstCons.cons {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν} {N : Finset ν}
  (x : ν) (A : Ty α) (hσ : Γ.SubstCons σ Δ N) (hx : x ∈ N) : (Γ.cons x A).SubstCons (σ.cons x) (Δ.cons x A) N
  := λ{y} h => if p: x = y then
    σ.cons_eq_left p ▸ UTm.FWf.var 1 (by
    cases p
    simp [<-get_eq, cons_eq, sdiff_except, sdiff_app])
  else by
    rw [FCtx.cons_get_ne _ _ _ (Ne.symm p) _, σ.cons_ne p]
    exact (hσ _ (cons_mem_support_ne _ _ _ (Ne.symm p) h)).wk (by
      intro z
      simp only [sdiff_except, sdiff_app, Finset.mem_erase]
      split
      . exact Or.inr rfl
      . rename_i h'
        simp only [Classical.not_and_iff_or_not_not, not_not] at h'
        cases h' with
        | inl h' =>
          cases h'
          apply Or.inr
          rw [FCtx.cons_ne]
          exact Ne.symm p
        | inr h' =>
          if hz : z ∈ Γ.support then
            apply Or.inr
            rw [FCtx.cons_ne]
            intro hz
            cases hz
            exact h' hx
          else
            apply Or.inl
            simp only [<-not_mem_support]
            exact hz
    )

theorem FCtx.SubstCons.cmp {Γ Δ Γ' Δ' : FCtx ν (Ty α)} {σ : USubst φ ν}
  (hσ : Γ.SubstCons σ Δ N) (hσ' : Γ'.SubstCons σ Δ' N') (hΓ : Γ.Cmp Γ') : Δ.Cmp Δ'
  := hσ.toSubst.cmp hσ'.toSubst hΓ

def FCtx.SubstCons.lsup {Γ Δ Γ' Δ' : FCtx ν (Ty α)} {σ : USubst φ ν}
  (hσ : Γ.SubstCons σ Δ N) (hσ' : Γ'.SubstCons σ Δ' N) (hΓ : Γ.Cmp Γ') : (Γ.lsup Γ').SubstCons σ (Δ.lsup Δ') N
  := λx h => by
    let hΔ : x ∈ Δ.support := by simp only [lsup_support, Finset.mem_inter] at h; exact h.1
    let hΔ' : x ∈ Δ'.support := by simp only [lsup_support, Finset.mem_inter] at h; exact h.2
    have hΔc := hσ.toSubst.cmp hσ'.toSubst hΓ
    let hxΓ := hσ x hΔ
    let _hxΓ' := hσ' x hΔ' -- BUG: spurious unused variable warning
    rw [<-hΔc.lsup_wk_left.get_eq h] at hxΓ
    rw [<-hΔc.lsup_wk_right.get_eq h] at _hxΓ'
    let hres := hxΓ.lsup _hxΓ'
    rw [<-lsup_sdiff_except]
    exact hres

def FCtx.SubstCons.restrict {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν} {N : Finset ν}
  (hσ : FCtx.SubstCons Γ σ Δ N) : FCtx.SubstCons (Γ.restrict (σ.vars Δ.support)) σ Δ N
  := λx h => (hσ x h).restrict.wk (by
    rw [sdiff_except_restrict_comm]
    exact FCtx.Wk.restrict_sub _ (σ.sub_vars Δ.support x h)
  )

def FCtx.SubstCons.unrestrict {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν} {N : Finset ν}
  (hσ : FCtx.SubstCons (Γ.restrict R) σ Δ N) : FCtx.SubstCons Γ σ Δ N
  := hσ.wkEntry (FCtx.Wk.wk_restrict Γ _)

def FCtx.SubstCons.vars_sub_support {Γ Δ : FCtx ν (Ty α)} {σ : USubst φ ν} (hσ : FCtx.SubstCons Γ σ Δ N)
  : σ.vars Δ.support ⊆ Γ.support
  := hσ.toSubst.vars_sub_support
