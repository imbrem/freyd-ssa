import Mathlib.Data.List.Basic
import Std.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Init.Classical

import FreydSSA.Ctx
import FreydSSA.InstSet
import FreydSSA.Tm

inductive InstSet.Subst (Φ : InstSet (Ty α)) : Ctx ν (Ty α) → Ctx ν (Ty α) → Type _
| nil (Γ) : Subst Φ Γ []
| cons {Γ Δ} :
  Φ.Tm 1 Γ A →
  Subst Φ Γ Δ →
  Subst Φ Γ (⟨x, A⟩::Δ)

def InstSet.Subst.wk_entry {Φ : InstSet (Ty α)}
  {Γ Δ Ξ : Ctx ν (Ty α)} (w: Γ.Wk Δ) : Φ.Subst Δ Ξ → Φ.Subst Γ Ξ
  | nil _ => nil _
  | cons e σ => cons (e.wk w) (σ.wk_entry w)

def InstSet.Subst.wk_exit {Φ : InstSet (Ty α)}
  {Γ Δ Ξ : Ctx ν (Ty α)} : Φ.Subst Γ Δ → Δ.Wk Ξ → Φ.Subst Γ Ξ
  | nil _, Ctx.Wk.nil => nil _
  | cons e σ, Ctx.Wk.cons _ w  => cons e (σ.wk_exit w)
  | cons _ σ, Ctx.Wk.skip _ w  => σ.wk_exit w

def InstSet.Subst.var {Φ : InstSet (Ty α)}
  {Γ Δ : Ctx ν (Ty α)} (σ : Φ.Subst Γ Δ) (hx : Δ.Wk [⟨x, A⟩])
  : Φ.Tm 1 Γ A := match σ.wk_exit hx with
  | cons e _ => e

def InstSet.Tm.subst {Φ : InstSet (Ty α)} {p : Purity}
  {Γ Δ : Ctx ν (Ty α)} (σ : Φ.Subst Γ Δ) {A : Ty α}
  : Φ.Tm p Δ A → Φ.Tm p Γ A
  | var _ w => σ.var w
  | op f e => op f (e.subst σ)
  | pair p l r => pair p (l.subst σ) (r.subst σ)
  | unit p => unit p
  | bool p b => bool p b

def InstSet.Subst.comp {Φ : InstSet (Ty α)}
  {Γ Δ Ξ : Ctx ν (Ty α)} (σ: Φ.Subst Γ Δ) : Φ.Subst Δ Ξ → Φ.Subst Γ Ξ
  | nil _ => nil _
  | cons e τ => cons (e.subst σ) (σ.comp τ)

--TODO: Subst.id, Subst.comp_id

--TODO: Subst.comp_assoc

--TODO: Subst.ofWk, Subst.comp_wk, Subst.wk_comp, Subst.wk_comp_wk, etc.

--TODO: Subst.Iso for alpha conversion...

--TODO: Isomorphic substitutions for the same input/output contexts are equal

--TODO: Isomorphic terms can be substituted for each other

--TODO: Substitution for bodies, terminators, blocks, CFGs, regions, and generalized regions
