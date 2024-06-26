import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Init.Classical
import Mathlib.Order.SuccPred.Basic
import Mathlib.Data.Finset.Functor

import FreydSSA.Ctx
import FreydSSA.InstSet
import FreydSSA.Utils

variable {φ ν ν' κ κ' α β} [DecidableEq ν] [DecidableEq κ]

--TODO: map_inst

inductive UTm (φ : Type _) (ν  : Type _)
   : Type _ where
  | var : ν → UTm φ ν
  | op : φ → UTm φ ν → UTm φ ν
  | pair : UTm φ ν → UTm φ ν → UTm φ ν
  | unit : UTm φ ν
  | bool : Bool → UTm φ ν

def UTm.rename (σ : ν → ν') : UTm φ ν → UTm φ ν'
  | var x => var (σ x)
  | op f e => op f (e.rename σ)
  | pair l r => pair (l.rename σ) (r.rename σ)
  | unit => unit
  | bool b => bool b

theorem UTm.rename_id (e : UTm φ ν) : e.rename id = e
  := by induction e <;> simp [UTm.rename, *]

theorem UTm.rename_comp (σ : ν → ν') (σ' : ν' → ν'') (e : UTm φ ν)
  : e.rename (σ' ∘ σ) = (e.rename σ).rename σ'
  := by induction e <;> simp [UTm.rename, *]

def USubst (φ : Type _) (ν  : Type _) : Type _ := ν → UTm φ ν

def USubst.id (φ ν) : USubst φ ν := UTm.var

def USubst.cons (x : ν) (σ : USubst φ ν) : USubst φ ν
  := Function.update σ x (UTm.var x)

theorem USubst.cons_eq (x : ν) (σ : USubst φ ν) : (σ.cons x) x = UTm.var x := by
  simp [cons, Function.update]
theorem USubst.cons_eq_left {x y} (σ : USubst φ ν) (p : x = y)
  : (σ.cons x) y = UTm.var x := by
  simp [p, cons, Function.update]
theorem USubst.cons_eq_right {x y} (σ : USubst φ ν) (p : x = y)
  : (σ.cons x) y = UTm.var y := by
  simp [p, cons, Function.update]
theorem USubst.cons_ne {x y} (σ : USubst φ ν) (p : x ≠ y)
  : (σ.cons x) y = σ y := by
  simp only [cons, Function.update, eq_rec_constant, dite_eq_ite, ite_eq_right_iff]
  intro h
  exact (p (h.symm)).elim

theorem USubst.cons_comm (x y : ν) (σ : USubst φ ν) : USubst.cons x (USubst.cons y σ) = USubst.cons y (USubst.cons x σ) := by
  funext z
  simp only [cons, Function.update]
  split <;> split <;> aesop

theorem USubst.cons_id (x : ν) : (id φ ν).cons x = (id φ ν) := by
  funext z
  simp only [cons, Function.update, id]
  split <;> simp [*]

def USubst.cons_list (xs : List ν) (σ : USubst φ ν) : USubst φ ν
  := xs.foldr (λx σ => σ.cons x) σ

def USubst.cons_list' (xs : List ν) (σ : USubst φ ν) : USubst φ ν
  := xs.foldl (λσ x => σ.cons x) σ

theorem USubst.nil_cons_list (σ : USubst φ ν) : USubst.cons_list [] σ = σ := rfl

theorem USubst.cons_cons_list (x : ν) (xs : List ν) (σ : USubst φ ν)
  : USubst.cons_list (x :: xs) σ = (USubst.cons_list xs σ).cons x := rfl

theorem USubst.nil_cons_list' (σ : USubst φ ν) : USubst.cons_list' [] σ = σ := rfl

theorem USubst.cons_cons_list' (x : ν) (xs : List ν) (σ : USubst φ ν)
  : USubst.cons_list' (x :: xs) σ = (σ.cons x).cons_list' xs := rfl

theorem USubst.cons_list_cons_list'
  : @USubst.cons_list = @USubst.cons_list' := by
  funext _ _ _ xs σ
  induction xs generalizing σ with
  | nil => rfl
  | cons x xs I =>
    rw [cons_cons_list, cons_list', List.foldl_eq_of_comm', I]
    rfl
    intro τ x y
    funext z
    simp only [cons, Function.update]
    split
    . rename_i h
      cases h
      split
      . rename_i h
        cases h
        rfl
      . rfl
    . rfl

theorem USubst.eq_cons (x : ν) (σ : USubst φ ν) (h : σ x = UTm.var x) : σ.cons x = σ := by
  funext y
  simp only [cons, Function.update, eq_rec_constant, dite_eq_ite, ite_eq_right_iff]
  intro hy
  cases hy
  exact h.symm

theorem USubst.eq_cons_list (σ : USubst φ ν) (xs : List ν)
  (hσc : {x | x ∈ xs}.EqOn σ UTm.var)
  : σ.cons_list xs = σ := by
  induction xs with
  | nil => rfl
  | cons x xs I =>
    rw [cons_cons_list, I]
    funext y
    rw [cons, Function.update]
    split
    . rename_i h
      cases h
      rw [<-hσc (by simp)]
    . rfl
    apply hσc.mono
    simp
    aesop

theorem USubst.cons_cons_list_rev (x : ν) (xs : List ν) (σ : USubst φ ν)
  : USubst.cons_list (x :: xs) σ = USubst.cons_list xs (σ.cons x) := by
    rw [cons_list_cons_list', cons_cons_list', <-cons_list_cons_list']

theorem USubst.cons_list_split (xs : List ν) (σ : USubst φ ν)
  : USubst.cons_list xs σ = λx => if x ∈ xs then UTm.var x else σ x := by
  induction xs generalizing σ with
  | nil => simp [cons_list]
  | cons _ _ I =>
    funext x
    simp only [cons_cons_list, List.mem_cons, cons, Function.update, I]
    split <;> simp [*]

theorem USubst.cons_list_split_app (xs : List ν) (σ : USubst φ ν) (x : ν)
  : USubst.cons_list xs σ x = if x ∈ xs then UTm.var x else σ x := by rw [cons_list_split]

def USubst.cons_set (xs : Finset ν) (σ : USubst φ ν) : USubst φ ν
  := λx => if x ∈ xs then UTm.var x else σ x

theorem USubst.cons_set_split (xs : Finset ν) (σ : USubst φ ν)
  : USubst.cons_set xs σ = λx => if x ∈ xs then UTm.var x else σ x := rfl

theorem USubst.cons_set_split_app (xs : Finset ν) (σ : USubst φ ν) (x : ν)
  : USubst.cons_set xs σ x = if x ∈ xs then UTm.var x else σ x := rfl

def USubst.cons_list_eq_cons_set (xs : List ν) (σ : USubst φ ν) : USubst.cons_list xs σ = USubst.cons_set xs.toFinset σ := by
  rw [cons_list_split, cons_set_split]
  funext x
  congr 1
  simp

def UTm.rewrite (σ : ν → UTm φ ν') : UTm φ ν → UTm φ ν'
  | var x => σ x
  | op f e => op f (e.rewrite σ)
  | pair l r => pair (l.rewrite σ) (r.rewrite σ)
  | unit => unit
  | bool b => bool b

theorem UTm.rewrite_var {ν}
  (e : UTm φ ν) : e.rewrite UTm.var = e
  := by induction e <;> simp [UTm.rewrite, *]

theorem UTm.rename_rewrite
  (σ : ν → ν') (e : UTm φ ν) : e.rename σ = e.rewrite (UTm.var ∘ σ)
  := by induction e <;> simp [UTm.rename, UTm.rewrite, *]

def UTm.comp
  (σ : ν₁ → UTm φ ν₂) (σ' : ν₂ → UTm φ ν₃) (x : ν₁) : UTm φ ν₃
  := (σ x).rewrite σ'

theorem UTm.comp_var
  (σ : ν → UTm φ ν') : comp σ UTm.var = σ
  := by funext x; simp [comp, UTm.rewrite_var]

theorem UTm.var_comp
  (σ : ν → UTm φ ν') : comp UTm.var σ = σ
  := rfl

abbrev USubst.comp (σ : USubst φ ν) (τ : USubst φ ν) := UTm.comp σ τ

theorem UTm.rewrite_comp {ν ν' ν''}
  (σ : ν → UTm φ ν') (σ' : ν' → UTm φ ν'') (e : UTm φ ν)
  : e.rewrite (comp σ σ') = (e.rewrite σ).rewrite σ'
  := by induction e <;> simp [comp, rewrite, *]

theorem UTm.comp_assoc {ν ν' ν'' ν'''}
  (σ : ν → UTm φ ν') (σ' : ν' → UTm φ ν'') (σ'' : ν'' → UTm φ ν''')
  : comp (comp σ σ') σ'' = comp σ (comp σ' σ'')
  := by funext x; simp [comp, rewrite_comp]

def UTm.vars : UTm φ ν → Finset ν
  | var x => {x}
  | op _ e => e.vars
  | pair l r => l.vars ∪ r.vars
  | _ => {}

def USubst.vars (σ : USubst φ ν) (N : Finset ν) : Finset ν
  := Finset.sup N (λx => (σ x).vars)

theorem USubst.vars_sub (σ : USubst φ ν) (N : Finset ν) (M : Finset ν)
  (h: ∀x ∈ N, (σ x).vars ⊆ M) : USubst.vars σ N ⊆ M
  := @Finset.sup_le _ _ _ _ _ _ M h

theorem USubst.sub_vars (σ : USubst φ ν) (N : Finset ν)
  : ∀x ∈ N, (σ x).vars ⊆ σ.vars N
  := λx h => @Finset.le_sup _ _ _ _ _ (λx => (σ x).vars) x h

theorem USubst.prop_on_vars (σ : USubst φ ν) (N : Finset ν) (P : ν → Prop)
  (h : ∀x ∈ N, ∀y ∈ (σ x).vars, P y) : ∀x ∈ σ.vars N, P x
  := by
  simp only [vars, Finset.mem_sup, forall_exists_index, and_imp]
  intro y x hx hy
  exact h x hx y hy

theorem USubst.of_prop_on_vars (σ : USubst φ ν) (N : Finset ν) (P : ν → Prop)
  (h : ∀x ∈ σ.vars N, P x) : ∀x ∈ N, ∀y ∈ (σ x).vars, P y
  := by
  simp only [vars, Finset.mem_sup, forall_exists_index, and_imp] at h
  intro x hx y hy
  exact h y x hx hy

theorem USubst.prop_on_vars_iff (σ : USubst φ ν) (N : Finset ν) (P : ν → Prop)
  : (∀x ∈ N, ∀y ∈ (σ x).vars, P y) ↔ (∀x ∈ σ.vars N, P x)
  := ⟨prop_on_vars _ _ _, of_prop_on_vars _ _ _⟩

inductive UBody (φ : Type _) (ν  : Type _)
   : Type _ where
  | nil : UBody φ ν
  | let1 : ν → UTm φ ν → UBody φ ν → UBody φ ν
  | let2 : ν → ν → UTm φ ν → UBody φ ν → UBody φ ν

def UBody.rename {φ ν ν'}
  (σ : ν → ν') : UBody φ ν → UBody φ ν'
  | nil => nil
  | let1 x e b => let1 (σ x) (e.rename σ) (b.rename σ)
  | let2 x y e b => let2 (σ x) (σ y) (e.rename σ) (b.rename σ)

theorem UBody.rename_comp {φ ν ν' ν''}
  (σ : ν → ν') (σ' : ν' → ν'') (b : UBody φ ν)
  : b.rename (σ' ∘ σ) = (b.rename σ).rename σ'
  := by induction b <;> simp [UBody.rename, UTm.rename_comp, *]

def UBody.rewrite {φ ν}
  (σ : ν → UTm φ ν) : UBody φ ν → UBody φ ν
  | nil => nil
  | let1 x e b => let1 x (e.rewrite σ) (b.rewrite σ)
  | let2 x y e b => let2 x y (e.rewrite σ) (b.rewrite σ)

def UBody.subst
  (σ : USubst φ ν) : UBody φ ν → UBody φ ν
  | nil => nil
  | let1 x e b => let1 x (e.rewrite σ) (b.subst (σ.cons x))
  | let2 x y e b => let2 x y
    (e.rewrite σ)
    (b.subst ((σ.cons x).cons y))

def UBody.capture_rename
  (σ : ν → ν) : UBody φ ν → UBody φ ν
  | nil => nil
  | let1 x e b => let1 x (e.rename σ) (b.capture_rename (Function.update σ x x))
  | let2 x y e b => let2 x y (e.rename σ) (b.capture_rename (Function.update (Function.update σ x x) y y))

theorem UBody.capture_rename_subst
  (σ : ν → ν) (b : UBody φ ν)
  : b.capture_rename σ = b.subst (UTm.var ∘ σ)
  := by induction b generalizing σ <;>
    simp [capture_rename, UTm.rename_rewrite, subst, USubst.cons, Function.comp_update, *]

theorem UBody.rewrite_var
  (b : UBody φ ν) : b.rewrite UTm.var = b
  := by induction b <;> simp [UBody.rewrite, UTm.rewrite_var, *]

theorem UBody.subst_var
  (b : UBody φ ν) : b.subst UTm.var = b
  := by induction b <;> simp [UBody.subst, USubst.cons, UTm.rewrite_var, *]

theorem UBody.rewrite_comp
  (σ σ' : ν → UTm φ ν) (b : UBody φ ν)
  : b.rewrite (UTm.comp σ σ') = (b.rewrite σ).rewrite σ'
  := by induction b <;> simp [UBody.rewrite, UTm.rewrite_comp, *]

-- TODO: think about this
-- theorem UBody.subst_comp
--   (σ σ' : ν → UTm φ ν) (b : UBody φ ν)
--   : b.subst (UTm.comp σ σ') = (b.subst σ).subst σ'
--   := by induction b generalizing σ σ' with
--   | nil => rfl
--   | let1 x _ _ I =>
--     simp only [subst, UTm.rewrite_comp, let1.injEq, true_and]
--     rw [<-I]
--     congr
--     funext y
--     if h : y = x then
--       cases h
--       simp [UTm.comp, UTm.rewrite]
--     else
--       rw [Function.update_noteq h]
--       simp only [UTm.comp]
--       rw [Function.update_noteq h]
--   | let2 => sorry

def UBody.rewrite' {φ ν}
  (σ : ν → ν' ⊕ UTm φ ν') : UBody φ ν → UBody φ ν'
  | nil => nil
  | let1 x e b => match σ x with
    | Sum.inl x' => let1 x' (e.rewrite (λz => (σ z).elim UTm.var id)) (b.rewrite' σ)
    | Sum.inr _ => (b.rewrite' σ)
  | let2 x y e b => match σ x, σ y with
    | Sum.inl x', Sum.inl y'
      => let2 x' y' (e.rewrite (λz => (σ z).elim UTm.var id)) (b.rewrite' σ)
    | _, _ => (b.rewrite' σ)

def UBody.defs
  : UBody φ ν → List ν
  | nil => []
  | let1 x _ b => x :: b.defs
  | let2 x y _ b => x :: y :: b.defs

def UBody.vars
  : UBody φ ν → Finset ν
  | nil => ∅
  | let1 x e b => b.vars ∪ (e.vars.erase x)
  | let2 x y e b => b.vars ∪ ((e.vars.erase x).erase y)

def UBody.vars_for (t : UBody φ ν) (Δ : Finset ν) : Finset ν
  := t.vars ∪ (Δ \ t.defs.toFinset)

theorem UBody.vars_for_sub_vars (t : UBody φ ν) (Δ : Finset ν) : t.vars ⊆ t.vars_for Δ
  := Finset.subset_union_left _ _

theorem UBody.vars_for_eq_of_sub (t : UBody φ ν) (Δ : Finset ν)
  : Δ ⊆ t.vars ∪ t.defs.toFinset → t.vars_for Δ = t.vars := by
  rw [vars_for, Finset.union_eq_left]
  intro h x hx
  simp only [Finset.mem_sdiff] at hx
  cases Finset.mem_union.mp (h hx.1) with
  | inl h => exact h
  | inr h => exact (hx.2 h).elim

theorem UBody.sub_of_vars_for_eq (t : UBody φ ν) (Δ : Finset ν)
  : t.vars_for Δ = t.vars → Δ ⊆ t.vars ∪ t.defs.toFinset := by
  rw [vars_for, Finset.union_eq_left]
  intro h x hx
  simp only [Finset.mem_union]
  if hx' : x ∈ t.defs.toFinset then
    exact Or.inr hx'
  else
    apply Or.inl
    apply h
    simp only [Finset.mem_sdiff]
    exact ⟨hx, hx'⟩

theorem UBody.vars_for_eq_iff (t : UBody φ ν) (Δ : Finset ν)
  : t.vars_for Δ = t.vars ↔ Δ ⊆ t.vars ∪ t.defs.toFinset :=
  ⟨t.sub_of_vars_for_eq Δ, t.vars_for_eq_of_sub Δ⟩

def UBody.comp {φ ν}
  : UBody φ ν → UBody φ ν → UBody φ ν
  | nil, b => b
  | let1 x e b, b' => let1 x e (b.comp b')
  | let2 x y e b, b' => let2 x y e (b.comp b')

theorem UBody.nil_comp {φ ν} (b : UBody φ ν)
  : UBody.comp UBody.nil b = b := rfl

theorem UBody.comp_nil {φ ν} (b : UBody φ ν)
  : UBody.comp b UBody.nil = b := by induction b <;> simp [UBody.comp, *]

theorem UBody.comp_assoc {φ ν} (b₁ b₂ b₃ : UBody φ ν)
  : UBody.comp (UBody.comp b₁ b₂) b₃ = UBody.comp b₁ (UBody.comp b₂ b₃)
  := by induction b₁ <;> simp [UBody.comp, *]

theorem UBody.comp_rewrite {φ ν}
  (σ : ν → UTm φ ν) (b₁ b₂ : UBody φ ν)
  : (b₁.comp b₂).rewrite σ = (b₁.rewrite σ).comp (b₂.rewrite σ)
  := by induction b₁ <;> simp [UBody.comp, UBody.rewrite, *]

def UBody.comp_defs {φ ν}
  (b₁ b₂ : UBody φ ν) : (b₁.comp b₂).defs = b₁.defs ++ b₂.defs
  := by induction b₁ <;> simp [defs, comp, *]

theorem UBody.rewrite_eq_subst
  (σ : USubst φ ν) (b : UBody φ ν) (hσ : {x | x ∈ b.defs}.EqOn σ UTm.var)
  : b.rewrite σ = b.subst σ
  := by induction b generalizing σ with
  | nil => rfl
  | let1 x e b I =>
    rw [rewrite, subst, I]
    congr
    funext y
    rw [USubst.cons, Function.update]
    split
    . rename_i h
      cases h
      rw [hσ]
      simp [defs]
    . rfl
    apply hσ.mono
    simp only [defs, List.mem_cons, Set.setOf_subset_setOf]
    aesop
  | let2 x y e b I =>
    rw [rewrite, subst, I]
    congr
    funext y
    rw [USubst.cons, Function.update]
    split
    . rename_i h
      cases h
      rw [hσ]
      simp [defs]
    rw [USubst.cons, Function.update]
    split
    . rename_i h
      cases h
      rw [hσ]
      simp [defs]
    . rfl
    apply hσ.mono
    simp only [defs, List.mem_cons, Set.setOf_subset_setOf]
    aesop

def UBody.SSA {φ ν} (Γ : List ν) (b : UBody φ ν) : Prop
  := Γ.Disjoint b.defs ∧ b.defs.Nodup

theorem UBody.SSA.of_let1 {φ ν}
  {Γ : List ν} {x : ν} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ (let1 x e b)) : UBody.SSA (x :: Γ) b
  := ⟨
    List.disjoint_cons_left.mpr ⟨h.2.not_mem, (List.disjoint_cons_right.mp h.1).2⟩,
    h.2.of_cons
  ⟩

theorem UBody.SSA.of_let2 {φ ν}
  {Γ : List ν} {x y : ν} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ (let2 x y e b)) : UBody.SSA (x :: y :: Γ) b
  := ⟨
    List.disjoint_cons_left.mpr
      ⟨List.not_mem_of_not_mem_cons h.2.not_mem,
        List.disjoint_cons_left.mpr ⟨h.2.of_cons.not_mem,
        (List.disjoint_cons_right.mp (List.disjoint_cons_right.mp h.1).2).2⟩⟩,
    h.2.of_cons.of_cons
  ⟩

theorem UBody.SSA.of_let1' {φ ν}
  {Γ : Ctx ν α} {x : Var ν α} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ.names (let1 x.name e b)) : UBody.SSA (Ctx.names (x :: Γ)) b
  := h.of_let1

theorem UBody.SSA.of_let1'' {φ ν}
  {Γ : Ctx ν α} {x A} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ.names (let1 x e b)) : UBody.SSA (Ctx.names (⟨x, A⟩ :: Γ)) b
  := h.of_let1

theorem UBody.SSA.of_let2' {φ ν}
  {Γ : Ctx ν α} {x y : Var ν α} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ.names (let2 x.name y.name e b)) : UBody.SSA (Ctx.names (x :: y :: Γ)) b
  := h.of_let2

theorem UBody.SSA.of_let2'' {φ ν}
  {Γ : Ctx ν α} {x A y B} {e : UTm φ ν} {b : UBody φ ν}
  (h : UBody.SSA Γ.names (let2 x y e b)) : UBody.SSA (Ctx.names (⟨x, A⟩ :: ⟨y, B⟩ :: Γ)) b
  := h.of_let2

def UBody.NSSA {φ ν}
  (Γ : List ν) (b : UBody φ ν) : Prop
  := (Γ ++ b.defs).Nodup

theorem UBody.NSSA.toSSA {φ ν}
  {Γ : List ν} {b : UBody φ ν} (h : UBody.NSSA Γ b) : UBody.SSA Γ b
  := ⟨List.disjoint_of_nodup_append h, h.of_append_right⟩

theorem UBody.SSA.entry_nodup {φ ν}
  {Γ : List ν} {b : UBody φ ν} (h : UBody.SSA Γ b) (h' : Γ.Nodup) : UBody.NSSA Γ b
  := h'.append h.2 h.1

theorem UBody.SSA.comp {φ ν}
  {Γ : List ν} {b₁ b₂ : UBody φ ν}
  (h₁ : UBody.SSA Γ b₁) (h₂ : UBody.SSA (b₁.defs.reverse ++ Γ) b₂)
  : UBody.SSA Γ (b₁.comp b₂)
  := by
    simp only
      [SSA, List.disjoint_append_left, comp_defs, List.disjoint_append_right,
        List.Disjoint.iff_reverse_left] at *
    exact ⟨⟨h₁.1, h₂.1.2⟩, h₁.2.append h₂.2 h₂.1.1⟩

theorem UBody.NSSA.comp {φ ν}
  {Γ : List ν} {b₁ b₂ : UBody φ ν}
  (h₂ : UBody.NSSA (b₁.defs.reverse ++ Γ) b₂)
  : UBody.NSSA Γ (b₁.comp b₂)
  := by
    simp only [NSSA, List.nodup_append, List.append_assoc, List.nodup_reverse,
      List.disjoint_append_right, List.Disjoint.iff_reverse_left, comp_defs] at *
    exact ⟨h₂.2.1.1, ⟨h₂.1, h₂.2.1.2.1, h₂.2.2.2⟩, h₂.2.2.1.symm, h₂.2.1.2.2⟩

inductive UTerminator (φ : Type _) (ν : Type _) (κ : Type _)
   : Type _ where
  | br : κ → UTm φ ν → UTerminator φ ν κ
  | ite : UTm φ ν → UTerminator φ ν κ → UTerminator φ ν κ → UTerminator φ ν κ

def UTerminator.targets : UTerminator φ ν κ → Finset κ
  | br ℓ _ => {ℓ}
  | ite _ s t => s.targets ∪ t.targets

def UTerminator.rename {φ ν ν' κ}
  (σ : ν → ν') : UTerminator φ ν κ → UTerminator φ ν' κ
  | br ℓ e => br ℓ (e.rename σ)
  | ite c t f => ite (c.rename σ) (t.rename σ) (f.rename σ)

theorem UTerminator.rename_comp {φ ν ν' ν'' κ}
  (σ : ν → ν') (σ' : ν' → ν'') (t : UTerminator φ ν κ)
  : t.rename (σ' ∘ σ) = (t.rename σ).rename σ'
  := by induction t <;> simp [UTm.rename_comp, UTerminator.rename, *]

def UTerminator.renameLabel {φ ν κ}
  (σ : κ → κ') : UTerminator φ ν κ → UTerminator φ ν κ'
  | br ℓ e => br (σ ℓ) e
  | ite c t f => ite c (t.renameLabel σ) (f.renameLabel σ)

theorem UTerminator.renameLabel_comp {φ ν κ κ'}
  (σ : κ → κ') (σ' : κ' → κ'') (t : UTerminator φ ν κ)
  : t.renameLabel (σ' ∘ σ) = (t.renameLabel σ).renameLabel σ'
  := by induction t <;> simp [UTm.rename_comp, UTerminator.renameLabel, *]

def UTerminator.rewrite {φ ν κ}
  (σ : ν → UTm φ ν) : UTerminator φ ν κ → UTerminator φ ν κ
  | br ℓ e => br ℓ (e.rewrite σ)
  | ite c t f => ite (c.rewrite σ) (t.rewrite σ) (f.rewrite σ)

theorem UTerminator.rewrite_var {φ ν κ}
  (t : UTerminator φ ν κ) : t.rewrite UTm.var = t
  := by induction t <;> simp [UTm.rewrite_var, UTerminator.rewrite, *]

theorem UTerminator.rewrite_comp {φ ν κ}
  (σ σ' : ν → UTm φ ν) (t : UTerminator φ ν κ)
  : t.rewrite (UTm.comp σ σ') = (t.rewrite σ).rewrite σ'
  := by induction t <;> simp [UTm.rewrite_comp, UTerminator.rewrite, *]

def UTerminator.rewriteBr {φ ν κ}
  (σ : κ → UTm φ ν → UTerminator φ ν κ) : UTerminator φ ν κ → UTerminator φ ν κ
  | br ℓ e => σ ℓ e
  | ite c t f => ite c (t.rewriteBr σ) (f.rewriteBr σ)

theorem UTerminator.rewriteBr_br {φ ν κ}
  (e : UTerminator φ ν κ) : e.rewriteBr br = e := by
    induction e <;> simp [UTm.rewrite_var, UTerminator.rewriteBr, *]

def UTerminator.comp {φ ν κ}
  (σ : κ → UTm φ ν → UTerminator φ ν κ) (τ : κ → UTm φ ν → UTerminator φ ν κ)
  (ℓ : κ) (e : UTm φ ν) : UTerminator φ ν κ
  := (σ ℓ e).rewriteBr τ

theorem UTerminator.comp_br {φ ν κ}
  (σ : κ → UTm φ ν → UTerminator φ ν κ)
  : UTerminator.comp σ br = σ
  := by funext ℓ e; simp [rewriteBr_br, comp]

theorem UTerminator.br_comp {φ ν κ}
  (σ : κ → UTm φ ν → UTerminator φ ν κ)
  (ℓ : κ) (e : UTm φ ν)
  : UTerminator.comp br σ ℓ e = σ ℓ e
  := rfl

theorem UTerminator.rewriteBr_comp {φ ν κ}
  (σ σ' : κ → UTm φ ν → UTerminator φ ν κ) (t : UTerminator φ ν κ)
  : t.rewriteBr (UTerminator.comp σ σ') = (t.rewriteBr σ).rewriteBr σ'
  := by induction t <;> simp [rewriteBr_br, comp, rewriteBr, *]

theorem UTerminator.comp_assoc {φ ν κ}
  (σ : κ → UTm φ ν → UTerminator φ ν κ) (τ : κ → UTm φ ν → UTerminator φ ν κ)
  (ρ : κ → UTm φ ν → UTerminator φ ν κ)
  : UTerminator.comp (UTerminator.comp σ τ) ρ
  = UTerminator.comp σ (UTerminator.comp τ ρ)
  := by funext ℓ e; simp [comp, rewriteBr_comp, *]

structure UBB (φ : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  body : UBody φ ν
  terminator : UTerminator φ ν κ

def UBB.rename {φ ν ν' κ}
  (σ : ν → ν') (β : UBB φ ν κ) : UBB φ ν' κ where
  body := β.body.rename σ
  terminator := β.terminator.rename σ

theorem UBB.rename_comp {φ ν ν' ν'' κ}
  (σ : ν → ν') (σ' : ν' → ν'') (β : UBB φ ν κ)
  : β.rename (σ' ∘ σ) = (β.rename σ).rename σ'
  := by simp [UBB.rename, UBody.rename_comp, UTerminator.rename_comp]

def UBB.renameLabel {φ ν κ κ'}
  (σ : κ → κ') (β : UBB φ ν κ) : UBB φ ν κ' where
  body := β.body
  terminator := β.terminator.renameLabel σ

theorem UBB.renameLabel_comp {φ ν κ κ'}
  (σ : κ → κ') (σ' : κ' → κ'') (β : UBB φ ν κ)
  : β.renameLabel (σ' ∘ σ) = (β.renameLabel σ).renameLabel σ'
  := by simp [UBB.renameLabel, UTerminator.renameLabel_comp]

def UBB.rewrite
  (σ : USubst φ ν) (β : UBB φ ν κ) : UBB φ ν κ where
  body := β.body.rewrite σ
  terminator := β.terminator.rewrite σ

def UBB.subst
  (σ : USubst φ ν) (β : UBB φ ν κ) : UBB φ ν κ where
  body := β.body.subst σ
  terminator := β.terminator.rewrite (σ.cons_list β.body.defs)

theorem UBB.rewrite_var {φ ν κ}
  (β : UBB φ ν κ) : β.rewrite UTm.var = β
  := by simp [UBB.rewrite, UBody.rewrite_var, UTerminator.rewrite_var]

theorem UBB.rewrite_comp {φ ν κ}
  (σ σ' : ν → UTm φ ν) (β : UBB φ ν κ)
  : β.rewrite (UTm.comp σ σ') = (β.rewrite σ).rewrite σ'
  := by simp [UBB.rewrite, UBody.rewrite_comp, UTerminator.rewrite_comp]

def UBB.rewriteBr {φ ν κ}
  (σ : κ → UTm φ ν → UTerminator φ ν κ) (β : UBB φ ν κ) : UBB φ ν κ where
  body := β.body
  terminator := β.terminator.rewriteBr σ

theorem UBB.rewriteBr_br {φ ν κ}
  (β : UBB φ ν κ) : β.rewriteBr UTerminator.br = β := by
    simp [UBB.rewriteBr, UTerminator.rewriteBr_br]

theorem UBB.rewriteBr_comp {φ ν κ}
  (σ σ' : κ → UTm φ ν → UTerminator φ ν κ) (β : UBB φ ν κ)
  : β.rewriteBr (UTerminator.comp σ σ') = (β.rewriteBr σ).rewriteBr σ'
  := by simp [UBB.rewriteBr, UTerminator.rewriteBr_comp]

def UBody.compBB {φ ν}
  (b : UBody φ ν) (β : UBB φ ν κ) : UBB φ ν κ
  := ⟨b.comp β.body, β.terminator⟩

inductive UCFG (φ : Type _) (α : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  | nil : UCFG φ α ν κ
  | cons : UCFG φ α ν κ → κ → ν → α → UBB φ ν κ → UCFG φ α ν κ

def UCFG.rename {φ α ν ν' κ}
  (σ : ν → ν') : UCFG φ α ν κ → UCFG φ α ν' κ
  | nil => nil
  | cons Φ κ x t b => cons (Φ.rename σ) κ (σ x) t (b.rename σ)

theorem UCFG.rename_comp {φ α ν ν' ν'' κ}
  (σ : ν → ν') (σ' : ν' → ν'') (Φ : UCFG φ α ν κ)
  : Φ.rename (σ' ∘ σ) = (Φ.rename σ).rename σ'
  := by induction Φ <;> simp [UCFG.rename, UBB.rename_comp, *]

def UCFG.renameLabel {φ α ν κ κ'}
  (σ : κ → κ') : UCFG φ α ν κ → UCFG φ α ν κ'
  | nil => nil
  | cons Φ κ x A b => cons (Φ.renameLabel σ) (σ κ) x A (b.renameLabel σ)

theorem UCFG.renameLabel_comp {φ α ν κ κ'}
  (σ : κ → κ') (σ' : κ' → κ'') (Φ : UCFG φ α ν κ)
  : Φ.renameLabel (σ' ∘ σ) = (Φ.renameLabel σ).renameLabel σ'
  := by induction Φ <;> simp [UCFG.renameLabel, UBB.renameLabel_comp, *]

def UCFG.rewrite {φ α ν κ}
  (σ : USubst φ ν) : UCFG φ α ν κ → UCFG φ α ν κ
  | nil => nil
  | cons Φ κ x A b => cons (Φ.rewrite σ) κ x A (b.rewrite σ)

theorem UCFG.rewrite_var {φ α ν κ}
  (Φ : UCFG φ α ν κ) : Φ.rewrite UTm.var = Φ := by
    induction Φ <;> simp [UCFG.rewrite, UBB.rewrite_var, *]

theorem UCFG.rewrite_comp {φ α ν κ}
  (σ σ' : USubst φ ν) (Φ : UCFG φ α ν κ)
  : Φ.rewrite (UTm.comp σ σ') = (Φ.rewrite σ).rewrite σ'
  := by induction Φ <;> simp [UCFG.rewrite, UBB.rewrite_comp, *]

def UCFG.rewriteBr {φ α ν κ}
  (σ : κ → UTm φ ν → UTerminator φ ν κ) : UCFG φ α ν κ → UCFG φ α ν κ
  | nil => nil
  | cons Φ κ x A b => cons (Φ.rewriteBr σ) κ x A (b.rewriteBr σ)

theorem UCFG.rewriteBr_br {φ α ν κ}
  (Φ : UCFG φ α ν κ) : Φ.rewriteBr UTerminator.br = Φ := by
    induction Φ <;> simp [UCFG.rewriteBr, UBB.rewriteBr_br, *]

theorem UCFG.rewriteBr_comp {φ α ν κ}
  (σ σ' : κ → UTm φ ν → UTerminator φ ν κ) (Φ : UCFG φ α ν κ)
  : Φ.rewriteBr (UTerminator.comp σ σ') = (Φ.rewriteBr σ).rewriteBr σ'
  := by induction Φ <;> simp [UCFG.rewriteBr, UBB.rewriteBr_comp, *]

def UCFG.labels {φ α ν κ}
  : UCFG φ α ν κ → List κ
  | nil => []
  | cons Φ κ _ _ _ => κ :: Φ.labels

def UCFG.defs {φ α ν κ}
  : UCFG φ α ν κ → List ν
  | nil => []
  | cons Φ _ x _ β => x :: β.body.defs ++ Φ.defs

def UCFG.comp {φ α ν κ}
  : UCFG φ α ν κ → UCFG φ α ν κ → UCFG φ α ν κ
  | nil, Φ => Φ
  | cons Φ κ x A b, Φ' => cons (Φ.comp Φ') κ x A b

theorem UCFG.nil_comp {φ α ν κ} (Φ : UCFG φ α ν κ)
  : UCFG.nil.comp Φ = Φ := rfl

theorem UCFG.comp_nil {φ α ν κ}
  (Φ : UCFG φ α ν κ) : Φ.comp UCFG.nil = Φ
  := by induction Φ <;> simp [comp, *]

theorem UCFG.comp_assoc {φ α ν κ}
  (Φ Φ' Φ'' : UCFG φ α ν κ)
  : (Φ.comp Φ').comp Φ'' = Φ.comp (Φ'.comp Φ'')
  := by induction Φ <;> simp [comp, *]

theorem UCFG.comp_labels {φ α ν κ}
  (Φ Φ' : UCFG φ α ν κ) : (Φ.comp Φ').labels = Φ.labels ++ Φ'.labels
  := by induction Φ <;> simp [labels, comp, *]

theorem UCFG.comp_defs {φ α ν κ}
  (Φ Φ' : UCFG φ α ν κ) : (Φ.comp Φ').defs = Φ.defs ++ Φ'.defs
  := by induction Φ <;> simp [defs, comp, *]

def UCFG.SSA {φ α ν κ}
  (Γ : List ν) (Φ : UCFG φ α ν κ) : Prop
  := Γ.Disjoint Φ.defs ∧ Φ.defs.Nodup

def UCFG.NSSA {φ α ν κ}
  (Γ : List ν) (Φ : UCFG φ α ν κ) : Prop
  := (Γ ++ Φ.defs).Nodup

def UCFG.NSSA.toSSA {φ α ν κ}
  {Γ : List ν} {Φ : UCFG φ α ν κ} (h : UCFG.NSSA Γ Φ) : UCFG.SSA Γ Φ
  := ⟨List.disjoint_of_nodup_append h, h.of_append_right⟩

def UCFG.SSA.entry_nodup {φ α ν κ}
  {Γ : List ν} {Φ : UCFG φ α ν κ} (h : UCFG.SSA Γ Φ) (h' : Γ.Nodup) : UCFG.NSSA Γ Φ
  := h'.append h.2 h.1

structure URegion (φ : Type _) (α : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  entry : UBB φ ν κ
  cfg : UCFG φ α ν κ

def URegion.rename {φ α ν ν' κ}
  (σ : ν → ν') (β : URegion φ α ν κ) : URegion φ α ν' κ where
  entry := β.entry.rename σ
  cfg := β.cfg.rename σ

theorem URegion.rename_comp {φ α ν ν' ν'' κ}
  (σ : ν → ν') (σ' : ν' → ν'') (β : URegion φ α ν κ)
  : β.rename (σ' ∘ σ) = (β.rename σ).rename σ'
  := by simp [URegion.rename, UBB.rename_comp, UCFG.rename_comp]

def URegion.renameLabel {φ α ν κ κ'}
  (σ : κ → κ') (β : URegion φ α ν κ) : URegion φ α ν κ' where
  entry := β.entry.renameLabel σ
  cfg := β.cfg.renameLabel σ

theorem URegion.renameLabel_comp {φ α ν κ κ'}
  (σ : κ → κ') (σ' : κ' → κ'') (β : URegion φ α ν κ)
  : β.renameLabel (σ' ∘ σ) = (β.renameLabel σ).renameLabel σ'
  := by simp [URegion.renameLabel, UBB.renameLabel_comp, UCFG.renameLabel_comp]

def URegion.rewrite {φ α ν κ}
  (σ : ν → UTm φ ν) (β : URegion φ α ν κ) : URegion φ α ν κ where
  entry := β.entry.rewrite σ
  cfg := β.cfg.rewrite σ

theorem URegion.rewrite_var {φ α ν κ}
  (β : URegion φ α ν κ) : β.rewrite UTm.var = β
  := by simp [URegion.rewrite, UBB.rewrite_var, UCFG.rewrite_var]

theorem URegion.rewrite_comp {φ α ν κ}
  (σ σ' : ν → UTm φ ν) (β : URegion φ α ν κ)
  : β.rewrite (UTm.comp σ σ') = (β.rewrite σ).rewrite σ'
  := by simp [URegion.rewrite, UBB.rewrite_comp, UCFG.rewrite_comp]

def URegion.rewriteBr {φ α ν κ}
  (σ : κ → UTm φ ν → UTerminator φ ν κ) (β : URegion φ α ν κ) : URegion φ α ν κ where
  entry := β.entry
  cfg := β.cfg.rewriteBr σ

theorem URegion.rewriteBr_br {φ α ν κ}
  (β : URegion φ α ν κ) : β.rewriteBr UTerminator.br = β := by
    simp [URegion.rewriteBr, UCFG.rewriteBr_br]

theorem URegion.rewriteBr_comp {φ α ν κ}
  (σ σ' : κ → UTm φ ν → UTerminator φ ν κ) (β : URegion φ α ν κ)
  : β.rewriteBr (UTerminator.comp σ σ') = (β.rewriteBr σ).rewriteBr σ'
  := by simp [URegion.rewriteBr, UCFG.rewriteBr_comp]

inductive UGRegion (φ : Type _) (α : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  | let1 : ν → UTm φ ν → UGRegion φ α ν κ → UGRegion φ α ν κ
  | let2 : ν → ν → UTm φ ν → UGRegion φ α ν κ → UGRegion φ α ν κ
  | br : κ → UTm φ ν → UGRegion φ α ν κ
  | ite : UTm φ ν → UGRegion φ α ν κ → UGRegion φ α ν κ → UGRegion φ α ν κ
  | dom : UGRegion φ α ν κ → UGRegion φ α ν κ → UGRegion φ α ν κ
  | nil : UGRegion φ α ν κ
  | cons : UGRegion φ α ν κ → κ → ν → α → UGRegion φ α ν κ → UGRegion φ α ν κ

def UGRegion.rename {φ α ν ν' κ}
  (σ : ν → ν') : UGRegion φ α ν κ → UGRegion φ α ν' κ
  | let1 x e b => let1 (σ x) (e.rename σ) (b.rename σ)
  | let2 x y e b => let2 (σ x) (σ y) (e.rename σ) (b.rename σ)
  | br ℓ e => br ℓ (e.rename σ)
  | ite c t f => ite (c.rename σ) (t.rename σ) (f.rename σ)
  | dom d r => dom (d.rename σ) (r.rename σ)
  | nil => nil
  | cons r ℓ x A b => cons (r.rename σ) ℓ (σ x) A (b.rename σ)

theorem UGRegion.rename_comp {φ α ν ν' ν'' κ}
  (σ : ν → ν') (σ' : ν' → ν'') (r : UGRegion φ α ν κ)
  : r.rename (σ' ∘ σ) = (r.rename σ).rename σ'
  := by induction r <;> simp [UGRegion.rename, UTm.rename_comp, *]

def UGRegion.renameLabel {φ α ν κ κ'}
  (σ : κ → κ') : UGRegion φ α ν κ → UGRegion φ α ν κ'
  | let1 x e b => let1 x e (b.renameLabel σ)
  | let2 x y e b => let2 x y e (b.renameLabel σ)
  | br ℓ e => br (σ ℓ) e
  | ite c t f => ite c (t.renameLabel σ) (f.renameLabel σ)
  | dom d r => dom (d.renameLabel σ) (r.renameLabel σ)
  | nil => nil
  | cons r ℓ x A b => cons (r.renameLabel σ) (σ ℓ) x A (b.renameLabel σ)

theorem UGRegion.renameLabel_comp {φ α ν κ κ'}
  (σ : κ → κ') (σ' : κ' → κ'') (r : UGRegion φ α ν κ)
  : r.renameLabel (σ' ∘ σ) = (r.renameLabel σ).renameLabel σ'
  := by induction r <;> simp [UGRegion.renameLabel, *]

def UGRegion.rewrite {φ α ν κ}
  (σ : ν → UTm φ ν) : UGRegion φ α ν κ → UGRegion φ α ν κ
  | let1 x e b => let1 x (e.rewrite σ) (b.rewrite σ)
  | let2 x y e b => let2 x y (e.rewrite σ) (b.rewrite σ)
  | br ℓ e => br ℓ (e.rewrite σ)
  | ite c t f => ite (c.rewrite σ) (t.rewrite σ) (f.rewrite σ)
  | dom d r => dom (d.rewrite σ) (r.rewrite σ)
  | nil => nil
  | cons r ℓ x A b => cons (r.rewrite σ) ℓ x A (b.rewrite σ)

theorem UGRegion.rewrite_var {φ α ν κ}
  (r : UGRegion φ α ν κ) : r.rewrite UTm.var = r
  := by induction r <;> simp [UGRegion.rewrite, UTm.rewrite_var, *]

theorem UGRegion.rewrite_comp {φ α ν κ}
  (σ σ' : ν → UTm φ ν) (r : UGRegion φ α ν κ)
  : r.rewrite (UTm.comp σ σ') = (r.rewrite σ).rewrite σ'
  := by induction r <;> simp [UGRegion.rewrite, UTm.rewrite_comp, *]

def UGRegion.rewriteBr {φ α ν κ}
  (σ : κ → UTm φ ν → UGRegion φ α ν κ) : UGRegion φ α ν κ → UGRegion φ α ν κ
  | let1 x e b => let1 x e (b.rewriteBr σ)
  | let2 x y e b => let2 x y e (b.rewriteBr σ)
  | br ℓ e => σ ℓ e
  | ite c t f => ite c (t.rewriteBr σ) (f.rewriteBr σ)
  | dom d r => dom (d.rewriteBr σ) (r.rewriteBr σ)
  | nil => nil
  | cons r ℓ x A b => cons (r.rewriteBr σ) ℓ x A (b.rewriteBr σ)

theorem UGRegion.rewriteBr_br {φ α ν κ}
  (r : UGRegion φ α ν κ) : r.rewriteBr br = r := by
    induction r <;> simp [UTm.rewrite_var, UGRegion.rewriteBr, *]

def UGRegion.comp {φ α ν κ}
  (σ : κ → UTm φ ν → UGRegion φ α ν κ) (τ : κ → UTm φ ν → UGRegion φ α ν κ)
  (ℓ : κ) (e : UTm φ ν) : UGRegion φ α ν κ
  := (σ ℓ e).rewriteBr τ

theorem UGRegion.comp_br {φ α ν κ}
  (σ : κ → UTm φ ν → UGRegion φ α ν κ)
  : UGRegion.comp σ br = σ
  := by funext ℓ e; simp [UGRegion.comp, rewriteBr_br]

theorem UGRegion.br_comp {φ α ν κ}
  (σ : κ → UTm φ ν → UGRegion φ α ν κ)
  : UGRegion.comp br σ = σ
  := rfl

theorem UGRegion.rewriteBr_comp {φ α ν κ}
  (σ σ' : κ → UTm φ ν → UGRegion φ α ν κ) (r : UGRegion φ α ν κ)
  : r.rewriteBr (UGRegion.comp σ σ') = (r.rewriteBr σ).rewriteBr σ'
  := by induction r <;> simp [UGRegion.rewriteBr, comp, *]

theorem UGRegion.comp_assoc {φ α ν κ}
  (σ : κ → UTm φ ν → UGRegion φ α ν κ) (τ : κ → UTm φ ν → UGRegion φ α ν κ)
  (ρ : κ → UTm φ ν → UGRegion φ α ν κ)
  : UGRegion.comp (UGRegion.comp σ τ) ρ
  = UGRegion.comp σ (UGRegion.comp τ ρ)
  := by funext ℓ e; simp [UGRegion.comp, rewriteBr_comp, *]

--TODO: map_ty for UGRegion

def UTerminator.toUGRegion {φ α ν κ}
  (t : UTerminator φ ν κ) : UGRegion φ α ν κ
  := match t with
    | UTerminator.br ℓ e => UGRegion.br ℓ e
    | UTerminator.ite c t f => UGRegion.ite c (t.toUGRegion) (f.toUGRegion)

def UBody.compRegion {φ α ν κ}
  (b : UBody φ ν) (r : UGRegion φ α ν κ) : UGRegion φ α ν κ
  := match b with
    | UBody.nil => r
    | UBody.let1 x e b => UGRegion.let1 x e (b.compRegion r)
    | UBody.let2 x y e b => UGRegion.let2 x y e (b.compRegion r)

def UBB.toUGRegion {φ α ν κ}
  (b : UBB φ ν κ) : UGRegion φ α ν κ
  := b.body.compRegion b.terminator.toUGRegion

def UCFG.toUGRegion {φ α ν κ}
  (Φ : UCFG φ α ν κ) : UGRegion φ α ν κ
  := match Φ with
    | UCFG.nil => UGRegion.nil
    | UCFG.cons Φ κ x t b => UGRegion.cons (Φ.toUGRegion) κ x t (b.toUGRegion)

inductive UPTerminator (φ : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  | br : κ → USubst φ ν → UPTerminator φ ν κ
  | ite : UTm φ ν → UPTerminator φ ν κ → UPTerminator φ ν κ → UPTerminator φ ν κ

structure UPBB (φ : Type _) (ν : Type _) (κ : Type _) : Type _ where
  body : UBody φ ν
  terminator : UPTerminator φ ν κ

inductive UPCFG (φ : Type _) (α : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  | nil : UPCFG φ α ν κ
  | cons : UPCFG φ α ν κ → κ → ν → α → UBB φ ν κ → UPCFG φ α ν κ

structure UPRegion (φ : Type _) (α : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  entry : UPBB φ ν κ
  cfg : UPCFG φ α ν κ

inductive UPGRegion (φ : Type _) (α : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  | let1 : ν → UTm φ ν → UPGRegion φ α ν κ → UPGRegion φ α ν κ
  | let2 : ν → ν → UTm φ ν → UPGRegion φ α ν κ → UPGRegion φ α ν κ
  | br : κ → (ν → UTm φ ν) → UPGRegion φ α ν κ
  | ite : UTm φ ν → UPGRegion φ α ν κ → UPGRegion φ α ν κ → UPGRegion φ α ν κ
  | dom : UPGRegion φ α ν κ → UPGRegion φ α ν κ → UPGRegion φ α ν κ
  | nil : UPGRegion φ α ν κ
  | cons : UPGRegion φ α ν κ → κ → ν → α → UPGRegion φ α ν κ → UPGRegion φ α ν κ
