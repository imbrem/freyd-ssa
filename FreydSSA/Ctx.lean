import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Init.Classical
import Mathlib.Order.SuccPred.Basic

import FreydSSA.Utils
import FreydSSA.Ctx.Var
import FreydSSA.Ctx.Label

def Var.rename {ν ν' α} (ρ : ν → ν') (v : Var ν α) : Var ν' α
  := ⟨ρ v.name, v.ty⟩

theorem Var.rename_eq {ν ν' α} (v: Var ν α) (ρ₁ ρ₂: ν → ν')
  : ρ₁ v.name = ρ₂ v.name → Var.rename ρ₁ v = Var.rename ρ₂ v
  := by cases v; simp [rename]

def Ctx.rename {ν ν' α} (ρ : ν → ν') (Γ : Ctx ν α) : Ctx ν' α
  := Γ.map (Var.rename ρ)

theorem Ctx.Fresh.rename {ν α} {ρ: ν → ν'} {Γ : Ctx ν α} {n}
  (hΓ : Γ.InjOn ρ) (hn : ∀x ∈ Γ.names, x ≠ n → ρ x ≠ ρ n)
  : Fresh n Γ → Fresh (ρ n) (rename ρ Γ)
  | nil => nil
  | cons hxn hn' => cons (hn _ (by simp) hxn) (hn'.rename hΓ.tail (λ x hx => hn _ (hx.tail _)))

def Ctx.Wk.rename {ν α} {ρ : ν → ν'} {Γ Δ : Ctx ν α} (hΓ : Γ.InjOn ρ)
  : Γ.Wk Δ → (rename ρ Γ).Wk (rename ρ Δ)
  | nil => nil
  | cons x h => cons ⟨ρ x.name, x.ty⟩ (rename hΓ.tail h)
  | skip hxn h => skip
    (hxn.rename (hΓ.wk (skip hxn h)) (hΓ.wk (cons _ h)).head_ne)
    (rename hΓ.tail h)

def Ctx.Wk.rename_iso {Γ Δ : Ctx ν α} {ρ: ν → ν'} (hΓ : Γ.InjOn ρ) (w: Γ.Wk Δ)
  : w.Iso (w.rename hΓ) := match Γ, Δ, w with
  | [], [], nil => Iso.nil
  | _::_, _::_, cons _ w => Iso.cons (w.rename_iso hΓ.tail)
  | _::_, _, skip _ w => Iso.skip (w.rename_iso hΓ.tail)

theorem Ctx.rename_id: (Γ : Ctx ν α) → Γ.rename id = Γ
  | [] => rfl
  | _::Γ => congrArg _ (rename_id Γ)

theorem Ctx.EqOn.rename {ρ₁ ρ₂ : ν → ν'} {Γ : Ctx ν α} (hΓ : Γ.EqOn ρ₁ ρ₂)
  : Γ.rename ρ₁ = Γ.rename ρ₂
  := List.map_congr (λ_ hx => Var.rename_eq _ _ _  (hΓ (List.mem_map_of_mem _ hx)))

theorem Ctx.EqOn.rename_id {ρ : ν → ν} {Γ : Ctx ν α} (hΓ : Γ.EqOn ρ id)
  : Γ.rename ρ = Γ
  := hΓ.rename.trans Γ.rename_id

def Ctx.deBruijn {ν α} (n : ℕ) : Ctx ν α → Ctx ℕ α
  | [] => []
  | ⟨_, a⟩::Γ => ⟨n, a⟩::deBruijn (n+1) Γ

def Ctx.Wk.target_deBruijn {ν α} {Γ Δ : Ctx ν α} (n : ℕ) : Γ.Wk Δ → Ctx ℕ α
  | Wk.nil => []
  | Wk.cons x h => ⟨n, x.ty⟩::target_deBruijn (n+1) h
  | Wk.skip _ h => target_deBruijn (n+1) h

theorem Ctx.Wk.target_deBruijn_fresh {ν α} {Γ Δ : Ctx ν α} {n m : ℕ} (H: n < m)
  : (w: Γ.Wk Δ) → Fresh n (w.target_deBruijn m)
  | nil => Fresh.nil
  | cons _ w => Fresh.cons (Nat.ne_of_lt H).symm (target_deBruijn_fresh (Nat.lt.step H) w)
  | skip _ w => target_deBruijn_fresh (Nat.lt.step H) w

def Ctx.Wk.deBruijn {ν α} {Γ Δ : Ctx ν α} (n : ℕ) : (w: Γ.Wk Δ)
  → (deBruijn n Γ).Wk (w.target_deBruijn n)
  | nil => nil
  | cons x w => cons ⟨n, x.ty⟩ (deBruijn (n+1) w)
  | skip hxn w => skip (w.target_deBruijn_fresh (Nat.lt.base _)) (deBruijn (n+1) w)

theorem Ctx.Wk.iso_deBruijn {ν α} {Γ Δ : Ctx ν α} (n : ℕ)
  : (w: Γ.Wk Δ) → w.Iso (w.deBruijn n)
  | nil => Iso.nil
  | cons _ w => Iso.cons (iso_deBruijn (n + 1) w)
  | skip _ w => Iso.skip (iso_deBruijn (n + 1) w)

inductive Ctx.HasVar {ν α : Type u} (A : α) : ℕ → ν → Ctx ν α → Prop
  | head : Ctx.HasVar A 0 x (⟨x, A⟩::Γ)
  | tail : x ≠ v.name → Ctx.HasVar A n x Γ → Ctx.HasVar A (n+1) x (v::Γ)

structure Ctx.Ix {ν α} (Γ : Ctx ν α) (x : ν) (A : α) : Type _ where
  val : ℕ
  hasVar : Ctx.HasVar A val x Γ

def Ctx.Ix.head {ν α} {Γ : Ctx ν α} {x : ν} {A : α} : Ctx.Ix (⟨x, A⟩::Γ) x A where
  val := 0
  hasVar := HasVar.head

def Ctx.Ix.tail {ν α} {Γ : Ctx ν α} {v : Var ν α} {x : ν} {A : α}
  (i : Ctx.Ix Γ x A) (h : x ≠ v.name)
  : Ctx.Ix (v::Γ) x A where
  val := i.val + 1
  hasVar := HasVar.tail h i.hasVar

def Ctx.Wk.var_ix {Γ : Ctx ν α} : Γ.Wk [⟨n, A⟩] → ℕ
  | Wk.cons _ w => 0
  | Wk.skip _ w => w.var_ix + 1

theorem Ctx.var_ix_hasVar {Γ : Ctx ν α}
  : (w: Γ.Wk [⟨x, A⟩]) → Γ.HasVar A w.var_ix x
  | Wk.cons _ _ => Ctx.HasVar.head
  | Wk.skip hxn w => Ctx.HasVar.tail hxn.head (var_ix_hasVar w)

def Ctx.HasVar.toWk {Γ : Ctx ν α} {A : α} {n} {x} (H : Γ.HasVar A n x) : Γ.Wk [⟨x, A⟩]
  := match n, Γ with
  | _, [] => nomatch H
  | 0, y::Γ =>
    have Hxy: ⟨x, A⟩ = y := by cases H; rfl
    Hxy ▸ Wk.cons ⟨x, A⟩ (Wk.drop Γ)
  | n + 1, _::_ => Wk.skip
    (match H with | tail hx _ => Fresh.cons hx Fresh.nil)
    (toWk (by cases H; assumption))

def Ctx.Wk.to_ix {Γ : Ctx ν α} {A : α} : Γ.Wk [⟨x, A⟩] → Ctx.Ix Γ x A
  | cons _ _ => Ctx.Ix.head
  | skip hx w => w.to_ix.tail hx.head

def Ctx.Wk.to_ix' {Γ : Ctx ν α} {A : α} (w: Γ.Wk [⟨x, A⟩]) : Ctx.Ix Γ x A
  := ⟨w.var_ix, var_ix_hasVar w⟩

def Ctx.HasVar.not_empty {Γ : Ctx ν α} {A : α} {n} {x} (H : Γ.HasVar A n x) : Γ ≠ []
  := by cases Γ with
  | nil => cases H
  | cons => simp

def Ctx.Ix.not_empty {Γ : Ctx ν α} {x : ν} {A : α} (i : Ctx.Ix Γ x A) : Γ ≠ []
  := i.hasVar.not_empty

theorem Ctx.Wk.drop_target_deBruijn {ν α} {Γ : Ctx ν α} (n : ℕ)
  : (w: Γ.Wk []) → w.target_deBruijn n = []
  | Wk.nil => rfl
  | Wk.skip _ w => drop_target_deBruijn (n+1) w

--FIXME: broken
-- theorem Ctx.Wk.var_target_deBruijn {ν α} {x: ν} {A: α} {Γ : Ctx ν α} (n : ℕ)
--   : (w: Γ.Wk [⟨x, A⟩]) → w.target_deBruijn n = [⟨n + w.var_ix, A⟩]
--   | cons _ w => by simp [target_deBruijn, drop_target_deBruijn, var_ix]
--   | skip _ w =>
--     let I := var_target_deBruijn (n + 1) w;
--     by simp_arith [
--       target_deBruijn, drop_target_deBruijn, var_ix, I
--     ]

--TODO: also broken...
-- theorem Ctx.Wk.var_target_deBruijn' {ν α} {x: ν} {A: α} {Γ Δ : Ctx ν α} (n : ℕ)
--   (w: Γ.Wk Δ) (h: Δ = [Var.mk x A]): w.target_deBruijn n = [⟨n + (h ▸ w).var_ix, A⟩]
--   := by induction w generalizing n with
--   | nil => cases h
--   | cons _ w I => cases h; simp [var_ix, target_deBruijn, drop_target_deBruijn]
--   | skip _ w I => cases h; simp_arith [var_ix, target_deBruijn, I]

theorem Ctx.Wk.var_target_deBruijn' {ν α} {x : ν} {A : α} {Γ Δ : Ctx ν α} (n : ℕ)
  (w : Γ.Wk Δ) (h : Δ = [Var.mk x A])
  : w.target_deBruijn n = [Var.mk (n + (h ▸ w).var_ix) A]
  := by induction w generalizing n with
  | nil => cases h
  | cons _ w I => cases h; simp [var_ix, target_deBruijn, drop_target_deBruijn]
  | skip _ w I =>
    cases h
    simp only [target_deBruijn]
    rw [I _ rfl]
    simp only [var_ix]
    rw [add_assoc, add_comm 1]

theorem Ctx.Wk.var_target_deBruijn {ν α} {x : ν} {A : α} {Γ : Ctx ν α} (n : ℕ)
  (w: Γ.Wk [⟨x, A⟩]) : w.target_deBruijn n = [⟨n + w.var_ix, A⟩]
  := w.var_target_deBruijn' n rfl

def Ctx.Wk.var_deBruijn {ν α} {Γ : Ctx ν α} {x : ν} {A : α} (n : ℕ)
  (w : Γ.Wk [⟨x, A⟩]) : (Γ.deBruijn n).Wk [⟨n + w.var_ix, A⟩]
  := w.var_target_deBruijn n ▸ w.deBruijn n

theorem Ctx.Wk.iso_cast {ν : Type u} {α : Type v} {Γ Δ Γ' Δ' : Ctx ν α}
  (h : Γ.Wk Δ = Γ'.Wk Δ')
  (hΓ : Γ = Γ')
  (hΔ : Δ = Δ')
  (w: Γ.Wk Δ) : w.Iso (cast h w)
  := by cases hΓ; cases hΔ; cases h; exact Iso.refl w

theorem Ctx.Wk.iso_var_deBruijn {ν α} {Γ : Ctx ν α} {x : ν} {A : α} (n : ℕ)
  (w : Γ.Wk [⟨x, A⟩]) : w.Iso (w.var_deBruijn n)
  := Iso.trans (w.iso_deBruijn n) (by
    simp only [var_deBruijn, Eq.rec_eq_cast]
    apply iso_cast
    rfl
    apply var_target_deBruijn
    )

--TODO: pass in base name to begin induction from?

def Ctx.max_name {ν α} [Preorder ν] [DecidableRel λl r: ν => l < r] (Γ : Ctx ν α) : WithBot ν
  := (Γ.argmax Var.name).map Var.name

theorem Ctx.max_name_maximum_names {ν α} [Preorder ν] [DecidableRel λl r: ν => l < r]
  (Γ : Ctx ν α) : Γ.max_name = Γ.names.maximum
  := List.argmax_map Γ Var.name

theorem Ctx.le_max_name_of_mem {ν α} [LinearOrder ν]
  {Γ : Ctx ν α} {x m : ν} (hx : x ∈ Γ.names) (hm: Γ.max_name = m) : x ≤ m := by
  rw [max_name_maximum_names] at hm
  apply List.le_maximum_of_mem hx
  exact hm

theorem Ctx.le_max_name_of_mem' {ν α} [LinearOrder ν]
  {Γ : Ctx ν α} {x: ν} (hx : x ∈ Γ.names) : x ≤ Γ.max_name := by
  rw [max_name_maximum_names]
  apply List.le_maximum_of_mem' hx

def Ctx.min_name {ν α} [Preorder ν] [DecidableRel λl r: ν => l < r] (Γ : Ctx ν α) : WithTop ν
  := (Γ.argmin Var.name).map Var.name

theorem Ctx.max_name_nil {ν α} [Preorder ν] [DecidableRel λl r: ν => l < r]
  : Ctx.max_name (@List.nil (Var ν α)) = ⊥
  := rfl

theorem Ctx.min_name_nil {ν α} [Preorder ν] [DecidableRel λl r: ν => l < r]
  : Ctx.min_name (@List.nil (Var ν α)) = ⊤
  := rfl

def Ctx.next_name {ν α}
  [Preorder ν] [OrderBot ν] [s: SuccOrder ν] [DecidableRel λl r: ν => l < r] (Γ : Ctx ν α) : ν
  := match Γ.argmax Var.name with
  | some v => s.succ v.name
  | none => ⊥

theorem Ctx.next_name_nil {ν α} [Preorder ν] [OrderBot ν] [SuccOrder ν]
  [DecidableRel λl r: ν => l < r]
  : Ctx.next_name (@List.nil (Var ν α)) = ⊥
  := rfl

theorem Ctx.next_name_succ_max_name {ν α} [Preorder ν] [OrderBot ν] [SuccOrder ν]
  [DecidableRel λl r: ν => l < r] (Γ : Ctx ν α)
  : Γ.next_name = match Γ.max_name with | some x => Order.succ x | none => ⊥
  := by
    simp only [next_name, max_name, Option.map]
    generalize hm: List.argmax Var.name Γ = m
    cases m <;> rfl

theorem Ctx.max_name_le_next_name {ν α} [Preorder ν] [OrderBot ν] [SuccOrder ν]
  [DecidableRel λl r: ν => l < r] (Γ : Ctx ν α)
  : Γ.max_name ≤ Γ.next_name
  := by
    rw [next_name_succ_max_name]
    split
    . rename_i hmn
      rw [WithBot.le_coe_iff]
      intro m hm
      rw [hm] at hmn
      cases hmn
      apply SuccOrder.le_succ
    . rename_i hm
      rw [hm]
      apply WithBot.none_le

theorem Ctx.le_next_name_of_mem {ν α} [LinearOrder ν] [OrderBot ν] [SuccOrder ν]
  {Γ : Ctx ν α} {x : ν} (hx : x ∈ Γ.names)
  : x ≤ Γ.next_name := by
    rw [<-WithBot.coe_le_coe]
    apply le_trans
    apply le_max_name_of_mem' hx
    apply max_name_le_next_name

theorem Ctx.max_name_lt_next_name_or_max {ν α} [Preorder ν] [OrderBot ν] [s: SuccOrder ν]
  [DecidableRel λl r: ν => l < r] (Γ : Ctx ν α)
  : Γ.max_name < Γ.next_name ∨ IsMax Γ.next_name
  := by
    rw [next_name_succ_max_name]
    split
    . rename_i x hmn
      rw [WithBot.lt_coe_iff]
      if h : Order.succ x ≤ x then
        apply Or.inr
        apply IsMax.mono
        apply Order.max_of_succ_le h
        apply Order.le_succ
      else
        apply Or.inl
        intro x hx
        rw [hx] at hmn
        cases hmn
        rw [lt_iff_le_not_le]
        constructor
        apply Order.le_succ
        assumption
    . rename_i hm
      rw [hm]
      apply Or.inl
      simp only [WithBot.lt_coe_bot]
      rfl

theorem Ctx.lt_next_name_of_mem_or_max {ν α} [LinearOrder ν] [OrderBot ν] [SuccOrder ν]
  {Γ : Ctx ν α} {x : ν} (hx : x ∈ Γ.names)
  : x < Γ.next_name ∨ IsMax Γ.next_name := by match Γ.max_name_lt_next_name_or_max with
  | Or.inl h =>
    apply Or.inl
    rw [<-WithBot.coe_lt_coe]
    apply lt_of_le_of_lt
    apply Ctx.le_max_name_of_mem' hx
    exact h
  | Or.inr h => exact Or.inr h

theorem Ctx.lt_next_name_of_mem_or_max' {ν α} [LinearOrder ν] [OrderBot ν] [SuccOrder ν]
  {Γ : Ctx ν α} {x : ν} (hx : x ∈ Γ.names)
  : x < Γ.next_name ∨ IsMax x
  := by if h : x < Γ.next_name then
      exact Or.inl h
    else
      apply Or.inr
      cases lt_next_name_of_mem_or_max hx with
      | inl => contradiction
      | inr h' =>
        if h'' : Γ.next_name ≤ x then
          apply IsMax.mono
          apply h'
          apply h''
        else
         exact (h (lt_of_le_not_le (le_next_name_of_mem hx) h'')).elim

theorem Ctx.lt_next_name_of_mem {ν α} [LinearOrder ν] [OrderBot ν] [SuccOrder ν] [NoMaxOrder ν]
  {Γ : Ctx ν α} {x : ν} (hx : x ∈ Γ.names)
  : x < Γ.next_name := match Γ.lt_next_name_of_mem_or_max' hx with
  | Or.inl h => h
  | Or.inr h =>
    have ⟨b, hb⟩ := NoMaxOrder.exists_gt x
    (isMax_iff_forall_not_lt.mp h b hb).elim

theorem Ctx.ne_next_name_of_mem {ν α} [LinearOrder ν] [OrderBot ν] [SuccOrder ν] [NoMaxOrder ν]
  {Γ : Ctx ν α} {x : ν} (hx : x ∈ Γ.names)
  : x ≠ Γ.next_name := ne_of_lt (lt_next_name_of_mem hx)

theorem Ctx.next_name_not_mem {ν α} [LinearOrder ν] [OrderBot ν] [SuccOrder ν] [NoMaxOrder ν]
  (Γ : Ctx ν α) : Γ.next_name ∉ Γ.names := λh => Γ.ne_next_name_of_mem h rfl

theorem Ctx.next_name_fresh {ν α} [LinearOrder ν] [OrderBot ν] [SuccOrder ν] [NoMaxOrder ν]
  (Γ : Ctx ν α) : Γ.Fresh Γ.next_name := Fresh.of_not_mem_names (Γ.next_name_not_mem)

instance : Append (Ctx ν α) := ⟨List.append⟩

def Ctx.reverse {ν α} (Γ : Ctx ν α) : Ctx ν α := List.reverse Γ

-- TODO: factor into files

-- TODO: indexed contexts, weakening of those, mappings; copy the Wk.lean file probably...

-- TODO: deduplication and dedup-weakening ==> dedup-substitution
