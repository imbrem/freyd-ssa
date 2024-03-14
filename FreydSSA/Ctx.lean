import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fin.Basic
import Mathlib.Init.Classical
import Mathlib.Order.SuccPred.Basic

import FreydSSA.Utils

open List.«term_<+_»

structure Var (ν : Type u) (α : Type v) : Type (max u v) where
  name: ν
  ty: α

def Ctx (ν : Type u) (α : Type v) : Type (max u v) := List (Var ν α)

instance {ν α} : Membership (Var ν α) (Ctx ν α) := List.instMembershipList

def Ctx.Typed (Γ : Ctx ν α) : Prop
  := ∀ v ∈ Γ, ∀ v' ∈ Γ, v.name = v'.name → v.ty = v'.ty

@[simp]
def Ctx.names {ν α} (Γ : Ctx ν α): List ν
  := Γ.map Var.name

def Ctx.Nodup {ν α} (Γ : Ctx ν α) : Prop
  := Γ.names.Nodup

theorem Ctx.Nodup.typed {Γ : Ctx ν α} (h : Γ.Nodup) : Γ.Typed
  := λ v hv v' hv' hvv' => open Classical in Classical.by_contradiction (λb => by
    induction Γ with
    | nil => cases hv
    | cons x Γ I =>
      cases hv with
      | head => cases hv' with
        | head => contradiction
        | tail _ hm =>
          have hm := List.mem_map_of_mem Var.name hm
          exact h.not_mem (hvv' ▸ hm)
      | tail _ hm =>
        cases hv' with
        | head =>
          have hm := List.mem_map_of_mem Var.name hm
          exact h.not_mem (hvv' ▸ hm)
        | tail _ hm' => exact I h.of_cons hm hm'
  )

instance {ν α} : Membership ν (Ctx ν α) where
  mem a Γ := a ∈ Γ.names

inductive Ctx.Fresh {ν α} (n : ν) : Ctx ν α → Prop
  | nil : Ctx.Fresh n []
  | cons {Γ x} : x.name ≠ n → Ctx.Fresh n Γ → Ctx.Fresh n (x::Γ)

theorem Ctx.Fresh.not_mem_names {ν α} {n} {Γ : Ctx ν α}
  : Γ.Fresh n → n ∉ Γ.names
  | nil, h => by cases h
  | cons hx hΓ, h => by cases h with
    | head => contradiction
    | tail _ h => exact not_mem_names hΓ h

theorem Ctx.Fresh.of_not_mem_names {ν α} {n} {Γ : Ctx ν α} (h: n ∉ Γ.names): Ctx.Fresh n Γ
  := by induction Γ with
  | nil => exact Fresh.nil
  | cons x Γ I =>
    apply Fresh.cons
    apply Ne.symm
    apply List.ne_of_not_mem_cons
    exact h
    apply I
    apply List.not_mem_of_not_mem_cons
    exact h

theorem Ctx.Fresh.iff_not_mem_names {ν α} (n) (Γ : Ctx ν α)
  : Γ.Fresh n ↔ n ∉ Γ.names
  := ⟨Fresh.not_mem_names, Fresh.of_not_mem_names⟩

theorem Ctx.nodup_cons {ν α} {v : Var ν α} {Γ : Ctx ν α}
  : Ctx.Nodup (v::Γ) ↔ Γ.Fresh v.name ∧ Γ.Nodup
  := by simp only [Fresh.iff_not_mem_names]; exact List.nodup_cons

theorem Ctx.Fresh.head {ν α} {n} {y : Var ν α} {Γ : Ctx ν α}
  : Ctx.Fresh n (y::Γ) → y.name ≠ n
  | cons hxn _ => hxn

theorem Ctx.Fresh.tail {ν α} {n} {y : Var ν α} {Γ : Ctx ν α}
  : Ctx.Fresh n (y::Γ) → Ctx.Fresh n Γ
  | cons _ hn => hn

theorem Ctx.Nodup.head {ν α} {v : Var ν α} {Γ : Ctx ν α}
  : Ctx.Nodup (v::Γ) → Γ.Fresh v.name
  := λh => (Ctx.nodup_cons.mp h).1

theorem Ctx.Nodup.tail {ν α} {v : Var ν α} {Γ : Ctx ν α}
  : Ctx.Nodup (v::Γ) → Γ.Nodup
  := λh => (Ctx.nodup_cons.mp h).2

inductive Ctx.Wk {ν: Type u} {α: Type v} : Ctx ν α → Ctx ν α → Type (max u v)
  | nil : Ctx.Wk [] []
  | cons {Γ Δ} (x : Var ν α) : Ctx.Wk Γ Δ → Ctx.Wk (x::Γ) (x::Δ)
  | skip {Γ Δ} : Ctx.Fresh x.name Δ → Ctx.Wk Γ Δ → Ctx.Wk (x::Γ) Δ

def Ctx.Wk.src {ν α} {Γ Δ : Ctx ν α} (_: Γ.Wk Δ) : Ctx ν α := Γ
def Ctx.Wk.trg {ν α} {Γ Δ : Ctx ν α} (_: Γ.Wk Δ) : Ctx ν α := Δ

theorem Ctx.Wk.ty_eq {Γ : Ctx ν α} : Wk Γ [⟨x, A⟩] → Wk Γ [⟨x, A'⟩] → A = A'
  | cons _ _, cons _ _ => rfl
  | cons _ _, skip hx _ | skip hx _, cons _ _ => by cases hx; contradiction
  | skip _ w, skip _ w' => w.ty_eq w'

theorem Ctx.Wk.from_nil {ν α} {Γ : Ctx ν α} : Wk [] Γ → Γ = []
  | nil => rfl

theorem Ctx.Fresh.wk {ν α} {Γ Δ: Ctx ν α} {n: ν}: Fresh n Γ → Γ.Wk Δ → Fresh n Δ
  | _, Wk.nil => nil
  | cons hxn hn, Wk.cons _ h => cons hxn (hn.wk h)
  | cons _ hn, Wk.skip _ h => hn.wk h

theorem Ctx.Nodup.wk {ν α} {Γ Δ: Ctx ν α} (hΓ: Γ.Nodup) (h: Γ.Wk Δ) : Δ.Nodup
  := by induction h with
  | nil => exact hΓ
  | cons v w I =>
    simp [Ctx.nodup_cons]
    exact ⟨hΓ.head.wk w, I hΓ.tail⟩
  | skip _ _ I =>
    exact I hΓ.tail

def Ctx.Wk.comp {ν α} {Γ Δ Ξ : Ctx ν α} : Γ.Wk Δ → Δ.Wk Ξ → Γ.Wk Ξ
  | nil, h => h
  | cons x h, cons _ h' => cons x (h.comp h')
  | cons _ h, skip hn h' => skip hn (h.comp h')
  | skip hn h, h' => skip (hn.wk h') (h.comp h')

theorem Ctx.Wk.allEq {ν α} {Γ Δ : Ctx ν α} (D D': Γ.Wk Δ): D = D'
  := by induction D with
  | nil => cases D'; rfl
  | cons _ _ I => cases D' with
    | cons => exact congrArg _ (I _)
    | skip hxn => exact (hxn.head rfl).elim
  | skip hxn _ I => cases D' with
    | cons _ _ => exact (hxn.head rfl).elim
    | skip h I' => exact congrArg _ (I I')

def Ctx.Wk.refl {ν α} : (Γ : Ctx ν α) → Γ.Wk Γ
  | [] => nil
  | x::Γ => cons x (refl Γ)

def Ctx.Wk.drop {ν α} : (Γ : Ctx ν α) → Γ.Wk []
  | [] => nil
  | _::Γ => skip Fresh.nil (drop Γ)

def Ctx.Wk.head {ν α} (v : Var ν α) (Γ : Ctx ν α) : Wk (v::Γ) [v]
  := cons v (drop Γ)

def Ctx.get_wk {ν α} (Γ : Ctx ν α) (i : Fin Γ.length)
  (hi : ∀ j, (Γ.get i).name = (Γ.get j).name -> i ≤ j) : Wk Γ [Γ.get i]
  := match Γ, i with
  | x::Γ, ⟨0, _⟩ => Wk.head x Γ
  | x::Γ, ⟨i+1, h⟩ => Wk.skip (Fresh.of_not_mem_names
      (λhm => by
        match x with
        | ⟨x, A⟩ =>
          simp only [
            names, List.get_cons_succ, List.map_cons, List.map_nil,
            List.mem_singleton
          ] at hm
          apply Nat.not_succ_le_zero
          apply hi ⟨0, by simp⟩
          simp [hm]
        )
    )
    (get_wk Γ
      ⟨i, Nat.lt_of_succ_lt_succ h⟩
      λj hj => Nat.le_of_succ_le_succ (hi j.succ hj))

def Ctx.Nodup.get {ν α} {Γ : Ctx ν α} (hΓ : Γ.Nodup) (i : Fin Γ.length)
  : Wk Γ [Γ.get i]
  := Γ.get_wk i (λ⟨j, hj⟩ hj' => le_of_eq $ open Classical in by
    match i with
    | ⟨i, hi⟩ =>
      apply Fin.ext
      rw [<-@List.get_indexOf _ (Classical.typeDecidableEq _) _ hΓ
        ⟨i, by rw [names, List.length_map]; exact hi⟩]
      rw [<-@List.get_indexOf _ (Classical.typeDecidableEq _) _ hΓ
        ⟨j, by rw [names, List.length_map]; exact hj⟩]
      simp [hj']
  )

theorem Ctx.names_indexOf_lt_length {ν α} [DecidableEq ν] {x : ν} {Γ : Ctx ν α}
  (h : x ∈ Γ.names) : Γ.names.indexOf x < Γ.length
  := cast (by simp) (List.indexOf_lt_length.mpr h)

-- Note this is just a poor reimplementation of Sigma, so maybe just use that...
def Ctx.nameIndex {ν α} [DecidableEq ν] (Γ : Ctx ν α) (x : ν): ℕ
  := Γ.findIdx (λv => v.name = x)

def Ctx.nameIndex_lt_length_of_mem {ν α} [DecidableEq ν] {x : ν} {Γ : Ctx ν α}
  (h : x ∈ Γ.names) : Γ.nameIndex x < Γ.length
  := List.findIdx_lt_length_of_exists (by
      induction Γ with
      | nil => cases h
      | cons v Γ I =>
        if h' : v.name = x then
          exact ⟨v, List.Mem.head _, by simp [h']⟩
        else
          cases h with
          | head => contradiction
          | tail _ h =>
            have ⟨v', hv', hveq⟩ := I h;
            exact ⟨v', hv'.tail _, hveq⟩
  )

theorem Ctx.get_nameIndex {ν α} [DecidableEq ν] {x : ν} {Γ : Ctx ν α}
  (h : x ∈ Γ.names) : (Γ.get ⟨Γ.nameIndex x, Γ.nameIndex_lt_length_of_mem h⟩).name = x
  := by
    simp only [nameIndex]
    apply of_decide_eq_true
    apply @List.findIdx_get _ (λv => v.name = x) Γ

theorem Ctx.nameIndex_cons {ν α} [DecidableEq ν] (v : Var ν α) (Γ : Ctx ν α) (x : ν)
  : nameIndex (v::Γ) x = if v.name = x then 0 else (nameIndex Γ x) + 1
  := by simp [nameIndex, List.findIdx_cons _ v Γ]

-- TODO: make this general findIdx, findIndex lemma; why is this not in stdlib
theorem Ctx.nameIndex_first {ν α} [DecidableEq ν] (x : ν) (Γ : Ctx ν α)
  : ∀j, x = (Γ.get j).name → Γ.nameIndex x ≤ j
  := λj hj => by induction Γ with
    | nil => exact Nat.zero_le _
    | cons v Γ I =>
      rw [nameIndex_cons]
      split
      simp
      match j with
      | ⟨0, _⟩ => cases hj; contradiction
      | ⟨j + 1, hj'⟩ =>
        simp only [add_le_add_iff_right]
        exact I ⟨j, (Nat.lt_of_succ_lt_succ hj')⟩ hj

def Ctx.get_first {ν α} [DecidableEq ν] {x : ν} {Γ : Ctx ν α} (h: x ∈ Γ.names)
   : Wk Γ [Γ.get ⟨Γ.nameIndex x, Γ.nameIndex_lt_length_of_mem h⟩]
  := Γ.get_wk
    ⟨Γ.nameIndex x, Γ.nameIndex_lt_length_of_mem h⟩
    ((Γ.get_nameIndex h).symm ▸ (Γ.nameIndex_first x))

-- def Ctx.get_typed {ν α} [DecidableEq ν] {v : Var ν α} {Γ : Ctx ν α} (h : v ∈ Γ)
--   (ht : ∀ v' ∈ Γ, v.name = v'.name → v.ty = v'.ty) : ...
--   := sorry

--TODO: Ctx.Typed.get, equal to other gets

inductive Ctx.Iso : Ctx ν α → Ctx ν' α → Prop
  | nil : Ctx.Iso [] []
  | cons : Ctx.Iso Γ Δ → Ctx.Iso (⟨n, a⟩::Γ) (⟨n', a⟩::Δ)

theorem Ctx.Iso.cons'
  : {x : Var ν α} → {x' : Var ν' α} → (hx: x.ty = x'.ty) → (h: Ctx.Iso Γ Δ)
    → Ctx.Iso (x::Γ) (x'::Δ)
  | ⟨_, _⟩, ⟨_, _⟩, rfl, h => Ctx.Iso.cons h

inductive Ctx.Wk.Iso : {Γ Δ : Ctx ν α} → {Γ' Δ' : Ctx ν' α'} → Ctx.Wk Γ Δ → Ctx.Wk Γ' Δ' → Prop
  | nil : Ctx.Wk.Iso nil nil
  | cons : Ctx.Wk.Iso w w' → Ctx.Wk.Iso (cons h w) (cons h' w')
  | skip : Ctx.Wk.Iso w w' → Ctx.Wk.Iso (skip h w) (skip h' w')

theorem Ctx.Wk.iso_refl {Γ Δ : Ctx ν α} : (w: Γ.Wk Δ) → w.Iso w
  | Wk.nil => Iso.nil
  | Wk.cons h w => Iso.cons w.iso_refl
  | Wk.skip h w => Iso.skip w.iso_refl

def Ctx.Wk.Iso.of_length_eq
  : {Γ : Ctx ν α} → {Γ' : Ctx ν' α'}
    → Γ.length = Γ'.length
    → (Ctx.Wk.refl Γ).Iso (Ctx.Wk.refl Γ')
  | [], [], rfl => nil
  | _::Γ, _::Γ', h => cons (of_length_eq
    (by simp only [List.length_cons, Nat.succ.injEq] at h; exact h))

def Ctx.Wk.Iso.length_eq_src {Γ Δ : Ctx ν α} {Γ' Δ' : Ctx ν' α'}
  {w : Γ.Wk Δ} {w' : Γ'.Wk Δ'} : w.Iso w' → Γ.length = Γ'.length
  | nil => rfl
  | cons hw => by simp [hw.length_eq_src]
  | skip hw => by simp [hw.length_eq_src]

def Ctx.Wk.Iso.length_eq_trg {Γ Δ : Ctx ν α} {Γ' Δ' : Ctx ν' α'}
  {w : Γ.Wk Δ} {w' : Γ'.Wk Δ'} : w.Iso w' → Δ.length = Δ'.length
  | nil => rfl
  | cons hw => by simp [hw.length_eq_trg]
  | skip hw => hw.length_eq_trg

theorem Ctx.Iso.toWk {Γ : Ctx ν α} {Γ' : Ctx ν' α}
  : (h: Ctx.Iso Γ Γ') → (Ctx.Wk.refl Γ).Iso (Ctx.Wk.refl Γ')
  | nil => Wk.Iso.nil
  | cons h => Wk.Iso.cons (toWk h)

theorem Ctx.Wk.Iso.refl {Γ Δ : Ctx ν α} : (w: Γ.Wk Δ) → w.Iso w
  | Wk.nil => Iso.nil
  | Wk.cons h w => Iso.cons w.iso_refl
  | Wk.skip h w => Iso.skip w.iso_refl

theorem Ctx.Wk.Iso.symm {Γ Δ : Ctx ν α} {Γ' Δ' : Ctx ν' α'} {w: Γ.Wk Δ} {w': Γ'.Wk Δ'}
  : w.Iso w' → w'.Iso w
  | Iso.nil => Iso.nil
  | Iso.cons I => Iso.cons (I.symm)
  | Iso.skip I => Iso.skip (I.symm)

theorem Ctx.Wk.Iso.trans {Γ Δ : Ctx ν α} {Γ' Δ' : Ctx ν' α'} {Γ'' Δ'' : Ctx ν'' α''}
  {w: Γ.Wk Δ} {w': Γ'.Wk Δ'} {w'': Γ''.Wk Δ''}
  : w.Iso w' → w'.Iso w'' → w.Iso w''
  | Iso.nil, Iso.nil => Iso.nil
  | Iso.cons I, Iso.cons I' => Iso.cons (I.trans I')
  | Iso.skip I, Iso.skip I' => Iso.skip (I.trans I')

theorem Ctx.Wk.Iso.comp {Γ Δ Ξ : Ctx ν α} {Γ' Δ' Ξ' : Ctx ν' α}
  {l: Γ.Wk Δ} {r: Δ.Wk Ξ} {l': Γ'.Wk Δ'} {r': Δ'.Wk Ξ'}
  : l.Iso l' → r.Iso r' → (l.comp r).Iso (l'.comp r')
  | Iso.nil, hr => hr
  | Iso.cons Il, Iso.cons Ir => Iso.cons (Il.comp Ir)
  | Iso.cons Il, Iso.skip Ir => Iso.skip (Il.comp Ir)
  | Iso.skip Il, hr => Iso.skip (Il.comp hr)

def Ctx.Wk.names {ν α} {Γ Δ : Ctx ν α} : Γ.Wk Δ → Δ.names.Sublist Γ.names
  | Wk.nil => List.Sublist.slnil
  | Wk.cons _ h => h.names.cons₂ _
  | Wk.skip _ h => h.names.cons _

def Ctx.InjOn (ρ : ν → ν') (Γ : Ctx ν α) : Prop
  := Set.InjOn ρ { x : ν | x ∈ Γ.names }

theorem Ctx.injOn_empty (ρ : ν → ν') : Ctx.InjOn ρ (@List.nil (Var ν α))
  := λ _ hx => nomatch hx

theorem Ctx.InjOn.tail {ρ: ν → ν'} {v} {Γ : Ctx ν α} (h: Ctx.InjOn ρ (v::Γ))
  : Ctx.InjOn ρ Γ
  := λ _ hx _ hy hxy => h (hx.tail _) (hy.tail _) hxy

theorem Ctx.InjOn.head {ρ: ν → ν'} {v} {Γ : Ctx ν α} (h: Ctx.InjOn ρ (v::Γ))
  : ∀x ∈ Γ.names, ρ x = ρ v.name → x = v.name
  := λ _ hx hx' => h (hx.tail _) (by simp) hx'

theorem Ctx.InjOn.head_ne {ρ : ν → ν'} {v} {Γ : Ctx ν α} (h : Ctx.InjOn ρ (v::Γ))
  : ∀x ∈ Γ.names, x ≠ v.name → ρ x ≠ ρ v.name
  := λ _ hx hx' => h.ne (hx.tail _) (by simp) hx'

theorem Ctx.InjOn.cons {ρ : ν → ν'} {v : Var ν α} {Γ : Ctx ν α}
  (hv : ∀x ∈ Γ.names, ρ x = ρ v.name → x = v.name) (h : Ctx.InjOn ρ Γ)
  : Ctx.InjOn ρ (v::Γ)
  | _, List.Mem.head _, _, List.Mem.head _, _ => rfl
  | _, List.Mem.head _, _, List.Mem.tail _ ha, hav => (hv _ ha hav.symm).symm
  | _, List.Mem.tail _ ha, _, List.Mem.head _, hav => hv _ ha hav
  | _, List.Mem.tail _ hx, _, List.Mem.tail _ hy, hxy => h hx hy hxy

theorem Ctx.InjOn.cons_ne {ρ : ν → ν'} {v : Var ν α} {Γ : Ctx ν α}
  (hv : ∀x ∈ Γ.names, x ≠ v.name → ρ x ≠ ρ v.name) (h : Ctx.InjOn ρ Γ)
  : Ctx.InjOn ρ (v::Γ)
  := h.cons (λ_ hx hxv => Classical.by_contradiction (λh => hv _ hx h hxv))

theorem Ctx.InjOn.wk {ρ : ν → ν'} {Γ : Ctx ν α} (hΓ : Γ.InjOn ρ) : Γ.Wk Δ → Δ.InjOn ρ
  | Wk.nil => Ctx.injOn_empty _
  | Wk.cons x h => (hΓ.tail.wk h).cons (λ_ hx hxv => hΓ.head _ (h.names.subset hx) hxv)
  | Wk.skip _ h => hΓ.tail.wk h

def Ctx.EqOn (ρ₁ ρ₂ : ν → ν') (Γ : Ctx ν α): Prop
  := Set.EqOn ρ₁ ρ₂ { x : ν | x ∈ Γ.names }

theorem Ctx.EqOn.head {ρ₁ ρ₂ : ν → ν'} {v} {Γ : Ctx ν α} (h : Ctx.EqOn ρ₁ ρ₂ (v::Γ))
  : ρ₁ v.name = ρ₂ v.name
  := h (by simp)

theorem Ctx.EqOn.tail {ρ₁ ρ₂ : ν → ν'} {v} {Γ : Ctx ν α} (h : Ctx.EqOn ρ₁ ρ₂ (v::Γ))
  : Ctx.EqOn ρ₁ ρ₂ Γ
  := λ _ hx => h (hx.tail _)

structure Label (ν κ : Type u) (α : Type v) where
  name : κ
  param : α
  live : Ctx ν α

structure Label.Wk (ℓ ℓ' : Label ν κ α) where
  name : ℓ.name = ℓ'.name
  param : ℓ.param = ℓ'.param
  live : ℓ.live.Wk ℓ'.live

def Label.Wk.refl (ℓ : Label ν κ α) : ℓ.Wk ℓ := ⟨rfl, rfl, Ctx.Wk.refl _⟩

def Label.Wk.comp {ℓ ℓ' ℓ'' : Label ν κ α} (w : ℓ.Wk ℓ') (w' : ℓ'.Wk ℓ'') : ℓ.Wk ℓ''
  := ⟨w.name.trans w'.name, w.param.trans w'.param, w.live.comp w'.live⟩

abbrev Label.Wk.Iso {ℓ ℓ' ℓ'' ℓ''' : Label ν κ α} (w : ℓ.Wk ℓ') (w' : ℓ''.Wk ℓ''')
  := w.live.Iso w'.live

structure Label.Fresh (ℓ : Label ν κ α) (n : ν): Prop where
  -- name : ℓ.name ≠ n
  live : ℓ.live.Fresh n

def LCtx (ν κ: Type u) (α: Type v) := List (Label ν κ α)

inductive LCtx.Fresh {ν κ α} (n : ν) : LCtx ν κ α → Prop
  | nil : LCtx.Fresh n []
  | cons : ℓ.Fresh n → Fresh n L → Fresh n (ℓ::L)

theorem LCtx.Fresh.head {ν α} {n} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : LCtx.Fresh n (ℓ::L) → ℓ.Fresh n
  | cons hxn _ => hxn

theorem LCtx.Fresh.tail {ν α} {n} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : LCtx.Fresh n (ℓ::L) → L.Fresh n
  | cons _ h => h

inductive LCtx.Wk {ν : Type u} {α : Type v} : LCtx ν κ α → LCtx ν κ α → Type (max u v)
  | nil : Wk [] []
  | cons {ℓ ℓ' : Label ν κ α} : ℓ.Wk ℓ' → Wk L K → Wk (ℓ::L) (ℓ'::K)
  | skip (ℓ : Label ν κ α) : Wk L K → Wk L (ℓ::K) --TODO: freshness?

def LCtx.Wk.comp {L K M : LCtx ν κ α} : L.Wk K → K.Wk M → L.Wk M
  | Wk.nil, w => w
  | Wk.cons h w, Wk.cons h' w' => Wk.cons (h.comp h') (w.comp w')
  | Wk.skip _ w, Wk.cons h w' => Wk.skip _ (w.comp w')
  | w, Wk.skip ℓ w' => Wk.skip _ (w.comp w')

inductive LCtx.Wk.Iso : {L K : LCtx ν κ α} → {L' K' : LCtx ν' κ' α'} → Wk L K → Wk L' K' → Prop
  | nil : Iso nil nil
  | cons : h.Iso h' → Iso w w' → Iso (cons h w) (cons h' w')
  | skip (ℓ ℓ') : Iso w w' → Iso (skip ℓ w) (skip ℓ' w')

theorem LCtx.Wk.Iso.refl {L K : LCtx ν κ α} : (w: L.Wk K) → w.Iso w
  | Wk.nil => nil
  | Wk.cons h w => cons h.live.iso_refl (refl w)
  | Wk.skip _ w => skip _ _ (refl w)

theorem LCtx.Wk.Iso.symm {L K : LCtx ν κ α} {L' K' : LCtx ν' κ' α'}
  {w: L.Wk K} {w': L'.Wk K'} : (h: w.Iso w') → w'.Iso w
  | nil => nil
  | cons h w => cons h.symm w.symm
  | skip _v _ w => skip _ _ w.symm

theorem LCtx.Wk.Iso.trans {L K : LCtx ν κ α} {L' K' : LCtx ν' κ' α'} {L'' K'' : LCtx ν'' κ'' α''}
  {w: L.Wk K} {w': L'.Wk K'} {w'': L''.Wk K''} : (h: w.Iso w') → (h': w'.Iso w'') → w.Iso w''
  | nil, nil => nil
  | cons h w, cons h' w' => cons (h.trans h') (w.trans w')
  | skip _ _v w, skip _ _ w' => skip _ _ (w.trans w')

theorem LCtx.Wk.Iso.comp {L K M : LCtx ν κ α} {L' K' M' : LCtx ν' κ' α'}
  {l: L.Wk K} {r: K.Wk M} {l': L'.Wk K'} {r': K'.Wk M'}
  (hl: l.Iso l') (hr: r.Iso r'): (l.comp r).Iso (l'.comp r') := by
  induction hr generalizing L
  <;> cases hl
  <;> repeat first | apply Ctx.Wk.Iso.comp | apply_assumption | constructor

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

--TODO: Define SCtx guaranteeing unique variable names?
