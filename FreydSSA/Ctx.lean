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

open List.«term_<+_»

structure Var (ν : Type u) (α : Type v) : Type (max u v) where
  name: ν
  ty: α
  deriving DecidableEq

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

inductive Ctx.Wk : Ctx ν α → Ctx ν α → Type _
  | nil : Ctx.Wk [] []
  | cons {Γ Δ} (x : Var ν α) : Ctx.Wk Γ Δ → Ctx.Wk (x::Γ) (x::Δ)
  | skip {Γ Δ} : Ctx.Fresh x.name Δ → Ctx.Wk Γ Δ → Ctx.Wk (x::Γ) Δ

def Ctx.Wk.src {ν α} {Γ Δ : Ctx ν α} (_: Γ.Wk Δ) : Ctx ν α := Γ
def Ctx.Wk.trg {ν α} {Γ Δ : Ctx ν α} (_: Γ.Wk Δ) : Ctx ν α := Δ

theorem Ctx.Wk.tyEq {Γ : Ctx ν α} : Wk Γ [⟨x, A⟩] → Wk Γ [⟨x, A'⟩] → A = A'
  | cons _ _, cons _ _ => rfl
  | cons _ _, skip hx _ | skip hx _, cons _ _ => by cases hx; contradiction
  | skip _ w, skip _ w' => w.tyEq w'

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

theorem Ctx.Wk.antisymm {ν α} {Γ Δ : Ctx ν α} (h : Γ.Wk Δ) (h' : Δ.Wk Γ) : Γ = Δ
  := by induction h with
  | nil => cases h'; rfl
  | cons x _ I =>
    cases h' with
    | cons x' h' =>
      congr
      exact I h'
    | skip hx => exact (hx.head rfl).elim
  | skip hx => exact ((hx.wk h').head rfl).elim

def Ctx.Wk.drop {ν α} : (Γ : Ctx ν α) → Γ.Wk []
  | [] => nil
  | _::Γ => skip Fresh.nil (drop Γ)

def Ctx.Wk.head {ν α} (v : Var ν α) (Γ : Ctx ν α) : Wk (v::Γ) [v]
  := cons v (drop Γ)

def Ctx.Wk.join {ν α} {Γ Δ Δ' : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : Ctx ν α
  := match Γ, w, w' with
  | [], _, _ => []
  | v::_, cons _ w, cons _ w' => v::(join w w')
  | v::_, cons _ w, skip _ w' => v::(join w w')
  | v::_, skip _ w, cons _ w' => v::(join w w')
  | _::_, skip _ w, skip _ w' => join w w'

def Ctx.Wk.join_left {ν α} {Γ Δ Δ' : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : (w.join w').Wk Δ
  := match Γ, w, w' with
  | [], nil, nil => nil
  | _::_, cons _ w, cons _ w' => cons _ (w.join_left w')
  | _::_, cons _ w, skip hx w' => cons _ (w.join_left w')
  | _::_, skip hx w, cons _ w' => skip hx (w.join_left w')
  | _::_, skip _ w, skip _ w' => w.join_left w'

def Ctx.Wk.join_right {ν α} {Γ Δ Δ' : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : (w.join w').Wk Δ'
  := match Γ, w, w' with
  | [], nil, nil => nil
  | _::_, cons _ w, cons _ w' => cons _ (w.join_right w')
  | _::_, cons _ w, skip hx w' => skip hx (w.join_right w')
  | _::_, skip _ w, cons _ w' => cons _ (w.join_right w')
  | _::_, skip _ w, skip _ w' => w.join_right w'

theorem Ctx.Fresh.join {ν α} {Γ Δ Δ' : Ctx ν α} {x : ν}
  (f : Δ.Fresh x) (f' : Δ'.Fresh x)
  (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : (w.join w').Fresh x
  := match Γ, w, w' with
  | [], Wk.nil, Wk.nil => nil
  | _::_, Wk.cons _ w, Wk.cons _ w' => cons f.head (join f.tail f'.tail w w')
  | _::_, Wk.cons _ w, Wk.skip hx w' => cons f.head (join f.tail f' w w')
  | _::_, Wk.skip _ w, Wk.cons _ w' => cons f'.head (join f f'.tail w w')
  | _::_, Wk.skip _ w, Wk.skip hx' w' => join f f' w w'

def Ctx.Wk.join_entry {ν α} {Γ Δ Δ' : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : Γ.Wk (w.join w')
  := match Γ, w, w' with
  | [], nil, nil => nil
  | _::_, cons _ w, cons _ w' => cons _ (w.join_entry w')
  | _::_, cons _ w, skip hx w' => cons _ (w.join_entry w')
  | _::_, skip _ w, cons _ w' => cons _ (w.join_entry w')
  | _::_, skip f w, skip f' w' => skip (f.join f' w w') (w.join_entry w')

theorem Ctx.Wk.join_nil {ν α} {Γ Δ : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk [])
  : w.join w' = Δ
  := by induction w <;> cases w' <;> simp [join, *]

theorem Ctx.Wk.join_idem {ν α} {Γ Δ : Ctx ν α} (w : Γ.Wk Δ)
  : w.join w = Δ
  := by induction w  <;> simp [join, *]

theorem Ctx.Wk.join_comm {ν α} {Γ Δ Δ' : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : w.join w' = w'.join w
  := by induction w generalizing Δ' with
  | nil => cases w'; simp [join]
  | cons _ w I => cases w' with
    | cons _ w' => simp [join, I w']
    | skip _ w' => simp [join, I w']
  | skip _ w I => cases w' with
    | cons _ w' => simp [join, I w']
    | skip _ w' => simp [join, I w']

--TODO: join_assoc

theorem Ctx.Wk.nil_join {ν α} {Γ Δ : Ctx ν α} (w : Γ.Wk []) (w' : Γ.Wk Δ)
  : w.join w' = Δ
  := by rw [join_comm, join_nil]

theorem Ctx.Wk.join_left_right {ν α} {Γ Δ Δ' : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : (w.join_left w').join (w.join_right w') = w.join w'
  := by induction w generalizing Δ' with
  | nil => cases w'; simp [join_left, join_right]
  | cons _ w I => cases w' with
    | cons _ w' => simp [join, join_left, I w']
    | skip _ w' => simp [join, join_left, I w']
  | skip _ w I => cases w' with
    | cons _ w' => simp [join, join_left, I w']
    | skip _ w' => simp [join, join_left, join_right, I w']

theorem Ctx.Wk.join_comp {ν α} {Γ' Γ Δ Δ' : Ctx ν α}
  (w : Γ'.Wk Γ) (wl : Γ.Wk Δ) (wr : Γ.Wk Δ')
  : (w.comp wl).join (w.comp wr) = wl.join wr
  := by induction w generalizing Δ Δ' <;>
    cases wl <;> cases wr <;> simp [join, comp, *]

theorem Ctx.Wk.join_eq {Ω Γ Γ' Δ Δ' : Ctx ν α}
  (w : Ω.Wk Γ) (w' : Ω.Wk Γ')
  (wl : Γ.Wk Δ) (wr : Γ.Wk Δ') (wl' : Γ'.Wk Δ) (wr' : Γ'.Wk Δ')
  : wl.join wr = wl'.join wr'
  := by
    rw [<-join_comp w wl wr, <-join_comp w' wl' wr']
    congr 1 <;> apply Ctx.Wk.allEq

--TODO: note this should work if Ω weakens both joins

def Ctx.Wk.join_join {ν α} {Ω Γ Γ' Δ Δ' : Ctx ν α}
  (w : Ω.Wk Γ) (w' : Ω.Wk Γ')
  (wl : Γ.Wk Δ) (wr : Γ.Wk Δ') (wl' : Γ'.Wk Δ) (wr' : Γ'.Wk Δ') : Γ'.Wk (wl.join wr)
  := w.join_eq w' wl wr wl' wr' ▸ wl'.join_entry wr'

--TODO: join iso

def Ctx.Wk.meet {ν α} {Γ Δ Δ' : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : Ctx ν α
  := match w, w' with
  | nil, nil => []
  | cons v w, cons _ w' => v::(meet w w')
  | cons _ w, skip _ w' => meet w w'
  | skip _ w, cons _ w' => meet w w'
  | skip _ w, skip _ w' => meet w w'

theorem Ctx.Wk.meet_comm {ν α} {Γ Δ Δ' : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : w.meet w' = w'.meet w
  := by induction w generalizing Δ' <;> cases w' <;> simp [meet, *]

theorem Ctx.Wk.mem_left_of_mem_meet {ν α} {Γ Δ Δ' : Ctx ν α} {x}
  : (w : Γ.Wk Δ) → (w' : Γ.Wk Δ') → x ∈ (w.meet w').names → x ∈ Δ.names
  | nil, nil => λh => by cases h
  | cons _ w, cons _ w' => λh => by
    simp only [names, List.map_cons, List.mem_cons, List.map] at *
    match h with
    | Or.inl h => exact Or.inl h
    | Or.inr h => exact Or.inr (mem_left_of_mem_meet w w' h)
  | cons _ w, skip _ w' => λh => List.mem_cons_of_mem _ (mem_left_of_mem_meet w w' h)
  | skip _ w, cons _ w' => mem_left_of_mem_meet w w'
  | skip _ w, skip _ w' => mem_left_of_mem_meet w w'

theorem Ctx.Wk.mem_right_of_mem_meet {ν α} {Γ Δ Δ' : Ctx ν α} {x}
  : (w : Γ.Wk Δ) → (w' : Γ.Wk Δ') → x ∈ (w.meet w').names → x ∈ Δ'.names
  | nil, nil => λh => by cases h
  | cons _ w, cons _ w' => λh => by
    simp only [names, List.map_cons, List.mem_cons, List.map] at *
    match h with
    | Or.inl h => exact Or.inl h
    | Or.inr h => exact Or.inr (mem_right_of_mem_meet w w' h)
  | cons _ w, skip _ w' => mem_right_of_mem_meet w w'
  | skip _ w, cons _ w' => λh => List.mem_cons_of_mem _ (mem_right_of_mem_meet w w' h)
  | skip _ w, skip _ w' => mem_right_of_mem_meet w w'

theorem Ctx.Fresh.meet_left {ν α} {Γ Δ Δ' : Ctx ν α} {x : ν} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : Δ.Fresh x → (w.meet w').Fresh x
  := λf => of_not_mem_names (λh => f.not_mem_names (w.mem_left_of_mem_meet w' h))

theorem Ctx.Fresh.meet_right {ν α} {Γ Δ Δ' : Ctx ν α} {x : ν} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : Δ'.Fresh x → (w.meet w').Fresh x
  := λf => of_not_mem_names (λh => f.not_mem_names (w.mem_right_of_mem_meet w' h))

def Ctx.Wk.meet_left {ν α} {Γ Δ Δ' : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : Δ.Wk (w.meet w')
  := match w, w' with
  | nil, nil => nil
  | cons _ w, cons _ w' => cons _ (w.meet_left w')
  | cons _ w, skip hx w' => skip (hx.meet_right w w') (w.meet_left w')
  | skip _ w, cons _ w' => w.meet_left w'
  | skip _ w, skip _ w' => w.meet_left w'

def Ctx.Wk.meet_right {ν α} {Γ Δ Δ' : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : Δ'.Wk (w.meet w')
  := match w, w' with
  | nil, nil => nil
  | cons _ w, cons _ w' => cons _ (w.meet_right w')
  | cons _ w, skip _ w' => w.meet_right w'
  | skip hx w, cons _ w' => skip (hx.meet_left w w') (w.meet_right w')
  | skip _ w, skip _ w' => w.meet_right w'

def Ctx.Wk.meet_entry {ν α} {Γ Δ Δ' : Ctx ν α} (w : Γ.Wk Δ) (w' : Γ.Wk Δ')
  : Γ.Wk (w.meet w')
  := w.comp (w.meet_left w')

theorem Ctx.Fresh.var_name_ne {ν α} {x : ν} {Γ : Ctx ν α} {v : Var ν α}
  : Γ.Fresh x → Γ.Wk [v] → v.name ≠ x
  | Fresh.cons hx _, Wk.cons _ _ => hx
  | Fresh.cons _ h, Wk.skip _ w => h.var_name_ne w

def Ctx.Wk.meet_var {ν α} {Γ Δ Δ' : Ctx ν α} {v : Var ν α}
  :  (w : Γ.Wk Δ) → (w' : Γ.Wk Δ') → Δ.Wk [v] → Δ'.Wk [v] → (w.meet w').Wk [v]
  | cons _ _, cons _ w', cons _ _, cons _ _ => cons _ (drop _)
  | cons _ _, cons _ _, cons _ _, skip hx _ => (hx.head rfl).elim
  | cons _ _, cons _ _, skip hx _, cons _ _ => (hx.head rfl).elim
  | cons _ w, cons _ w', skip hx i, skip _ i' => skip hx (w.meet_var w' i i')
  | cons _ _, skip hx w', cons _ _, cons _ _ => (hx.head rfl).elim
  | cons _ _, skip hx _, cons _ _, skip _ i' => (hx.tail.var_name_ne i' rfl).elim
  | cons _ w, skip _ w', skip hx i, i' => w.meet_var w' i i'
  | skip hx _, cons _ w', cons _ _, cons _ _ => (hx.head rfl).elim
  | skip hx _, cons _ _, skip _ i, cons _ _ => (hx.tail.var_name_ne i rfl).elim
  | skip _ w, cons _ w', i, skip _ i' => w.meet_var w' i i'
  | skip _ w, skip _ w', i, i' => w.meet_var w' i i'

-- TODO: might need basepoint... think about this...
--
-- def Ctx.Wk.meet_meet {ν α} {Γ Δ Δ' Ξ : Ctx ν α}
--   : (w : Γ.Wk Δ) → (w' : Γ.Wk Δ') → Δ.Wk Ξ → Δ'.Wk Ξ → (w.meet w').Wk Ξ
--   | nil, nil, nil, nil => nil
--   | cons _ w, cons _ w', cons _ l, cons _ r => cons _ (meet_meet w w' l r)
--   | cons _ w, cons _ w', cons _ l, skip hx r => (hx.head rfl).elim
--   | cons _ w, cons _ w', skip hx l, cons _ r => (hx.head rfl).elim
--   | cons _ w, cons _ w', skip hx l, skip _ r => skip hx (meet_meet w w' l r)
--   | cons _ w, skip hx w', cons _ l, cons _ r => (hx.head rfl).elim
--   | cons v w, skip hx w', cons _ l, skip hx' r => by
--     simp [meet]
--     sorry
--   | cons _ w, skip _ w', skip hx l, r => meet_meet w w' l r
--   | skip _ w, cons _ w', cons _ l, cons _ r => sorry
--   | skip _ w, cons _ w', skip _ l, cons _ r => sorry
--   | skip _ w, cons _ w', l, skip hx r => meet_meet w w' l r
--   | skip _ w, skip _ w', l, r => meet_meet w w' l r

-- TODO: meet_{nil, idem, comm, assoc}

-- TODO: meet iso

-- TODO: unique up to permutations?

def Ctx.inter {ν α} [BEq (Var ν α)] (Γ Δ : Ctx ν α) : Ctx ν α
  := Γ.bagInter Δ

theorem Ctx.inter_nil {ν α} [DecidableEq (Var ν α)] (Γ : Ctx ν α) : Γ.inter [] = []
  := by simp only [Ctx.inter, List.bagInter_nil]

--TODO: meet is inter?

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

theorem Label.Wk.antisymm {ℓ ℓ' : Label ν κ α} (h : ℓ.Wk ℓ') (h' : ℓ'.Wk ℓ) : ℓ = ℓ'
  := by
    cases ℓ; cases ℓ';
    simp only [Label.mk.injEq]
    exact ⟨h.name, h.param, h.live.antisymm h'.live⟩

theorem Label.Wk.allEq {ℓ ℓ' : Label ν κ α} (D D': ℓ.Wk ℓ') : D = D'
  := by cases D; cases D'; simp only [mk.injEq]; apply Ctx.Wk.allEq

def Label.Wk.refl (ℓ : Label ν κ α) : ℓ.Wk ℓ := ⟨rfl, rfl, Ctx.Wk.refl _⟩

def Label.Wk.comp {ℓ ℓ' ℓ'' : Label ν κ α} (w : ℓ.Wk ℓ') (w' : ℓ'.Wk ℓ'') : ℓ.Wk ℓ''
  := ⟨w.name.trans w'.name, w.param.trans w'.param, w.live.comp w'.live⟩

def Label.Wk.Iso {ℓ₁ ℓ₂ : Label ν κ α} {ℓ₁' ℓ₂' : Label ν' κ' α} (w : ℓ₁.Wk ℓ₂) (w' : ℓ₁'.Wk ℓ₂')
  := w.live.Iso w'.live

def Label.Wk.Iso.comp {ℓ₁ ℓ₂ ℓ₃ : Label ν κ α} {ℓ₁' ℓ₂' ℓ₃' : Label ν' κ' α}
  {l : ℓ₁.Wk ℓ₂}
  {r : ℓ₂.Wk ℓ₃}
  {l' : ℓ₁'.Wk ℓ₂'}
  {r' : ℓ₂'.Wk ℓ₃'}
  (hl : l.Iso l') (hr : r.Iso r')
  : (l.comp r).Iso (l'.comp r')
  := Ctx.Wk.Iso.comp hl hr

def Label.FreshVar (ℓ : Label ν κ α) (n : ν) := ℓ.live.Fresh n

theorem Label.FreshVar.wk {ℓ ℓ' : Label ν κ α} {l : ν}
  (h : ℓ.FreshVar l) (w : ℓ.Wk ℓ') : ℓ'.FreshVar l
  := Ctx.Fresh.wk h w.live

def Label.Fresh (ℓ : Label ν κ α) (l : κ) := ℓ.name ≠ l

theorem Label.Fresh.wk_exit {ℓ ℓ' : Label ν κ α} {l : κ}
  (h : ℓ.Fresh l) (w : ℓ.Wk ℓ') : ℓ'.Fresh l
  := by simp only [<-w.name, Fresh]; exact h

theorem Label.Fresh.rwk_exit {ℓ ℓ' : Label ν κ α} {l : κ}
  (h : ℓ.Fresh l) (w : ℓ'.Wk ℓ) : ℓ'.Fresh l
  := by simp only [w.name, Fresh]; exact h

theorem Label.Fresh.wk_entry {ℓ ℓ' : Label ν κ α} {l : κ}
  (w : ℓ.Wk ℓ') (h : ℓ'.Fresh l) : ℓ.Fresh l
  := by simp only [w.name, Fresh]; exact h

def LCtx (ν κ α) := List (Label ν κ α)

def LCtx.labels {ν κ α} (L : LCtx ν κ α): List κ
  := L.map Label.name

inductive LCtx.FreshVar {ν κ α} (n : ν) : LCtx ν κ α → Prop
  | nil : LCtx.FreshVar n []
  | cons : ℓ.FreshVar n → FreshVar n L → FreshVar n (ℓ::L)

theorem LCtx.FreshVar.head {ν α} {n} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : FreshVar n (ℓ::L) → ℓ.FreshVar n
  | cons hxn _ => hxn

theorem LCtx.FreshVar.tail {ν α} {n} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : FreshVar n (ℓ::L) → L.FreshVar n
  | cons _ h => h

inductive LCtx.Fresh {ν κ α} (l : κ) : LCtx ν κ α → Prop
  | nil : LCtx.Fresh l []
  | cons : ℓ.Fresh l → Fresh l L → Fresh l (ℓ::L)

theorem LCtx.Fresh.head {ν κ α} {l : κ} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : Fresh l (ℓ::L) → ℓ.Fresh l
  | cons hxn _ => hxn

theorem LCtx.Fresh.tail {ν κ α} {l : κ} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : Fresh l (ℓ::L) → L.Fresh l
  | cons _ h => h

theorem LCtx.Fresh.not_mem {ν κ α} {l : κ} {L : LCtx ν κ α}
  (h : L.Fresh l) : l ∉ L.labels := by induction h with
  | nil => exact List.not_mem_nil _
  | cons hℓ _ I =>
    apply List.not_mem_cons_of_ne_of_not_mem
    exact hℓ.symm
    apply I

theorem LCtx.Fresh.of_not_mem {ν κ α} {l : κ} {L : LCtx ν κ α}
  (h : l ∉ L.labels) : L.Fresh l
  := by induction L with
  | nil => exact Fresh.nil
  | cons ℓ L I =>
    apply Fresh.cons
    apply Ne.symm
    apply List.ne_of_not_mem_cons
    exact h
    apply I
    apply List.not_mem_of_not_mem_cons
    exact h

theorem LCtx.Fresh.not_mem_iff {ν κ α} {l : κ} {L : LCtx ν κ α}
  : L.Fresh l ↔ l ∉ L.labels
  := ⟨LCtx.Fresh.not_mem, LCtx.Fresh.of_not_mem⟩

inductive LCtx.Wk {ν κ α} : LCtx ν κ α → LCtx ν κ α → Type _
  | nil : Wk [] []
  | cons {ℓ ℓ' : Label ν κ α} : ℓ.Wk ℓ' → Wk L K → Wk (ℓ::L) (ℓ'::K)
  | skip {ℓ : Label ν κ α} : L.Fresh ℓ.name → Wk L K → Wk L (ℓ::K)

def LCtx.Wk.refl {ν κ α} : (L : LCtx ν κ α) → L.Wk L
  | [] => nil
  | ℓ::L => cons (Label.Wk.refl ℓ) (refl L)

theorem LCtx.Fresh.wk {ν κ α} {L K: LCtx ν κ α} {l: κ}
  (w : L.Wk K) (h : K.Fresh l) : L.Fresh l
  := by induction w with
  | nil => exact h
  | cons h _ I =>
    cases h;
    constructor
    apply Label.Fresh.wk_entry
    assumption
    assumption
    apply I
    assumption
  | skip _ _ I =>
    apply I
    cases h
    assumption

theorem LCtx.Wk.antisymm {ν κ α} {L K : LCtx ν κ α} (h : L.Wk K) (h' : K.Wk L)
  : L = K
  := by induction h with
  | nil => cases h'; rfl
  | cons hℓ _ I =>
    cases h' with
    | cons hℓ' h' =>
      congr
      apply Label.Wk.antisymm <;> assumption
      exact I h'
    | skip h' => exact (h'.head hℓ.name.symm).elim
  | skip h => exact ((h.wk h').head rfl).elim

theorem LCtx.Wk.allEq {ν κ α} {L K : LCtx ν κ α} (D D': L.Wk K): D = D'
  := by induction D with
  | nil => cases D'; rfl
  | cons hℓ _ I => cases D' with
    | cons =>
      congr
      apply Label.Wk.allEq
      exact I _
    | skip h => exact (h.head hℓ.name).elim
  | skip h _ I => cases D' with
    | cons hℓ _ => exact (h.head hℓ.name).elim
    | skip h' => congr; exact I _

theorem LCtx.Wk.not_mem {ν κ α} {ℓ : Label ν κ α} {L K : LCtx ν κ α}
  (w : L.Wk K) (h : ℓ.name ∉ K.labels) : ℓ.name ∉ L.labels := by induction w with
  | nil => exact h
  | cons hℓ _ I =>
    apply List.not_mem_cons_of_ne_of_not_mem
    apply List.ne_of_not_mem_cons
    rw [hℓ.name]
    exact h
    apply I
    apply List.not_mem_of_not_mem_cons
    exact h
  | skip _ _ I =>
    apply I
    apply List.not_mem_of_not_mem_cons
    exact h

def LCtx.Wk.comp {L K M : LCtx ν κ α} : L.Wk K → K.Wk M → L.Wk M
  | Wk.nil, w => w
  | Wk.cons h w, Wk.cons h' w' => Wk.cons (h.comp h') (w.comp w')
  | Wk.skip hℓ w, Wk.cons hℓw w' => Wk.skip (hℓw.name ▸ hℓ) (w.comp w')
  | w, Wk.skip hℓ w' => Wk.skip (hℓ.wk w) (w.comp w')

def Ctx.Wk.to_lctx {ν α κ} {Γ Δ : Ctx ν α} (ℓ: κ) (A: α) (w: Γ.Wk Δ)
  : LCtx.Wk [⟨ℓ, A, Γ⟩] [⟨ℓ, A, Δ⟩]
  := LCtx.Wk.cons ⟨rfl, rfl, w⟩ LCtx.Wk.nil

inductive LCtx.Wk.Iso : {L K : LCtx ν κ α} → {L' K' : LCtx ν' κ' α'} → Wk L K → Wk L' K' → Prop
  | nil : Iso nil nil
  | cons : h.Iso h' → Iso w w' → Iso (cons h w) (cons h' w')
  | skip : Iso w w' → Iso (skip hℓ w) (skip hℓ' w')

theorem LCtx.Wk.Iso.refl {L K : LCtx ν κ α} : (w: L.Wk K) → w.Iso w
  | Wk.nil => nil
  | Wk.cons h w => cons h.live.iso_refl (refl w)
  | Wk.skip h w => skip (refl w)

theorem LCtx.Wk.Iso.symm {L K : LCtx ν κ α} {L' K' : LCtx ν' κ' α'}
  {w: L.Wk K} {w': L'.Wk K'} : (h: w.Iso w') → w'.Iso w
  | nil => nil
  | cons h w => cons h.symm w.symm
  | skip w => skip w.symm

theorem LCtx.Wk.Iso.trans {L K : LCtx ν κ α} {L' K' : LCtx ν' κ' α'} {L'' K'' : LCtx ν'' κ'' α''}
  {w: L.Wk K} {w': L'.Wk K'} {w'': L''.Wk K''} : (h: w.Iso w') → (h': w'.Iso w'') → w.Iso w''
  | nil, nil => nil
  | cons h w, cons h' w' => cons (h.trans h') (w.trans w')
  | skip w, skip w' => skip (w.trans w')

theorem LCtx.Wk.Iso.comp {L K M : LCtx ν κ α} {L' K' M' : LCtx ν' κ' α'}
  {l: L.Wk K} {r: K.Wk M} {l': L'.Wk K'} {r': K'.Wk M'}
  (hl: l.Iso l') (hr: r.Iso r'): (l.comp r).Iso (l'.comp r') := by
    induction hr generalizing L <;>
    cases hl <;>
    constructor
    --TODO: probably go clean up or smt
    apply Label.Wk.Iso.comp <;> assumption
    apply_assumption
    assumption
    case cons.skip I _ _ _ _ h =>
      apply_assumption
      assumption
    case skip.cons I =>
      apply_assumption
      constructor <;> assumption
    case skip.skip I =>
      apply_assumption
      constructor
      assumption
    assumption

def Label.Wk.join {ℓ ℓ₁ ℓ₂ : Label ν κ α} (w : ℓ.Wk ℓ₁) (w' : ℓ.Wk ℓ₂) : Label ν κ α where
  name := ℓ.name
  param := ℓ.param
  live := w.live.join w'.live

def Label.Wk.src {ℓ ℓ' : Label ν κ α} (_ : ℓ.Wk ℓ') : Label ν κ α := ℓ
def Label.Wk.trg {ℓ ℓ' : Label ν κ α} (_ : ℓ.Wk ℓ') : Label ν κ α := ℓ'

def LCtx.Wk.shared_entry {L K M : LCtx ν κ α} : L.Wk M → K.Wk M → LCtx ν κ α
  | Wk.nil, _ => []
  | Wk.cons h w, Wk.cons _ w' => h.trg::(shared_entry w w')
  | Wk.skip _ w, Wk.cons h w' => h.trg::(shared_entry w w')
  | Wk.cons h w, Wk.skip _ w' => h.trg::(shared_entry w w')
  | Wk.skip _ w, Wk.skip _ w' => shared_entry w w'

def LCtx.Wk.shared_entry_left {L K M : LCtx ν κ α}
  : (w : L.Wk M) → (w' : K.Wk M) → L.Wk (w.shared_entry w')
  | nil, nil => nil
  | cons h w, cons h' w' => cons h (shared_entry_left w w')
  | skip h w, cons h' w' => skip h (shared_entry_left w w')
  | cons h w, skip _ w' => cons h (shared_entry_left w w')
  | skip _ w, skip _ w' => shared_entry_left w w'

def LCtx.Wk.shared_entry_right {L K M : LCtx ν κ α}
  : (w : L.Wk M) → (w' : K.Wk M) → K.Wk (w.shared_entry w')
  | nil, nil => nil
  | cons _ w, cons h' w' => cons h' (shared_entry_right w w')
  | skip _ w, cons h' w' => cons h' (shared_entry_right w w')
  | cons _ w, skip h' w' => skip h' (shared_entry_right w w')
  | skip _ w, skip _ w' => shared_entry_right w w'

theorem LCtx.Wk.mem_labels_shared_entry_of_mem_labels_left {L K M : LCtx ν κ α}
  (w : L.Wk M) (w' : K.Wk M) (hℓm : ℓ ∈ L.labels)
  : ℓ ∈ (w.shared_entry w').labels
  := match w, w' with
  | nil, nil => by simp [labels] at hℓm
  | cons hℓ w, cons hℓ' w' => by cases hℓm with
    | head =>
      simp only [labels, shared_entry, List.map, Label.Wk.trg]
      rw [hℓ.name]
      exact List.Mem.head _
    | tail _ hℓm =>
      exact List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_left w w' hℓm)
  | skip _ w, cons _ w' =>
    List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_left w w' hℓm)
  | cons hℓ w, skip _ w' => by cases hℓm with
    | head =>
      simp only [labels, shared_entry, List.map, Label.Wk.trg]
      rw [hℓ.name]
      exact List.Mem.head _
    | tail _ hℓm =>
      exact List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_left w w' hℓm)
  | skip _ w, skip _ w' => mem_labels_shared_entry_of_mem_labels_left w w' hℓm

theorem LCtx.Wk.mem_labels_shared_entry_of_mem_labels_right {L K M : LCtx ν κ α}
  (w : L.Wk M) (w' : K.Wk M) (hℓm : ℓ ∈ K.labels)
  : ℓ ∈ (w.shared_entry w').labels
  := match w, w' with
  | nil, nil => by simp [labels] at hℓm
  | cons _ w, cons hℓ' w' => by cases hℓm with
    | head =>
      simp only [labels, shared_entry, List.map, Label.Wk.trg]
      rw [hℓ'.name]
      exact List.Mem.head _
    | tail _ hℓm =>
      exact List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_right w w' hℓm)
  | skip _ w, cons hℓ' w' => by cases hℓm with
    | head =>
      simp only [labels, shared_entry, List.map, Label.Wk.trg]
      rw [hℓ'.name]
      exact List.Mem.head _
    | tail _ hℓm =>
      exact List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_right w w' hℓm)
  | cons _ w, skip hℓ' w' =>
    List.mem_cons_of_mem _ (mem_labels_shared_entry_of_mem_labels_right w w' hℓm)
  | skip _ w, skip _ w' => mem_labels_shared_entry_of_mem_labels_right w w' hℓm

def LCtx.Wk.mem_shared_entry_labels_left_or_right {L K M : LCtx ν κ α}
  (w : L.Wk M) (w' : K.Wk M) (hℓm : ℓ ∈ (w.shared_entry w').labels)
  : ℓ ∈ L.labels ∨ ℓ ∈ K.labels
  := match w, w' with
  | nil, nil => by simp [labels, shared_entry] at hℓm
  | cons hℓ w, cons hℓ' w' => by
    cases hℓm with
    | head => left; rw [labels, List.map, hℓ.name]; exact List.Mem.head _
    | tail _ hℓm => cases mem_shared_entry_labels_left_or_right w w' hℓm with
      | inl hℓm => left; exact List.mem_cons_of_mem _ hℓm
      | inr hℓm => right; exact List.mem_cons_of_mem _ hℓm
  | skip _ w, cons hℓ' w' => by
    cases hℓm with
    | head => right; rw [labels, List.map, hℓ'.name]; exact List.Mem.head _
    | tail _ hℓm => cases mem_shared_entry_labels_left_or_right w w' hℓm with
      | inl hℓm => left; exact hℓm
      | inr hℓm => right; exact List.mem_cons_of_mem _ hℓm
  | cons hℓ w, skip hℓ' w' => by
    cases hℓm with
    | head => left; rw [labels, List.map, hℓ.name]; exact List.Mem.head _
    | tail _ hℓm => cases mem_shared_entry_labels_left_or_right w w' hℓm with
      | inl hℓm => left; exact List.mem_cons_of_mem _ hℓm
      | inr hℓm => right; exact hℓm
  | skip _ w, skip _ w' => mem_shared_entry_labels_left_or_right w w' hℓm

def LCtx.Wk.shared_entry_exit {L K M : LCtx ν κ α}
  : (w : L.Wk M) → (w' : K.Wk M) → (w.shared_entry w').Wk M
  | nil, nil => nil
  | cons h w, cons h' w' => cons (Label.Wk.refl _) (shared_entry_exit w w')
  | skip _ w, cons h' w' => cons (Label.Wk.refl _) (shared_entry_exit w w')
  | cons h w, skip h' w' => cons (Label.Wk.refl _) (shared_entry_exit w w')
  | skip h w, skip h' w' => skip (by
    apply Fresh.of_not_mem
    intro hℓ
    cases mem_shared_entry_labels_left_or_right w w' hℓ with
    | inl hℓ => exact h.not_mem hℓ
    | inr hℓ => exact h'.not_mem hℓ
  ) (shared_entry_exit w w')

--TODO: LCtx shared properties (e.g. comm...), isos

inductive LCtx.PWk {ν κ α} : LCtx ν κ α → LCtx ν κ α → Type _
  | nil : PWk [] []
  | cons {ℓ ℓ' : Label ν κ α} : ℓ.Wk ℓ' → PWk L K → PWk (ℓ::L) (ℓ'::K)

theorem LCtx.PWk.allEq {ν κ α} {L K : LCtx ν κ α} (D D': L.PWk K): D = D'
  := by induction D with
  | nil => cases D'; rfl
  | cons h _ I => cases D' with
    | cons =>
      congr
      apply Label.Wk.allEq
      exact I _

theorem LCtx.PWk.comp {L K M : LCtx ν κ α} : L.PWk K → K.PWk M → L.PWk M
  | nil, w => w
  | cons h w, PWk.cons h' w' => PWk.cons (h.comp h') (w.comp w')

theorem LCtx.PWk.refl : (L : LCtx ν κ α) → L.PWk L
  | [] => nil
  | ℓ::L => cons (Label.Wk.refl ℓ) (refl L)

def LCtx.PWk.toWk {ν κ α} {L K : LCtx ν κ α} : L.PWk K → L.Wk K
  | PWk.nil => Wk.nil
  | PWk.cons h w => Wk.cons h (toWk w)

theorem LCtx.PWk.labels {ν κ α} {L K : LCtx ν κ α} (w : L.PWk K) : L.labels = K.labels
  := by induction w with
  | nil => rfl
  | cons h w I =>
    simp only [LCtx.labels, List.map]
    rw [h.name]
    congr 1

theorem LCtx.Fresh.pwk {ν κ α} {L K : LCtx ν κ α} {l : κ}
  (w : L.PWk K) : K.Fresh l → L.Fresh l
  := by
    rw [not_mem_iff, not_mem_iff, w.labels]
    exact λx => x

theorem LCtx.Fresh.pwk_r {ν κ α} {L K : LCtx ν κ α} {l : κ}
  (w : L.PWk K) : L.Fresh l → K.Fresh l
  := by
    rw [not_mem_iff, not_mem_iff, w.labels]
    exact λx => x

inductive Ctx.LWk {ν κ α} : Ctx ν α → LCtx ν κ α → Type _
  | nil Γ : LWk Γ []
  | cons : Γ.Wk ℓ.live → LWk Γ L → LWk Γ (ℓ::L)

theorem Ctx.LWk.allEq {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (w w' : Γ.LWk L)
  : w = w'
  := by induction w with
  | nil => cases w'; rfl
  | cons h _ I => cases w' with
    | cons =>
      congr
      apply Ctx.Wk.allEq
      exact I _

theorem Ctx.LWk.wk_entry {ν κ α} {Γ Δ : Ctx ν α} {L : LCtx ν κ α} (w : Γ.Wk Δ)
  : Δ.LWk L → Γ.LWk L
  | nil _ => nil Γ
  | cons w' lw => cons (w.comp w') (lw.wk_entry w)

theorem Ctx.LWk.wk_exit {ν κ α} {Γ : Ctx ν α} {L K : LCtx ν κ α}
  : Γ.LWk L → L.PWk K → Γ.LWk K
  | nil _, LCtx.PWk.nil => nil _
  | cons w lw, LCtx.PWk.cons w' pw => cons (w.comp w'.live) (lw.wk_exit pw)

inductive Ctx.RWk {ν κ α} : Ctx ν α → LCtx ν κ α → Type _
  | nil Γ : RWk Γ []
  | cons : ℓ.live.Wk Γ → RWk Γ L → RWk Γ (ℓ::L)

theorem Ctx.RWk.allEq {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (w w' : Γ.RWk L)
  : w = w'
  := by induction w with
  | nil => cases w'; rfl
  | cons h _ I => cases w' with
    | cons =>
      congr
      apply Ctx.Wk.allEq
      exact I _

theorem Ctx.RWk.wk_entry {ν κ α} {Γ Δ : Ctx ν α} {L : LCtx ν κ α} (w : Γ.Wk Δ)
  : Γ.RWk L → Δ.RWk L
  | nil _ => nil Δ
  | cons w' lw => cons (w'.comp w) (lw.wk_entry w)

theorem Ctx.RWk.wk_exit {ν κ α} {Γ : Ctx ν α} {L K : LCtx ν κ α}
  : Γ.RWk L → K.PWk L → Γ.RWk K
  | nil _, LCtx.PWk.nil => nil _
  | cons w lw, LCtx.PWk.cons w' pw => cons (w'.live.comp w) (lw.wk_exit pw)

inductive Ctx.LEq {ν κ α} : Ctx ν α → LCtx ν κ α → Prop
  | nil Γ : LEq Γ []
  | cons : Γ = ℓ.live → LEq Γ L → LEq Γ (ℓ::L)

theorem Ctx.LEq.head {ν κ α} {Γ : Ctx ν α} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : Γ.LEq (ℓ::L) → Γ = ℓ.live
  | cons h _ => h

theorem Ctx.LEq.tail {ν κ α} {Γ : Ctx ν α} {ℓ : Label ν κ α} {L : LCtx ν κ α}
  : Γ.LEq (ℓ::L) → Γ.LEq L
  | cons _ h => h

def Ctx.LEq.toLWk {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (h : Γ.LEq L) : Γ.LWk L
  := match L with
  | [] => LWk.nil Γ
  | _::_ => LWk.cons (h.head ▸ Wk.refl _) (toLWk h.tail)

def Ctx.LEq.toRWk {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (h : Γ.LEq L) : Γ.RWk L
  := match L with
  | [] => Ctx.RWk.nil Γ
  | _::_ => RWk.cons (h.head ▸ Wk.refl _) (toRWk h.tail)

theorem Ctx.LEq.head₂ {ν κ α} {Γ : Ctx ν α} {ℓ₁ ℓ₂ : Label ν κ α} {L K : LCtx ν κ α}
  : Γ.LEq (ℓ₁::L) → Γ.LEq (ℓ₂::K) → ℓ₁.name = ℓ₂.name → ℓ₁.param = ℓ₂.param → ℓ₁ = ℓ₂
  | cons h₁ _, cons h₂ _, hn, hp => by
    cases ℓ₁
    cases ℓ₂
    cases hn
    cases hp
    cases h₁
    cases h₂
    rfl

theorem Ctx.LWk.antisymm {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (h : Γ.LWk L) (h' : Γ.RWk L)
  : Γ.LEq L
  := by induction h with
  | nil => cases h'; constructor
  | cons h _ I => cases h' with
    | cons =>
      constructor
      apply Ctx.Wk.antisymm <;> assumption
      exact I (by assumption)

theorem Ctx.RWk.antisymm {ν κ α} {Γ : Ctx ν α} {L : LCtx ν κ α} (h : Γ.RWk L) (h' : Γ.LWk L)
  : Γ.LEq L
  := h'.antisymm h

inductive LCtx.SJoin {ν κ α}
  : LCtx ν κ α → LCtx ν κ α → LCtx ν κ α → Type _
  | nil : SJoin [] [] []
  | left : K.Fresh ℓ.name → SJoin L K M → SJoin (ℓ::L) K (ℓ::M)
  | right : L.Fresh ℓ.name → SJoin L K M → SJoin L (ℓ::K) (ℓ::M)
  | both ℓ : SJoin L K M → SJoin (ℓ::L) (ℓ::K) (ℓ::M)

def LCtx.SJoin.comm {ν κ α} {L K M : LCtx ν κ α}
  : L.SJoin K M → K.SJoin L M
  | SJoin.nil => SJoin.nil
  | SJoin.left h j => SJoin.right h j.comm
  | SJoin.right h j => SJoin.left h j.comm
  | SJoin.both _ j => SJoin.both _ j.comm

def LCtx.SJoin.left_wk {ν κ α} {L K M : LCtx ν κ α}
  : L.SJoin K M → L.Wk M
  | SJoin.nil => Wk.nil
  | SJoin.left _ j => Wk.cons (Label.Wk.refl _) (left_wk j)
  | SJoin.right h j => Wk.skip h (left_wk j)
  | SJoin.both _ j => Wk.cons (Label.Wk.refl _) (left_wk j)

def LCtx.SJoin.right_wk {ν κ α} {L K M : LCtx ν κ α}
  : L.SJoin K M → K.Wk M
  | SJoin.nil => Wk.nil
  | SJoin.left h j => Wk.skip h (right_wk j)
  | SJoin.right _ j => Wk.cons (Label.Wk.refl _) (right_wk j)
  | SJoin.both _ j => Wk.cons (Label.Wk.refl _) (right_wk j)

theorem LCtx.SJoin.allEq {ν κ α} {L K M : LCtx ν κ α} (j j': L.SJoin K M): j = j'
  := by induction j with
  | nil => cases j'; rfl
  | left h j I =>
    cases j' with
    | left h' j' => congr; apply I
    | right h' j' => exact (h'.head rfl).elim
    | both _ j' => exact (h.head rfl).elim
  | right h j I =>
    cases j' with
    | left h' j' => exact (h'.head rfl).elim
    | right h' j' => congr; apply I
    | both _ j' => exact (h.head rfl).elim
  | both _ j I =>
    cases j' with
    | left h' j' => exact (h'.head rfl).elim
    | right h' j' => exact (h'.head rfl).elim
    | both _ j' => congr; apply I

theorem LCtx.SJoin.lEq {ν κ α} {Γ : Ctx ν α} {L K M : LCtx ν κ α}
  (j : L.SJoin K M)
  : Γ.LEq L → Γ.LEq K → Γ.LEq M
  := match j with
  | nil => λ_ h' => h'
  | left hl j => λh h' => Ctx.LEq.cons h.head (j.lEq h.tail h')
  | right hl j => λh h' => Ctx.LEq.cons h'.head (j.lEq h h'.tail)
  | both _ j => λh h' => Ctx.LEq.cons h.head (j.lEq h.tail h'.tail)

structure LCtx.Comp {ν κ α} (L K : LCtx ν κ α) where
  base : LCtx ν κ α
  left : L.Wk base
  right : K.Wk base

def LCtx.Wk.uncons₂ {ν κ α}
  {ℓ : Label ν κ α} {L K Ω : LCtx ν κ α}
  : Wk (ℓ::L) Ω → Wk (ℓ::K) Ω → L.Comp K
  | cons _ w, cons _ w' => ⟨_, w, w'⟩
  | skip h w, cons h' w' => by
    rw [Fresh.not_mem_iff, <-h'.name] at h
    simp [labels] at h
  | cons h _, skip h' w' => by
    rw [Fresh.not_mem_iff, <-h.name] at h'
    simp [labels] at h'
  | skip _ w, skip _ w' => uncons₂ w w'

def LCtx.Comp.uncons {ν κ α} {ℓ : Label ν κ α} {L K : LCtx ν κ α}
  (c : Comp (ℓ::L) (ℓ::K)) : Comp L K
  := c.left.uncons₂ c.right

theorem LCtx.Comp.head {ν κ α} {ℓ ℓ' : Label ν κ α} {L K : LCtx ν κ α}
  : Comp (ℓ::L) (ℓ'::K) → ℓ.name = ℓ'.name ∨ L.Fresh ℓ'.name ∨ K.Fresh ℓ.name
  | ⟨_, Wk.cons lw _, Wk.cons lw' _⟩ => Or.inl (lw.name.trans lw'.name.symm)
  | ⟨_, Wk.skip h _, Wk.cons lw' _⟩ => Or.inr (Or.inl (lw'.name ▸ h.tail))
  | ⟨_, Wk.cons lw _, Wk.skip h' _⟩ => Or.inr (Or.inr (lw.name ▸ h'.tail))
  | ⟨_, Wk.skip _ w, Wk.skip _ w'⟩ => head ⟨_, w, w'⟩

theorem LCtx.SJoin.trgEq {ν κ α} {L K M M' : LCtx ν κ α}
  (j : L.SJoin K M) (j' : L.SJoin K M') (oM : M.Comp M') : M = M' := by
  induction j generalizing M' with
  | nil => cases j'; rfl
  | left h j I =>
    cases j' with
    | left h' j' => rw [I j' oM.uncons]
    | right h' j' => match oM.head with
      | Or.inl hn => exact (h'.head hn).elim
      | Or.inr (Or.inl hn) => exact ((hn.wk j.right_wk).head rfl).elim
      | Or.inr (Or.inr hn) => exact ((hn.wk j'.left_wk).head rfl).elim
    | both _ j' => exact (h.head rfl).elim
  | right h j I =>
    cases j' with
    | left h' j' => match oM.head with
      | Or.inl hn => exact (h'.head hn).elim
      | Or.inr (Or.inl hn) => exact ((hn.wk j.left_wk).head rfl).elim
      | Or.inr (Or.inr hn) => exact ((hn.wk j'.right_wk).head rfl).elim
    | right h' j' => rw [I j' oM.uncons]
    | both _ j' => exact (h.head rfl).elim
  | both _ _ I =>
    cases j' with
    | left h' j' => exact (h'.head rfl).elim
    | right h' j' => exact (h'.head rfl).elim
    | both _ j' => rw [I j' oM.uncons]

inductive LCtx.Join {ν κ α}
  : LCtx ν κ α → LCtx ν κ α → LCtx ν κ α → Type _
  | nil : Join [] [] []
  | left : ℓ.Wk ℓ' → K.Fresh ℓ.name → Join L K M → Join (ℓ::L) K (ℓ'::M)
  | right : L.Fresh ℓ.name → ℓ.Wk ℓ' → Join L K M → Join L (ℓ::K) (ℓ'::M)
  | both : ℓ₁.Wk ℓ → ℓ₂.Wk ℓ → Join L K M → Join (ℓ₁::L) (ℓ₂::K) (ℓ::M)

def LCtx.Join.wk_exit {ν κ α} {L K M N : LCtx ν κ α}
  : L.Join K M → M.PWk N → L.Join K N
  | Join.nil, PWk.nil => Join.nil
  | Join.left w h lw, PWk.cons w' pw'
    => Join.left (w.comp w') h (wk_exit lw pw')
  | Join.right h w lw, PWk.cons w' pw'
    => Join.right h (w.comp w') (wk_exit lw pw')
  | Join.both w₁ w₂ lw, PWk.cons w' pw'
    => Join.both (w₁.comp w') (w₂.comp w') (wk_exit lw pw')

def LCtx.Join.wk_left {ν κ α} {L' L K M : LCtx ν κ α}
  : L'.PWk L → L.Join K M → L'.Join K M
  | PWk.nil, Join.nil => Join.nil
  | PWk.cons w pw, Join.left w' h lw => Join.left (w.comp w') (w.name ▸ h) (wk_left pw lw)
  | pw, Join.right h w' lw => Join.right (h.pwk pw) w' (wk_left pw lw)
  | PWk.cons w pw, Join.both w₁ w₂ lw => Join.both (w.comp w₁) w₂ (wk_left pw lw)

def LCtx.Join.wk_right {ν κ α} {K' K L M : LCtx ν κ α}
  : K'.PWk K → L.Join K M → L.Join K' M
  | PWk.nil, Join.nil => Join.nil
  | pw, Join.left w' h lw => Join.left w' (h.pwk pw) (wk_right pw lw)
  | PWk.cons w pw, Join.right h w' lw => Join.right (w.name ▸ h) (w.comp w') (wk_right pw lw)
  | PWk.cons w pw, Join.both w₁ w₂ lw => Join.both w₁ (w.comp w₂) (wk_right pw lw)

def LCtx.Join.comm {ν κ α} {L K M : LCtx ν κ α}
  : L.Join K M → K.Join L M
  | Join.nil => Join.nil
  | Join.left w h lw => Join.right h w lw.comm
  | Join.right h w lw => Join.left w h lw.comm
  | Join.both w₁ w₂ lw => Join.both w₂ w₁ lw.comm

def LCtx.SJoin.toJoin {ν κ α} {L K M : LCtx ν κ α}
  : L.SJoin K M → L.Join K M
  | SJoin.nil => Join.nil
  | SJoin.left h j => Join.left (Label.Wk.refl _) h (toJoin j)
  | SJoin.right h j => Join.right h (Label.Wk.refl _) (toJoin j)
  | SJoin.both _ j => Join.both (Label.Wk.refl _) (Label.Wk.refl _) (toJoin j)

structure LCtx.Join' {ν κ α} (L K M : LCtx ν κ α) where
  left : LCtx ν κ α
  right : LCtx ν κ α
  lPwk : L.PWk left
  rPwk : K.PWk right
  sJoin : left.SJoin right M

--TODO: try hand at uniqueness resuls
--TODO: assoc and friends

def LCtx.Join.factor {ν κ α} {L K M : LCtx ν κ α}
  : L.Join K M → L.Join' K M
  | Join.nil => ⟨[], [], PWk.nil, PWk.nil, SJoin.nil⟩
  | Join.left w h lw => match factor lw with
    | ⟨L', K', pw, pk, j⟩
      => ⟨_::L', K', PWk.cons w pw, pk, SJoin.left (w.name ▸ h.pwk_r pk) j⟩
  | Join.right h w lw => match factor lw with
    | ⟨L', K', pw, pk, j⟩
      => ⟨L', _::K', pw, PWk.cons w pk, SJoin.right (w.name ▸ h.pwk_r pw) j⟩
  | Join.both w₁ w₂ lw => match factor lw with
    | ⟨L', K', pw, pk, j⟩ => ⟨_::L', _::K', PWk.cons w₁ pw, PWk.cons w₂ pk, SJoin.both _ j⟩

def LCtx.Join.lEqFactor {ν κ α} {Γ : Ctx ν α} {L K M : LCtx ν κ α}
  (j : L.Join K M) : Γ.LEq L → Γ.LEq K → (M' : LCtx ν κ α) × L.SJoin K M' × M'.Wk M
  := match j with
  | Join.nil => λ_ _ => ⟨[], SJoin.nil, Wk.nil⟩
  | Join.left w h lw => λhl hr =>
    let lw' := lw.lEqFactor hl.tail hr;
    ⟨_, lw'.2.1.left h, lw'.2.2.cons w⟩
  | Join.right h w lw => λhl hr =>
    let lw' := lw.lEqFactor hl hr.tail;
    ⟨_, lw'.2.1.right h, lw'.2.2.cons w⟩
  | Join.both w₁ w₂ lw => λhl hr =>
    let lw' := lw.lEqFactor hl.tail hr.tail;
    ⟨_,
      hl.head₂ hr (w₁.name.trans w₂.name.symm) (w₁.param.trans w₂.param.symm) ▸ lw'.2.1.both _,
      lw'.2.2.cons w₁⟩

theorem LCtx.Fresh.join_left {ν κ α} {L K M : LCtx ν κ α} {l : κ}
  : L.Join K M → M.Fresh l → L.Fresh l
  | Join.nil, h => h
  | Join.left w _ j, cons hh hl => cons (hh.rwk_exit w) (join_left j hl)
  | Join.right _ _ j, cons _ hl => join_left j hl
  | Join.both w₁ _ j, cons hh hl => cons (hh.rwk_exit w₁) (join_left j hl)

theorem LCtx.Fresh.join_right {ν κ α} {L K M : LCtx ν κ α} {l : κ}
  : L.Join K M → M.Fresh l → K.Fresh l
  | Join.nil, h => h
  | Join.left _ _ j, cons hh hl => join_right j hl
  | Join.right _ w j, cons hh hl => cons (hh.rwk_exit w) (join_right j hl)
  | Join.both _ w₂ j, cons hh hl => cons (hh.rwk_exit w₂) (join_right j hl)

theorem LCtx.Fresh.join {ν κ α} {L K M : LCtx ν κ α} {l : κ}
  : L.Join K M → L.Fresh l → K.Fresh l → M.Fresh l
  | Join.nil, h, _ => h
  | Join.left w _ j, cons hh hl, hk => cons (hh.wk_exit w) (join j hl hk)
  | Join.right _ w j, hl, cons hh hk => cons (hh.wk_exit w) (join j hl hk)
  | Join.both w₁ _ j, cons hh hl, cons hh' hk => cons (hh.wk_exit w₁) (join j hl hk)

--TODO: skipwk, skipjoin, etc...

def LCtx.Join.ofWk {ν κ α} {L K M : LCtx ν κ α}
  : L.Wk M → K.Wk M → (M' : LCtx ν κ α) × L.Join K M' × M'.Wk M
  | Wk.nil, Wk.nil => ⟨[], Join.nil, Wk.nil⟩
  | Wk.cons w lw, Wk.cons w' lw' =>
    let j := ofWk lw lw';
    ⟨_, j.2.1.both w w', j.2.2.cons (Label.Wk.refl _)⟩
  | Wk.skip h lw, Wk.cons w' lw' =>
    let j := ofWk lw lw';
    ⟨_, j.2.1.right (w'.name ▸ h) w', j.2.2.cons (Label.Wk.refl _)⟩
  | Wk.cons w lw, Wk.skip h lw' =>
    let j := ofWk lw lw';
    ⟨_, j.2.1.left w (w.name ▸ h), j.2.2.cons (Label.Wk.refl _)⟩
  | Wk.skip h lw, Wk.skip h' lw' =>
    let j := ofWk lw lw';
    ⟨_, j.2.1, j.2.2.skip (h.join j.2.1 h')⟩

theorem LCtx.Fresh.sJoin {ν κ α} {L K M : LCtx ν κ α} {l : κ}
  : L.SJoin K M → L.Fresh l → K.Fresh l → M.Fresh l
  := λj => join j.toJoin

def LCtx.SJoin.ofWk {ν κ α} {Γ : Ctx ν α} {L K M : LCtx ν κ α}
  (wl : L.Wk M) (wr : K.Wk M) (eql : Γ.LEq L) (eqr : Γ.LEq K)
  : (M' : LCtx ν κ α) × L.SJoin K M' × M'.Wk M
  :=
    let j := Join.ofWk wl wr;
    let j' := j.2.1.lEqFactor eql eqr;
    ⟨j'.1, j'.2.1, j'.2.2.comp j.2.2⟩

def LCtx.Join'.toJoin {ν κ α} {L K M : LCtx ν κ α} (j : L.Join' K M) : L.Join K M
  := (j.sJoin.toJoin.wk_left j.lPwk).wk_right j.rPwk

inductive LCtx.EWk {ν κ α} : LCtx ν κ α → LCtx ν κ α → Type _
  | nil : EWk [] []
  | cons (ℓ) : EWk L K → EWk (ℓ::L) (ℓ::K)
  | skip {ℓ} : L.Fresh ℓ.name → EWk L K → EWk L (ℓ::K)

def LCtx.EWk.toWk {ν κ α} {L K : LCtx ν κ α} : L.EWk K → L.Wk K
  | EWk.nil => Wk.nil
  | EWk.cons _ w => Wk.cons (Label.Wk.refl _) (toWk w)
  | EWk.skip h w => Wk.skip h (toWk w)

def LCtx.EWk.comp {ν κ α} {L K M : LCtx ν κ α} : L.EWk K → K.EWk M → L.EWk M
  | EWk.nil, w => w
  | EWk.cons _ w, EWk.cons _ w' => EWk.cons _ (comp w w')
  | EWk.skip h w, EWk.cons _ w' => EWk.skip h (comp w w')
  | w, EWk.skip h w' => EWk.skip (h.wk w.toWk) (comp w w')

def LCtx.EWk.refl {ν κ α} : (L : LCtx ν κ α) → L.EWk L
  | [] => EWk.nil
  | _::L => EWk.cons _ (refl L)

theorem LCtx.EWk.antisymm {ν κ α} {L K : LCtx ν κ α} (w : L.EWk K) (w' : K.EWk L) : L = K
  := w.toWk.antisymm w'.toWk

theorem LCtx.EWk.allEq {ν κ α} {L K : LCtx ν κ α} : (w w' : L.EWk K) → w = w'
  | EWk.nil, EWk.nil => rfl
  | EWk.cons _ w, EWk.cons _ w' => congrArg _ (allEq w w')
  | EWk.skip _ w, EWk.skip _ w' => congrArg _ (allEq w w')
  | EWk.cons _ _, EWk.skip h _ => (h.head rfl).elim
  | EWk.skip h _, EWk.cons _ _ => (h.head rfl).elim

structure LCtx.Wk' {ν κ α} (L K : LCtx ν κ α) where
  base : LCtx ν κ α
  pWk : L.PWk base
  eWk : base.EWk K

def LCtx.Wk'.toWk {ν κ α} {L K : LCtx ν κ α} (w : L.Wk' K) : L.Wk K
  := w.pWk.toWk.comp w.eWk.toWk

def LCtx.Wk.factor {ν κ α} {L K : LCtx ν κ α} : L.Wk K → L.Wk' K
  | Wk.nil => ⟨[], PWk.nil, EWk.nil⟩
  | Wk.cons w lw =>
    let lw' := factor lw
    ⟨_, lw'.pWk.cons w, lw'.eWk.cons _⟩
  | Wk.skip h lw =>
    let lw' := factor lw
    ⟨_, lw'.pWk, lw'.eWk.skip (h.pwk_r lw'.pWk)⟩

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
