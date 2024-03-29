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
