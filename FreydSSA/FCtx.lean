import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Init.Classical
import Mathlib.Order.SuccPred.Basic

variable {ν ν' α β} [DecidableEq ν] [DecidableEq ν']

structure FCtx (ν : Type u) (α : Type v) : Type (max u v) where
  toFun : ν → WithBot α
  support : Finset ν
  mem_support_toFun : ∀x, x ∈ support ↔ toFun x ≠ ⊥

theorem FCtx.ext {Γ Δ : FCtx ν α} (h : Γ.toFun = Δ.toFun)
  : Γ = Δ
  := match Γ, Δ with
  | ⟨fΓ, n, hm⟩, ⟨fΔ, n', hm'⟩ => by
    cases h
    simp only [mk.injEq, true_and]
    apply Finset.ext
    intro x
    rw [hm, hm']

theorem FCtx.ext_iff {Γ Δ : FCtx ν α}
  : Γ = Δ ↔ Γ.toFun = Δ.toFun
  := ⟨(λh => by cases h; rfl), FCtx.ext⟩

instance FCtx.instFunLike : FunLike (FCtx ν α) ν (WithBot α) where
  coe := FCtx.toFun
  coe_injective' := by intro Γ Δ; apply FCtx.ext

def FCtx.map_ty (Γ : FCtx ν α) (f : α → β) : FCtx ν β where
  toFun x := (Γ.toFun x).map (f)
  support := Γ.support
  mem_support_toFun := by
    intro x
    rw [Γ.mem_support_toFun x]
    simp only []
    generalize Γ.toFun x = a
    cases a <;> simp [WithBot.map, Bot.bot]

def FCtx.cons (x : ν) (a : α) (Γ : FCtx ν α) : FCtx ν α where
  toFun := Function.update Γ.toFun x a
  support := Γ.support ∪ {x}
  mem_support_toFun := by
    intro y
    simp only [Finset.mem_union, Function.update]
    split <;> simp [*, mem_support_toFun]

def FCtx.cons_inj {x : ν} {a a' : α} {Γ : FCtx ν α}
  (h : Γ.cons x a = Γ.cons x a') : a = a' :=
  have hl : Γ.cons x a x = a := by simp [FCtx.cons, DFunLike.coe]
  have hr : Γ.cons x a' x = a' := by simp [FCtx.cons, DFunLike.coe]
  by rw [<-WithBot.coe_inj, <-hl, <-hr, h]

def FCtx.Wk (Γ Δ : FCtx ν α) : Prop := ∀x, Δ.toFun x = ⊥ ∨ Δ.toFun x = Γ.toFun x

theorem FCtx.Wk.refl (Γ : FCtx ν α) : FCtx.Wk Γ Γ := by simp [FCtx.Wk]
theorem FCtx.Wk.trans {Γ Δ Θ : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Δ Θ)
  : FCtx.Wk Γ Θ := by
  intro x
  cases w x <;> cases w' x <;> simp [*]
theorem FCtx.Wk.antisymm {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Δ Γ)
  : Γ = Δ := by
  apply FCtx.ext
  funext x
  cases w x with
  | inl h => cases w' x with | inl h' => rw [h, h'] | inr h' => exact h'
  | inr h => exact h.symm

def FCtx.Wk.src {Γ Δ : FCtx ν α} (_ : FCtx.Wk Γ Δ) : FCtx ν α := Γ
def FCtx.Wk.trg {Γ Δ : FCtx ν α} (_ : FCtx.Wk Γ Δ) : FCtx ν α := Δ

theorem FCtx.Wk.eq_bot {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) (x : ν) (h : Γ.toFun x = ⊥)
  : Δ.toFun x = ⊥ := by cases w x <;> simp [*]
theorem FCtx.Wk.ne_bot {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) (x : ν) (h : Δ.toFun x ≠ ⊥)
  : Γ.toFun x ≠ ⊥ := λh' => h (w.eq_bot _ h')
theorem FCtx.Wk.eq_some_ne_bot {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ)
  (x : ν) (h : Δ.toFun x ≠ ⊥)
  : Γ.toFun x ≠ ⊥ := λh' => h (w.eq_bot _ h')

theorem FCtx.Wk.support_subset {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ)
  : Δ.support ⊆ Γ.support := by
  intro x
  rw [Γ.mem_support_toFun, Δ.mem_support_toFun]
  exact w.ne_bot x

instance FCtx.instPartialOrder : PartialOrder (FCtx ν α) where
  le := FCtx.Wk
  le_refl := FCtx.Wk.refl
  le_trans _ _ _ := FCtx.Wk.trans
  le_antisymm _ _ := FCtx.Wk.antisymm

def FCtx.linf (Δ Δ' : FCtx ν α)
  : FCtx ν α where
  toFun x := match Δ.toFun x, Δ'.toFun x with
    | ⊥, _ | _, ⊥ => ⊥
    | some a, some _ => some a
  support := Δ.support ∩ Δ'.support
  mem_support_toFun := by
    intro x
    simp only [Finset.mem_inter, mem_support_toFun]
    split <;> simp [Bot.bot, *]

def FCtx.rinf (Δ Δ' : FCtx ν α)
  : FCtx ν α where
  toFun x := match Δ.toFun x, Δ'.toFun x with
    | ⊥, _ | _, ⊥ => ⊥
    | some _, some a => some a
  support := Δ.support ∩ Δ'.support
  mem_support_toFun := by
    intro x
    simp only [Finset.mem_inter, mem_support_toFun]
    split <;> simp [Bot.bot, *]

theorem FCtx.Wk.var_eq {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) (x : ν) (a b : α)
  (h : Γ.toFun x = a) (h' : Δ.toFun x = b)
  : a = b := by
  cases w x
  case inl hw => rw [hw] at h'; cases h'
  case inr hw => rw [hw] at h'; rw [h'] at h; cases h; rfl

theorem FCtx.Wk.var {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) (x : ν) (a : α)
  (h : Δ.toFun x = a) : Γ.toFun x = a := by
  cases w x
  case inl hw => rw [hw] at h; cases h
  case inr hw => rw [hw] at h; exact h

def FCtx.Wk.var_eq₂' {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  (x : ν) (a b : α) (h : Δ.toFun x = a) (h' : Δ'.toFun x = b)
  : (a : WithBot α) = (b : WithBot α) := by rw [<-var w x a h, <-var w' x b h']

def FCtx.Wk.var_eq₂ {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  (x : ν) (a b : α) (h : Δ.toFun x = a) (h' : Δ'.toFun x = b)
  : a = b := by cases var_eq₂' w w' x a b h h'; rfl

def FCtx.Wk.linf_eq_rinf {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  : FCtx.linf Δ Δ' = FCtx.rinf Δ Δ' := by
  apply FCtx.ext
  funext x
  simp only [linf, rinf]
  split
  . rfl
  . rfl
  . apply var_eq₂' w w' <;> assumption
