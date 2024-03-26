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

theorem FCtx.toFun_inj_mp {Γ Δ : FCtx ν α} (h : Γ.toFun = Δ.toFun)
  : Γ = Δ
  := match Γ, Δ with
  | ⟨fΓ, n, hm⟩, ⟨fΔ, n', hm'⟩ => by
    cases h
    simp only [mk.injEq, true_and]
    apply Finset.ext
    intro x
    rw [hm, hm']

theorem FCtx.toFun_inj {Γ Δ : FCtx ν α}
  : Γ = Δ ↔ Γ.toFun = Δ.toFun
  := ⟨(λh => by cases h; rfl), FCtx.toFun_inj_mp⟩

--TODO: Injective instance? Naming convention...

instance FCtx.instFunLike : FunLike (FCtx ν α) ν (WithBot α) where
  coe := FCtx.toFun
  coe_injective' := by intro Γ Δ; apply FCtx.toFun_inj_mp

theorem FCtx.ext {Γ Δ : FCtx ν α} (h : ∀x, Γ x = Δ x)
  : Γ = Δ
  := DFunLike.coe_injective' (by funext x; apply h)

theorem FCtx.mem_support {Γ : FCtx ν α} (x : ν)
  : x ∈ Γ.support ↔ Γ x ≠ ⊥ := Γ.mem_support_toFun x

theorem FCtx.mem_support_exists {Γ : FCtx ν α} (x : ν)
  : x ∈ Γ.support ↔ ∃a : α, Γ x = a := by
  rw [mem_support]
  apply Iff.intro
  . cases Γ x with
    | none => intro h; contradiction
    | some a => intro _; exact ⟨a, rfl⟩
  . intro ⟨a, ha⟩
    rw [ha]
    simp

theorem FCtx.mem_support_of_var {Γ : FCtx ν α} (x : ν) (a : α)
  (h : Γ x = a) : x ∈ Γ.support := by
  rw [mem_support]
  intro h'
  rw [h] at h'
  contradiction

theorem FCtx.not_mem_support_of_null {Γ : FCtx ν α} (x : ν)
  (h : Γ x = ⊥) : x ∉ Γ.support := by
  rw [mem_support]
  intro h'
  contradiction

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

def FCtx.Wk (Γ Δ : FCtx ν α) : Prop := ∀x, Δ x = ⊥ ∨ Δ x = Γ x

theorem FCtx.Wk.refl (Γ : FCtx ν α) : FCtx.Wk Γ Γ := by simp [FCtx.Wk]
theorem FCtx.Wk.trans {Γ Δ Θ : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Δ Θ)
  : FCtx.Wk Γ Θ := by
  intro x
  cases w x <;> cases w' x <;> simp [*]
theorem FCtx.Wk.antisymm {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Δ Γ)
  : Γ = Δ := by
  apply FCtx.ext
  intro x
  cases w x with
  | inl h => cases w' x with | inl h' => rw [h, h'] | inr h' => exact h'
  | inr h => exact h.symm

def FCtx.Wk.src {Γ Δ : FCtx ν α} (_ : FCtx.Wk Γ Δ) : FCtx ν α := Γ
def FCtx.Wk.trg {Γ Δ : FCtx ν α} (_ : FCtx.Wk Γ Δ) : FCtx ν α := Δ

theorem FCtx.Wk.eq_bot {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) (x : ν) (h : Γ x = ⊥)
  : Δ x = ⊥ := by cases w x <;> simp [*]
theorem FCtx.Wk.ne_bot {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) (x : ν) (h : Δ x ≠ ⊥)
  : Γ x ≠ ⊥ := λh' => h (w.eq_bot _ h')
theorem FCtx.Wk.eq_some_ne_bot {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ)
  (x : ν) (h : Δ x ≠ ⊥)
  : Γ x ≠ ⊥ := λh' => h (w.eq_bot _ h')

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
  toFun x := match Δ x, Δ' x with
    | ⊥, _ | _, ⊥ => ⊥
    | some a, some _ => some a
  support := Δ.support ∩ Δ'.support
  mem_support_toFun := by
    intro x
    simp only [Finset.mem_inter, mem_support]
    split <;> simp [Bot.bot, *]

theorem FCtx.linf_app (Δ Δ' : FCtx ν α) (x : ν)
  : (FCtx.linf Δ Δ') x = match Δ x, Δ' x with
    | ⊥, _ | _, ⊥ => ⊥
    | some a, some _ => some a := by rfl

theorem FCtx.linf_support {Δ Δ' : FCtx ν α}
  : (FCtx.linf Δ Δ').support = Δ.support ∩ Δ'.support := rfl
theorem FCtx.linf_mem_support {Δ Δ' : FCtx ν α} (x : ν)
  : x ∈ (FCtx.linf Δ Δ').support ↔ x ∈ Δ.support ∧ x ∈ Δ'.support := by
  simp [linf_support]

def FCtx.rinf (Δ Δ' : FCtx ν α)
  : FCtx ν α where
  toFun x := match Δ x, Δ' x with
    | ⊥, _ | _, ⊥ => ⊥
    | some _, some a => some a
  support := Δ.support ∩ Δ'.support
  mem_support_toFun := by
    intro x
    simp only [Finset.mem_inter, mem_support]
    split <;> simp [Bot.bot, *]

theorem FCtx.rinf_app (Δ Δ' : FCtx ν α) (x : ν)
  : (FCtx.rinf Δ Δ') x = match Δ x, Δ' x with
    | ⊥, _ | _, ⊥ => ⊥
    | some _, some a => some a := by rfl

theorem FCtx.rinf_support {Δ Δ' : FCtx ν α}
  : (FCtx.rinf Δ Δ').support = Δ.support ∩ Δ'.support := rfl

theorem FCtx.linf_wk (Δ Δ' : FCtx ν α) : FCtx.Wk Δ (FCtx.linf Δ Δ') := by
  intro x
  simp [linf_app]
  split <;> simp [*]

theorem FCtx.rinf_wk (Δ Δ' : FCtx ν α) : FCtx.Wk Δ' (FCtx.rinf Δ Δ') := by
  intro x
  simp [rinf_app]
  split <;> simp [*]

theorem FCtx.Wk.var_eq {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) (x : ν) (a b : α)
  (h : Γ x = a) (h' : Δ x = b)
  : a = b := by
  cases w x
  case inl hw => rw [hw] at h'; cases h'
  case inr hw => rw [hw] at h'; rw [h'] at h; cases h; rfl

theorem FCtx.Wk.var {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) (x : ν) (a : α)
  (h : Δ x = a) : Γ x = a := by
  cases w x
  case inl hw => rw [hw] at h; cases h
  case inr hw => rw [hw] at h; exact h

theorem FCtx.Wk.var_eq₂' {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  (x : ν) (a b : α) (h : Δ x = a) (h' : Δ' x = b)
  : (a : WithBot α) = (b : WithBot α) := by rw [<-var w x a h, <-var w' x b h']

theorem FCtx.Wk.var_eq₂ {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  (x : ν) (a b : α) (h : Δ x = a) (h' : Δ' x = b)
  : a = b := by cases var_eq₂' w w' x a b h h'; rfl

theorem FCtx.Wk.eq_on {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ)
  : ∀x ∈ Δ.support, Δ x = Γ x := by
  intro x hx
  cases w x with
  | inl h => rw [mem_support] at hx; exact (hx h).elim
  | inr h => exact h

theorem FCtx.Wk.linf_eq_rinf {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  : FCtx.linf Δ Δ' = FCtx.rinf Δ Δ' := by
  apply FCtx.ext
  intro x
  simp only [DFunLike.coe, linf, rinf]
  split
  . rfl
  . rfl
  . apply var_eq₂' w w' <;> assumption

theorem FCtx.Wk.linf_wk_left {Γ Δ Δ' : FCtx ν α} (_ : FCtx.Wk Γ Δ) (_ : FCtx.Wk Γ Δ')
  : FCtx.Wk Δ (FCtx.linf Δ Δ') := linf_wk Δ Δ'
theorem FCtx.Wk.linf_wk_right {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  : FCtx.Wk Δ' (FCtx.linf Δ Δ') := linf_eq_rinf w w' ▸ rinf_wk Δ Δ'

theorem FCtx.Wk.rinf_wk_left {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  : FCtx.Wk Δ (FCtx.rinf Δ Δ') := linf_eq_rinf w w' ▸ linf_wk Δ Δ'
theorem FCtx.Wk.rinf_wk_right {Γ Δ Δ' : FCtx ν α} (_ : FCtx.Wk Γ Δ) (_ : FCtx.Wk Γ Δ')
  : FCtx.Wk Δ' (FCtx.rinf Δ Δ') := rinf_wk Δ Δ'

theorem FCtx.linf_eq_none_left {Δ Δ' : FCtx ν α} (x : ν) (h : Δ x = ⊥)
  : FCtx.linf Δ Δ' x = ⊥ := by
  simp only [linf_app]
  split <;> simp only [h] at *
theorem FCtx.linf_eq_none_right {Δ Δ' : FCtx ν α} (x : ν) (h : Δ' x = ⊥)
  : FCtx.linf Δ Δ' x = ⊥ := by
  simp only [linf_app] at *
  split <;> simp only [h] at *
theorem FCtx.linf_eq_none_or {Δ Δ' : FCtx ν α} (x : ν) (h : FCtx.linf Δ Δ' x = ⊥)
  : Δ x = ⊥ ∨ Δ' x = ⊥ := by
  simp only [linf_app] at h
  rw [<-h] -- hack until term-to-split is supported...
  split <;> simp [*, Bot.bot]
theorem FCtx.linf_eq_none_iff {Δ Δ' : FCtx ν α} (x : ν)
  : FCtx.linf Δ Δ' x = ⊥ ↔ Δ x = ⊥ ∨ Δ' x = ⊥ :=
  ⟨linf_eq_none_or x, λh => h.elim (linf_eq_none_left x) (linf_eq_none_right x)⟩

theorem FCtx.linf_var_left {Δ Δ' : FCtx ν α} (x : ν) (a : α)
  : FCtx.linf Δ Δ' x = a → Δ x = a := by
  simp only [linf_app]
  split
  . intro h; cases h
  . intro h; cases h
  . intro h; rw [<-h]; assumption
theorem FCtx.linf_var_right {Δ Δ' : FCtx ν α} (x : ν) (a : α)
  : FCtx.linf Δ Δ' x = a → ∃b : α, Δ' x = b := by
  simp only [linf_app]
  split
  . intro h; cases h
  . intro h; cases h
  . intro _; constructor; assumption

theorem FCtx.linf_var_left_eq' {Δ Δ' : FCtx ν α} (x : ν) (a : α) (bb : WithBot α)
  (h : FCtx.linf Δ Δ' x = a) (h' : Δ x = bb) : a = bb := by
    rw [<-linf_var_left x a h]; assumption
theorem FCtx.linf_var_left_eq {Δ Δ' : FCtx ν α} (x : ν) (a b : α)
  (h : FCtx.linf Δ Δ' x = a) (h' : Δ x = b) : a = b := by
    cases linf_var_left_eq' x a b h h'; rfl

theorem FCtx.linf_support_eq_left {Δ Δ' : FCtx ν α} (x : ν)
  (h : x ∈ (linf Δ Δ').support) : FCtx.linf Δ Δ' x = Δ x := (linf_wk Δ Δ').eq_on x h

theorem FCtx.linf_var_eq_left {Δ Δ' : FCtx ν α} (x : ν) (a : α)
  (h : FCtx.linf Δ Δ' x = a)
  : FCtx.linf Δ Δ' x = Δ x := by
    rw [h]
    apply Eq.symm
    apply linf_var_left
    exact h
theorem FCtx.linf_right_var_eq_left {Δ Δ' : FCtx ν α} (x : ν) (a : α)
  (h : Δ' x = a)
  : FCtx.linf Δ Δ' x = Δ x := by
    rw [linf_app]
    split
    . simp [*, Bot.bot] at *
    . rw [h] at *; contradiction
    . simp [*]

theorem FCtx.linf_some_eq_left {Δ Δ' : FCtx ν α} (x : ν)
: (∃a : α, FCtx.linf Δ Δ' x = a) → FCtx.linf Δ Δ' x = Δ x := by
  intro ⟨a, h⟩
  rw [h]
  apply Eq.symm
  apply linf_var_left
  exact h
theorem FCtx.linf_right_some_eq_left {Δ Δ' : FCtx ν α} (x : ν)
  : (∃a: α, Δ' x = a) → FCtx.linf Δ Δ' x = Δ x := by
  intro ⟨a, h⟩
  apply linf_right_var_eq_left _ _ h
theorem FCtx.linf_right_support_eq_left {Δ Δ' : FCtx ν α} (x : ν)
  (h : x ∈ Δ'.support) : FCtx.linf Δ Δ' x = Δ x := by
  apply linf_right_some_eq_left _ ((mem_support_exists _).mp h)
  rfl

theorem FCtx.linf_assoc (Δ₁ Δ₂ Δ₃ : FCtx ν α)
  : FCtx.linf (FCtx.linf Δ₁ Δ₂) Δ₃ = FCtx.linf Δ₁ (FCtx.linf Δ₂ Δ₃) := by
  apply FCtx.ext
  intro x
  conv =>
    rhs
    rw [linf_app]
  split
  . apply linf_eq_none_left; apply linf_eq_none_left; assumption
  . simp only [linf_eq_none_iff]
    rw [or_assoc]
    apply Or.inr
    apply linf_eq_none_or
    assumption
  . rename_i h
    rw [linf_right_some_eq_left _ (linf_var_right _ _ h)]
    rw [linf_right_var_eq_left _ _ (linf_var_left _ _ h)]
    assumption

theorem FCtx.linf_comm (Δ Δ' : FCtx ν α)
  : FCtx.linf Δ Δ' = FCtx.rinf Δ' Δ := by
  apply FCtx.ext
  intro x;
  simp only [linf_app, rinf_app]
  split
  . split
    . rfl
    . rfl
    . simp [*] at *
  . split
    . rfl
    . rfl
    . simp [*] at *
  . split
    . simp [*] at *
    . simp [*] at *
    . rename_i h _ _ _ _ _ _ h'
      rw [<-h, <-h']

theorem FCtx.rinf_comm (Δ Δ' : FCtx ν α)
  : FCtx.rinf Δ Δ' = FCtx.linf Δ' Δ := by
  rw [linf_comm]

--TODO: rinf_assoc, etc...

def FCtx.lsup (Δ Δ' : FCtx ν α)
  : FCtx ν α where
  toFun x := match Δ x, Δ' x with
    | ⊥, _ => Δ' x
    | _, ⊥ => Δ x
    | some a, some _ => some a
  support := Δ.support ∪ Δ'.support
  mem_support_toFun := by
    intro x
    simp only [Finset.mem_union, mem_support]
    split <;> simp [Bot.bot, *]

def FCtx.rsup (Δ Δ' : FCtx ν α)
  : FCtx ν α where
  toFun x := match Δ x, Δ' x with
    | ⊥, _ => Δ' x
    | _, ⊥ => Δ x
    | some _, some a => some a
  support := Δ.support ∪ Δ'.support
  mem_support_toFun := by
    intro x
    simp only [Finset.mem_union, mem_support]
    split <;> simp [Bot.bot, *]

--TODO: wk lemmas, assoc, etc...

structure FLCtx (κ : Type _) (ν : Type _) (α : Type _) : Type _ where
  toFun : κ → WithBot (FCtx ν α)
  support : Finset κ
  mem_support_toFun : ∀x, x ∈ support ↔ toFun x ≠ ⊥

--TODO: FLCtx.linf, rinf, lsup, rsup, and lemmata
