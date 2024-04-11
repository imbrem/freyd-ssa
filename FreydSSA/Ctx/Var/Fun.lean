import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Init.Classical
import Mathlib.Order.SuccPred.Basic

variable {ν ν' α β} [DecidableEq ν] [DecidableEq ν'] [DecidableEq α]

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

theorem FCtx.isSome_of_mem_support {Γ : FCtx ν α} {x : ν} (h : x ∈ Γ.support) : (Γ x).isSome := by
  simp only [Option.isSome]
  split
  rfl
  rw [mem_support] at h
  exfalso
  apply h
  assumption

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

theorem FCtx.not_mem_support_of_eq_bot {Γ : FCtx ν α} (x : ν)
  (h : Γ x = ⊥) : x ∉ Γ.support := by
  rw [mem_support]
  intro h'
  contradiction

theorem FCtx.eq_bot_of_not_mem_support {Γ : FCtx ν α} (x : ν)
  (h : x ∉ Γ.support) : Γ x = ⊥ := by
  simp [mem_support] at h
  exact h

theorem FCtx.not_mem_support {Γ : FCtx ν α} (x : ν)
  : x ∉ Γ.support ↔ Γ x = ⊥ := ⟨eq_bot_of_not_mem_support x, not_mem_support_of_eq_bot x⟩

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

def FCtx.get {Γ : FCtx ν α} {x : ν} (h : x ∈ Γ.support) : α :=
  (Γ x).get (isSome_of_mem_support h)

theorem FCtx.get_eq {Γ : FCtx ν α} {x : ν} (h : x ∈ Γ.support)
  : Γ x = Γ.get h := by
  simp [FCtx.get, Option.get]
  split
  rename_i h _
  rw [h]
  rfl

theorem FCtx.get_var {Γ : FCtx ν α} {x : ν} {a : α} (h : Γ x = a)
  : Γ.get (Γ.mem_support_of_var _ _ h) = a := by
  simp [FCtx.get, Option.get]
  split
  rename_i h' _
  rw [h] at h'
  cases h'
  rfl

def FCtx.Wk (Γ Δ : FCtx ν α) : Prop := ∀x, Δ x = ⊥ ∨ Δ x = Γ x

theorem FCtx.Wk.refl (Γ : FCtx ν α) : FCtx.Wk Γ Γ := by simp [FCtx.Wk]
theorem FCtx.Wk.comp {Γ Δ Θ : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Δ Θ)
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

-- theorem FCtx.Wk.mem_support {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ)
--   : ∀{x}, x ∈ Δ.support → x ∈ Γ.support := by
--   intro x
--   rw [Γ.mem_support_toFun, Δ.mem_support_toFun]
--   exact w.ne_bot x

instance FCtx.instPartialOrder : PartialOrder (FCtx ν α) where
  le a b := FCtx.Wk b a
  le_refl := FCtx.Wk.refl
  le_trans _ _ _ h h' := FCtx.Wk.comp h' h
  le_antisymm _ _ h h' := FCtx.Wk.antisymm h' h

def FCtx.Cmp (Δ Δ' : FCtx ν α) : Prop := ∀x, Δ x = Δ' x ∨ Δ x = ⊥ ∨ Δ' x = ⊥

theorem FCtx.Cmp.refl (Γ : FCtx ν α) : FCtx.Cmp Γ Γ := by simp [FCtx.Cmp]

theorem FCtx.Cmp.symm {Γ Δ : FCtx ν α} (c : FCtx.Cmp Γ Δ) : FCtx.Cmp Δ Γ := λx =>
  match c x with
  | Or.inl h => Or.inl h.symm
  | Or.inr (Or.inl h) => Or.inr (Or.inr h)
  | Or.inr (Or.inr h) => Or.inr (Or.inl h)

theorem FCtx.Cmp.of_wk₂ {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  : FCtx.Cmp Δ Δ' := by
  intro x
  cases w x <;> cases w' x <;> simp [*]

theorem FCtx.Cmp.of_wk {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) : FCtx.Cmp Γ Δ := by
  intro x
  cases w x <;> simp [*]

theorem FCtx.Wk.cmp₂ {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  : FCtx.Cmp Δ Δ' := FCtx.Cmp.of_wk₂ w w'
theorem FCtx.Wk.cmp {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) : FCtx.Cmp Γ Δ := FCtx.Cmp.of_wk w

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

theorem FCtx.Cmp.var_eq' {Γ Δ : FCtx ν α} (c : FCtx.Cmp Γ Δ) (x : ν) (a b : α)
  (h : Γ x = a) (h' : Δ x = b)
  : (a : WithBot α) = (b : WithBot α) := match c x with
  | Or.inl c => h.symm.trans (c.trans h')
  | Or.inr (Or.inl c) => by cases h.symm.trans c
  | Or.inr (Or.inr c) => by cases h'.symm.trans c

theorem FCtx.Cmp.var_eq {Γ Δ : FCtx ν α} (c : FCtx.Cmp Γ Δ) (x : ν) (a b : α)
  (h : Γ x = a) (h' : Δ x = b)
  : a = b := by cases var_eq' c x a b h h'; rfl

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

theorem FCtx.Wk.get_eq {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ)
  : ∀{x} (h : x ∈ Δ.support), Δ.get h = Γ.get (w.support_subset h) := by
  intro x h
  simp only [get]
  congr 1
  apply w.eq_on x h

theorem FCtx.Wk.of_eq_on {Γ Δ : FCtx ν α}
  : (∀x ∈ Δ.support, Δ x = Γ x) → FCtx.Wk Γ Δ := by
  intro h
  intro x
  if h' : x ∈ Δ.support then
    simp [h _ h']
  else
    simp [eq_bot_of_not_mem_support _ h']

theorem FCtx.Wk.eq_on_iff {Γ Δ : FCtx ν α}
  : FCtx.Wk Γ Δ ↔ (∀x ∈ Δ.support, Δ x = Γ x) := ⟨eq_on, of_eq_on⟩

theorem FCtx.Wk.cons {Γ Δ : FCtx ν α} (w : FCtx.Wk Γ Δ) (x : ν) (a : α)
  : FCtx.Wk (Γ.cons x a) (Δ.cons x a) := by
  intro y
  simp only [FCtx.cons, DFunLike.coe, Function.update]
  split
  simp
  exact w y

theorem FCtx.Cmp.linf_eq_rinf {Δ Δ' : FCtx ν α} (c : FCtx.Cmp Δ Δ')
  : FCtx.linf Δ Δ' = FCtx.rinf Δ Δ' := by
  apply FCtx.ext
  intro x
  simp only [DFunLike.coe, linf, rinf]
  split
  . rfl
  . rfl
  . apply var_eq' c <;> assumption

theorem FCtx.Wk.linf_eq_rinf {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  : FCtx.linf Δ Δ' = FCtx.rinf Δ Δ' := (w.cmp₂ w').linf_eq_rinf

theorem FCtx.Cmp.linf_wk_left {Δ Δ' : FCtx ν α} (_ : FCtx.Cmp Δ Δ')
  : FCtx.Wk Δ (FCtx.linf Δ Δ') := linf_wk Δ Δ'
theorem FCtx.Cmp.linf_wk_right {Δ Δ' : FCtx ν α} (c : FCtx.Cmp Δ Δ')
  : FCtx.Wk Δ' (FCtx.linf Δ Δ') := c.linf_eq_rinf ▸ rinf_wk Δ Δ'

theorem FCtx.Wk.linf_wk_left {Γ Δ Δ' : FCtx ν α} (_ : FCtx.Wk Γ Δ) (_ : FCtx.Wk Γ Δ')
  : FCtx.Wk Δ (FCtx.linf Δ Δ') := linf_wk Δ Δ'
theorem FCtx.Wk.linf_wk_right {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  : FCtx.Wk Δ' (FCtx.linf Δ Δ') := linf_eq_rinf w w' ▸ rinf_wk Δ Δ'

theorem FCtx.Cmp.rinf_wk_left {Δ Δ' : FCtx ν α} (c : FCtx.Cmp Δ Δ')
  : FCtx.Wk Δ (FCtx.rinf Δ Δ') := c.linf_eq_rinf ▸ linf_wk Δ Δ'
theorem FCtx.Cmp.rinf_wk_right {Δ Δ' : FCtx ν α} (_ : FCtx.Cmp Δ Δ')
  : FCtx.Wk Δ' (FCtx.rinf Δ Δ') := rinf_wk Δ Δ'

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
  split <;> intro h <;> cases h; assumption
theorem FCtx.linf_var_right {Δ Δ' : FCtx ν α} (x : ν) (a : α)
  : FCtx.linf Δ Δ' x = a → ∃b : α, Δ' x = b := by
  simp only [linf_app]
  split <;> intro h <;> cases h; exact ⟨_, by assumption⟩

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
theorem FCtx.linf_left_not_support {Δ Δ' : FCtx ν α} (x : ν)
  (h : x ∉ Δ.support) : FCtx.linf Δ Δ' x = ⊥ := by
  apply linf_eq_none_left
  apply eq_bot_of_not_mem_support
  exact h
theorem FCtx.linf_right_not_support {Δ Δ' : FCtx ν α} (x : ν)
  (h : x ∉ Δ'.support) : FCtx.linf Δ Δ' x = ⊥ := by
  apply linf_eq_none_right
  apply eq_bot_of_not_mem_support
  exact h
theorem FCtx.linf_eq_eq_left {Δ Δ' : FCtx ν α} (x : ν)
  (h : Δ x = Δ' x) : FCtx.linf Δ Δ' x = Δ x := by
  if h': x ∈ Δ'.support then
    rw [linf_right_support_eq_left _ h']
  else
    rw [linf_right_not_support _ h']
    rw [eq_bot_of_not_mem_support _ h'] at h
    rw [h]
theorem FCtx.linf_eq_eq_right {Δ Δ' : FCtx ν α} (x : ν)
  (h : Δ x = Δ' x) : FCtx.linf Δ Δ' x = Δ' x := by
  rw [linf_eq_eq_left _ h]
  exact h

theorem FCtx.Wk.linf_wk {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Δ Γ) (w' : FCtx.Wk Δ' Γ)
  : FCtx.Wk (FCtx.linf Δ Δ') Γ := by
  simp only [eq_on_iff] at *
  intro x hx
  rw [linf_eq_eq_left]
  . rw [<-w _ hx]
  . rw [<-w' _ hx]
    rw [<-w _ hx]

theorem FCtx.rinf_eq_none_left {Δ Δ' : FCtx ν α} (x : ν) (h : Δ x = ⊥)
  : FCtx.rinf Δ Δ' x = ⊥ := by
  simp only [rinf_app]
  split <;> simp only [h] at *
theorem FCtx.rinf_eq_none_right {Δ Δ' : FCtx ν α} (x : ν) (h : Δ' x = ⊥)
  : FCtx.rinf Δ Δ' x = ⊥ := by
  simp only [rinf_app] at *
  split <;> simp only [h] at *
theorem FCtx.rinf_eq_none_or {Δ Δ' : FCtx ν α} (x : ν) (h : FCtx.rinf Δ Δ' x = ⊥)
  : Δ x = ⊥ ∨ Δ' x = ⊥ := by
  simp only [rinf_app] at h
  rw [<-h] -- hack until term-to-split is supported...
  split <;> simp [*, Bot.bot]
theorem FCtx.rinf_eq_none_iff {Δ Δ' : FCtx ν α} (x : ν)
  : FCtx.rinf Δ Δ' x = ⊥ ↔ Δ x = ⊥ ∨ Δ' x = ⊥ :=
  ⟨rinf_eq_none_or x, λh => h.elim (rinf_eq_none_left x) (rinf_eq_none_right x)⟩

theorem FCtx.rinf_var_left {Δ Δ' : FCtx ν α} (x : ν) (a : α)
  : FCtx.rinf Δ Δ' x = a → ∃b : α, Δ x = b := by
  simp only [rinf_app]
  split <;> intro h <;> cases h; exact ⟨_, by assumption⟩
theorem FCtx.rinf_var_right {Δ Δ' : FCtx ν α} (x : ν) (a : α)
  : FCtx.rinf Δ Δ' x = a → Δ' x = a := by
  simp only [rinf_app]
  split <;> intro h <;> cases h; assumption

theorem FCtx.rinf_var_right_eq' {Δ Δ' : FCtx ν α} (x : ν) (a : α) (bb : WithBot α)
  (h : FCtx.rinf Δ Δ' x = a) (h' : Δ' x = bb) : a = bb := by
    rw [<-rinf_var_right x a h]; assumption
theorem FCtx.rinf_var_right_eq {Δ Δ' : FCtx ν α} (x : ν) (a b : α)
  (h : FCtx.rinf Δ Δ' x = a) (h' : Δ' x = b) : a = b := by
    cases rinf_var_right_eq' x a b h h'; rfl

theorem FCtx.rinf_support_eq_right {Δ Δ' : FCtx ν α} (x : ν)
  (h : x ∈ (rinf Δ Δ').support) : FCtx.rinf Δ Δ' x = Δ' x := (rinf_wk Δ Δ').eq_on x h

theorem FCtx.rinf_var_eq_right {Δ Δ' : FCtx ν α} (x : ν) (a : α)
  (h : FCtx.rinf Δ Δ' x = a)
  : FCtx.rinf Δ Δ' x = Δ' x := by
    rw [h]
    apply Eq.symm
    apply rinf_var_right
    exact h
theorem FCtx.rinf_left_var_eq_right {Δ Δ' : FCtx ν α} (x : ν) (a : α)
  (h : Δ x = a)
  : FCtx.rinf Δ Δ' x = Δ' x := by
    rw [rinf_app]
    split
    . rw [h] at *; contradiction
    . simp [*, Bot.bot] at *
    . simp [*]

theorem FCtx.rinf_some_eq_right {Δ Δ' : FCtx ν α} (x : ν)
: (∃a : α, FCtx.rinf Δ Δ' x = a) → FCtx.rinf Δ Δ' x = Δ' x := by
  intro ⟨a, h⟩
  rw [h]
  apply Eq.symm
  apply rinf_var_right
  exact h
theorem FCtx.rinf_left_some_eq_right {Δ Δ' : FCtx ν α} (x : ν)
  : (∃a: α, Δ x = a) → FCtx.rinf Δ Δ' x = Δ' x := by
  intro ⟨a, h⟩
  apply rinf_left_var_eq_right _ _ h
theorem FCtx.rinf_left_support_eq_right {Δ Δ' : FCtx ν α} (x : ν)
  (h : x ∈ Δ.support) : FCtx.rinf Δ Δ' x = Δ' x := by
  apply rinf_left_some_eq_right _ ((mem_support_exists _).mp h)
  rfl
theorem FCtx.rinf_right_not_support {Δ Δ' : FCtx ν α} (x : ν)
  (h : x ∉ Δ.support) : FCtx.rinf Δ Δ' x = ⊥ := by
  apply rinf_eq_none_left
  apply eq_bot_of_not_mem_support
  exact h
theorem FCtx.rinf_eq_eq_right {Δ Δ' : FCtx ν α} (x : ν)
  (h : Δ x = Δ' x) : FCtx.rinf Δ Δ' x = Δ' x := by
  if h': x ∈ Δ.support then
    rw [rinf_left_support_eq_right _ h']
  else
    rw [rinf_right_not_support _ h']
    rw [eq_bot_of_not_mem_support _ h'] at h
    rw [h]
theorem FCtx.rinf_eq_eq_left {Δ Δ' : FCtx ν α} (x : ν)
  (h : Δ x = Δ' x) : FCtx.rinf Δ Δ' x = Δ x := by
    rw [rinf_eq_eq_right _ h]
    exact h.symm

theorem FCtx.Wk.rinf_wk {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Δ Γ) (w' : FCtx.Wk Δ' Γ)
  : FCtx.Wk (FCtx.rinf Δ Δ') Γ := by
  simp only [eq_on_iff] at *
  intro x hx
  rw [rinf_eq_eq_left]
  . rw [<-w _ hx]
  . rw [<-w' _ hx]
    rw [<-w _ hx]

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

theorem FCtx.rinf_assoc (Δ₁ Δ₂ Δ₃ : FCtx ν α)
  : FCtx.rinf (FCtx.rinf Δ₁ Δ₂) Δ₃ = FCtx.rinf Δ₁ (FCtx.rinf Δ₂ Δ₃) := by
  apply FCtx.ext
  intro x
  conv =>
    rhs
    rw [rinf_app]
  split
  . apply rinf_eq_none_left; apply rinf_eq_none_left; assumption
  . simp only [rinf_eq_none_iff]
    rw [or_assoc]
    apply Or.inr
    apply rinf_eq_none_or
    assumption
  . rename_i h
    have ⟨b, hb⟩ := rinf_var_left _ _ h;
    rw [rinf_left_var_eq_right _ b]
    exact rinf_var_right _ _ h
    rw [rinf_left_var_eq_right _ _]
    exact hb
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

theorem FCtx.linf_idem (Δ : FCtx ν α)
  : FCtx.linf Δ Δ = Δ := by
  apply FCtx.ext
  intro x
  simp only [linf_app]
  split <;> simp [WithBot.bot, *]

theorem FCtx.rinf_idem (Δ : FCtx ν α)
  : FCtx.rinf Δ Δ = Δ := by
  rw [<-(FCtx.Cmp.refl Δ).linf_eq_rinf, linf_idem]

--TODO: linf_nil, nil_linf, rinf_nil, nil_rinf

--TODO: inf eq iff wk

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

theorem FCtx.lsup_app (Δ Δ' : FCtx ν α) (x : ν)
  : (FCtx.lsup Δ Δ') x = match Δ x, Δ' x with
    | ⊥, _ => Δ' x
    | _, ⊥ => Δ x
    | some a, some _ => some a := by rfl

theorem FCtx.lsup_support {Δ Δ' : FCtx ν α}
  : (FCtx.lsup Δ Δ').support = Δ.support ∪ Δ'.support := rfl

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

theorem FCtx.rsup_app (Δ Δ' : FCtx ν α) (x : ν)
  : (FCtx.rsup Δ Δ') x = match Δ x, Δ' x with
    | ⊥, _ => Δ' x
    | _, ⊥ => Δ x
    | some _, some a => some a := by rfl

theorem FCtx.rsup_support {Δ Δ' : FCtx ν α}
  : (FCtx.rsup Δ Δ').support = Δ.support ∪ Δ'.support := rfl

theorem FCtx.lsup_wk (Δ Δ' : FCtx ν α) : FCtx.Wk (FCtx.lsup Δ Δ') Δ := by
  intro x
  simp [lsup_app]
  split <;> simp [Bot.bot, *]

theorem FCtx.rsup_wk (Δ Δ' : FCtx ν α) : FCtx.Wk (FCtx.rsup Δ Δ') Δ' := by
  intro x
  simp [rsup_app]
  split <;> simp [Bot.bot, *]

theorem FCtx.Cmp.lsup_eq_rsup {Δ Δ' : FCtx ν α} (c : FCtx.Cmp Δ Δ')
  : FCtx.lsup Δ Δ' = FCtx.rsup Δ Δ' := by
  apply FCtx.ext
  intro x
  simp only [DFunLike.coe, lsup, rsup]
  split
  . rfl
  . rfl
  . apply var_eq' c <;> assumption

theorem FCtx.Wk.lsup_eq_rsup {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  : FCtx.lsup Δ Δ' = FCtx.rsup Δ Δ' := (w.cmp₂ w').lsup_eq_rsup

theorem FCtx.Cmp.lsup_wk_left {Δ Δ' : FCtx ν α} (_ : FCtx.Cmp Δ Δ')
  : FCtx.Wk (FCtx.lsup Δ Δ') Δ := lsup_wk Δ Δ'
theorem FCtx.Cmp.lsup_wk_right {Δ Δ' : FCtx ν α} (c : FCtx.Cmp Δ Δ')
  : FCtx.Wk (FCtx.lsup Δ Δ') Δ' := c.lsup_eq_rsup ▸ rsup_wk Δ Δ'

theorem FCtx.Wk.lsup_wk_left {Γ Δ Δ' : FCtx ν α} (_ : FCtx.Wk Γ Δ) (_ : FCtx.Wk Γ Δ')
  : FCtx.Wk (FCtx.lsup Δ Δ') Δ := lsup_wk Δ Δ'
theorem FCtx.Wk.lsup_wk_right {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  : FCtx.Wk (FCtx.lsup Δ Δ') Δ' := lsup_eq_rsup w w' ▸ rsup_wk Δ Δ'

theorem FCtx.Cmp.rsup_wk_left {Δ Δ' : FCtx ν α} (c : FCtx.Cmp Δ Δ')
  : FCtx.Wk (FCtx.rsup Δ Δ') Δ := c.lsup_eq_rsup ▸ lsup_wk Δ Δ'
theorem FCtx.Cmp.rsup_wk_right {Δ Δ' : FCtx ν α} (_ : FCtx.Cmp Δ Δ')
  : FCtx.Wk (FCtx.rsup Δ Δ') Δ' := rsup_wk Δ Δ'

theorem FCtx.Wk.rsup_wk_left {Γ Δ Δ' : FCtx ν α} (w : FCtx.Wk Γ Δ) (w' : FCtx.Wk Γ Δ')
  : FCtx.Wk (FCtx.rsup Δ Δ') Δ := lsup_eq_rsup w w' ▸ lsup_wk Δ Δ'
theorem FCtx.Wk.rsup_wk_right {Γ Δ Δ' : FCtx ν α} (_ : FCtx.Wk Γ Δ) (_ : FCtx.Wk Γ Δ')
  : FCtx.Wk (FCtx.rsup Δ Δ') Δ' := rsup_wk Δ Δ'

--TODO: wk lemmas, assoc, idem, nil, etc.

theorem FCtx.Cmp.iff_exists_wk {Δ Δ' : FCtx ν α}
  : FCtx.Cmp Δ Δ' ↔ ∃Γ : FCtx ν α, Γ.Wk Δ ∧ Γ.Wk Δ'
  := ⟨λc => ⟨_, c.lsup_wk_left, c.lsup_wk_right⟩, λ⟨_, w, w'⟩ => w.cmp₂ w'⟩

def FCtx.inf (Δ Δ' : FCtx ν α) : FCtx ν α where
  toFun x := if Δ x = Δ' x then Δ x else ⊥
  support := Δ.support.filter (λx => Δ x = Δ' x)
  mem_support_toFun := by
    intro x
    simp [mem_support_toFun]
    exact ⟨λh => ⟨h.2, h.1⟩, λh => ⟨h.2, h.1⟩⟩

theorem FCtx.inf_support_left {Δ Δ' : FCtx ν α}
  : (FCtx.inf Δ Δ').support = Δ.support.filter (λx => Δ x = Δ' x) := rfl

theorem FCtx.inf_comm (Δ Δ' : FCtx ν α)
  : FCtx.inf Δ Δ' = FCtx.inf Δ' Δ := by
  apply FCtx.ext
  intro x
  simp only [DFunLike.coe, inf]
  split
  . simp [*]
  . split
    . simp [*] at *
    . rfl

--TODO: inf_assoc
--TODO: inf_idem
--TODO: inf_nil

theorem FCtx.inf_support_right {Δ Δ' : FCtx ν α}
  : (FCtx.inf Δ Δ').support = Δ'.support.filter (λx => Δ x = Δ' x) := by
  rw [inf_comm, inf_support_left]
  congr
  funext x
  apply propext; constructor <;> intro h <;> rw [h]

theorem FCtx.Cmp.inf_eq_linf {Δ Δ' : FCtx ν α} (c : FCtx.Cmp Δ Δ')
  : FCtx.inf Δ Δ' = FCtx.linf Δ Δ' := by
  apply FCtx.ext
  intro x
  simp only [DFunLike.coe, inf, linf]
  split
  . rename_i h
    simp [h]
    split <;> assumption
  . split
    . rfl
    . rfl
    . rename_i hΔ hΔ'; match c x with
      | Or.inl h => contradiction
      | Or.inr (Or.inl h) => cases hΔ.symm.trans h
      | Or.inr (Or.inr h) => cases hΔ'.symm.trans h

theorem FCtx.Cmp.inf_eq_rinf {Δ Δ' : FCtx ν α} (c : FCtx.Cmp Δ Δ')
  : FCtx.inf Δ Δ' = FCtx.rinf Δ Δ' := by rw [c.inf_eq_linf, c.linf_eq_rinf]

--TODO: instantiate semilattice structure

--TODO: compatible contexts with the same support are equal

theorem FCtx.Cmp.eq_of_eq_support {Δ Δ' : FCtx ν α} (c : FCtx.Cmp Δ Δ')
  (h : Δ.support = Δ'.support)
  : Δ = Δ' := by
  apply FCtx.ext
  rw [Finset.ext_iff] at h
  intro x
  match c x with
  | Or.inl h => exact h
  | Or.inr (Or.inl hx) =>
    rw [hx]
    apply Eq.symm
    apply eq_bot_of_not_mem_support
    intro hx'
    rw [<-h] at hx'
    exact not_mem_support_of_eq_bot _ hx hx'
  | Or.inr (Or.inr hx) =>
    rw [hx]
    apply eq_bot_of_not_mem_support
    intro hx'
    rw [h] at hx'
    exact not_mem_support_of_eq_bot _ hx hx'

def FCtx.restrict (Γ : FCtx ν α) (vars : Finset ν) : FCtx ν α where
  toFun x := if x ∈ vars then Γ x else ⊥
  support := Γ.support ∩ vars
  mem_support_toFun := by simp [mem_support, And.comm]

theorem FCtx.restrict_app (Γ : FCtx ν α) (vars : Finset ν) (x : ν)
  : (FCtx.restrict Γ vars) x = if x ∈ vars then Γ x else ⊥
  := rfl

theorem FCtx.restrict_support (Γ : FCtx ν α) : Γ.restrict Γ.support = Γ
  := ext (λx => by
    simp only [restrict_app, mem_support, ne_eq, ite_not, ite_eq_right_iff];
    intro h; rw [h])

theorem FCtx.restrict_sub_support {Γ : FCtx ν α} {v : Finset ν} (hv : Γ.support ⊆ v)
  : Γ.restrict v = Γ := by
  --TODO: clean this up...
  apply ext
  intro x
  simp only [restrict_app, ite_eq_left_iff]
  intro hx
  have hx := λc => hx (Finset.mem_of_subset hv c)
  simp only [mem_support, ne_eq, imp_false, not_not] at hx
  rw [hx]

theorem FCtx.sub_support_of_restrict_eq {Γ : FCtx ν α} {v : Finset ν} (hv : Γ.restrict v = Γ)
  : Γ.support ⊆ v := by
  intro x hx
  simp only [mem_support, Finset.mem_inter] at hx
  rw [<-hv, restrict_app] at hx
  simp only [ne_eq, ite_eq_right_iff, not_forall, exists_prop] at hx
  exact hx.1

theorem FCtx.restrict_sub_support_iff (Γ : FCtx ν α) (v : Finset ν)
  : Γ.restrict v = Γ ↔ Γ.support ⊆ v := ⟨sub_support_of_restrict_eq, restrict_sub_support⟩

theorem FCtx.restrict_inter (Γ : FCtx ν α) (v v' : Finset ν)
  : Γ.restrict (v ∩ v') = (Γ.restrict v).restrict v' := by
  apply FCtx.ext
  intro x
  apply Eq.symm
  simp only [restrict_app, Finset.mem_inter]
  split <;> simp [*]

theorem FCtx.restrict_restrict (Γ : FCtx ν α) (v : Finset ν)
  : (Γ.restrict v).restrict v = Γ.restrict v := by
  apply FCtx.ext
  intro x
  apply Eq.symm
  simp only [restrict_app, Finset.mem_inter]
  split <;> simp [*]

theorem FCtx.Wk.wk_restrict (Γ : FCtx ν α) (v : Finset ν)
  : Γ.Wk (Γ.restrict v)
  := of_eq_on (λx hx => by
    simp only [restrict_app, ite_eq_left_iff]
    intro hx'
    exact (hx' (Finset.mem_of_mem_inter_right hx)).elim)

theorem FCtx.Cmp.cmp_restrict (Γ : FCtx ν α) (v : Finset ν)
  : FCtx.Cmp Γ (Γ.restrict v) := of_wk (Wk.wk_restrict Γ v)

theorem FCtx.Wk.restrict_sub {v v' : Finset ν} (Γ : FCtx ν α) (hv : v' ⊆ v)
  : (Γ.restrict v).Wk (Γ.restrict v')
  := of_eq_on (λx hx =>
    have hxv := Finset.mem_of_mem_inter_right hx
    have hxv' := Finset.mem_of_subset hv hxv
    by simp [restrict_app, *])

theorem FCtx.Wk.restrict_union_left (Γ : FCtx ν α) (l r : Finset ν)
  : (Γ.restrict (l ∪ r)).Wk (Γ.restrict l)
  := restrict_sub Γ (Finset.subset_union_left l r)

theorem FCtx.Wk.restrict_union_right (Γ : FCtx ν α) (l r : Finset ν)
  : (Γ.restrict (l ∪ r)).Wk (Γ.restrict r)
  := restrict_sub Γ (Finset.subset_union_right l r)

theorem FCtx.Wk.restrict_inter_left (Γ : FCtx ν α) (l r : Finset ν)
  : (Γ.restrict l).Wk (Γ.restrict (l ∩ r))
  := restrict_sub Γ (Finset.inter_subset_left l r)

theorem FCtx.Wk.restrict_inter_right (Γ : FCtx ν α) (l r : Finset ν)
  : (Γ.restrict r).Wk (Γ.restrict (l ∩ r))
  := restrict_sub Γ (Finset.inter_subset_right l r)

theorem FCtx.Wk.restrict {Γ Δ : FCtx ν α} (w : Γ.Wk Δ) (v : Finset ν)
  : (Γ.restrict v).Wk (Δ.restrict v)
  := of_eq_on (λx hx =>
    have hxv := Finset.mem_of_mem_inter_right hx
    by simp only [restrict_app, ↓reduceIte, hxv]; exact w.eq_on _ (Finset.mem_of_mem_inter_left hx))

-- TODO: FCtx.Cmp.restrict

--TODO: in a coherent setting, any two contexts typing a term have equal restrictions
