import FreydSSA.Ctx.Var.Fun

variable {ν : Type u₁} {ν' : Type u₂} {κ : Type u₃} {κ' : Type u₄} {α : Type u₅} {β : Type u₆}
  [DecidableEq ν] [DecidableEq ν']
  [DecidableEq κ] [DecidableEq κ']
  [DecidableEq α] [DecidableEq β]

structure FLabel (ν : Type _) (α : Type _) where
  -- TODO: Fun with parameter contexts? Parameter sets? Many options...
  live : FCtx ν α
  param : α

def FLabel.toFCtx (L : FLabel ν α) (x : ν) : FCtx ν α := L.live.cons x L.param

theorem FLabel.ext {L K : FLabel ν α} (h : L.live = K.live) (h' : L.param = K.param)
  : L = K := by
  cases L; cases K
  cases h; cases h'
  rfl

structure FLabel.Wk (L K : FLabel ν α) : Prop where
  live : L.live.Wk K.live
  param : L.param = K.param

theorem FLabel.Wk.refl (L : FLabel ν α) : FLabel.Wk L L := ⟨FCtx.Wk.refl _, rfl⟩
theorem FLabel.Wk.comp {L K M : FLabel ν α} (h : FLabel.Wk L K) (h' : FLabel.Wk K M)
  : FLabel.Wk L M := ⟨h.live.comp h'.live, h.param ▸ h'.param⟩
theorem FLabel.Wk.antisymm {L K : FLabel ν α} (h : FLabel.Wk L K) (h' : FLabel.Wk K L)
  : L = K := FLabel.ext (h.live.antisymm h'.live) h.param

instance FLabel.instPartialOrder : PartialOrder (FLabel ν α) where
  le L K := FLabel.Wk L K
  le_refl _ := FLabel.Wk.refl _
  le_trans _ _ _ h h' := h.comp h'
  le_antisymm _ _ h h' := Wk.antisymm h h'

structure FLabel.Cmp (L K : FLabel ν α) : Prop where
  live : L.live.Cmp K.live
  param : L.param = K.param

theorem FLabel.Cmp.refl (L : FLabel ν α) : FLabel.Cmp L L := ⟨FCtx.Cmp.refl _, rfl⟩
theorem FLabel.Cmp.symm {L K : FLabel ν α} (h : FLabel.Cmp L K) : FLabel.Cmp K L
  := ⟨h.live.symm, h.param.symm⟩

theorem FLabel.Cmp.of_le {L K : FLabel ν α} (h : L ≤ K) : FLabel.Cmp L K
  := ⟨FCtx.Cmp.of_wk h.live, h.param⟩
theorem FLabel.Cmp.of_le₂ {L K M : FLabel ν α} (h : M ≤ L) (h' : M ≤ K) : FLabel.Cmp L K
  := ⟨h.live.cmp₂ h'.live, h.param.symm.trans h'.param⟩

def FLabel.lsup (L K : FLabel ν α) : FLabel ν α where
  param := L.param
  live := L.live.lsup K.live

theorem FLabel.lsup_le (L K : FLabel ν α) : L ≤ lsup L K := ⟨FCtx.lsup_wk _ _, rfl⟩

theorem FLabel.Wk.lsup_wk {L L' K : FLabel ν α} (hL : L.Wk K) (hL' : L'.Wk K) : (L.lsup L').Wk K
  := ⟨hL.live.lsup_wk hL'.live, hL.param⟩

def FLabel.rsup (L K : FLabel ν α) : FLabel ν α where
  param := K.param
  live := L.live.rsup K.live

theorem FLabel.rsup_le (L K : FLabel ν α) : K ≤ rsup L K := ⟨FCtx.rsup_wk _ _, rfl⟩

def FLabel.sup (L K : FLabel ν α) : FLabel ν α where
  param := L.param
  live := L.live.sup K.live

theorem FLabel.Cmp.lsup_eq_rsup {L K : FLabel ν α} (h : FLabel.Cmp L K)
  : lsup L K = rsup L K := by
  cases L; cases K
  cases h.param
  simp [lsup, rsup, FCtx.Cmp.lsup_eq_rsup h.live]

def FLabel.linf (L K : FLabel ν α) : FLabel ν α where
  param := L.param
  live := L.live.linf K.live

def FLabel.rinf (L K : FLabel ν α) : FLabel ν α where
  param := K.param
  live := L.live.rinf K.live

structure FLCtx (κ : Type _) (ν : Type _) (α : Type _) : Type _ where
  toFun : κ → WithBot (FLabel ν α)
  support : Finset κ
  mem_support_toFun : ∀x, x ∈ support ↔ toFun x ≠ ⊥

def FLCtx.empty (κ : Type _) (ν : Type _) (α : Type _) : FLCtx κ ν α where
  toFun _ := ⊥
  support := ∅
  mem_support_toFun x := by simp

instance FLCtx.instBot : Bot (FLCtx κ ν α) where
  bot := FLCtx.empty κ ν α

instance FLCtx.instEmptyCollection : EmptyCollection (FLCtx κ ν α) where
  emptyCollection := FLCtx.empty κ ν α

def FLCtx.singleton (x : κ) (L : FLabel ν α) : FLCtx κ ν α where
  toFun y := if y = x then L else ⊥
  support := {x}
  mem_support_toFun y := by simp

def FLCtx.splat (xs : Finset κ) (L : FLabel ν α) : FLCtx κ ν α where
  toFun y := if y ∈ xs then L else ⊥
  support := xs
  mem_support_toFun y := by simp

theorem FLCtx.toFun_inj_mp {L K : FLCtx κ ν α} (h : L.toFun = K.toFun)
  : L = K
  := match L, K with
  | ⟨fΓ, n, hm⟩, ⟨fΔ, n', hm'⟩ => by
    cases h
    simp only [mk.injEq, true_and]
    apply Finset.ext
    intro x
    rw [hm, hm']

theorem FLCtx.toFun_inj {L K : FLCtx κ ν α}
  : L = K ↔ L.toFun = K.toFun
  := ⟨(λh => by cases h; rfl), FLCtx.toFun_inj_mp⟩

--TODO: Injective instance? Naming convention...

instance FLCtx.instFunLike : FunLike (FLCtx κ ν α) κ (WithBot (FLabel ν α)) where
  coe := FLCtx.toFun
  coe_injective' := by intro Γ Δ; apply FLCtx.toFun_inj_mp

theorem FLCtx.empty_app (x : κ) : (FLCtx.empty κ ν α) x = ⊥ := rfl

theorem FLCtx.bot_app (x : κ) : (⊥ : FLCtx κ ν α) x = ⊥ := rfl

theorem FLCtx.singleton_app (x : κ) (L : FLabel ν α) (y : κ)
  : FLCtx.singleton x L y = (if y = x then ↑L else ⊥)
  := rfl

theorem FLCtx.splat_app (xs : Finset κ) (L : FLabel ν α) (y : κ)
  : FLCtx.splat xs L y = (if y ∈ xs then ↑L else ⊥)
  := rfl

theorem FLCtx.mem_support {L : FLCtx κ ν α} (ℓ : κ)
  : ℓ ∈ L.support ↔ L ℓ ≠ ⊥ := L.mem_support_toFun ℓ

theorem FLCtx.not_mem_support {L : FLCtx κ ν α} (ℓ : κ)
  : ℓ ∉ L.support ↔ L ℓ = ⊥ := by simp [mem_support]

theorem FLCtx.ext {L K : FLCtx κ ν α} (h : ∀x, L x = K x)
  : L = K
  := DFunLike.coe_injective' (by funext x; apply h)

theorem FLCtx.eq_bot_of_not_mem_support {L : FLCtx κ ν α} (x : κ) (hx : x ∉ L.support) : L x = ⊥ := by
  simp only [mem_support, ne_eq, not_not] at hx;
  exact hx

def FLCtx.cons (x : κ) (L : FLabel ν α) (K : FLCtx κ ν α) : FLCtx κ ν α where
  toFun := Function.update K.toFun x L
  support := insert x K.support
  mem_support_toFun _ := by
    simp only [Function.update]
    split <;> simp [*, mem_support_toFun]

theorem FLCtx.cons_app (x : κ) (L : FLabel ν α) (K : FLCtx κ ν α) (y : κ)
  : (FLCtx.cons x L K) y = if y = x then ↑L else K y := by simp [cons, DFunLike.coe, Function.update]

def FLCtx.get {L : FLCtx κ ν α} (x : κ) (h : x ∈ L.support) : FLabel ν α
  := (L x).get (by simp only [Option.isSome]; split; rfl; simp [mem_support, Bot.bot, *] at h)

theorem FLCtx.get_eq {L : FLCtx κ ν α} (x : κ) (h : x ∈ L.support)
  : L.get x h = L x
  := by simp [get, WithBot.some]

theorem FLCtx.splat_empty (L : FLabel ν α) : FLCtx.splat ∅ L = FLCtx.empty κ _ _ := by
  apply FLCtx.ext
  intro x
  simp [splat_app, empty_app]

theorem FLCtx.splat_empty_emp {L : FLabel ν α} : FLCtx.splat ∅ L = (∅ : FLCtx κ _ _) :=
  splat_empty L

theorem FLCtx.splat_empty_bot {L : FLabel ν α} : FLCtx.splat ∅ L = (⊥ : FLCtx κ _ _) :=
  splat_empty L

theorem FLCtx.splat_singleton (x : κ) (L : FLabel ν α)
  : FLCtx.splat {x} L = FLCtx.singleton x L := by
  apply FLCtx.ext
  intro y
  simp [splat_app, singleton_app]

-- TODO: cons lore

-- TODO: cons vs update

def FLCtx.erase (x : κ) (L : FLCtx κ ν α) : FLCtx κ ν α where
  toFun y := if y = x then ⊥ else L y
  support := L.support.erase x
  mem_support_toFun y := by
    simp only [Finset.mem_erase, mem_support_toFun]
    split <;> aesop

theorem FLCtx.erase_app (x : κ) (L : FLCtx κ ν α) (y : κ)
  : (FLCtx.erase x L) y = if y = x then ⊥ else L y := rfl

def FLCtx.Wk (L K : FLCtx κ ν α) : Prop := ∀x, L x ≤ K x

theorem FLCtx.Wk.refl (L : FLCtx κ ν α) : FLCtx.Wk L L := λ_ => le_refl _
theorem FLCtx.Wk.comp {L K M : FLCtx κ ν α} (h : FLCtx.Wk L K) (h' : FLCtx.Wk K M)
  : FLCtx.Wk L M := λx => le_trans (h x) (h' x)
theorem FLCtx.Wk.antisymm {L K : FLCtx κ ν α} (h : FLCtx.Wk L K) (h' : FLCtx.Wk K L)
  : L = K := FLCtx.ext (λx => le_antisymm (h x) (h' x))

instance FLCtx.instPartialOrder : PartialOrder (FLCtx κ ν α) where
  le L K := ∀x, L x ≤ K x
  le_refl _ := Wk.refl _
  le_trans _ _ _ h h' := Wk.comp h h'
  le_antisymm _ _ h h' := Wk.antisymm h h'

theorem FLCtx.Wk.iff_ge (L K : FLCtx κ ν α) : FLCtx.Wk L K ↔ L ≤ K := Iff.rfl
theorem FLCtx.Wk.iff_le (L K : FLCtx κ ν α) : FLCtx.Wk L K ↔ K ≥ L := Iff.rfl
theorem FLCtx.Wk.ge {L K : FLCtx κ ν α} (h : FLCtx.Wk L K) : L ≤ K := h
theorem FLCtx.Wk.le {L K : FLCtx κ ν α} (h : FLCtx.Wk L K) : K ≥ L := h
theorem FLCtx.Wk.of_ge {L K : FLCtx κ ν α} (h : K ≥ L) : FLCtx.Wk L K := h
theorem FLCtx.Wk.of_le {L K : FLCtx κ ν α} (h : L ≤ K) : FLCtx.Wk L K := h

theorem FLCtx.Wk.cons {L K : FLCtx κ ν α} (x : κ) (w : FLabel.Wk Γ Δ) (w' : FLCtx.Wk L K)
  : FLCtx.Wk (FLCtx.cons x Γ L) (FLCtx.cons x Δ K)
  := λy => if h: y = x
  then by cases h; simp only [cons_app, ↓reduceIte, WithBot.coe_le_coe]; exact w
  else by simp [cons_app, h, w' y]

theorem FLCtx.Wk.cons_refl {L K : FLCtx κ ν α} (x : κ) (Γ : FLabel ν α) (w' : FLCtx.Wk L K)
  : FLCtx.Wk (FLCtx.cons x Γ L) (FLCtx.cons x Γ K)
  := cons x (FLabel.Wk.refl _) w'

theorem FLCtx.Wk.of_cons {L : FLCtx κ ν α} (x : κ) (Γ : FLabel ν α) (hL : x ∉ L.support)
  : FLCtx.Wk L (FLCtx.cons x Γ L)
  := λy => if h: y = x
  then by cases h; simp [cons_app, eq_bot_of_not_mem_support _ hL]
  else by simp [cons_app, h]

theorem FLabel.Wk.toSingleton {L K : FLabel ν α} (x : κ) (w : FLabel.Wk L K)
  : FLCtx.Wk (FLCtx.singleton x L) (FLCtx.singleton x K)
  := λy => by
    simp only [FLCtx.singleton_app]
    split
    simp only [WithBot.coe_le_coe]
    exact w
    simp

theorem FLabel.Wk.toSplat {L K : FLabel ν α} (xs : Finset κ) (w : FLabel.Wk L K)
  : FLCtx.Wk (FLCtx.splat xs L) (FLCtx.splat xs K)
  := λy => by
    simp only [FLCtx.splat_app]
    split
    simp only [WithBot.coe_le_coe]
    exact w
    simp

def FLabel.Wk.of_le_coe {L K : FLabel ν α} (h : (L : WithBot (FLabel ν α)) ≤ (K : WithBot (FLabel ν α))) : L ≤ K
  := by simp only [WithBot.coe_le_coe] at h; exact h

def FCtx.toLabel (Γ : FCtx ν α) (param : α) : FLabel ν α where
  live := Γ
  param := param

theorem FCtx.Wk.toLabel {Γ Δ : FCtx ν α} (w : Γ.Wk Δ) (param : α)
  : (Γ.toLabel param).Wk (Δ.toLabel param) := ⟨w, rfl⟩

def FCtx.toSingleton (x : κ) (Γ : FCtx ν α) (param : α) : FLCtx κ ν α
  := FLCtx.singleton x (Γ.toLabel param)

def FCtx.toSplat (xs : Finset κ) (Γ : FCtx ν α) (param : α) : FLCtx κ ν α
  := FLCtx.splat xs (Γ.toLabel param)

def FCtx.tensor (xs : FCtx κ α) (Γ : FCtx ν α) : FLCtx κ ν α where
  toFun ℓ := if h : ℓ ∈ xs.support then Γ.toLabel (xs.get ℓ h) else ⊥
  support := xs.support
  mem_support_toFun := by simp

-- Note: this is annoying because xs here is contravariant. Should be ⊥ not ⊤, but _elas_...
theorem FCtx.tensor_app (xs : FCtx κ α) (Γ : FCtx ν α) (ℓ : κ)
  : (FCtx.tensor xs Γ) ℓ = if h : ℓ ∈ xs.support then ↑(Γ.toLabel (xs.get ℓ h)) else ⊥ := rfl

theorem FCtx.tensor_app' (xs : FCtx κ α) (Γ : FCtx ν α) (ℓ : κ)
  : (FCtx.tensor xs Γ) ℓ = match xs ℓ with | some A => Γ.toLabel A | ⊤ => ⊥ := by
  simp only [tensor_app]
  split
  case inl h => rw [FCtx.get_eq h]
  case inr h => rw [eq_top_of_not_mem_support _ h]

theorem FCtx.tensor_eq_bot (xs : FCtx κ α) (Γ : FCtx ν α) (ℓ : κ)
  : (FCtx.tensor xs Γ) ℓ = ⊥ ↔ xs ℓ = ⊤ := by simp [tensor_app, not_mem_support]

theorem FCtx.tensor_eq_bot_mp (xs : FCtx κ α) (Γ : FCtx ν α) (ℓ : κ)
  : (FCtx.tensor xs Γ) ℓ = ⊥ → xs ℓ = ⊤ := by simp [tensor_app, not_mem_support]

theorem FCtx.tensor_eq_bot_mpr (xs : FCtx κ α) (Γ : FCtx ν α) (ℓ : κ)
  : xs ℓ = ⊤ -> (FCtx.tensor xs Γ) ℓ = ⊥ := by simp [tensor_app, not_mem_support]

theorem FCtx.tensor_eq_label_param (xs : FCtx κ α) (Γ : FCtx ν α) (ℓ : κ) (L : FLabel ν α)
  : (FCtx.tensor xs Γ) ℓ = some L → xs ℓ = L.param := by
  simp only [tensor_app']
  split
  case _ h => intro h'; cases h'; rw [h]; rfl
  case _ => intro h'; contradiction

theorem FCtx.tensor_top (Γ : FCtx ν α) : FCtx.tensor ⊤ Γ = (⊥ : FLCtx κ _ _) := by
  apply FLCtx.ext
  intro x
  simp [tensor_app, FLCtx.bot_app]

def FLCtx.params (L : FLCtx κ ν α) : FCtx κ α where
  toFun ℓ := if h : ℓ ∈ L.support then (L.get ℓ h).param else ⊤
  support := L.support
  mem_support_toFun := by simp

theorem FLCtx.params_app (L : FLCtx κ ν α) (ℓ : κ)
  : L.params ℓ = if h : ℓ ∈ L.support then ↑(L.get ℓ h).param else ⊤ := rfl

theorem FLCtx.params_app' (L : FLCtx κ ν α) (ℓ : κ)
  : L.params ℓ = match L ℓ with | some Γ => Γ.param | ⊥ => ⊤ := by
  simp only [params_app]
  split
  case inl h => rw [<-L.get_eq ℓ h] -- TODO: inconsistent ordering here...
  case inr h => rw [eq_bot_of_not_mem_support _ h]

theorem FCtx.tensor_params (xs : FCtx κ α) (Γ : FCtx ν α) : (FCtx.tensor xs Γ).params = xs := by
  apply FCtx.ext
  intro x
  simp only [FLCtx.params_app']
  split
  case _ h => rw [tensor_eq_label_param _ _ _ _ h]
  case _ h => rw [tensor_eq_bot_mp _ _ _ h]

theorem FCtx.Wk.toSingleton {Γ Δ : FCtx ν α} (x : κ) (w : Γ.Wk Δ) (param : α)
  : (Γ.toSingleton x param).Wk (Δ.toSingleton x param)
  := (w.toLabel param).toSingleton x

def FLCtx.EWk (L K : FLCtx κ ν α) : Prop := ∀x, L x = K x ∨ L x = ⊥

theorem FLCtx.EWk.refl (L : FLCtx κ ν α) : FLCtx.EWk L L := λ_ => Or.inl rfl
theorem FLCtx.EWk.trans {L K M : FLCtx κ ν α} (h : FLCtx.EWk L K) (h' : FLCtx.EWk K M)
  : FLCtx.EWk L M := λx => match h x, h' x with
  | Or.inl h, Or.inl h' => Or.inl (h.trans h')
  | Or.inl h, Or.inr h' => Or.inr (h.trans h')
  | Or.inr h, _ => Or.inr h

theorem FLCtx.EWk.to_wk {L K : FLCtx κ ν α} (h : FLCtx.EWk L K) : FLCtx.Wk L K
  := λx => by cases h x <;> simp [*]
theorem FLCtx.EWk.antisymm {L K : FLCtx κ ν α} (h : FLCtx.EWk L K) (h' : FLCtx.EWk K L)
  : L = K := h.to_wk.antisymm h'.to_wk

def FLCtx.restrict (L : FLCtx κ ν α) (labels : Finset κ) : FLCtx κ ν α where
  toFun x := if x ∈ labels then L x else ⊥
  support := L.support ∩ labels
  mem_support_toFun := by simp [mem_support, And.comm]

theorem FLCtx.restrict_app (L : FLCtx κ ν α) (labels : Finset κ) (x : κ)
  : (L.restrict labels) x = if x ∈ labels then L x else ⊥ := rfl

theorem FLCtx.restrict_sub_support {L : FLCtx κ ν α} {ls : Finset κ} (hls : L.support ⊆ ls)
  : L.restrict ls = L := by
  --TODO: clean this up...
  apply ext
  intro x
  simp only [restrict_app, ite_eq_left_iff]
  intro hx
  have hx := λc => hx (Finset.mem_of_subset hls c)
  simp only [mem_support, ne_eq, imp_false, not_not] at hx
  rw [hx]

def FLCtx.Restricts (L : FLCtx κ ν α) (K : FLCtx κ ν α) : Prop := K.restrict L.support = L

theorem FLCtx.Restricts.to_ewk {L K : FLCtx κ ν α} (h : L.Restricts K) : L.EWk K
  := λℓ => by
    if h' : L ℓ = K ℓ ∨ L ℓ = ⊥ then
      exact h'
    else
      simp only [Restricts] at h
      rw [not_or, <-h, restrict_app] at h'
      split at h' <;> simp at h'

def FLCtx.EWk.restricts {L K : FLCtx κ ν α} (h : L.EWk K) : L.Restricts K
  := by
  apply FLCtx.ext
  intro ℓ
  rw [restrict_app]
  cases h ℓ with
  | inl h =>
    split
    . exact h.symm
    . apply Eq.symm
      apply eq_bot_of_not_mem_support
      assumption
  | inr h =>
    rw [<-not_mem_support] at h
    simp only [h, ↓reduceIte]
    apply Eq.symm
    rw [<-not_mem_support]
    exact h

def FLCtx.EWk.iff_restricts (L K : FLCtx κ ν α) : L.EWk K ↔ L.Restricts K
  := ⟨restricts, Restricts.to_ewk⟩

def FLCtx.Restricts.to_wk {L K : FLCtx κ ν α} (h : L.Restricts K) : L.Wk K
  := h.to_ewk.to_wk

theorem FLCtx.EWk.of_cons {L : FLCtx κ ν α} (x : κ) (Γ : FLabel ν α) (hL : x ∉ L.support)
  : FLCtx.EWk L (FLCtx.cons x Γ L)
  := λy => if h: y = x
  then by cases h; simp [cons_app, eq_bot_of_not_mem_support _ hL]
  else by simp [cons_app, h]

def FLCtx.PWk (L K : FLCtx κ ν α) : Prop := L.Wk K ∧ L.support = K.support

theorem FLCtx.PWk.refl (L : FLCtx κ ν α) : FLCtx.PWk L L
  := ⟨FLCtx.Wk.refl _, rfl⟩
theorem FLCtx.PWk.comp {L K M : FLCtx κ ν α} (h : FLCtx.PWk L K) (h' : FLCtx.PWk K M)
  : FLCtx.PWk L M := ⟨h.1.comp h'.1, h.2.trans h'.2⟩

theorem FLCtx.PWk.to_wk {L K : FLCtx κ ν α} (h : FLCtx.PWk L K) : FLCtx.Wk L K
  := h.1
theorem FLCtx.PWk.antisymm {L K : FLCtx κ ν α} (h : FLCtx.PWk L K) (h' : FLCtx.PWk K L)
  : L = K := h.to_wk.antisymm h'.to_wk

theorem FLCtx.PWk.support_eq {L K : FLCtx κ ν α} (h : FLCtx.PWk L K)
  : L.support = K.support := h.2

-- TODO: commute EWk and PWk

-- TODO: factor Wk into PWk followed by EWk _or_ EWk followed by PWk

inductive FLCtx.CmpBot : (Γ Δ : WithBot (FLabel ν α)) → Prop
  | left (Γ : WithBot (FLabel ν α)) : CmpBot Γ ⊥
  | right (Δ : WithBot (FLabel ν α)) : CmpBot ⊥ Δ
  | both {Γ Δ : FLabel ν α} : Γ.Cmp Δ -> CmpBot Γ Δ

theorem FLCtx.CmpBot.refl (Γ : WithBot (FLabel ν α)) : FLCtx.CmpBot Γ Γ
  := match Γ with
  | ⊥ => left _
  | some Γ => both (FLabel.Cmp.refl Γ)

theorem FLCtx.CmpBot.symm {Γ Δ : WithBot (FLabel ν α)}
  : FLCtx.CmpBot Γ Δ → FLCtx.CmpBot Δ Γ
  | left _ => right _
  | right _ => left _
  | both h => both h.symm

theorem FLCtx.CmpBot.of_le {Γ Δ : WithBot (FLabel ν α)} (h : Γ ≤ Δ) : FLCtx.CmpBot Γ Δ
  := match Γ, Δ with
  | ⊥, _ => right _
  | _, ⊥ => left _
  | some Γ, some Δ => both (FLabel.Cmp.of_le (by simp only [WithBot.some_le_some] at h; exact h))

def FLCtx.Cmp (L K : FLCtx κ ν α) : Prop := ∀x, CmpBot (L x) (K x)

theorem FLCtx.Cmp.refl (L : FLCtx κ ν α) : FLCtx.Cmp L L := λ_ => FLCtx.CmpBot.refl _
theorem FLCtx.Cmp.symm {L K : FLCtx κ ν α} (h : FLCtx.Cmp L K) : FLCtx.Cmp K L
  := λx => FLCtx.CmpBot.symm (h x)

theorem FLCtx.Cmp.of_le {L K : FLCtx κ ν α} (h : L ≤ K) : FLCtx.Cmp L K
  := λx => FLCtx.CmpBot.of_le (h x)
theorem FLCtx.Wk.cmp {L K : FLCtx κ ν α} (h : L.Wk K) : FLCtx.Cmp L K
  := Cmp.of_le h

def FLCtx.lsup_bot : WithBot (FLabel ν α) → WithBot (FLabel ν α) → WithBot (FLabel ν α)
  | ⊥, x => x
  | x, ⊥ => x
  | some Γ, some Δ => some (FLabel.lsup Γ Δ)

@[simp]
theorem FLCtx.bot_lsup_bot {Γ : WithBot (FLabel ν α)} : lsup_bot ⊥ Γ = Γ
  := match Γ with
  | ⊥ => rfl
  | some Γ => by simp [lsup_bot]

@[simp]
theorem FLCtx.lsup_bot_bot {Γ : WithBot (FLabel ν α)} : lsup_bot Γ ⊥ = Γ
  := match Γ with
  | ⊥ => rfl
  | some Γ => by simp [lsup_bot]

theorem FLCtx.lsup_bot_le {Γ Δ : WithBot (FLabel ν α)} : Γ ≤ lsup_bot Γ Δ
  := match Γ, Δ with
  | ⊥, _ => by simp
  | _, ⊥ => by simp
  | some Γ, some Δ => by simp [lsup_bot, FLabel.lsup_le Γ Δ]

def FLCtx.rsup_bot : WithBot (FLabel ν α) → WithBot (FLabel ν α) → WithBot (FLabel ν α)
  | ⊥, x => x
  | x, ⊥ => x
  | some Γ, some Δ => some (FLabel.rsup Γ Δ)

@[simp]
theorem FLCtx.bot_rsup_bot {Γ : WithBot (FLabel ν α)} : rsup_bot ⊥ Γ = Γ
  := match Γ with
  | ⊥ => rfl
  | some Γ => by simp [rsup_bot]

@[simp]
theorem FLCtx.rsup_bot_bot {Γ : WithBot (FLabel ν α)} : rsup_bot Γ ⊥ = Γ
  := match Γ with
  | ⊥ => rfl
  | some Γ => by simp [rsup_bot]

theorem FLCtx.rsup_bot_le {Γ Δ : WithBot (FLabel ν α)} : Δ ≤ rsup_bot Γ Δ
  := match Γ, Δ with
  | ⊥, _ => by simp
  | _, ⊥ => by simp
  | some Γ, some Δ => by simp [rsup_bot, FLabel.rsup_le Γ Δ]

theorem FLCtx.CmpBot.lsup_eq_rsup {Γ Δ : WithBot (FLabel ν α)} (h : FLCtx.CmpBot Γ Δ)
  : lsup_bot Γ Δ = rsup_bot Γ Δ := by
    simp only [lsup_bot]
    split <;> simp only [rsup_bot]
    cases h with
    | both h => rw [h.lsup_eq_rsup]

theorem FLCtx.le_lsup_bot {Γ Δ Ξ : WithBot (FLabel ν α)} (hΓ : Γ ≤ Ξ) (hΔ : Δ ≤ Ξ) : lsup_bot Γ Δ ≤ Ξ
  := match Γ, Δ with
  | ⊥, _ => by simp [hΔ]
  | _, ⊥ => by simp [hΓ]
  | some Γ, some Δ => match Ξ with
    | ⊥ => by simp at hΓ
    | some Ξ => by simp only [lsup_bot, WithBot.some_le_some] at *; exact hΓ.lsup_wk hΔ

-- TODO: lattice lore

def FLCtx.sup_bot : WithBot (FLabel ν α) → WithBot (FLabel ν α) → WithBot (FLabel ν α)
  | ⊥, x => x
  | x, ⊥ => x
  | some Γ, some Δ => if Γ.param = Δ.param then some (FLabel.sup Γ Δ) else ⊥

def FLCtx.linf_bot : WithBot (FLabel ν α) → WithBot (FLabel ν α) → WithBot (FLabel ν α)
  | ⊥, _ => ⊥
  | _, ⊥ => ⊥
  | some Γ, some Δ => some (FLabel.linf Γ Δ)

def FLCtx.rinf_bot : WithBot (FLabel ν α) → WithBot (FLabel ν α) → WithBot (FLabel ν α)
  | ⊥, _ => ⊥
  | _, ⊥ => ⊥
  | some Γ, some Δ => some (FLabel.rinf Γ Δ)

def FLCtx.lsup (L K : FLCtx κ ν α) : FLCtx κ ν α where
  toFun x := lsup_bot (L x) (K x)
  support := L.support ∪ K.support
  mem_support_toFun x := by
    simp only [Finset.mem_union, lsup_bot, mem_support]
    split <;> simp [*, Bot.bot]

theorem FLCtx.lsup_app (L K : FLCtx κ ν α) (x : κ)
  : (FLCtx.lsup L K) x = lsup_bot (L x) (K x) := rfl

theorem FLCtx.lsup_wk (L K : FLCtx κ ν α) : FLCtx.Wk L (FLCtx.lsup L K) := λx => by
  simp only [lsup_app, FLCtx.lsup_bot_le]

def FLCtx.rsup (L K : FLCtx κ ν α) : FLCtx κ ν α where
  toFun x := rsup_bot (L x) (K x)
  support := L.support ∪ K.support
  mem_support_toFun x := by
    simp only [Finset.mem_union, rsup_bot, mem_support]
    split <;> simp [*, Bot.bot]

theorem FLCtx.rsup_app (L K : FLCtx κ ν α) (x : κ)
  : (FLCtx.rsup L K) x = rsup_bot (L x) (K x) := rfl

theorem FLCtx.rsup_wk (L K : FLCtx κ ν α) : FLCtx.Wk K (FLCtx.rsup L K) := λx => by
  simp only [rsup_app, FLCtx.rsup_bot_le]

theorem FLCtx.Cmp.lsup_eq_rsup {L K : FLCtx κ ν α} (h : FLCtx.Cmp L K)
  : FLCtx.lsup L K = FLCtx.rsup L K := by
  apply FLCtx.ext
  intro x
  simp only [FLCtx.lsup_app, FLCtx.rsup_app]
  exact FLCtx.CmpBot.lsup_eq_rsup (h x)

theorem FLCtx.Cmp.lsup_wk_left {L K : FLCtx κ ν α} (_ : FLCtx.Cmp L K)
  : FLCtx.Wk L (FLCtx.lsup L K) := lsup_wk L K
theorem FLCtx.Cmp.lsup_wk_right {L K : FLCtx κ ν α} (h : FLCtx.Cmp L K)
  : FLCtx.Wk K (FLCtx.lsup L K) := h.lsup_eq_rsup ▸ rsup_wk L K
theorem FLCtx.Cmp.rsup_wk_left {L K : FLCtx κ ν α} (h : FLCtx.Cmp L K)
  : FLCtx.Wk L (FLCtx.rsup L K) := h.lsup_eq_rsup ▸ lsup_wk L K
theorem FLCtx.Cmp.rsup_wk_right {L K : FLCtx κ ν α} (_ : FLCtx.Cmp L K)
  : FLCtx.Wk K (FLCtx.rsup L K) := rsup_wk L K

theorem FLCtx.Wk.lsup_wk {L L' K : FLCtx κ ν α} (hL : L.Wk K) (hL' : L'.Wk K) : (L.lsup L').Wk K
  := λx => le_lsup_bot (hL x) (hL' x)

inductive FLCtx.PCmpBot : (Γ Δ : WithBot (FLabel ν α)) → Prop
  | left (Γ : WithBot (FLabel ν α)) : PCmpBot Γ ⊥
  | right (Δ : WithBot (FLabel ν α)) : PCmpBot ⊥ Δ
  | both {Γ Δ : FLabel ν α} : Γ.param = Δ.param -> PCmpBot Γ Δ

def FLCtx.PCmp (L K : FLCtx κ ν α) : Prop := ∀x, PCmpBot (L x) (K x)

inductive FCtx.LEqBot (Γ : FCtx ν α) : (Δ : WithBot (FLabel ν α)) → Prop
  | bot : LEqBot Γ ⊥
  | refl (A) : LEqBot Γ (some ⟨Γ, A⟩)

def FCtx.LEq (Γ : FCtx ν α) (L : FLCtx κ ν α) : Prop := ∀x, Γ.LEqBot (L x)

-- TODO: LEq Γ iff = tensor Γ params

-- TODO: LWk Γ iff ≤ₚ tensor Γ params

theorem FCtx.singletonLEq (x : κ) (Γ : FCtx ν α) (param : α) : Γ.LEq (Γ.toSingleton x param)
  := λy => by
    simp only [toSingleton, FLCtx.singleton_app]
    split <;> constructor

theorem FCtx.LEqBot.lsup {Γ : FCtx ν α} {Δ Ξ : WithBot (FLabel ν α)}
  : Γ.LEqBot Δ → Γ.LEqBot Ξ → Γ.LEqBot (FLCtx.lsup_bot Δ Ξ)
  | bot, _ => by simp [*]
  | _, bot => by simp [*]
  | refl A, refl A' => by
    simp only [FLCtx.lsup_bot, FLabel.lsup, FCtx.lsup_idem]
    exact refl A

theorem FCtx.LEq.lsup {Γ : FCtx ν α} {L K : FLCtx κ ν α}
  (hL : Γ.LEq L) (hK : Γ.LEq K) : Γ.LEq (L.lsup K)
  := λx => (hL x).lsup (hK x)

inductive FCtx.LWkBot (Γ : FCtx ν α) : (Δ : WithBot (FLabel ν α)) → Prop
  | bot : LWkBot Γ ⊥
  | wk (A) : Γ.Wk Δ → LWkBot Γ (some ⟨Δ, A⟩)

theorem FCtx.LEqBot.toLWkBot {Γ : FCtx ν α} {Δ : WithBot (FLabel ν α)}
  : Γ.LEqBot Δ → Γ.LWkBot Δ
  | bot => LWkBot.bot
  | refl A => LWkBot.wk A (Wk.refl _)

--BUG: says hΔ' and hΞ' are unused, which is obviously not the case...
theorem FCtx.LWkBot.cmp₂ {Γ : FCtx ν α} {Δ Ξ M : WithBot (FLabel ν α)}
  (hΔ : Γ.LWkBot Δ) (hΞ : Γ.LWkBot Ξ) (_hΔ' : Δ ≤ M) (_hΞ' : Ξ ≤ M)
  : FLCtx.CmpBot Δ Ξ
  := match hΔ, hΞ with
  | bot, _ => by constructor
  | _, bot => by constructor
  | wk A w, wk A' w' => by
    constructor
    cases M with
    | none =>
      --BUG: kernel says invalid projection if done that way, investigate
      have ⟨_, h, _⟩ := (_hΔ' _ rfl)
      cases h
    | some M =>
      cases M
      simp only [WithBot.some_le_some] at *
      cases _hΔ'.param
      cases _hΞ'.param
      exact ⟨w.cmp₂ w', rfl⟩

def FCtx.LWk (Γ : FCtx ν α) (L : FLCtx κ ν α) : Prop := ∀x, Γ.LWkBot (L x)

theorem FCtx.LWk.cmp₂ {L K M : FLCtx κ ν α} {Γ : FCtx ν α}
  (hL : Γ.LWk L) (hK : Γ.LWk K) (hLM : L.Wk M) (hKM : K.Wk M)
  : L.Cmp K
  := λx => (hL x).cmp₂ (hK x) (hLM x) (hKM x)

theorem FCtx.LEq.toLWk {Γ : FCtx ν α} {L : FLCtx κ ν α} (hΓ : Γ.LEq L) : Γ.LWk L
  := λx => (hΓ x).toLWkBot

 -- TODO: lawful

-- TODO: RWk, RWk to cmp...

--TODO: lattice lore

--TODO: ECmp and PCmp

--TODO: *strict* lattice lore; need a wrapper or smt...

--TODO: tfw we just overloaded things :(
