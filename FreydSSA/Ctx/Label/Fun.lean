import FreydSSA.Ctx.Var.Fun

variable {ν ν' κ κ' α β}
  [DecidableEq ν] [DecidableEq ν']
  [DecidableEq κ] [DecidableEq κ']
  [DecidableEq α] [DecidableEq β]

structure FLabel (ν : Type _) (α : Type _) where
  -- TODO: Fun with parameter contexts? Parameter sets? Many options...
  param : α
  live : FCtx ν α

theorem FLabel.ext {L K : FLabel ν α} (h : L.param = K.param) (h' : L.live = K.live)
  : L = K := by
  cases L; cases K
  cases h; cases h'
  rfl

structure FLabel.Wk (L K : FLabel ν α) : Prop where
  param : L.param = K.param
  live : L.live.Wk K.live

theorem FLabel.Wk.refl (L : FLabel ν α) : FLabel.Wk L L := ⟨rfl, FCtx.Wk.refl _⟩
theorem FLabel.Wk.comp {L K M : FLabel ν α} (h : FLabel.Wk L K) (h' : FLabel.Wk K M)
  : FLabel.Wk L M := ⟨h.param ▸ h'.param, h.live.comp h'.live⟩
theorem FLabel.Wk.antisymm {L K : FLabel ν α} (h : FLabel.Wk L K) (h' : FLabel.Wk K L)
  : L = K := FLabel.ext h.param (h.live.antisymm h'.live)

instance FLabel.instPartialOrder : PartialOrder (FLabel ν α) where
  le L K := FLabel.Wk K L
  le_refl _ := FLabel.Wk.refl _
  le_trans _ _ _ h h' := h'.comp h
  le_antisymm _ _ h h' := Wk.antisymm h' h

structure FLabel.Cmp (L K : FLabel ν α) : Prop where
  param : L.param = K.param
  live : L.live.Cmp K.live

theorem FLabel.Cmp.refl (L : FLabel ν α) : FLabel.Cmp L L := ⟨rfl, FCtx.Cmp.refl _⟩
theorem FLabel.Cmp.symm {L K : FLabel ν α} (h : FLabel.Cmp L K) : FLabel.Cmp K L
  := ⟨h.param.symm, h.live.symm⟩

def FLabel.linf (L K : FLabel ν α) : FLabel ν α where
  param := L.param
  live := L.live.linf K.live

def FLabel.rinf (L K : FLabel ν α) : FLabel ν α where
  param := K.param
  live := L.live.rinf K.live

def FLabel.inf (L K : FLabel ν α) : FLabel ν α where
  param := L.param
  live := L.live.inf K.live

def FLabel.lsup (L K : FLabel ν α) : FLabel ν α where
  param := L.param
  live := L.live.lsup K.live

def FLabel.rsup (L K : FLabel ν α) : FLabel ν α where
  param := K.param
  live := L.live.rsup K.live

structure FLCtx (κ : Type _) (ν : Type _) (α : Type _) : Type _ where
  toFun : κ → WithTop (FLabel ν α)
  support : Finset κ
  mem_support_toFun : ∀x, x ∈ support ↔ toFun x ≠ ⊤

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

instance FLCtx.instFunLike : FunLike (FLCtx κ ν α) κ (WithTop (FLabel ν α)) where
  coe := FLCtx.toFun
  coe_injective' := by intro Γ Δ; apply FLCtx.toFun_inj_mp

theorem FLCtx.ext {L K : FLCtx κ ν α} (h : ∀x, L x = K x)
  : L = K
  := DFunLike.coe_injective' (by funext x; apply h)

def FLCtx.Wk (L K : FLCtx κ ν α) : Prop := ∀x, L x ≥ K x

theorem FLCtx.Wk.refl (L : FLCtx κ ν α) : FLCtx.Wk L L := λ_ => le_refl _
theorem FLCtx.Wk.comp {L K M : FLCtx κ ν α} (h : FLCtx.Wk L K) (h' : FLCtx.Wk K M)
  : FLCtx.Wk L M := λx => le_trans (h' x) (h x)
theorem FLCtx.Wk.antisymm {L K : FLCtx κ ν α} (h : FLCtx.Wk L K) (h' : FLCtx.Wk K L)
  : L = K := FLCtx.ext (λx => le_antisymm (h' x) (h x))

instance FLCtx.instPartialOrder : PartialOrder (FLCtx κ ν α) where
  le L K := ∀x, L x ≤ K x
  le_refl _ := Wk.refl _
  le_trans _ _ _ h h' := Wk.comp h' h
  le_antisymm _ _ h h' := Wk.antisymm h' h

theorem FLCtx.Wk.iff_ge (L K : FLCtx κ ν α) : FLCtx.Wk L K ↔ L ≥ K := Iff.rfl
theorem FLCtx.Wk.iff_le (L K : FLCtx κ ν α) : FLCtx.Wk L K ↔ K ≤ L := Iff.rfl
theorem FLCtx.Wk.ge {L K : FLCtx κ ν α} (h : FLCtx.Wk L K) : L ≥ K := h
theorem FLCtx.Wk.le {L K : FLCtx κ ν α} (h : FLCtx.Wk L K) : K ≤ L := h
theorem FLCtx.Wk.of_ge {L K : FLCtx κ ν α} (h : L ≥ K) : FLCtx.Wk L K := h
theorem FLCtx.Wk.of_le {L K : FLCtx κ ν α} (h : K ≤ L) : FLCtx.Wk L K := h

def FLCtx.EWk (L K : FLCtx κ ν α) : Prop := ∀x, L x = K x ∨ L x = ⊤

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

def FLCtx.PWk (L K : FLCtx κ ν α) : Prop := ∀x, L x ≥ K x ∧ (K x = ⊤ -> L x = ⊤)

theorem FLCtx.PWk.refl (L : FLCtx κ ν α) : FLCtx.PWk L L
  := λ_ => ⟨le_refl _, by intro; trivial⟩
theorem FLCtx.PWk.trans {L K M : FLCtx κ ν α} (h : FLCtx.PWk L K) (h' : FLCtx.PWk K M)
  : FLCtx.PWk L M := λx => match h x, h' x with
  | ⟨h, h'⟩, ⟨h'', h'''⟩ => ⟨h''.trans h, h' ∘ h'''⟩

theorem FLCtx.PWk.to_wk {L K : FLCtx κ ν α} (h : FLCtx.PWk L K) : FLCtx.Wk L K
  := λx => (h x).left
theorem FLCtx.PWk.antisymm {L K : FLCtx κ ν α} (h : FLCtx.PWk L K) (h' : FLCtx.PWk K L)
  : L = K := h.to_wk.antisymm h'.to_wk

def FLCtx.CmpTop : WithTop (FLabel ν α) → WithTop (FLabel ν α) → Prop
  | ⊤, _ => true
  | _, ⊤ => true
  | some Γ, some Δ => Γ.Cmp Δ

theorem FLCtx.CmpTop.refl (Γ : WithTop (FLabel ν α)) : FLCtx.CmpTop Γ Γ
  := match Γ with
  | ⊤ => by trivial
  | some Γ => FLabel.Cmp.refl Γ

theorem FLCtx.CmpTop.symm {Γ Δ : WithTop (FLabel ν α)} (h : FLCtx.CmpTop Γ Δ)
  : FLCtx.CmpTop Δ Γ := by
  cases Γ <;> cases Δ
  case some.some => exact FLabel.Cmp.symm h
  all_goals exact h

def FLCtx.Cmp (L K : FLCtx κ ν α) : Prop := ∀x, CmpTop (L x) (K x)

theorem FLCtx.Cmp.refl (L : FLCtx κ ν α) : FLCtx.Cmp L L := λ_ => FLCtx.CmpTop.refl _
theorem FLCtx.Cmp.symm {L K : FLCtx κ ν α} (h : FLCtx.Cmp L K) : FLCtx.Cmp K L
  := λx => FLCtx.CmpTop.symm (h x)

def FLCtx.linf_top : WithTop (FLabel ν α) → WithTop (FLabel ν α) → WithTop (FLabel ν α)
  | ⊤, x => x
  | x, ⊤ => x
  | some Γ, some Δ => some (FLabel.linf Γ Δ)

def FLCtx.rinf_top : WithTop (FLabel ν α) → WithTop (FLabel ν α) → WithTop (FLabel ν α)
  | ⊤, x => x
  | x, ⊤ => x
  | some Γ, some Δ => some (FLabel.rinf Γ Δ)

def FLCtx.inf_top : WithTop (FLabel ν α) → WithTop (FLabel ν α) → WithTop (FLabel ν α)
  | ⊤, _ => ⊤
  | _, ⊤ => ⊤
  | some Γ, some Δ => if Γ.param = Δ.param then some (FLabel.inf Γ Δ) else ⊤

def FLCtx.lsup_top : WithTop (FLabel ν α) → WithTop (FLabel ν α) → WithTop (FLabel ν α)
  | ⊤, _ => ⊤
  | _, ⊤ => ⊤
  | some Γ, some Δ => some (FLabel.lsup Γ Δ)

def FLCtx.rsup_top : WithTop (FLabel ν α) → WithTop (FLabel ν α) → WithTop (FLabel ν α)
  | ⊤, _ => ⊤
  | _, ⊤ => ⊤
  | some Γ, some Δ => some (FLabel.rsup Γ Δ)

-- def FLCtx.linf (L K : FLCtx κ ν α) : FLCtx κ ν α where
--   toFun x := linf_top (L x) (K x)
--   support := L.support ∩ K.support
--   mem_support_toFun x := sorry

-- def FLCtx.rinf (L K : FLCtx κ ν α) : FLCtx κ ν α where
--   toFun x := rinf_top (L x) (K x)
--   support := L.support ∩ K.support
--   mem_support_toFun x := sorry

-- def FLCtx.inf (L K : FLCtx κ ν α) : FLCtx κ ν α where
--   toFun x := inf_top (L x) (K x)
--   support := sorry
--   mem_support_toFun x := sorry

-- def FLCtx.lsup (L K : FLCtx κ ν α) : FLCtx κ ν α where
--   toFun x := lsup_top (L x) (K x)
--   support := L.support ∪ K.support
--   mem_support_toFun x := sorry

-- def FLCtx.rsup (L K : FLCtx κ ν α) : FLCtx κ ν α where
--   toFun x := rsup_top (L x) (K x)
--   support := L.support ∪ K.support
--   mem_support_toFun x := sorry

--TODO: lattice lore

--TODO: ECmp and PCmp

--TODO: *strict* lattice lore; need a wrapper or smt...
