import FreydSSA.Ctx.Var.Fun

variable {ν ν' κ κ' α β}
  [DecidableEq ν] [DecidableEq ν']
  [DecidableEq κ] [DecidableEq κ']
  [DecidableEq α] [DecidableEq β]

structure Label (ν : Type _) (α : Type _) where
  -- TODO: Fun with parameter contexts? Parameter sets? Many options...
  param : α
  live : FCtx ν α

theorem Label.ext {L K : Label ν α} (h : L.param = K.param) (h' : L.live = K.live)
  : L = K := by
  cases L; cases K
  cases h; cases h'
  rfl

structure Label.Wk (L K : Label ν α) : Prop where
  param : L.param = K.param
  live : L.live.Wk K.live

theorem Label.Wk.refl (L : Label ν α) : Label.Wk L L := ⟨rfl, FCtx.Wk.refl _⟩
theorem Label.Wk.comp {L K M : Label ν α} (h : Label.Wk L K) (h' : Label.Wk K M)
  : Label.Wk L M := ⟨h.param ▸ h'.param, h.live.comp h'.live⟩
theorem Label.Wk.antisymm {L K : Label ν α} (h : Label.Wk L K) (h' : Label.Wk K L)
  : L = K := Label.ext h.param (h.live.antisymm h'.live)

instance Label.instPartialOrder : PartialOrder (Label ν α) where
  le L K := Label.Wk K L
  le_refl _ := Label.Wk.refl _
  le_trans _ _ _ h h' := h'.comp h
  le_antisymm _ _ h h' := Wk.antisymm h' h

structure Label.Cmp (L K : Label ν α) : Prop where
  param : L.param = K.param
  live : L.live.Cmp K.live

theorem Label.Cmp.refl (L : Label ν α) : Label.Cmp L L := ⟨rfl, FCtx.Cmp.refl _⟩
theorem Label.Cmp.symm {L K : Label ν α} (h : Label.Cmp L K) : Label.Cmp K L
  := ⟨h.param.symm, h.live.symm⟩

def Label.linf (L K : Label ν α) : Label ν α where
  param := L.param
  live := L.live.linf K.live

def Label.rinf (L K : Label ν α) : Label ν α where
  param := K.param
  live := L.live.rinf K.live

def Label.inf (L K : Label ν α) : Label ν α where
  param := L.param
  live := L.live.inf K.live

def Label.lsup (L K : Label ν α) : Label ν α where
  param := L.param
  live := L.live.lsup K.live

def Label.rsup (L K : Label ν α) : Label ν α where
  param := K.param
  live := L.live.rsup K.live

structure FLCtx (κ : Type _) (ν : Type _) (α : Type _) : Type _ where
  toFun : κ → WithTop (Label ν α)
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

instance FLCtx.instFunLike : FunLike (FLCtx κ ν α) κ (WithTop (Label ν α)) where
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

def FLCtx.CmpTop : WithTop (Label ν α) → WithTop (Label ν α) → Prop
  | ⊤, _ => true
  | _, ⊤ => true
  | some Γ, some Δ => Γ.Cmp Δ

theorem FLCtx.CmpTop.refl (Γ : WithTop (Label ν α)) : FLCtx.CmpTop Γ Γ
  := match Γ with
  | ⊤ => by trivial
  | some Γ => Label.Cmp.refl Γ

theorem FLCtx.CmpTop.symm {Γ Δ : WithTop (Label ν α)} (h : FLCtx.CmpTop Γ Δ)
  : FLCtx.CmpTop Δ Γ := by
  cases Γ <;> cases Δ
  case some.some => exact Label.Cmp.symm h
  all_goals exact h

def FLCtx.Cmp (L K : FLCtx κ ν α) : Prop := ∀x, CmpTop (L x) (K x)

theorem FLCtx.Cmp.refl (L : FLCtx κ ν α) : FLCtx.Cmp L L := λ_ => FLCtx.CmpTop.refl _
theorem FLCtx.Cmp.symm {L K : FLCtx κ ν α} (h : FLCtx.Cmp L K) : FLCtx.Cmp K L
  := λx => FLCtx.CmpTop.symm (h x)

def FLCtx.linf_top : WithTop (Label ν α) → WithTop (Label ν α) → WithTop (Label ν α)
  | ⊤, x => x
  | x, ⊤ => x
  | some Γ, some Δ => some (Label.linf Γ Δ)

def FLCtx.rinf_top : WithTop (Label ν α) → WithTop (Label ν α) → WithTop (Label ν α)
  | ⊤, x => x
  | x, ⊤ => x
  | some Γ, some Δ => some (Label.rinf Γ Δ)

def FLCtx.inf_top : WithTop (Label ν α) → WithTop (Label ν α) → WithTop (Label ν α)
  | ⊤, _ => ⊤
  | _, ⊤ => ⊤
  | some Γ, some Δ => if Γ.param = Δ.param then some (Label.inf Γ Δ) else ⊤

def FLCtx.lsup_top : WithTop (Label ν α) → WithTop (Label ν α) → WithTop (Label ν α)
  | ⊤, _ => ⊤
  | _, ⊤ => ⊤
  | some Γ, some Δ => some (Label.lsup Γ Δ)

def FLCtx.rsup_top : WithTop (Label ν α) → WithTop (Label ν α) → WithTop (Label ν α)
  | ⊤, _ => ⊤
  | _, ⊤ => ⊤
  | some Γ, some Δ => some (Label.rsup Γ Δ)

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
