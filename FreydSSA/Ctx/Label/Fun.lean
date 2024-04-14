import FreydSSA.Ctx.Var.Fun

variable {ν : Type u₁} {ν' : Type u₂} {κ : Type u₃} {κ' : Type u₄} {α : Type u₅} {β : Type u₆}
  [DecidableEq ν] [DecidableEq ν']
  [DecidableEq κ] [DecidableEq κ']
  [DecidableEq α] [DecidableEq β]

structure FLabel (ν : Type _) (α : Type _) where
  -- TODO: Fun with parameter contexts? Parameter sets? Many options...
  live : FCtx ν α
  param : α

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
  param : L.param = K.param
  live : L.live.Cmp K.live

theorem FLabel.Cmp.refl (L : FLabel ν α) : FLabel.Cmp L L := ⟨rfl, FCtx.Cmp.refl _⟩
theorem FLabel.Cmp.symm {L K : FLabel ν α} (h : FLabel.Cmp L K) : FLabel.Cmp K L
  := ⟨h.param.symm, h.live.symm⟩

theorem FLabel.Cmp.of_le {L K : FLabel ν α} (h : L ≤ K) : FLabel.Cmp L K
  := ⟨h.param, FCtx.Cmp.of_wk h.live⟩
theorem FLabel.Cmp.of_le₂ {L K M : FLabel ν α} (h : M ≤ L) (h' : M ≤ K) : FLabel.Cmp L K
  := ⟨h.param.symm.trans h'.param, h.live.cmp₂ h'.live⟩

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

def FLCtx.singleton (x : κ) (L : FLabel ν α) : FLCtx κ ν α where
  toFun y := if y = x then L else ⊥
  support := {x}
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

theorem FLCtx.singleton_app (x : κ) (L : FLabel ν α) (y : κ)
  : FLCtx.singleton x L y = (if y = x then ↑L else ⊥)
  := rfl

theorem FLCtx.mem_support {L : FLCtx κ ν α} (ℓ : κ)
  : ℓ ∈ L.support ↔ L ℓ ≠ ⊥ := L.mem_support_toFun ℓ

theorem FLCtx.ext {L K : FLCtx κ ν α} (h : ∀x, L x = K x)
  : L = K
  := DFunLike.coe_injective' (by funext x; apply h)

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

theorem FLabel.Wk.toSingleton {L K : FLabel ν α} (x : κ) (w : FLabel.Wk L K)
  : FLCtx.Wk (FLCtx.singleton x L) (FLCtx.singleton x K)
  := λy => by
    simp only [FLCtx.singleton_app]
    split
    simp only [WithBot.coe_le_coe]
    exact w
    simp

def FCtx.toLabel (Γ : FCtx ν α) (param : α) : FLabel ν α where
  live := Γ
  param := param

theorem FCtx.Wk.toLabel {Γ Δ : FCtx ν α} (w : Γ.Wk Δ) (param : α)
  : (Γ.toLabel param).Wk (Δ.toLabel param) := ⟨w, rfl⟩

def FCtx.toSingleton (x : κ) (Γ : FCtx ν α) (param : α) : FLCtx κ ν α
  := FLCtx.singleton x (Γ.toLabel param)

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

def FLCtx.PWk (L K : FLCtx κ ν α) : Prop := ∀x, L x ≤ K x ∧ (K x = ⊥ -> L x = ⊥)

theorem FLCtx.PWk.refl (L : FLCtx κ ν α) : FLCtx.PWk L L
  := λ_ => ⟨le_refl _, by intro; trivial⟩
theorem FLCtx.PWk.trans {L K M : FLCtx κ ν α} (h : FLCtx.PWk L K) (h' : FLCtx.PWk K M)
  : FLCtx.PWk L M := λx => match h x, h' x with
  | ⟨h, h'⟩, ⟨h'', h'''⟩ => ⟨h.trans h'', h' ∘ h'''⟩

theorem FLCtx.PWk.to_wk {L K : FLCtx κ ν α} (h : FLCtx.PWk L K) : FLCtx.Wk L K
  := λx => (h x).left
theorem FLCtx.PWk.antisymm {L K : FLCtx κ ν α} (h : FLCtx.PWk L K) (h' : FLCtx.PWk K L)
  : L = K := h.to_wk.antisymm h'.to_wk

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

-- TODO: LEq to cmp...

inductive FCtx.LWkBot (Γ : FCtx ν α) : (Δ : WithBot (FLabel ν α)) → Prop
  | bot : LWkBot Γ ⊥
  | wk (A Δ) : Γ.Wk Δ → LWkBot Γ (some ⟨Δ, A⟩)

def FCtx.LWk (Γ : FCtx ν α) (L : FLCtx κ ν α) : Prop := ∀x, Γ.LWkBot (L x)

-- TODO: RWk, RWk to cmp...

--TODO: lattice lore

--TODO: ECmp and PCmp

--TODO: *strict* lattice lore; need a wrapper or smt...

--TODO: tfw we just overloaded things :(
