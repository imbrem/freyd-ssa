import FreydSSA.Ctx.Var
import FreydSSA.Ctx.Var.Fun

variable {ν ν' α β} [DecidableEq ν] [DecidableEq ν'] [DecidableEq α]

structure TCtx (α : Type v) : Type _ where
  length : ℕ
  ty : Fin length → α

def TCtx.nil : TCtx α := ⟨0, λi => i.elim0⟩
def TCtx.cons (A : α) (Γ : TCtx α) : TCtx α := ⟨Γ.length + 1, Fin.cons A Γ.ty⟩

--TODO: get extensionality

theorem TCtx.length_zero_eq_nil {Γ : TCtx α} (h : Γ.length = 0) : Γ = TCtx.nil := by
  cases Γ
  cases h
  simp only [nil, mk.injEq, heq_eq_eq, true_and] at *
  funext i
  exact i.elim0

theorem TCtx.length_zero_eq {Γ Δ : TCtx α} (hΓ : Γ.length = 0) (hΔ : Δ.length = 0) : Γ = Δ
  := Γ.length_zero_eq_nil hΓ ▸ Δ.length_zero_eq_nil hΔ ▸ rfl

def TCtx.append (Γ Δ : TCtx α) : TCtx α := ⟨Γ.length + Δ.length, Fin.append Γ.ty Δ.ty⟩

def TCtx.fromList : List α → TCtx α
  | [] => TCtx.nil
  | A :: Γ => TCtx.cons A (TCtx.fromList Γ)

def TCtx.toList : TCtx α → List α
  | ⟨0, _⟩ => []
  | ⟨n+1, ty⟩ => ty 0 :: TCtx.toList ⟨n, λi => ty i.succ⟩

theorem TCtx.toList_fromList (Γ : List α) : (TCtx.fromList Γ).toList = Γ := by
  induction Γ with
  | nil => rfl
  | cons A Γ I =>
    simp only [toList, fromList, cons]
    congr 1

theorem TCtx.fromList_toList : (Γ : TCtx α) → TCtx.fromList Γ.toList = Γ := by
  intro ⟨n, Γi⟩
  induction n with
  | zero => exact length_zero_eq rfl rfl
  | succ n I =>
    simp only [toList]
    rw [fromList, cons, I]
    simp only [mk.injEq, heq_eq_eq, true_and]
    funext ⟨i, hi⟩
    cases i <;> rfl

theorem TCtx.toList_length : (Γ : TCtx α) → Γ.toList.length = Γ.length := by
  intro ⟨n, Γi⟩
  induction n with
  | zero => rfl
  | succ n I =>
    simp only [toList]
    rw [List.length_cons, I]

theorem TCtx.fromList_length (Γ : List α) : (TCtx.fromList Γ).length = Γ.length := by
  induction Γ with
  | nil => rfl
  | cons A Γ I =>
    simp only [fromList, cons, length]
    rw [I]
    rfl

def TCtx.map (f : α → β) (Γ : TCtx α) : TCtx β := ⟨Γ.length, f ∘ Γ.ty⟩

theorem TCtx.fromList_map {f : α → β} (Γ : List α) : (TCtx.fromList (Γ.map f)) = (TCtx.fromList Γ).map f := by
  induction Γ with
  | nil => exact length_zero_eq rfl rfl
  | cons A Γ I =>
    simp only [fromList, map, cons, mk.injEq, heq_eq_eq, true_and, I]
    funext ⟨i, hi⟩
    cases i <;> rfl

theorem TCtx.toList_map {f : α → β} : (Γ : TCtx α) → (Γ.map f).toList = Γ.toList.map f := by
  intro ⟨n, Γi⟩
  induction n with
  | zero => rfl
  | succ n I =>
    simp only [toList, map]
    rw [List.map, <-I]
    rfl

structure ICtx (ν : Type u) (α : Type v) extends TCtx α : Type (max u v) where
  name : Fin length → ν

def ICtx.map (f: α → β) (Γ : ICtx ν α) : ICtx ν β := ⟨Γ.toTCtx.map f, Γ.name⟩
def ICtx.map_names (f : ν → ν') (Γ : ICtx ν α) : ICtx ν' α := ⟨Γ.toTCtx, f ∘ Γ.name⟩

--TODO: ICtx ≅ Ctx
--TODO: TCtx iso preservation...

structure IFCtx (ν : Type u) (α : Type v) extends ICtx (WithBot ν) α : Type (max u v) where
  no_shadow : ∀ i j, name i = name j -> name i = ⊥ ∨ i = j

def IFCtx.map (f: α → β) (Γ : IFCtx ν α) : IFCtx ν β := ⟨Γ.toICtx.map f, Γ.no_shadow⟩
--TODO: IFCtx name mapping

structure ISCtx (ν : Type u) (α : Type v) extends ICtx ν α : Type (max u v) where
  nodup : Function.Injective name

def ISCtx.map (f: α → β) (Γ : ISCtx ν α) : ISCtx ν β := ⟨Γ.toICtx.map f, Γ.nodup⟩
--TODO: ISCtx name mapping

structure FICtx (ν : Type u) (α : Type v) extends TCtx α : Type (max u v) where
  ix : FCtx ν (Fin length)
  injective : Function.Injective ix

def FICtx.map (f: α → β) (Γ : FICtx ν α) : FICtx ν β := ⟨Γ.toTCtx.map f, Γ.ix, Γ.injective⟩
--TODO: FICtx name mapping

--TODO: map functions, positional map functions

--TODO: ICtx → (IFCtx, FICtx)

--TODO: FICtx ≅ IFCtx, TCtx equal...
--TODO: ISCtx → IFCtx via map_names coe

def TCtx.Var (Γ : TCtx α) (A : α) (i : Fin Γ.length) : Prop := Γ.ty i = A

--TODO: factor out ix for Wk variants? can then use subset types...

structure TCtx.Wk (Γ : TCtx α) (Δ : TCtx α) (ρ : Fin Δ.length → Fin Γ.length) : Prop where
  ty_eq : ∀i, Γ.ty (ρ i) = Δ.ty i
  injective : Function.Injective ρ

theorem TCtx.id (Γ : TCtx α) : TCtx.Wk Γ Γ id where
  ty_eq _ := rfl
  injective := Function.injective_id

theorem TCtx.comp {Γ Δ Ξ : TCtx α} {ρ σ} (hρ : TCtx.Wk Γ Δ ρ) (hσ : TCtx.Wk Δ Ξ σ) : TCtx.Wk Γ Ξ (ρ ∘ σ) where
  ty_eq i := by rw [Function.comp, hρ.ty_eq, hσ.ty_eq]
  injective := hρ.injective.comp hσ.injective

theorem TCtx.Var.wk {Γ Δ : TCtx α} {ρ A i} (hρ : TCtx.Wk Γ Δ ρ) (h : Δ.Var A i) : Γ.Var A (ρ i)
  := (hρ.ty_eq i).trans h

structure ICtx.Var (Γ : ICtx ν α) (x : ν) (A : α) (i : Fin Γ.length) : Prop where
  ix_name : Γ.name i = x
  ix_ty : Γ.ty i = A
  ix_last : ∀j, Γ.name j = x → j ≤ i

structure IFCtx.Var (Γ : IFCtx ν α) (x : ν) (A : α) (i : Fin Γ.length) : Prop where
  ix_name : Γ.name i = x
  ix_ty : Γ.ty i = A

--TODO: IFCtx.Var ↔ ICtx.Var (using toICtx)

structure ISCtx.Var (Γ : ISCtx ν α) (x : ν) (A : α) (i : Fin Γ.length) extends Γ.toICtx.Var x A i : Prop where
  ix_last _ hj := le_of_eq (Γ.nodup (hj.trans ix_name.symm))

--TODO: nicer constructors?

structure FICtx.Var (Γ : FICtx ν α) (x : ν) (A : α) (i : Fin Γ.length) : Prop where
  ix_name : Γ.ix x = i
  ix_ty : Γ.ty i = A

-- *syntactic* weakening, in which shadowed variables are simply ignored
def ICtx.VWk (Γ : ICtx ν α) (Δ : ICtx ν α) (ρ : Fin Δ.length → Fin Γ.length) := ∀{x A i}, Δ.Var x A i → Γ.Var x A (ρ i)

-- *semantic* weakening, which can be interpreted nicely for affine variables
-- Note that the _names_ of shadowed variables don't matter
structure ICtx.Wk (Γ : ICtx ν α) (Δ : ICtx ν α) (ρ : Fin Δ.length → Fin Γ.length) extends TCtx.Wk Γ.toTCtx Δ.toTCtx ρ : Prop where
  var : ∀{x A i}, Δ.Var x A i → Γ.Var x A (ρ i)

theorem ICtx.Var.wk {Γ Δ : ICtx ν α} {ρ x A i} (hρ : ICtx.Wk Γ Δ ρ) (h : Δ.Var x A i) : Γ.Var x A (ρ i)
  := hρ.var h

-- *strict* weakening, which does not swap variables, and respects all variable names
structure ICtx.SWk (Γ : ICtx ν α) (Δ : ICtx ν α) (ρ : Fin Δ.length → Fin Γ.length) extends Wk Γ Δ ρ : Prop where
  name_eq : ∀i, Γ.name (ρ i) = Δ.name i
  monotone : Monotone ρ

-- theorem ICtx.SWk.wk_eq {Γ Δ : ICtx ν α} {ρ σ} (hρ : ICtx.SWk Γ Δ ρ) (hσ : ICtx.SWk Γ Δ σ) : ρ = σ := by
--   funext i

--TODO: Strict weakning ≅ Ctx weakening, or think about this...

--TODO: Weakening _preorder_ on ICtx

--TODO: Connection between FCtx and ICtx

--TODO: ICtx comparability

structure IFCtx.VWk (Γ : IFCtx ν α) (Δ : IFCtx ν α) (ρ : Fin Δ.length → Fin Γ.length) extends TCtx.Wk Γ.toTCtx Δ.toTCtx ρ : Prop where
  var : ∀{x A i}, Δ.Var x A i → Γ.Var x A (ρ i)

structure IFCtx.Wk (Γ : IFCtx ν α) (Δ : IFCtx ν α) (ρ : Fin Δ.length → Fin Γ.length) extends TCtx.Wk Γ.toTCtx Δ.toTCtx ρ : Prop where
  name_eq : ∀i, Γ.name (ρ i) = Δ.name i

--TODO: IFCtx.Wk --> IFCtx.VWk

structure ISCtx.Wk (Γ : ISCtx ν α) (Δ : ISCtx ν α) (ρ : Fin Δ.length → Fin Γ.length) extends TCtx.Wk Γ.toTCtx Δ.toTCtx ρ : Prop where
  name_eq : ∀i, Γ.name (ρ i) = Δ.name i

structure FICtx.Wk (Γ : FICtx ν α) (Δ : FICtx ν α) (ρ : Fin Δ.length → Fin Γ.length) extends TCtx.Wk Γ.toTCtx Δ.toTCtx ρ : Prop where
  name_eq : ∀x, (Δ.ix x).map ρ ⊆ Γ.ix x
