import Mathlib.Data.List.Basic

structure Var (ν : Type u) (α : Type v) : Type (max u v) where
  name: ν
  ty: α

def Ctx (ν: Type u) (α: Type v): Type (max u v) := List (Var ν α)

inductive Ctx.notin {ν α} (n : ν) : Ctx ν α → Prop
  | nil : Ctx.notin n []
  | cons {Γ x} : x.name ≠ n → Ctx.notin n Γ → Ctx.notin n (x::Γ)

theorem Ctx.notin.head {ν α} {n} {y : Var ν α} {Γ : Ctx ν α}
  : Ctx.notin n (y::Γ) → y.name ≠ n
  | cons hxn _ => hxn

inductive Ctx.wk {ν: Type u} {α: Type v} : Ctx ν α → Ctx ν α → Type (max u v)
  | nil : Ctx.wk [] []
  | cons {Γ Δ} (x : Var ν α) : Ctx.wk Γ Δ → Ctx.wk (x::Γ) (x::Δ)
  | skip {Γ Δ} : Ctx.notin x.name Δ → Ctx.wk Γ Δ → Ctx.wk (x::Γ) Δ

theorem Ctx.notin.wk {ν α} {Γ Δ: Ctx ν α} {n: ν}: notin n Γ → Γ.wk Δ → notin n Δ
  | _, wk.nil => nil
  | cons hxn hn, wk.cons _ h => cons hxn (hn.wk h)
  | cons _ hn, wk.skip _ h => hn.wk h

def Ctx.wk.comp {ν α} {Γ Δ Ξ : Ctx ν α} : Γ.wk Δ → Δ.wk Ξ → Γ.wk Ξ
  | nil, h => h
  | cons x h, cons _ h' => cons x (h.comp h')
  | cons _ h, skip hn h' => skip hn (h.comp h')
  | skip hn h, h' => skip (hn.wk h') (h.comp h')

theorem Ctx.wk.allEq {ν α} {Γ Δ : Ctx ν α} (D D': Γ.wk Δ): D = D'
  := by induction D with
  | nil => cases D'; rfl
  | cons _ _ I => cases D' with
    | cons => exact congrArg _ (I _)
    | skip hxn => exact (hxn.head rfl).elim
  | skip hxn _ I => cases D' with
    | cons _ _ => exact (hxn.head rfl).elim
    | skip h I' => exact congrArg _ (I I')

def Ctx.wk.refl {ν α}: (Γ : Ctx ν α) → Γ.wk Γ
  | [] => nil
  | x::Γ => cons x (refl Γ)

--TODO: antisymm...

inductive Ty (α: Type u): Type u where
  | base (a : α)
  | pair (a b : Ty α)
  | unit

inductive Purity
  | pure
  | impure

instance : OfNat Purity 0 where
  ofNat := Purity.impure

instance : OfNat Purity 1 where
  ofNat := Purity.pure

--TODO: make into struct parameter?
class InstSet (α : Type u) : Type _ where
  inst : Purity → α → α → Type
  pure_to_impure : inst 1 a b -> inst 0 a b

def InstSet.to_impure {α : Type u} [InstSet α] {p} {a b : α} (f: inst p a b)
  : inst 0 a b
  := match p with
  | Purity.pure => pure_to_impure f
  | Purity.impure => f

inductive Tm {ν : Type u} {α : Type v} [InstSet (Ty α)]
  : Purity -> Ctx ν (Ty α) → Ty α → Type (max u v) where
  | var (p) : Γ.wk [x] → Tm p Γ x.ty
  | op (f: InstSet.inst p a b) : Tm 1 Γ a → Tm p Γ b
  | pair (p) : Tm 1 Γ a → Tm 1 Γ b → Tm p Γ (Ty.pair a b)
  | unit (p) : Tm p Γ Ty.unit

def Tm.to_impure [InstSet (Ty α)] {a: Ty α} : Tm p Γ a → Tm 0 Γ a
  | var p h => var 0 h
  | op f e => op (InstSet.to_impure f) e
  | pair p x y => pair 0 x y
  | unit p => unit 0

def Tm.wk [InstSet (Ty α)] {a: Ty α} : Γ.wk Δ -> Tm p Δ a -> Tm p Γ a
  | h, var p h' => var p (h.comp h')
  | h, op f e => op f (wk h e)
  | h, pair p x y => pair p (wk h x) (wk h y)
  | h, unit p => unit p

inductive Body {ν: Type u} {α: Type v} [InstSet (Ty α)]
  : Purity -> Ctx ν (Ty α) -> Ctx ν (Ty α) -> Type (max u v) where
  | nil (p) : Γ.wk Δ -> Body p Γ Δ
  | let1 : Tm p Γ a -> Body p (⟨x, a⟩::Γ) Δ -> Body p Γ Δ
  | let2 : Tm p Γ (Ty.pair a b)
    -> Body p (⟨x, b⟩::⟨y, a⟩::Γ) Δ
    -> Body p Γ Δ

def Body.to_impure {Γ Δ: Ctx ν (Ty α)} [InstSet (Ty α)] : Body p Γ Δ → Body 0 Γ Δ
  | nil _ h => nil 0 h
  | let1 e b => let1 e.to_impure b.to_impure
  | let2 e b => let2 e.to_impure b.to_impure

def Body.wk_entry {Γ Δ Ξ: Ctx ν (Ty α)} [InstSet (Ty α)]
  : Γ.wk Δ -> Body p Δ Ξ -> Body p Γ Ξ
  | h, nil p h' => nil p (h.comp h')
  | h, let1 e b => let1 (Tm.wk h e) (wk_entry (h.cons _) b)
  | h, let2 e b => let2 (Tm.wk h e) (wk_entry ((h.cons _).cons _) b)

def Body.wk_exit {Γ Δ Ξ: Ctx ν (Ty α)} [InstSet (Ty α)]
  : Body p Γ Δ -> Δ.wk Ξ -> Body p Γ Ξ
  | nil p h, h' => nil p (h.comp h')
  | let1 e b, h' => let1 e (wk_exit b h')
  | let2 e b, h' => let2 e (wk_exit b h')

def Body.cat {Γ Δ Ξ: Ctx ν (Ty α)} [InstSet (Ty α)]
  : Body p Γ Δ -> Body p Δ Ξ -> Body p Γ Ξ
  | nil p h, b => wk_entry h b
  | let1 e b, b' => let1 e (cat b b')
  | let2 e b, b' => let2 e (cat b b')
