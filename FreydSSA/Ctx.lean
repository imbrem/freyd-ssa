import Mathlib.Data.List.Basic
import Std.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Init.Classical

open List.«term_<+_»

structure Var (ν : Type u) (α : Type v) : Type (max u v) where
  name: ν
  ty: α

def Ctx (ν : Type u) (α : Type v) : Type (max u v) := List (Var ν α)

@[simp]
def Ctx.names {ν α} (Γ : Ctx ν α): List ν
  := Γ.map Var.name

inductive Ctx.Fresh {ν α} (n : ν) : Ctx ν α → Prop
  | nil : Ctx.Fresh n []
  | cons {Γ x} : x.name ≠ n → Ctx.Fresh n Γ → Ctx.Fresh n (x::Γ)

theorem Ctx.Fresh.head {ν α} {n} {y : Var ν α} {Γ : Ctx ν α}
  : Ctx.Fresh n (y::Γ) → y.name ≠ n
  | cons hxn _ => hxn

theorem Ctx.Fresh.tail {ν α} {n} {y : Var ν α} {Γ : Ctx ν α}
  : Ctx.Fresh n (y::Γ) → Ctx.Fresh n Γ
  | cons _ hn => hn

inductive Ctx.Wk {ν: Type u} {α: Type v} : Ctx ν α → Ctx ν α → Type (max u v)
  | nil : Ctx.Wk [] []
  | cons {Γ Δ} (x : Var ν α) : Ctx.Wk Γ Δ → Ctx.Wk (x::Γ) (x::Δ)
  | skip {Γ Δ} : Ctx.Fresh x.name Δ → Ctx.Wk Γ Δ → Ctx.Wk (x::Γ) Δ

theorem Ctx.Fresh.wk {ν α} {Γ Δ: Ctx ν α} {n: ν}: Fresh n Γ → Γ.Wk Δ → Fresh n Δ
  | _, Wk.nil => nil
  | cons hxn hn, Wk.cons _ h => cons hxn (hn.wk h)
  | cons _ hn, Wk.skip _ h => hn.wk h

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

def Ctx.Wk.drop {ν α} : (Γ : Ctx ν α) → Γ.Wk []
  | [] => nil
  | _::Γ => skip Fresh.nil (drop Γ)

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

inductive Ctx.HasVar {ν α : Type u} (A : α) : ℕ → Ctx ν α → Prop
  | head : Ctx.HasVar A 0 (⟨n, A⟩::Γ)
  | tail : Ctx.HasVar A n Γ → Ctx.HasVar A (n+1) (x::Γ)

structure Ctx.Ix {ν α} (Γ : Ctx ν α) (A : α) : Type where
  val : ℕ
  hasVar : Ctx.HasVar A val Γ

structure Label (ν : Type u) (α : Type v) extends Var ν α where
  live : Ctx ν α

structure Label.Wk (ℓ ℓ' : Label ν α) where
  var : ℓ.toVar = ℓ'.toVar
  live : ℓ.live.Wk ℓ'.live

def Label.Wk.refl (ℓ : Label ν α) : ℓ.Wk ℓ := ⟨rfl, Ctx.Wk.refl _⟩

def Label.Wk.comp {ℓ ℓ' ℓ'' : Label ν α} (w : ℓ.Wk ℓ') (w' : ℓ'.Wk ℓ'') : ℓ.Wk ℓ''
  := ⟨w.var.trans w'.var, w.live.comp w'.live⟩

abbrev Label.Wk.Iso {ℓ ℓ' ℓ'' ℓ''' : Label ν α} (w : ℓ.Wk ℓ') (w' : ℓ''.Wk ℓ''')
  := w.live.Iso w'.live

structure Label.Fresh (ℓ : Label ν α) (n : ν): Prop where
  name : ℓ.name ≠ n
  live : ℓ.live.Fresh n

def LCtx (ν: Type u) (α: Type v) := List (Label ν α)

inductive LCtx.Fresh {ν α} (n : ν) : LCtx ν α → Prop
  | nil : LCtx.Fresh n []
  | cons : ℓ.Fresh n → Fresh n L → Fresh n (ℓ::L)

theorem LCtx.Fresh.head {ν α} {n} {ℓ : Label ν α} {L : LCtx ν α}
  : LCtx.Fresh n (ℓ::L) → ℓ.Fresh n
  | cons hxn _ => hxn

theorem LCtx.Fresh.tail {ν α} {n} {ℓ : Label ν α} {L : LCtx ν α}
  : LCtx.Fresh n (ℓ::L) → L.Fresh n
  | cons _ h => h

inductive LCtx.Wk {ν : Type u} {α : Type v} : LCtx ν α → LCtx ν α → Type (max u v)
  | nil : Wk [] []
  | cons {ℓ ℓ' : Label ν α} : ℓ.Wk ℓ' → Wk L K → Wk (ℓ::L) (ℓ'::K)
  | skip (ℓ : Label ν α) : Wk L K → Wk L (ℓ::K) --TODO: freshness?

def LCtx.Wk.comp {L K M : LCtx ν α} : L.Wk K → K.Wk M → L.Wk M
  | Wk.nil, w => w
  | Wk.cons h w, Wk.cons h' w' => Wk.cons (h.comp h') (w.comp w')
  | Wk.skip _ w, Wk.cons h w' => Wk.skip _ (w.comp w')
  | w, Wk.skip ℓ w' => Wk.skip _ (w.comp w')

inductive LCtx.Wk.Iso : {L K : LCtx ν α} → {L' K' : LCtx ν' α'} → Wk L K → Wk L' K' → Prop
  | nil : Iso nil nil
  | cons : h.Iso h' → Iso w w' → Iso (cons h w) (cons h' w')
  | skip (ℓ ℓ') : Iso w w' → Iso (skip ℓ w) (skip ℓ' w')

theorem LCtx.Wk.Iso.refl {L K : LCtx ν α} : (w: L.Wk K) → w.Iso w
  | Wk.nil => nil
  | Wk.cons h w => cons h.live.iso_refl (refl w)
  | Wk.skip _ w => skip _ _ (refl w)

theorem LCtx.Wk.Iso.symm {L K : LCtx ν α} {L' K' : LCtx ν' α'}
  {w: L.Wk K} {w': L'.Wk K'} : (h: w.Iso w') → w'.Iso w
  | nil => nil
  | cons h w => cons h.symm w.symm
  | skip _ _ w => skip _ _ w.symm

theorem LCtx.Wk.Iso.trans {L K : LCtx ν α} {L' K' : LCtx ν' α'} {L'' K'' : LCtx ν'' α''}
  {w: L.Wk K} {w': L'.Wk K'} {w'': L''.Wk K''} : (h: w.Iso w') → (h': w'.Iso w'') → w.Iso w''
  | nil, nil => nil
  | cons h w, cons h' w' => cons (h.trans h') (w.trans w')
  | skip _ _ w, skip _ _ w' => skip _ _ (w.trans w')

theorem LCtx.Wk.Iso.comp {L K M : LCtx ν α} {L' K' M' : LCtx ν' α'}
  {l: L.Wk K} {r: K.Wk M} {l': L'.Wk K'} {r': K'.Wk M'}
  (hl: l.Iso l') (hr: r.Iso r'): (l.comp r).Iso (l'.comp r') := by
  induction hr generalizing L
  <;> cases hl
  <;> repeat first | apply Ctx.Wk.Iso.comp | apply_assumption | constructor
