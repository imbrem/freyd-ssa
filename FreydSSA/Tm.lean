import Mathlib.Data.List.Basic
import Std.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Init.Classical

import FreydSSA.Ctx
import FreydSSA.InstSet

inductive InstSet.Tm {ν : Type u} {α : Type v} (Φ : InstSet (Ty α))
  : Purity → Ctx ν (Ty α) → Ty α → Type (max u v) where
  | var {n A} (p) : Γ.Wk [⟨n, A⟩] → Tm Φ p Γ A
  | op (f: Φ.Op p A B) : Tm Φ 1 Γ A → Tm Φ p Γ B
  | pair (p) : Tm Φ 1 Γ A → Tm Φ 1 Γ B → Tm Φ p Γ (Ty.pair A B)
  | unit (p) : Tm Φ p Γ Ty.unit
  | bool (p) (b: Bool) : Tm Φ p Γ Ty.bool

def InstSet.Tm.var_head {Φ : InstSet (Ty α)} (p)
  (x : ν) (A : Ty α) (Γ : Ctx ν (Ty α)) : Φ.Tm p (⟨x, A⟩::Γ) A
  := Tm.var p (Ctx.Wk.head _ _)

inductive InstSet.Tm.IsoSh {Φ : InstSet (Ty α)}: Φ.Tm p Γ A → Φ.Tm p' Γ' A' → Prop
  | var (p p') : w.Iso w' → IsoSh (Tm.var p w) (Tm.var p' w')
  | op (f) : Tm.IsoSh e e' → IsoSh (Tm.op f e) (Tm.op f e')
  | pair (p p') : Tm.IsoSh l l' → Tm.IsoSh r r' → IsoSh (Tm.pair p l r) (Tm.pair p' l' r')
  | unit (p p') : IsoSh (Tm.unit p) (Tm.unit p')
  | bool (p p') : IsoSh (Tm.bool p b) (Tm.bool p' b)

inductive InstSet.Tm.Iso {Φ : InstSet (Ty α)}: Φ.Tm p Γ A → Φ.Tm p Γ' A → Prop
  | var {Γ: Ctx ν (Ty α)} {Γ': Ctx ν' (Ty α)} (p)
    {w: Γ.Wk [⟨n, a⟩]} {w': Γ'.Wk [⟨n', a⟩]}: w.Iso w' → Iso (Tm.var p w) (Tm.var p w')
  | op (f) : Tm.Iso e e' → Iso (Tm.op f e) (Tm.op f e')
  | pair (p) : Tm.Iso l l' → Tm.Iso r r' → Iso (Tm.pair p l r) (Tm.pair p l' r')
  | unit (p) : Iso (Tm.unit p) (Tm.unit p)
  | bool (p) : Iso (Tm.bool p b) (Tm.bool p b)

theorem InstSet.Tm.Iso.refl {Φ : InstSet (Ty α)} {Γ : Ctx ν (Ty α)} {A : Ty α} {e : Φ.Tm p Γ A}
  : e.Iso e
  := by induction e with
  | var => constructor; apply Ctx.Wk.Iso.refl
  | _ => constructor <;> apply_assumption

--TODO: isomorphic terms for the same context are equal!

theorem InstSet.Tm.Iso.symm {Φ : InstSet (Ty α)}
  {e : Φ.Tm p Γ A} {e' : Φ.Tm p Γ' A}
  (h : e.Iso e') : e'.Iso e
  := by induction h with
  | var _ I => constructor; exact I.symm
  | _ => constructor <;> apply_assumption

theorem InstSet.Tm.Iso.trans {Φ : InstSet (Ty α)}
  {e : Φ.Tm p Γ A} {e' : Φ.Tm p Γ' A} {e'' : Φ.Tm p Γ'' A}
  (h : e.Iso e') (h' : e'.Iso e'') : e.Iso e''
  := by induction h with
  | var _ I => cases h'; constructor; apply I.trans; assumption
  | _ => cases h'; constructor <;> apply_assumption <;> assumption

def InstSet.Tm.to_impure {Φ : InstSet (Ty α)} {A : Ty α} : Φ.Tm p Γ A → Φ.Tm 0 Γ A
  | var p h => var 0 h
  | op f e => op (Φ.to_impure f) e
  | pair p x y => pair 0 x y
  | unit p => unit 0
  | bool p b => bool 0 b

instance {Φ : InstSet (Ty α)} : Coe (Φ.Tm 1 Γ A) (Φ.Tm p Γ A) where
  coe := match p with
    | 1 => id
    | 0 => InstSet.Tm.to_impure

def InstSet.Tm.wk {Φ : InstSet (Ty α)} {A : Ty α} : Γ.Wk Δ → Φ.Tm p Δ A → Φ.Tm p Γ A
  | h, var p h' => var p (h.comp h')
  | h, op f e => op f (wk h e)
  | h, pair p x y => pair p (wk h x) (wk h y)
  | h, unit p => unit p
  | h, bool p b => bool p b

theorem InstSet.Tm.Iso.wk {Φ : InstSet (Ty α)}
  {Γ Δ : Ctx ν (Ty α)} {Γ' Δ' : Ctx ν' (Ty α)}
  {w : Γ.Wk Δ} {w' : Γ'.Wk Δ'}
  {e : Φ.Tm p Δ A} {e' : Φ.Tm p Δ' A}
  (hw : w.Iso w') (he : e.Iso e') : (e.wk w).Iso (e'.wk w')
  := by induction he with
  | var => simp only [Tm.wk]; constructor; apply Ctx.Wk.Iso.comp <;> assumption
  | _ => simp only [Tm.wk]; constructor <;> apply_assumption <;> assumption

def InstSet.Tm.deBruijn {Φ : InstSet (Ty α)} {Γ : Ctx ν (Ty α)} {A : Ty α} (n: ℕ)
  : Φ.Tm p Γ A → Φ.Tm p (Γ.deBruijn n) A
  | var p w => var p (w.var_deBruijn n)
  | op f e => op f (e.deBruijn n)
  | pair p l r => pair p (l.deBruijn n) (r.deBruijn n)
  | unit p => unit p
  | bool p b => bool p b

theorem InstSet.Tm.deBruijn_iso {Φ : InstSet (Ty α)} {Γ : Ctx ν (Ty α)} {A : Ty α}
  (e: Φ.Tm p Γ A) : e.Iso (e.deBruijn n)
  := by induction e with
  | var p w => simp only [deBruijn]; exact Iso.var p (w.iso_var_deBruijn n)
  | _ => simp only [deBruijn]; constructor <;> assumption

def InstSet.Tm.rename {Φ : InstSet (Ty α)} {Γ : Ctx ν (Ty α)} {a : Ty α}
  {ρ : ν → ν'} (hρ : Γ.InjOn ρ) : Φ.Tm p Γ a → Φ.Tm p (Γ.rename ρ) a
  | var p h' => @var _ _ _ _ (ρ _) _ p (h'.rename hρ)
  | op f e => op f (e.rename hρ)
  | pair p l r => pair p (l.rename hρ) (r.rename hρ)
  | unit p => unit p
  | bool p b => bool p b

theorem InstSet.Tm.rename_iso {Φ : InstSet (Ty α)} {Γ : Ctx ν (Ty α)} {a : Ty α}
  {ρ : ν → ν'} (hρ : Γ.InjOn ρ) (e: Φ.Tm p Γ a) : e.Iso (e.rename hρ)
  := by induction e with
  | @var Γ n a p w => simp only [rename]; constructor; exact w.rename_iso hρ
  | _ => simp only [rename]; constructor <;> apply_assumption
