import Mathlib.Data.List.Basic
import Std.Data.List.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Init.Classical

import FreydSSA.Ctx
import FreydSSA.InstSet
import FreydSSA.Tm
import FreydSSA.Body

inductive InstSet.Terminator
  (Φ : InstSet (Ty α)) (Γ : Ctx ν (Ty α)) (L : LCtx ν κ (Ty α))
  : Type _
  | br : Φ.Tm 1 Γ A → LCtx.Wk [⟨ℓ, A, Γ⟩] L → Φ.Terminator Γ L
  | ite : Φ.Tm 1 Γ Ty.bool → Φ.Terminator Γ L → Φ.Terminator Γ L → Φ.Terminator Γ L

def InstSet.Terminator.wk_entry {Φ : InstSet (Ty α)}
  (w: Γ.Wk Δ): Φ.Terminator Δ L → Φ.Terminator Γ L
  | br e h => br (e.wk w) --TODO: clean this up
    (@LCtx.Wk.comp _ _ _ [⟨_, _, Γ⟩] [⟨_, _, Δ⟩] _
      (LCtx.Wk.cons ⟨rfl, rfl, w⟩ LCtx.Wk.nil) h)
  | ite e t f => ite (e.wk w) (t.wk_entry w) (f.wk_entry w)

def InstSet.Terminator.wk_exit {Φ: InstSet (Ty α)}
  : Φ.Terminator Γ L → L.Wk K → Φ.Terminator Γ K
  | br e h, w => br e (h.comp w)
  | ite e t f, w => ite e (t.wk_exit w) (f.wk_exit w)

structure InstSet.BB (Φ : InstSet (Ty α)) (Γ : Ctx ν (Ty α)) (L : LCtx ν κ (Ty α)) where
  body: Φ.Body p Γ Δ
  -- Issue: underspecified: can change Δ, so must quotient somehow
  terminator: Φ.Terminator Δ L

def InstSet.BB.wk_entry {Φ : InstSet (Ty α)}
  (w: Γ.Wk Δ) (β: Φ.BB Δ L): Φ.BB Γ L where
  body := β.body.wk_entry w
  terminator := β.terminator

def InstSet.BB.wk_exit {Φ : InstSet (Ty α)}
  (β: Φ.BB Γ L) (w: L.Wk K): Φ.BB Γ K where
  body := β.body
  terminator := β.terminator.wk_exit w

inductive InstSet.ICFG
  (Φ : InstSet (Ty α))
  : (L K : LCtx ν κ (Ty α)) -> Type _
  | nil : L.Wk K → InstSet.ICFG Φ L K
  | cons : InstSet.ICFG Φ L (⟨ℓ, A, Γ⟩::K) → Φ.BB (⟨x, A⟩::Γ) L → InstSet.ICFG Φ L K

def InstSet.ICFG.wk_exit
  {Φ : InstSet (Ty α)} {L K M : LCtx ν κ (Ty α)}
  : (κ: Φ.ICFG L K) → K.Wk M → Φ.ICFG L M
  | nil w, w' => nil (w.comp w')
  | cons κ β, w' => cons (κ.wk_exit (w'.cons (Label.Wk.refl _))) β

structure InstSet.CFG (Φ : InstSet (Ty α)) (L K : LCtx ν κ (Ty α))
  where
  looped : L.Wk W
  inner : Φ.ICFG W K

def InstSet.CFG.wk_exit
  {Φ : InstSet (Ty α)} {L K M : LCtx ν κ (Ty α)}
  (κ: Φ.CFG L K) (w: K.Wk M): Φ.CFG L M where
  looped := κ.looped
  inner := κ.inner.wk_exit w

def InstSet.CFG.wk_entry
  {Φ : InstSet (Ty α)} {L K M : LCtx ν κ (Ty α)}
  (w: L.Wk K) (κ: Φ.CFG K M): Φ.CFG L M where
  looped := w.comp κ.looped
  inner := κ.inner

structure InstSet.Region (Φ : InstSet (Ty α)) (Γ : Ctx ν (Ty α)) (L : LCtx ν κ (Ty α)) where
  entry : Φ.BB Γ K
  -- Issue: underspecified: can change K, so must quotient somehow
  cfg : Φ.ICFG K L

inductive GCtx (ν κ : Type u) (α : Type v) where
  | ctx : Ctx ν α → GCtx ν κ α
  | lctx : LCtx ν κ α → GCtx ν κ α

inductive InstSet.GRegion (Φ : InstSet (Ty α)) : GCtx ν κ (Ty α) → LCtx ν κ (Ty α) → Type _
  | br : Φ.Tm 1 Γ A → LCtx.Wk [⟨ℓ, A, Γ⟩] L → Φ.GRegion (GCtx.ctx Γ) L
  | ite : Φ.Tm 1 Γ Ty.bool
    → Φ.GRegion (GCtx.ctx Γ) L
    → Φ.GRegion (GCtx.ctx Γ) L
    → Φ.GRegion (GCtx.ctx Γ) L
  | dom : Φ.GRegion (GCtx.ctx Γ) K → Φ.GRegion (GCtx.lctx L) K → Φ.GRegion (GCtx.ctx Γ) L
  | nil : L.Wk K → Φ.GRegion (GCtx.lctx L) K
  | cons : Φ.GRegion (GCtx.lctx L) (⟨ℓ, A, Γ⟩::K) → Φ.BB (⟨x, A⟩::Γ) L → Φ.GRegion (GCtx.lctx L) K
