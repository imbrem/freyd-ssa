import FreydSSA.Body.Intrinsic.Basic
import FreydSSA.Terminator.Intrinsic.Basic

structure InstSet.BB [Φ : InstSet φ (Ty α)] (Γ : Ctx ν (Ty α)) (L : LCtx ν κ (Ty α)) where
  body: Φ.Body p Γ Δ
  -- Issue: underspecified: can change Δ, so must quotient somehow
  -- Or need intrinsic version of WfM...
  terminator: Φ.Terminator Δ L

def InstSet.BB.wk_entry [Φ : InstSet φ (Ty α)]
  (w: Γ.Wk Δ) (β: Φ.BB Δ L): Φ.BB Γ L where
  body := β.body.wk_entry w
  terminator := β.terminator

def InstSet.BB.wk_exit [Φ : InstSet φ (Ty α)]
  (β: Φ.BB Γ L) (w: L.Wk K): Φ.BB Γ K where
  body := β.body
  terminator := β.terminator.wk_exit w
