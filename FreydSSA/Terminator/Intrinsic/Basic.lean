import FreydSSA.Term.Intrinsic.Basic

inductive InstSet.Terminator
  [Φ : InstSet φ (Ty α)] (Γ : Ctx ν (Ty α)) (L : LCtx ν κ (Ty α))
  : Type _
  | br : Φ.Tm 1 Γ A → LCtx.Wk [⟨ℓ, A, Γ⟩] L → Φ.Terminator Γ L
  | ite : Φ.Tm 1 Γ Ty.bool → Φ.Terminator Γ L → Φ.Terminator Γ L → Φ.Terminator Γ L

def InstSet.Terminator.wk_entry [Φ : InstSet φ (Ty α)]
  (w: Γ.Wk Δ): Φ.Terminator Δ L → Φ.Terminator Γ L
  | br e h => br (e.wk w) --TODO: clean this up
    (@LCtx.Wk.comp _ _ _ [⟨_, _, Γ⟩] [⟨_, _, Δ⟩] _
      (LCtx.Wk.cons ⟨rfl, rfl, w⟩ LCtx.Wk.nil) h)
  | ite e t f => ite (e.wk w) (t.wk_entry w) (f.wk_entry w)

def InstSet.Terminator.wk_exit [Φ : InstSet φ (Ty α)]
  : Φ.Terminator Γ L → L.Wk K → Φ.Terminator Γ K
  | br e h, w => br e (h.comp w)
  | ite e t f, w => ite e (t.wk_exit w) (f.wk_exit w)
