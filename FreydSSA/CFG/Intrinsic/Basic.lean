import FreydSSA.BasicBlock.Intrinsic.Basic

inductive InstSet.ICFG
  [Φ : InstSet φ (Ty α)]
  : (L K : LCtx ν κ (Ty α)) -> Type _
  | nil : L.Wk K → Φ.ICFG L K
  | cons : Φ.ICFG L (⟨ℓ, A, Γ⟩::K) → Φ.BB (⟨x, A⟩::Γ) L → Φ.ICFG L K

def InstSet.ICFG.wk_exit
  [Φ : InstSet φ (Ty α)] {L K M : LCtx ν κ (Ty α)}
  : (κ: Φ.ICFG L K) → K.Wk M → Φ.ICFG L M
  | nil w, w' => nil (w.comp w')
  | cons κ β, w' => cons (κ.wk_exit (w'.cons (Label.Wk.refl _))) β

structure InstSet.CFG [Φ : InstSet φ (Ty α)] (L K : LCtx ν κ (Ty α))
  where
  looped : L.Wk W
  inner : Φ.ICFG W K

def InstSet.CFG.wk_exit
  [Φ : InstSet φ (Ty α)] {L K M : LCtx ν κ (Ty α)}
  (κ: Φ.CFG L K) (w: K.Wk M): Φ.CFG L M where
  looped := κ.looped
  inner := κ.inner.wk_exit w

def InstSet.CFG.wk_entry
  [Φ : InstSet φ (Ty α)] {L K M : LCtx ν κ (Ty α)}
  (w: L.Wk K) (κ: Φ.CFG K M): Φ.CFG L M where
  looped := w.comp κ.looped
  inner := κ.inner
