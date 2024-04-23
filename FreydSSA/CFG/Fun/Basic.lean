import FreydSSA.BasicBlock.Fun.Basic

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

inductive UCFG.FWfIL : FLCtx κ ν (Ty α) → UCFG φ (Ty α) ν κ → FLCtx κ ν (Ty α) → Type _
  | nil : L.Wk K → FWfIL L nil K
  | cons (ℓ x A) : FWfIL L g (K.cons ℓ Γℓ) → β.FWf 0 (Γℓ.toFCtx x) L → FWfIL L (g.cons ℓ x A β) K

def UCFG.FWfIL.wkExit {L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K K' : FLCtx κ ν (Ty α)}
  (dg : FWfIL L g K) (w : K.Wk K') : FWfIL L g K'
  := match dg with
  | nil w' => nil $ w'.comp w
  | cons ℓ x A dg dβ => cons ℓ x A (dg.wkExit (w.cons_refl ℓ _)) dβ

inductive UCFG.FWfI : FLCtx κ ν (Ty α) → UCFG φ (Ty α) ν κ → FLCtx κ ν (Ty α) → Type _
  | nil : L.Wk K → FWfI L nil K
  | cons (ℓ x A) : FWfI L g (K.cons ℓ Γℓ) → β.FWf 0 (Γℓ.toFCtx x) L → FWfI L (g.cons ℓ x A β) K
  | dead (ℓ x A) : FWfI L g K → ℓ ∉ L.support → FWfI L (g.cons ℓ x A β) K

def UCFG.FWfI.wkExit {L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K K' : FLCtx κ ν (Ty α)}
  (dg : FWfI L g K) (w : K.Wk K') : FWfI L g K'
  := match dg with
  | nil w' => nil $ w'.comp w
  | cons ℓ x A dg dβ => cons ℓ x A (dg.wkExit (w.cons_refl ℓ _)) dβ
  | dead ℓ x A dg hℓ => dead ℓ x A (dg.wkExit w) hℓ

inductive UCFG.FWfILM : FLCtx κ ν (Ty α) → UCFG φ (Ty α) ν κ → FLCtx κ ν (Ty α) → Type _
  | nil (L) : FWfILM L nil L
  | cons (ℓ x A) : FWfILM L g (K.cons ℓ Γℓ) → β.FWf 0 (Γℓ.toFCtx x) L → FWfILM L (g.cons ℓ x A β) K

-- Note: if there are multiple definitions for g, this forces us to ignore them _all_
-- More subtle hax could allow us to redefine things... but later...
inductive UCFG.FWfIM : FLCtx κ ν (Ty α) → UCFG φ (Ty α) ν κ → FLCtx κ ν (Ty α) → Type _
  | nil (L) : FWfIM L nil L
  | cons (ℓ Γℓ x A) : FWfIM L g (K.cons ℓ Γℓ) → ℓ ∉ K.support → β.FWf 0 (Γℓ.toFCtx x) L
    → FWfIM L (g.cons ℓ x A β) K
  | dead (ℓ x A) : FWfIM L g K → ℓ ∉ L.support → FWfIM L (g.cons ℓ x A β) K

-- TODO: transformation lore

-- TODO: composition lore

-- TODO: minimal variants?

-- TODO: uniqueness and friends?
