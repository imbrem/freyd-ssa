import FreydSSA.CFG.Fun.Basic
import FreydSSA.BasicBlock.Fun.Subst

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

-- def UCFG.FWfIL.subst {L' L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
--   (hσ : L'.PSubstCons σ L N) (dg : g.FWfIL L K) (hN : g.defs.toFinset ⊆ N) (hσc : {x | x ∈ g.defs}.EqOn σ UTm.var)
--   : ΣK', (g.rewrite σ).FWfIL L' K' × K'.SubstCons σ K N
--   := ⟨
--     sorry,
--     sorry,
--     sorry
--   ⟩

-- def UCFG.FWfI.subst {L' L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
--   (hσ : L'.Subst σ L) (dg : g.FWfI L K) (hσc : {x | x ∈ g.defs}.EqOn σ UTm.var)
--   : ΣK', (g.rewrite σ).FWfI L' K' × K'.Subst σ K := sorry
