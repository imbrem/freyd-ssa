import FreydSSA.CFG.Extrinsic.Basic
import FreydSSA.BasicBlock.Extrinsic.Subst

variable {φ ν κ α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

-- def UCFG.WfIL.subst {σ : ν → UTm ν φ} {L L' : LCtx ν κ (Ty α)} {g : UCFG φ (Ty α) ν κ} (hσ : L.Subst σ L')
--   : g.WfIL L K → g.WfIL L' K := sorry

-- def UCFG.WfI.subst {σ : ν → UTm ν φ} {L L' : LCtx ν κ (Ty α)} {g : UCFG φ (Ty α) ν κ} (hσ : L.Subst σ L')
--   : g.WfI L K → g.WfI L' K := sorry
