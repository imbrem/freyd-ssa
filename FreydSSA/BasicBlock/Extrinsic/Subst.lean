import FreydSSA.BasicBlock.Extrinsic.Basic
import FreydSSA.Terminator.Extrinsic.Subst
import FreydSSA.Body.Extrinsic.Subst

variable {φ ν α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

def UBB.Wf.subst {β : UBB φ ν κ}
  (hσ : Γ.Subst σ Δ) (hσ' : ∀ x ∈  β.body.defs, σ x = UTm.var x) (hβ : β.body.SSA Γ.names)
  (dβ : β.Wf p Δ K) : (L : LCtx ν κ (Ty α)) ×' (β.rewrite σ).Wf p Γ L × L.Subst σ K :=
  let body' := dβ.body.subst hσ hσ' hβ;
  let terminator' := dβ.terminator.subst body'.2.2;
  ⟨_, ⟨_, body'.2.1, terminator'.2.1⟩, terminator'.2.2⟩
