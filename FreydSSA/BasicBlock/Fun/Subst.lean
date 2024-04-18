import FreydSSA.BasicBlock.Fun.Basic
import FreydSSA.Body.Fun.Subst
import FreydSSA.Terminator.Fun.Subst

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

def UBB.FWf.substCons {Γ : FCtx ν (Ty α)} {β : UBB φ ν κ}
  (hσ : Γ.SubstCons σ Δ N) (dβ : β.FWf p Δ L) (hN : β.body.defs.toFinset ⊆ N)
    : (L' : FLCtx κ ν (Ty α)) × (β.subst σ).FWfM p Γ L' × (L'.SubstCons (σ.cons_list β.body.defs) L N)
  :=
  let db' := dβ.body.toFWf.substCons hσ hN;
  let dt' := dβ.terminator.substCons db'.2.2;
  ⟨
    dt'.1,
    ⟨
      db'.1,
      db'.2.1,
      dt'.2.1
    ⟩,
    dt'.2.2
  ⟩

def UBB.FWf.rewrite {Γ : FCtx ν (Ty α)} {β : UBB φ ν κ}
  (hσ : Γ.SubstCons σ Δ N) (dβ : β.FWf p Δ L) (hN : β.body.defs.toFinset ⊆ N)
  (hσc : {x | x ∈ β.body.defs}.EqOn σ UTm.var)
    : (L' : FLCtx κ ν (Ty α)) × (β.rewrite σ).FWfM p Γ L' × (L'.SubstCons σ L N)
  :=
  let db' := dβ.body.toFWf.rewrite hσ hN hσc;
  let dt' := dβ.terminator.substCons db'.2.2;
  ⟨
    dt'.1,
    ⟨
      db'.1,
      db'.2.1,
      dt'.2.1
    ⟩,
    dt'.2.2
  ⟩
