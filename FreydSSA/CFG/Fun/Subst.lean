import FreydSSA.CFG.Fun.Basic
import FreydSSA.BasicBlock.Fun.Subst

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]


-- TODO: rune of ℓ erasure?
-- def FLCtx.PSubstCons.consSrc {L' : FLCtx κ ν (Ty α)} {σ : USubst φ ν} {L : FLCtx κ ν (Ty α)}
--   (hσ : L'.PSubstCons σ (L.cons ℓ Γℓ) N) : Σ'Γℓ', L' = (L'.erase ℓ).cons ℓ Γℓ'
--   := sorry

-- -- TODO: factor out insertion lemmas...
-- def UCFG.FWfIM.subst {L' L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
--   (hσ : L'.PSubstCons σ L N) (dg : g.FWfIM L K) (hN : g.defs.toFinset ⊆ N)
--   (hσc : {x | x ∈ g.defs}.EqOn σ UTm.var)
--   : ΣK', (g.rewrite σ).FWfIM L' K' × K'.PSubstCons σ K N
--   := match dg with
--   | nil _ => ⟨_, nil _, hσ⟩
--   | cons ℓ x A dg hℓ dβ =>
--   let ⟨K', dg', hσ'⟩ := dg.subst hσ
--     (by apply Finset.Subset.trans _ hN; simp [defs])
--     (hσc.mono (λ_ => by simp only [Set.mem_setOf_eq, defs]; exact List.mem_cons_of_mem _))
--   let ⟨Γℓ', hK'⟩ := hσ'.consSrc;
--   ⟨
--     K'.erase ℓ,
--     cons ℓ x A (hK' ▸ dg') (by simp [FLCtx.erase]) sorry,
--     sorry
--   ⟩
--   | dead ℓ x A dg hℓ =>
--     let ⟨K', dg', hσ'⟩ := dg.subst hσ
--       (by apply Finset.Subset.trans _ hN; simp [defs])
--       (hσc.mono (λ_ => by simp only [Set.mem_setOf_eq, defs]; exact List.mem_cons_of_mem _));
--     ⟨K', dead ℓ x A dg' (hσ.not_mem_support_mpr ℓ hℓ), hσ'⟩

-- def UCFG.FWfI.subst {L' L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
--   (hσ : L'.Subst σ L) (dg : g.FWfI L K) (hσc : {x | x ∈ g.defs}.EqOn σ UTm.var)
--   : ΣK', (g.rewrite σ).FWfI L' K' × K'.Subst σ K := sorry
