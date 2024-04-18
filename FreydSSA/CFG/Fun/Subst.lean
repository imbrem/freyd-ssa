import FreydSSA.CFG.Fun.Basic
import FreydSSA.BasicBlock.Fun.Subst

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

-- TODO: better: it's a _restriction_, i.e. L.restrict K.support = K
def UCFG.FWfIM.toWk {L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
  : g.FWfIM L K → K.Wk L
  | nil _ => FLCtx.Wk.refl _
  | cons _ℓ _Γℓ _x _A dg hℓ dβ => (FLCtx.Wk.of_cons _ _ hℓ).comp dg.toWk
  | dead _ℓ _x _A dg hℓ => dg.toWk

-- -- TODO: factor out insertion lemmas...
-- TODO: specifically restrict L' to K' to get substitution target...
-- Note we don't even need PSubstCons then!
-- def UCFG.FWfIM.rewrite {L' L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
--   (hσ : L'.PSubstCons σ L N) (dg : g.FWfIM L K) (hN : g.defs.toFinset ⊆ N)
--   (hσc : {x | x ∈ g.defs}.EqOn σ UTm.var)
--   : ΣK', (g.rewrite σ).FWfIM L' K' × K'.PSubstCons σ K N
--   := match dg with
--   | nil _ => ⟨_, nil _, hσ⟩
--   | cons ℓ Γℓ x A dg hℓ dβ =>
--   let ⟨K', dg', hσ'⟩ := dg.rewrite hσ
--     (by
--       apply Finset.Subset.trans _ hN
--       simp only [defs, List.cons_append, List.toFinset_cons, List.toFinset_append]
--       apply Finset.Subset.trans (Finset.subset_union_right _ _)
--       apply Finset.subset_insert)
--     (hσc.mono (λ_ => by simp only [defs]; aesop))
--   let ⟨Γℓ', hK'⟩ := hσ'.consSrc;
--   let hσβ := hσ.getToFCtx ℓ Γℓ' Γℓ x sorry sorry sorry;
--   -- TODO: rewrite rather than subst...
--   let ⟨Lβ', dβ', hσβ'⟩ := dβ.rewrite hσβ (by
--     apply Finset.Subset.trans _ hN
--     simp only [defs, List.cons_append, List.toFinset_cons, List.toFinset_append]
--     apply Finset.Subset.trans (Finset.subset_union_left _ _)
--     apply Finset.subset_insert
--   ) (hσc.mono (by simp only [defs, List.cons_append, List.mem_cons, List.mem_append,
--     Set.setOf_subset_setOf]; aesop));
--   have w := dg'.toWk;
--   have w' := hK' ▸ w;
--   ⟨
--     K'.erase ℓ,
--     cons ℓ _ x A (hK' ▸ dg') (by simp [FLCtx.erase]) (dβ'.toFWf.wkExit sorry),
--     sorry
--   ⟩
--   | dead ℓ x A dg hℓ =>
--     let ⟨K', dg', hσ'⟩ := dg.rewrite hσ
--       (by
--         apply Finset.Subset.trans _ hN
--         simp only [defs, List.cons_append, List.toFinset_cons, List.toFinset_append]
--         apply Finset.Subset.trans (Finset.subset_union_right _ _)
--         apply Finset.subset_insert)
--       (hσc.mono (λ_ => by simp only [defs]; aesop));
--     ⟨K', dead ℓ x A dg' (hσ.not_mem_support_mpr ℓ hℓ), hσ'⟩

-- def UCFG.FWfI.subst {L' L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
--   (hσ : L'.Subst σ L) (dg : g.FWfI L K) (hσc : {x | x ∈ g.defs}.EqOn σ UTm.var)
--   : ΣK', (g.rewrite σ).FWfI L' K' × K'.Subst σ K := sorry
