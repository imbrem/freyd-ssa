import FreydSSA.CFG.Fun.Basic
import FreydSSA.BasicBlock.Fun.Subst

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

def UCFG.FWfIM.to_ewk {L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
  : g.FWfIM L K → K.EWk L
  | nil _ => FLCtx.EWk.refl _
  | cons _ℓ _Γℓ _x _A dg hℓ dβ => (FLCtx.EWk.of_cons _ _ hℓ).trans dg.to_ewk
  | dead _ℓ _x _A dg hℓ => dg.to_ewk

def UCFG.FWfIM.rewrite_exact {L' L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
  {σ : USubst φ ν}
  (hσ : L'.PSubstCons σ L N) (dg : g.FWfIM L K) (hN : g.defs.toFinset ⊆ N)
  (hσM : hσ.isMin)
  (hσc : {x | x ∈ g.defs}.EqOn σ UTm.var)
  : (g.rewrite σ).FWfIM L' (L'.restrict K.support)
  := match dg with
  | nil L => by
    have h : L'.support ⊆ L.support := by rw [hσ.support_eq]
    rw [L'.restrict_sub_support h]
    exact nil L'
  | cons ℓ Γℓ x A dg hℓ dβ =>
    let dg' := dg.rewrite_exact hσ
      (by
        apply Finset.Subset.trans _ hN
        simp only [defs, List.cons_append, List.toFinset_cons, List.toFinset_append]
        apply Finset.Subset.trans (Finset.subset_union_right _ _)
        apply Finset.subset_insert)
      hσM (hσc.mono (λ_ => by simp only [defs]; aesop));
    let hℓ' : ℓ ∈ (L'.restrict K.support).support := sorry;
    let hσβ := hσ.getToFCtx ℓ (FLCtx.get _ hℓ') Γℓ x
      sorry
      sorry
      sorry;
    let ⟨Lβ', dβ', hσβ'⟩ := dβ.rewrite hσβ (by
      apply Finset.Subset.trans _ hN
      simp only [defs, List.cons_append, List.toFinset_cons, List.toFinset_append]
      apply Finset.Subset.trans (Finset.subset_union_left _ _)
      apply Finset.subset_insert
    ) (hσc.mono (by simp only [defs, List.cons_append, List.mem_cons, List.mem_append,
      Set.setOf_subset_setOf]; aesop));
    have w := dg'.to_ewk.to_wk;
    have h
      : (L'.restrict (K.cons ℓ Γℓ).support) = (L'.restrict K.support).cons ℓ (FLCtx.get _ hℓ')
      := sorry
    cons ℓ _ x A (h ▸ dg') sorry (dβ'.toFWf.wkExit sorry)
  | dead ℓ x A dg hℓ =>
    let dg' := dg.rewrite_exact hσ
      (by
        apply Finset.Subset.trans _ hN
        simp only [defs, List.cons_append, List.toFinset_cons, List.toFinset_append]
        apply Finset.Subset.trans (Finset.subset_union_right _ _)
        apply Finset.subset_insert)
      hσM (hσc.mono (λ_ => by simp only [defs]; aesop));
    dead ℓ x A dg' (hσ.not_mem_support_mpr ℓ hℓ)

-- def UCFG.FWfIM.rewrite {L' L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
--   (hσ : L'.PSubstCons σ L N) (dg : g.FWfIM L K) (hN : g.defs.toFinset ⊆ N)
--   (hσM : hσ.isMin)
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
--     hσM (hσc.mono (λ_ => by simp only [defs]; aesop))
--   let hℓ := hσ'.consSrc;
--   let hσβ := hσ.getToFCtx ℓ (K'.get _ hℓ) Γℓ x
--     sorry
--     sorry
--     sorry;
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
--     hσ'.erase' ℓ sorry rfl
--   ⟩
--   | dead ℓ x A dg hℓ =>
--     let ⟨K', dg', hσ'⟩ := dg.rewrite hσ
--       (by
--         apply Finset.Subset.trans _ hN
--         simp only [defs, List.cons_append, List.toFinset_cons, List.toFinset_append]
--         apply Finset.Subset.trans (Finset.subset_union_right _ _)
--         apply Finset.subset_insert)
--       hσM (hσc.mono (λ_ => by simp only [defs]; aesop));
--     ⟨K', dead ℓ x A dg' (hσ.not_mem_support_mpr ℓ hℓ), hσ'⟩

-- def UCFG.FWfI.subst {L' L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
--   (hσ : L'.Subst σ L) (dg : g.FWfI L K) (hσc : {x | x ∈ g.defs}.EqOn σ UTm.var)
--   : ΣK', (g.rewrite σ).FWfI L' K' × K'.Subst σ K := sorry
