import FreydSSA.CFG.Fun.Basic
import FreydSSA.BasicBlock.Fun.Subst

variable {φ : Type u₁} {ν : Type u₂} {κ : Type u₃} {α : Type u₄} [Φ : InstSet φ (Ty α)]
  [Φc : CohInstSet φ (Ty α)] [Φi : InjInstSet φ (Ty α)]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq α]

def UCFG.FWfIM.to_ewk {L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ} {K : FLCtx κ ν (Ty α)}
  : g.FWfIM L K → K.EWk L
  | nil _ => FLCtx.EWk.refl _
  | cons _ℓ _Γℓ _x _A dg hℓ dβ => (FLCtx.EWk.of_cons _ _ hℓ).trans dg.to_ewk
  | dead _ℓ _x _A dg hℓ => dg.to_ewk

def UCFG.FWfIM.rewrite_exact {L' L : FLCtx κ ν (Ty α)} {g : UCFG φ (Ty α) ν κ}
{K : FLCtx κ ν (Ty α)}
  {σ : USubst φ ν}
  (hσ : L'.PSubstCons σ L N) (dg : g.FWfIM L K) (hN : g.defs.toFinset ⊆ N)
  (hσM : hσ.SupSrc)
  (hσc : {x | x ∈ g.defs}.EqOn σ UTm.var) -- TODO: might be able to relax this a tiny bit
  : (g.rewrite σ).FWfIM L' (L'.restrict K.support)
  := match dg with
  | nil L => by
    have h : L'.support ⊆ L.support := by rw [hσ.support_eq]
    rw [L'.restrict_sub_support h]
    exact nil L'
  | cons ℓ Γℓ x A dg hℓ dβ =>
    let ewk := dg.to_ewk;
    let dg' := dg.rewrite_exact hσ
      (by
        apply Finset.Subset.trans _ hN
        simp only [defs, List.cons_append, List.toFinset_cons, List.toFinset_append]
        apply Finset.Subset.trans (Finset.subset_union_right _ _)
        apply Finset.subset_insert)
      hσM (hσc.mono (λ_ => by simp only [defs]; aesop));
    have hℓL : ℓ ∈ L.support := ewk.support_subset (by simp [FLCtx.cons]);
    have hℓL' : ℓ ∈ L'.support := hσ.support_eq ▸ hℓL;
    let hσβ := hσ.getToFCtx ℓ (FLCtx.get _ hℓL') Γℓ x
      (by rw [FLCtx.get_eq])
      ewk.cons_eq
      (by simp only [defs, List.cons_append, List.toFinset_cons, List.toFinset_append,
        Finset.insert_subset_iff] at hN; exact hN.1)
      (@hσc x (by simp [defs]));
    let ⟨Lβ', dβ', hσβ'⟩ := dβ.rewrite hσβ (by
      apply Finset.Subset.trans _ hN
      simp only [defs, List.cons_append, List.toFinset_cons, List.toFinset_append]
      apply Finset.Subset.trans (Finset.subset_union_left _ _)
      apply Finset.subset_insert
    ) (hσc.mono (by simp only [defs, List.cons_append, List.mem_cons, List.mem_append,
      Set.setOf_subset_setOf]; aesop));
    have h
      : (L'.restrict (K.cons ℓ Γℓ).support) = (L'.restrict K.support).cons ℓ (FLCtx.get _ hℓL')
      := FLCtx.restrict_insert_eq _ _ _
    cons ℓ _ x A (h ▸ dg')
      (FLCtx.not_mem_restrict_of_not_mem hℓ)
      (dβ'.toFWf.wkExit (hσβ'.wk_sup_src hσ hσM))
  | dead ℓ x A dg hℓ =>
    let dg' := dg.rewrite_exact hσ
      (by
        apply Finset.Subset.trans _ hN
        simp only [defs, List.cons_append, List.toFinset_cons, List.toFinset_append]
        apply Finset.Subset.trans (Finset.subset_union_right _ _)
        apply Finset.subset_insert)
      hσM (hσc.mono (λ_ => by simp only [defs]; aesop));
    dead ℓ x A dg' (hσ.not_mem_support_mpr ℓ hℓ)
