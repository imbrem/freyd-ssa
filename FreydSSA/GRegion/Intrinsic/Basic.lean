import FreydSSA.Term.Intrinsic.Basic

--TODO: add extra index rather than GCtx? Or mutual inductive?

inductive GCtx (ν κ α) where
  | ctx : Ctx ν α → GCtx ν κ α
  | lctx : LCtx ν κ α → GCtx ν κ α

inductive InstSet.GRegion [Φ : InstSet φ (Ty α)] : GCtx ν κ (Ty α) → LCtx ν κ (Ty α) → Type _
  | br : Φ.Tm 1 Γ A → LCtx.Wk [⟨ℓ, A, Γ⟩] L → Φ.GRegion (GCtx.ctx Γ) L
  | ite : Φ.Tm 1 Γ Ty.bool
    → Φ.GRegion (GCtx.ctx Γ) L
    → Φ.GRegion (GCtx.ctx Γ) L
    → Φ.GRegion (GCtx.ctx Γ) L
  | dom : Φ.GRegion (GCtx.ctx Γ) K → Φ.GRegion (GCtx.lctx L) K → Φ.GRegion (GCtx.ctx Γ) L
  | nil : L.Wk K → Φ.GRegion (GCtx.lctx L) K
  | cons : Φ.GRegion (GCtx.lctx L) (⟨ℓ, A, Γ⟩::K)
    → Φ.GRegion (GCtx.ctx (⟨x, A⟩::Γ)) L
    → Φ.GRegion (GCtx.lctx L) K
