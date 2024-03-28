import FreydSSA.BasicBlock.Extrinsic.Basic

variable {φ ν κ α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

inductive UCFG.Step : LCtx ν κ (Ty α) → UCFG φ (Ty α) ν κ → LCtx ν κ (Ty α) → Type _
  | nil : Step [] nil K
  | cons (ℓ x A) : Step L g K → β.Wf 0 (⟨x, A⟩::Γ) K → Step (⟨ℓ, A, Γ⟩::L) (g.cons ℓ x A β) K

inductive UCFG.StepM : LCtx ν κ (Ty α) → UCFG φ (Ty α) ν κ → LCtx ν κ (Ty α) → Type _
  | nil : StepM [] nil []
  -- Note: we allow weakening here, to be stricter we could define a minimum join...
  | cons (ℓ x A)
    : StepM L g K → β.WfM 0 (⟨x, A⟩::Γ) Kβ → K.Join Kβ K'
      → StepM (⟨ℓ, A, Γ⟩::L) (g.cons ℓ x A β) K'

inductive UCFG.WfI : LCtx ν κ (Ty α) → UCFG φ (Ty α) ν κ → LCtx ν κ (Ty α) → Type _
  | nil : L.Wk K → WfI L nil K
  | cons (ℓ x A) : WfI L g (⟨ℓ, A, Γ⟩::K) → β.Wf 0 (⟨x, A⟩::Γ) L → WfI (⟨ℓ, A, Γ⟩::L) (g.cons ℓ x A β) K

inductive UCFG.WfIM : LCtx ν κ (Ty α) → UCFG φ (Ty α) ν κ → LCtx ν κ (Ty α) → Type _
  | nil (L) : WfIM L nil L
  | cons (ℓ x A) : WfIM L g (⟨ℓ, A, Γ⟩::K) → β.Wf 0 (⟨x, A⟩::Γ) L → WfIM (⟨ℓ, A, Γ⟩::L) (g.cons ℓ x A β) K

-- Note: Step = StepM ; Wk
-- Note: WfI = WfIM ; Wk

structure UCFG.Wf (L : LCtx ν κ (Ty α)) (g : UCFG φ (Ty α) ν κ) (K : LCtx ν κ (Ty α)) : Type _ :=
  labels : LCtx ν κ (Ty α)
  wk : L.Wk labels
  wfI : g.WfI labels K
  -- Note: unqiueness failures here due to β input weakening... try exact-output?
