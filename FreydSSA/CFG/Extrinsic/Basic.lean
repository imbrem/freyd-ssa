import FreydSSA.BasicBlock.Extrinsic.Basic

variable {φ ν κ α} [Φ : InstSet φ (Ty α)] [Φc : CohInstSet φ (Ty α)]

inductive UCFG.Step : LCtx ν κ (Ty α) → UCFG φ (Ty α) ν κ → LCtx ν κ (Ty α) → Type _
  | nil : Step [] nil K
  | cons (ℓ x A) : Step L g K → β.Wf 0 (⟨x, A⟩::Γ) K → Step (⟨ℓ, A, Γ⟩::L) (g.cons ℓ x A β) K

inductive UCFG.StepM : LCtx ν κ (Ty α) → UCFG φ (Ty α) ν κ → LCtx ν κ (Ty α) → Type _
  | nil : StepM [] nil []
  -- Note: we allow weakening here via the join, to be stricter we could define a minimum join...
  | cons (ℓ x A)
    : StepM L g K → β.WfM 0 (⟨x, A⟩::Γ) Kβ → K.Join Kβ K'
      → StepM (⟨ℓ, A, Γ⟩::L) (g.cons ℓ x A β) K'

structure UCFG.WfRM (I : LCtx ν κ (Ty α)) (g : UCFG φ (Ty α) ν κ) (O : LCtx ν κ (Ty α)) : Type _ :=
  labels : LCtx ν κ (Ty α)
  recursiveLabels : LCtx ν κ (Ty α)
  stepM : g.StepM I labels
  wkRecursiveLabels : labels.EWk recursiveLabels
  splitRecursiveLabels : recursiveLabels.SSplit O I

-- theorem UCFG.WfRM.trgEq {I O O' : LCtx ν κ (Ty α)} {g : UCFG φ (Ty α) ν κ}
--   (dg : UCFG.WfRM I g O) (dg' : UCFG.WfRM I g O') (hO : O.Comp O') : O = O' :=
--   sorry

inductive UCFG.WfI : LCtx ν κ (Ty α) → UCFG φ (Ty α) ν κ → LCtx ν κ (Ty α) → Type _
  | nil : L.Wk K → WfI L nil K
  | cons (ℓ x A) : WfI L g (⟨ℓ, A, Γ⟩::K) → β.Wf 0 (⟨x, A⟩::Γ) L → WfI L (g.cons ℓ x A β) K
  | dead (ℓ x A) : WfI L g K → L.Fresh ℓ → WfI L (g.cons ℓ x A β) K

inductive UCFG.WfIM : LCtx ν κ (Ty α) → UCFG φ (Ty α) ν κ → LCtx ν κ (Ty α) → Type _
  | nil (L) : WfIM L nil L
  | cons (ℓ x A) : WfIM L g (⟨ℓ, A, Γ⟩::K) → β.Wf 0 (⟨x, A⟩::Γ) L → WfIM L (g.cons ℓ x A β) K
  | dead (ℓ x A) : WfIM L g K → L.Fresh ℓ → WfIM L (g.cons ℓ x A β) K

structure UCFG.WfI' (L : LCtx ν κ (Ty α)) (g : UCFG φ (Ty α) ν κ) (K : LCtx ν κ (Ty α)) : Type _ :=
  labels : LCtx ν κ (Ty α)
  wfM : g.WfIM L labels
  wk : labels.Wk K

-- def UCFG.WfI.factor {L K} {g : UCFG φ (Ty α) ν κ} : UCFG.WfI L g K → UCFG.WfI' L g K
--   | nil w => ⟨_, WfIM.nil _, w⟩
--   | cons ℓ x A dg dβ =>
--     let dg' := dg.factor
--     ⟨_, dg'.wfM.cons ℓ x A dβ, sorry⟩
--   | _ => sorry

inductive UCFG.WfIS : LCtx ν κ (Ty α) → UCFG φ (Ty α) ν κ → LCtx ν κ (Ty α) → Type _
  | nil (L) : WfIS L nil L
  | cons (ℓ x A) : WfIS L g (⟨ℓ, A, Γ⟩::K) → β.Wf 0 (⟨x, A⟩::Γ) L → WfIS L (g.cons ℓ x A β) K
  | skip (ℓ): WfIS L g (ℓ::K) → L.Fresh ℓ.name → WfIS L g K --TODO: K.Fresh?
  | dead (ℓ x A) : WfIS L g K → L.Fresh ℓ → WfIS L (g.cons ℓ x A β) K

structure UCFG.WfIS' (L : LCtx ν κ (Ty α)) (g : UCFG φ (Ty α) ν κ) (K : LCtx ν κ (Ty α)) : Type _ :=
  labels : LCtx ν κ (Ty α)
  wfISM : g.WfIM L labels
  wk : labels.EWk K

-- Note: Step = StepM ; Wk
-- Note: WfI = WfIM ; Wk

structure UCFG.Wf (L : LCtx ν κ (Ty α)) (g : UCFG φ (Ty α) ν κ) (K : LCtx ν κ (Ty α)) : Type _ :=
  labels : LCtx ν κ (Ty α)
  wk : L.Wk labels
  wfI : g.WfIM labels K
  -- Note: unqiueness failures here due to dead code, β-failures, etc.
  -- Directly called code should be unique
  -- Indirectly called code _might_ be unique
