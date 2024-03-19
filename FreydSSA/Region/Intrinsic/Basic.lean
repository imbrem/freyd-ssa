import FreydSSA.CFG.Intrinsic.Basic

structure InstSet.Region [Φ : InstSet φ (Ty α)] (Γ : Ctx ν (Ty α)) (L : LCtx ν κ (Ty α)) where
  entry : Φ.BB Γ K
  -- Issue: underspecified: can change K, so must quotient somehow
  cfg : Φ.ICFG K L
