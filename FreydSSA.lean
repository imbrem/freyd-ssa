import FreydSSA.Term.Extrinsic.Basic
import FreydSSA.Term.Extrinsic.Subst
import FreydSSA.Body.Extrinsic.Basic
import FreydSSA.Body.Extrinsic.Subst
import FreydSSA.Terminator.Extrinsic.Basic
import FreydSSA.Terminator.Extrinsic.Subst
import FreydSSA.BasicBlock.Extrinsic.Basic
import FreydSSA.BasicBlock.Extrinsic.Subst
import FreydSSA.CFG.Extrinsic.Basic
import FreydSSA.CFG.Extrinsic.Subst
import FreydSSA.Region.Extrinsic.Basic
import FreydSSA.Region.Extrinsic.Subst
import FreydSSA.GRegion.Extrinsic.Basic
import FreydSSA.GRegion.Extrinsic.Subst
import FreydSSA.Term.Intrinsic.Basic
import FreydSSA.Term.Intrinsic.Subst
import FreydSSA.Body.Intrinsic.Basic
import FreydSSA.Body.Intrinsic.Subst
import FreydSSA.Terminator.Intrinsic.Basic
-- import FreydSSA.Terminator.Intrinsic.Subst
import FreydSSA.BasicBlock.Intrinsic.Basic
-- import FreydSSA.BasicBlock.Intrinsic.Subst
import FreydSSA.CFG.Intrinsic.Basic
-- import FreydSSA.CFG.Intrinsic.Subst
import FreydSSA.Region.Intrinsic.Basic
-- import FreydSSA.Region.Intrinsic.Subst
import FreydSSA.GRegion.Intrinsic.Basic
-- import FreydSSA.GRegion.Intrinsic.Subst

import FreydSSA.Term.Fun.Basic
import FreydSSA.Term.Fun.Subst
import FreydSSA.Body.Fun.Basic
import FreydSSA.Body.Fun.Subst
import FreydSSA.Terminator.Fun.Basic
import FreydSSA.Terminator.Fun.Subst
import FreydSSA.BasicBlock.Fun.Basic
import FreydSSA.BasicBlock.Fun.Subst
import FreydSSA.CFG.Fun.Basic
import FreydSSA.CFG.Fun.Subst
import FreydSSA.Region.Fun.Basic
import FreydSSA.Region.Fun.Subst
import FreydSSA.GRegion.Fun.Basic
import FreydSSA.GRegion.Fun.Subst

-- TODO: Untyped folder...
-- TODO: Indexed intrinsic/extrinsic (dominator tree)
-- TODO: Dominated intrinsic/extrinsic (dominator tree)
-- TODO: capture-avoiding subst over extrinsic (which is just Γ ⊢ b ▷ Γ for blocks!)
-- TODO: resource algebra for substructurality, r ⊗ ℓ ⊆ L, and so on...
  -- TODO: resourceful intrinsic
  -- TODO: resourceful extrinsic
  -- TODO: resourceful indexed
  -- TODO: resourceful intrinsic-dom
  -- TODO: resourceful extrinsic-dom
-- TODO: Freyd category semantics...
-- TODO: Monadic semantics, equality w/ categorical semantics
-- TODO: Initial model for Freyd: show quotient respects Freyd rules
  -- TODO: use dominator quotient?
-- TODO: Initial model for Elgot: show quotient respects Elgot rules
  -- TODO: use dominator quotient?
