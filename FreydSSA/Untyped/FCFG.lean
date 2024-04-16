import FreydSSA.Untyped.Basic
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Data.Finsupp.Defs

def FCFG (φ : Type _) (ν : Type _) (κ : Type _) := Finsupp κ (WithZero (UBB φ ν κ))

instance FCFG.instFunLike : FunLike (FCFG φ ν κ) κ (WithZero (UBB φ ν κ))
  := Finsupp.instFunLike

def FPCFG (φ : Type _) (ν : Type _) (κ : Type _) := Finsupp κ (WithZero (UPBB φ ν κ))

-- TODO: do we actually need finsupp here? after all, all our judgements are finite since our contexts
-- are finite...

inductive FGRegion (φ : Type _) (α : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  | let1 : ν → UTm φ ν → FGRegion φ α ν κ → FGRegion φ α ν κ
  | let2 : ν → ν → UTm φ ν → FGRegion φ α ν κ → FGRegion φ α ν κ
  | br : κ → UTm φ ν → FGRegion φ α ν κ
  | ite : UTm φ ν → FGRegion φ α ν κ → FGRegion φ α ν κ → FGRegion φ α ν κ
  | dom : FGRegion φ α ν κ → (κ → Option (FGRegion φ α ν κ)) → FGRegion φ α ν κ

inductive FPGRegion (φ : Type _) (α : Type _) (ν : Type _) (κ : Type _)
  : Type _ where
  | let1 : ν → UTm φ ν → FPGRegion φ α ν κ → FPGRegion φ α ν κ
  | let2 : ν → ν → UTm φ ν → FPGRegion φ α ν κ → FPGRegion φ α ν κ
  | br : κ → (ν → UTm φ ν) → FPGRegion φ α ν κ
  | ite : UTm φ ν → FPGRegion φ α ν κ → FPGRegion φ α ν κ → FPGRegion φ α ν κ
  | dom : FPGRegion φ α ν κ → (κ → Option (FPGRegion φ α ν κ)) → FPGRegion φ α ν κ
