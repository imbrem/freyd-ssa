inductive MCFG (G : Type _)
  : Type _ where
  | id : MCFG G
  | inl : MCFG G → MCFG G
  | inr : MCFG G → MCFG G
  | join : MCFG G → MCFG G → MCFG G
  | seq : MCFG G → MCFG G → MCFG G
  | fix : MCFG G → MCFG G
  | atom : G → MCFG G
