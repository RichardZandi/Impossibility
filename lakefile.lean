import Lake
open Lake DSL

package Impossibility where
  -- add package configuration options here

-- require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

require mathlib from
  git "https://github.com/leanprover-community/mathlib4.git" @ "v4.20.0"

require godelnumbering from
  git "https://github.com/RichardZandi/godelnumbering.git" @ "main"

require Kleene2 from
  git "https://github.com/RichardZandi/kleene2.git" @ "main"

--require UCI from
--  git "https://github.com/RichardZandi/Universal-Classification-Impossibility.git" @ "main"

@[default_target]
lean_lib Impossibility where
  roots := #[`Impossibility.Evolution, `Impossibility.PartExtras,
  `Impossibility.CatAndTail.CatTailWitness,`Impossibility.CatAndTail.CatTailUCI,
  `Impossibility.Halting.HaltingUCI,`Impossibility.Halting.HaltingEvolution,
  `Impossibility.PZI.PZIUCI,`Impossibility.PZI.PZIEvolution,
  `Impossibility.Totality.TotalityUCI,
  `Impossibility.Rice.RiceUCI,
  `Impossibility.TimeOne.TimeOneUCI,
  `Impossibility.TimeTwo.TimeTwoUCI,
  `Impossibility.Cantor.CantorUCI,
  `Impossibility.Cantor.CantorUCI2,
  `Impossibility.TimeLoop.TimeLoopUCI,
  `Impossibility.CreatorParadox.CreatorParadoxUCI,
  `Impossibility.Russell.RussellUCI,
  `Impossibility.EvolutionInstance,
  `Impossibility.Arrow.ArrowTypes,`Impossibility.EncodableBasic,
  `Impossibility.UCICoreTest]

-- `Impossibility.PreferenceCodec,
-- `Impossibility.Arrow.ArrowHelper,
-- `Impossibility.Arrow.ArrowUCI,
--  `Impossibility.Arrow.ArrowAxioms,
--   `Impossibility.Arrow.ArrowProof,
