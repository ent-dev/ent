module Tools.Ent.Compiler

import Tools.Ent.AST
import Control.Monad.State

entInit : EState
entInit = MkEState []

runMain : Ent () -> IO ()
runMain prog = do ress <- execEnt prog entInit
                  pure ()
