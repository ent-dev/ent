module Main

import Tools.Ent.Main

import Effects
import Effect.File
import Effect.StdIO
import Effect.State

main : IO ()
main = do (pr :: args) <- getArgs
          runInit [(), (), LArgs := args, LEState := MkEState []] entMain
          pure ()
