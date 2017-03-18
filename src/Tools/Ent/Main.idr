module Tools.Ent.Main

import Effects
import Effect.File
import Effect.StdIO
import Effect.State
import Tools.Ent.EState

data Label = LArgs | LEState

fileContents : (fname : String) ->
               Eff () [STDIO, FILE (), LEState ::: STATE EState]
fileContents fn = do (Result str) <- readFile fn
                     LEState :- put (
                       record { scopes $= ((fn, str) ::) } !(LEState :- get))
                     pure ()

collectContents : (List String) -> Eff () [STDIO, FILE (), LEState ::: STATE EState]
collectContents [] = do pure ()
collectContents (x :: xs) = do putStrLn x
                               fileContents x
                               collectContents xs

smain : Eff () [STDIO,
                FILE (),
                LArgs ::: STATE (List String),
                LEState ::: STATE EState]
smain = do putStrLn "Welcome to ent interactive!"
           putStr "Ent>"
           collectContents !(LArgs :- get)
           st <- LEState :- get
           putStrLn $ show $ scopes st
           putStrLn "Bye"
           pure ()

main : IO ()
main = do (pr :: args) <- getArgs
          runInit [(), (), LArgs := args, LEState := MkEState []] smain
          pure ()
