module Tools.Ent.Main

import Effects
import Effect.File
import Effect.StdIO
import Effect.State

import Tools.Ent.AST

%access export

public export
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


entMain : Eff () [STDIO,
                FILE (),
                LArgs ::: STATE (List String),
                LEState ::: STATE EState]
entMain = do putStrLn "Welcome to ent interactive!"
             putStr "Ent>"
             collectContents !(LArgs :- get)
             st <- LEState :- get
             putStrLn $ show $ scopes st
             putStrLn "Bye"
             pure ()


