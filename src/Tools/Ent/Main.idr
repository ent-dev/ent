module Tools.Ent.Main

import Effects
import Effect.File
import Effect.StdIO
import Effect.State
import Tools.Ent.EState

fileContents : (fname : String) -> Eff () [STDIO, FILE (), STATE EState]
fileContents fn = do (Result str) <- readFile fn
                     pure ()

printArgs : (List String) -> Eff () [STDIO, FILE (), STATE EState]
printArgs [] = do pure ()
printArgs (x :: xs) = do putStrLn x
                         fileContents x                         
                         printArgs xs

smain : Eff () [STDIO, FILE (), STATE (List String), STATE EState]
smain = do putStrLn "Welcome to ent interactive!"
           Success <- open "test.file" Read 
             | (FError err) => do putStrLn "Error"
                                  pure ()
           (Result str) <- readLine
           putStrLn str
           putStr "Ent>"
           -- ch <- getChar
           close
           printArgs !get
           putStrLn "Bye"

main : IO ()
main = do args <- getArgs
          runInit [(), (), args, MkEState []] smain
          pure ()

