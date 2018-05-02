module Tools.Ent.STExt

import Control.ST

interface FileIO (m : Type -> Type) where
  readFile : String -> STrans m (Either FileError String) xs (const xs)
  writeFile : String -> String -> STrans m (Either FileError ()) xs (const xs)


FileIO IO where
  readFile name = lift (File.readFile name)
  writeFile name str = lift $ File.writeFile name str
