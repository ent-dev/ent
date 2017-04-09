module Tools.Ent.AST

import Control.Monad.State      

%access public export

record EState where
  constructor MkEState
  scopes : List (String, String)

Ent : Type -> Type
Ent = StateT EState IO

runEnt : Ent a -> EState -> IO (a, EState)
runEnt e s = (runStateT e) s

evalEnt : Ent a -> EState -> IO a
evalEnt e s = pure $ fst !(runEnt e s)
                 
execEnt : Ent a -> EState -> IO EState
execEnt e s = pure $ snd !(runEnt e s)

data SimpleValue = A

data BindingType = Insertion

data Name = UN String
          | MN String
          
Show Name where
  show (UN s) = "UN " ++ s
  show (MN s) = "MN " ++ s

data PTerm
  = PScope (List String)
  | PImport
  | PRef Name
  | PSimpleExpr String String
  | PApp PTerm (List Name)
  | PBinding BindingType
  
Show PTerm where
  show (PScope xs) = "PScope " ++ (show xs)
  show (PSimpleExpr nme exp) = "PSimpleExpr " ++ nme ++ " " ++ exp
  show (PRef n) = "PRef (" ++ show n ++ ")"
  show (PApp t xs) = "PApp (" ++ show t ++ ", " ++ show xs ++ ")"
