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

data BindType = Insertion

data Decl 
  = ScopeDecl
  | ImportStmt
  | SimpleExpr
  | Binding BindType
  
a : Decl
a = Binding Insertion  
