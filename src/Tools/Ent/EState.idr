module Tools.Ent.EState

%access public export

record EState where
  constructor MkEState
  scopes : List (String, String)
