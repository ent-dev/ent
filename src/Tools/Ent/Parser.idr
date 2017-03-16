module Tools.Ent.Parser

import public Control.Monad.Identity



data Result a = Success String a | Failure (List (String, String)) 

export
record Parser (m : Type -> Type) a where
  constructor MkParser
  run : 
    (ret : Type) -> 
    (succ : (a -> String -> m ret)) ->
    (fail : ((List (String, String) ) -> m ret)) -> 
    String ->
    m ret
    
execParser : Monad m => Parser m a -> (input : String) -> m (Result a)
execParser {a} (MkParser p) input = p (Result a) succ fail input 
  where succ x i = pure $ Success i x
        fail     = pure . Failure
        
using(Monad m)  
  Functor (Parser m) where
    map f (MkParser p) = MkParser $ \r, succ => p r (succ . f)
    
  Applicative (Parser m) where
    pure x = MkParser $ \r, succ, fail => succ x
    (<*>) (MkParser f) (MkParser g) = 
      MkParser $ \r, succ, fail =>
        f r (\f' => g r (succ . f') fail) fail
  
satisfy : Monad m => (Char -> Bool) -> Parser m Char
satisfy c = MkParser $ \ret, sc, fc, inp => 
  case unpack inp of
    (x :: xs) => if c x then sc x (pack xs)
                        else fc [(inp, "a different character")]

%access export

parse : Parser Identity a -> String -> Either String a
parse f input = let Id r = execParser f input in 
  case r of
    Success _ x => Right x
    Failure es  => Left "Whatever"

char : Monad m => Char -> Parser m Char
char ch = satisfy (== ch)
    
string : Monad m => String -> Parser m String
string s = pack <$> (traverse char $ unpack s)
