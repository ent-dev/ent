module Tools.Ent.Parser.Core

import Control.Monad.Identity

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

fail : String -> Parser m a
fail s = MkParser $ \r, succ, fail, inp => fail [(inp, s)]

infixl 0 <?>
public export
interface Alternative m => Parsing (m : Type -> Type) where
  (<?>) : m a -> String -> m a

  token : m a -> m () -> m a
  token p seps = p <* (seps <|> pure ())

infixr 0 ~$
infixl 4 <**>

(~$) : (a -> b) -> a -> b
(~$) f a = f a

export
(<**>) : Applicative m => m a -> m (a -> b) -> m b
(<**>) = liftA2 (flip (~$))

using(Monad m)
  Functor (Parser m) where
    map f (MkParser p) = MkParser $ \r, succ => p r (succ . f)

  export
  Applicative (Parser m) where
    pure x = MkParser $ \r, succ, fail => succ x
    (<*>) (MkParser f) (MkParser g) =
      MkParser $ \r, succ, fail =>
        f r (\f' => g r (succ . f') fail) fail

  export
  Alternative (Parser m) where
    empty = fail "non-empty alternative"
    (<|>) (MkParser x) (MkParser y) = MkParser $ \r, succ, fail, inp =>
      x r succ (\err => y r succ (fail . (err ++)) inp) inp

  export
  Monad m => Monad (Parser m) where
    (>>=) (MkParser x) f = MkParser $ \r, sc, fc =>
      x r (\x' => let MkParser y = f x' in y r sc fc) fc

  export
  Alternative (Parser m) => Parsing (Parser m) where
    (MkParser f) <?> msg = MkParser $ \r, sc, fc, i =>
      f r sc (fc . ((i, msg) ::)) i


infixl 2 <*>|

(<*>|) : Parser m (a -> b) -> Lazy (Parser m a) -> Parser m b
(<*>|) (MkParser f) x = MkParser $ \r, sc, fc =>
  f r (\f' => let MkParser g = x in g r (sc . f') fc) fc

%access export

many : Monad m => Parser m a -> Parser m (List a)
many p = (pure (List.(::)) <*> p <*>| many p) <|> pure List.Nil

some : Monad m => Parser m a -> Parser m (List a)
some p = [| p :: many p |]

satisfy : Monad m => (Char -> Bool) -> Parser m Char
satisfy c = MkParser $ \ret, sc, fc, inp =>
  case unpack inp of
    (x :: xs) => if c x then sc x (pack xs)
                        else fc [(inp, "a different character")]
    []        => fc [(inp, "a token, not EOF")]

parse : Parser Identity a -> String -> Either (List (String, String)) a
parse f input = let Id r = execParser f input in
  case r of
    Success _ x => Right x
    Failure es  => Left es
