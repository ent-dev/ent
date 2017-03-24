module Tools.Ent.Parser

import public Control.Monad.Identity

import Tools.Ent.AST

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

using(Monad m)
  Functor (Parser m) where
    map f (MkParser p) = MkParser $ \r, succ => p r (succ . f)

  export
  Applicative (Parser m) where
    pure x = MkParser $ \r, succ, fail => succ x
    (<*>) (MkParser f) (MkParser g) =
      MkParser $ \r, succ, fail =>
        f r (\f' => g r (succ . f') fail) fail

  Alternative (Parser m) where
    empty = fail "non-empty alternative"
    (<|>) (MkParser x) (MkParser y) = MkParser $ \r, succ, fail, inp =>
      x r succ (\err => y r succ (fail . (err ++)) inp) inp

  Monad m => Monad (Parser m) where
    (>>=) (MkParser x) f = MkParser $ \r, sc, fc =>
      x r (\x' => let MkParser y = f x' in y r sc fc) fc

infixl 2 <*>|

(<*>|) : Parser m (a -> b) -> Lazy (Parser m a) -> Parser m b
(<*>|) (MkParser f) x = MkParser $ \r, sc, fc =>
  f r (\f' => let MkParser g = x in g r (sc . f') fc) fc

many : Monad m => Parser m a -> Parser m (List a)
many p = (pure (List.(::)) <*> p <*>| many p) <|> pure List.Nil

satisfy : Monad m => (Char -> Bool) -> Parser m Char
satisfy c = MkParser $ \ret, sc, fc, inp =>
  case unpack inp of
    (x :: xs) => if c x then sc x (pack xs)
                        else fc [(inp, "a different character")]
    []        => fc [(inp, "a token, not EOF")]


%access export

parse : Parser Identity a -> String -> Either (List (String, String)) a
parse f input = let Id r = execParser f input in
  case r of
    Success _ x => Right x
    Failure es  => Left es

space : Monad m => Parser m Char
space = satisfy isSpace

anyAlphaChar : Monad m => Parser m Char
anyAlphaChar = satisfy isAlpha

digit : Monad m => Parser m Char
digit = satisfy isDigit

char : Monad m => Char -> Parser m Char
char ch = satisfy (== ch)

dot : Monad m => Parser m Char
dot = satisfy (== '.')

equals : Monad m => Parser m Char
equals = satisfy (== '=')

charRep : Monad m => Char -> Parser m (List Char)
charRep ch = many $ char ch

upperChar : Monad m => Parser m Char
upperChar = satisfy isUpper

lowerChar : Monad m => Parser m Char
lowerChar = satisfy isLower

upperId : Monad m => Parser m String
upperId = do fl <- upperChar
             xs <- many $ anyAlphaChar
             pure (pack $ fl :: xs)

lowerId : Monad m => Parser m String
lowerId = do fl <- lowerChar
             xs <- many $ anyAlphaChar
             pure (pack $ fl :: xs)

namespace lang
  scopeDecl : Monad m => Parser m String
  scopeDecl = do fp <- upperId
                 rems <- many (do dot; upperId)
                 pure (foldr (++) fp rems)

  simpleDef : Monad m => Parser m (String, String)
  simpleDef = do it <- do lowerId <|> upperId
                 many space
                 equals
                 many space
                 xs <- many digit
                 pure (it, pack xs)

string : Monad m => String -> Parser m String
string s = pack <$> (traverse char $ unpack s)

stringRep : Monad m => String -> Parser m (List String)
stringRep s = many $ string s

oneOf : Monad m => String -> Parser m Char
oneOf chs = satisfy (\c => elem c $ unpack chs)
