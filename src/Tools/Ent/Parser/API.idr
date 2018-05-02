module Tools.Ent.Parser.API

import Tools.Ent.Parser.Core

infixl 4 <$
(<$) : Functor f => a -> f b -> f a
(<$) = map . const

%access export

space : Monad m => Parser m Char
space = satisfy isSpace

skipMany : Monad m => Parser m a -> Parser m ()
skipMany p = () <$ many p

manySpaces : Monad m => Parser m ()
manySpaces = skipMany space

someSpaces : Monad m => Parser m ()
someSpaces = space *> skipMany space

anyAlphaChar : Monad m => Parser m Char
anyAlphaChar = satisfy isAlpha

digit : Monad m => Parser m Char
digit = satisfy isDigit

natural' : Monad m => Parser m (List Char)
natural' = some digit



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

string : Monad m => String -> Parser m String
string s = pack <$> (traverse char $ unpack s)

stringRep : Monad m => String -> Parser m (List String)
stringRep s = many $ string s

oneOf : Monad m => String -> Parser m Char
oneOf chs = satisfy (\c => elem c $ unpack chs)
