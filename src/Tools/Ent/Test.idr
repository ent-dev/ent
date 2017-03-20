module Tools.Ent.Test

import Control.Monad.Identity
import Tools.Ent.Parser

Parser : Type -> Type
Parser = Parser Identity

ParserResult : Type -> Type
ParserResult a = Either (List (String, String))  a

ch : Char -> Parser Char
ch x = char x

chR : Char -> Parser (List Char)
chR ch = charRep ch

str : String -> Parser String
str s = string s

strR : String -> Parser (List String)
strR s = stringRep s

test : ParserResult String
test = parse (str "xjd") "xfdls"

t2 : ParserResult (List Char)
t2 = parse (chR 'c') "cccfjkd"

t3 : ParserResult (List String)
t3 = parse (strR "ab") "ababcd"

main : IO ()
main = do printLn $ parse scopeDecl "Tools.Compiler.Utils"
          printLn $ parse simpleDef "ala = 8383"
          printLn $ parse simpleDef "Ala = 8383"
          pure ()
