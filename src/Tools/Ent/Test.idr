module Tools.Ent.Test

import Control.Monad.Identity
import Tools.Ent.Parser
import Tools.Ent.AST

%access public export

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

tbep : String -> ParserResult PTerm
tbep s = parse opExpr s

ppar : String -> ParserResult (PTerm, List PTerm, List PTerm)
ppar s = parse progParser s

showb : Show b => Either (List (String, String)) b -> IO ()
showb (Right b) = putStrLn $ show b
showb (Left a) = putStrLn $ show a

Show (PTerm -> PTerm) where
  show a = "PT -> PT"

tprog : String
tprog = """Main.Scope

f = 3 + 4

g = "jfdlsj"

main : IO ()
main = <= print "Hello world"
"""



main : IO ()
main = do --showb $ parse scopeDecl "Tools.Compiler.Utils"
          --showb $ parse simpleDef "ala = 8383"
          --showb $ parse simpleDef "Ala = 8383"
          --showb $ tbep  "2 ^ 3 ^ 8 + 4 * 5 ^ 3"
          --showb $ parse opmany "-3"
          --showb $ tbep "32 + \"jdflk\""
          --showb $ ppar tprog
          (Right s) <- readFile "a.ent"
            | Left err => putStrLn "Error reading file"
          showb $ ppar s
          pure ()
