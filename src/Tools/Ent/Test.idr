module Tools.Ent.Test

import Control.Monad.Identity
import Tools.Ent.Parser

Parser : Type -> Type
Parser = Parser Identity

ch : Char -> Parser Char
ch x = char x

str : String -> Parser String
str s = string s

test : Either String String
test = parse (str "xjd") "xjdls"

