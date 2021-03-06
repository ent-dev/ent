module Tools.Ent.Parser

import public Control.Monad.Identity

import Tools.Ent.AST
import Tools.Ent.Util
import Tools.Ent.Parser.Expr
import Tools.Ent.Parser.API
import Tools.Ent.Parser.Core

import Debug.Trace

-- data Result a = Success String a | Failure (List (String, String))

-- export
-- record Parser (m : Type -> Type) a where
--   constructor MkParser
--   run :
--     (ret : Type) ->
--     (succ : (a -> String -> m ret)) ->
--     (fail : ((List (String, String) ) -> m ret)) ->
--     String ->
--     m ret

-- execParser : Monad m => Parser m a -> (input : String) -> m (Result a)
-- execParser {a} (MkParser p) input = p (Result a) succ fail input
--   where succ x i = pure $ Success i x
--         fail     = pure . Failure

-- fail : String -> Parser m a
-- fail s = MkParser $ \r, succ, fail, inp => fail [(inp, s)]


-- infixr 0 ~$
-- infixl 4 <**>
-- --infixl 4 <**>|
-- infixl 4 <$
-- (~$) : (a -> b) -> a -> b
-- (~$) f a = f a

-- (<**>) : Applicative m => m a -> m (a -> b) -> m b
-- (<**>) = liftA2 (flip (~$))

-- -- (<**>|) : Applicative m => m a -> Lazy (m (a -> b)) -> m b
-- -- (<**>|) f  g = liftA2 (flip (~$)) f (Force g)

-- (<$) : Functor f => a -> f b -> f a
-- (<$) = map . const

-- infixl 0 <?>
-- public export
-- interface Alternative m => Parsing (m : Type -> Type) where
--   (<?>) : m a -> String -> m a

--   token : m a -> m () -> m a
--   token p seps = p <* (seps <|> pure ())



-- using(Monad m)
--   Functor (Parser m) where
--     map f (MkParser p) = MkParser $ \r, succ => p r (succ . f)

--   export
--   Applicative (Parser m) where
--     pure x = MkParser $ \r, succ, fail => succ x
--     (<*>) (MkParser f) (MkParser g) =
--       MkParser $ \r, succ, fail =>
--         f r (\f' => g r (succ . f') fail) fail

--   Alternative (Parser m) where
--     empty = fail "non-empty alternative"
--     (<|>) (MkParser x) (MkParser y) = MkParser $ \r, succ, fail, inp =>
--       x r succ (\err => y r succ (fail . (err ++)) inp) inp

--   Monad m => Monad (Parser m) where
--     (>>=) (MkParser x) f = MkParser $ \r, sc, fc =>
--       x r (\x' => let MkParser y = f x' in y r sc fc) fc

--   Alternative (Parser m) => Parsing (Parser m) where
--     (MkParser f) <?> msg = MkParser $ \r, sc, fc, i =>
--       f r sc (fc . ((i, msg) ::)) i


-- infixl 2 <*>|

-- (<*>|) : Parser m (a -> b) -> Lazy (Parser m a) -> Parser m b
-- (<*>|) (MkParser f) x = MkParser $ \r, sc, fc =>
--   f r (\f' => let MkParser g = x in g r (sc . f') fc) fc

-- -- infixl 0 <?>
-- -- (<?>) : Monad m => Parser m a -> String -> Parser m a
-- -- (MkParser f) <?> msg = MkParser $ \r, sc, fc, i =>
-- --   f r sc (fc . ((i, msg) ::)) ie

-- many : Monad m => Parser m a -> Parser m (List a)
-- many p = (pure (List.(::)) <*> p <*>| many p) <|> pure List.Nil

-- some : Monad m => Parser m a -> Parser m (List a)
-- some p = [| p :: many p |]

-- satisfy : Monad m => (Char -> Bool) -> Parser m Char
-- satisfy c = MkParser $ \ret, sc, fc, inp =>
--   case unpack inp of
--     (x :: xs) => if c x then sc x (pack xs)
--                         else fc [(inp, "a different character")]
--     []        => fc [(inp, "a token, not EOF")]


-- %access export

-- parse : Parser Identity a -> String -> Either (List (String, String)) a
-- parse f input = let Id r = execParser f input in
--   case r of
--     Success _ x => Right x
--     Failure es  => Left es

-- space : Monad m => Parser m Char
-- space = satisfy isSpace

-- skipMany : Monad m => Parser m a -> Parser m ()
-- skipMany p = () <$ many p

-- manySpaces : Monad m => Parser m ()
-- manySpaces = skipMany space

-- someSpaces : Monad m => Parser m ()
-- someSpaces = space *> skipMany space

-- anyAlphaChar : Monad m => Parser m Char
-- anyAlphaChar = satisfy isAlpha

-- digit : Monad m => Parser m Char
-- digit = satisfy isDigit

-- natural' : Monad m => Parser m (List Char)
-- natural' = some digit



-- char : Monad m => Char -> Parser m Char
-- char ch = satisfy (== ch)

-- dot : Monad m => Parser m Char
-- dot = satisfy (== '.')

-- equals : Monad m => Parser m Char
-- equals = satisfy (== '=')

-- charRep : Monad m => Char -> Parser m (List Char)
-- charRep ch = many $ char ch

-- upperChar : Monad m => Parser m Char
-- upperChar = satisfy isUpper

-- lowerChar : Monad m => Parser m Char
-- lowerChar = satisfy isLower

-- string : Monad m => String -> Parser m String
-- string s = pack <$> (traverse char $ unpack s)

upperId : Monad m => Parser m String
upperId = do fl <- upperChar
             xs <- many $ anyAlphaChar
             pure (pack $ fl :: xs)

lowerId : Monad m => Parser m String
lowerId = do fl <- lowerChar
             xs <- many $ anyAlphaChar
             pure (pack $ fl :: xs)

-- stringRep : Monad m => String -> Parser m (List String)
-- stringRep s = many $ string s

-- oneOf : Monad m => String -> Parser m Char
-- oneOf chs = satisfy (\c => elem c $ unpack chs)



-- ---------------[Operators]------------------------------------------------ --
-- %access export

-- data Assoc = AssocLeft | AssocRight | AssocNone

-- data Operator : (m : Type -> Type) -> a -> Type where
--   Infix : (m (a -> a -> a)) -> Assoc -> Operator m a
--   Prefix : (m (a -> a)) -> Operator m a
--   Postfix : (m (a -> a)) -> Operator m a

-- OperatorTable : (Type -> Type) -> Type -> Type
-- OperatorTable m a = List $ List $ Operator m a

postfixOp : Monad m => String -> (PTerm -> PTerm) -> Operator (Parser m) PTerm
postfixOp s f = Postfix $ do token (string s) someSpaces
                             pure f

prefixOp : Monad m => String -> (PTerm -> PTerm) -> Operator (Parser m) PTerm
prefixOp s f = Prefix $ do string s
                           pure f

binaryOp : Monad m => String
                   -> (PTerm -> PTerm -> PTerm)
                   -> Assoc
                   -> Operator (Parser m) PTerm
binaryOp name f    =  Infix (do token (string name) someSpaces
                                pure f)

table : Monad m => OperatorTable (Parser m) PTerm
table = [[binaryOp "^"
                   (\t1, t2 => PApp (PRef $ UN "exp")
                                    [MN ("arg1 = " ++ show t1),
                                     MN ("arg2 = " ++ show t2)])
                   AssocRight],

         [prefixOp "-"
                   (\t => PApp (PRef (UN "negate"))
                               [MN ("arg = " ++ show t)]),
          postfixOp "++" (\t => PRef (UN $ "postfix ++" ++ show t))],
         [binaryOp "*" (\t1, t2 => PApp (PRef $ UN "mult")
                                        [MN ("arg1 = " ++ show t1),
                                         MN ("arg2 = " ++ show t2)]) AssocLeft,
          binaryOp "/" (\t1, t2 => PApp (PRef $ UN "div")
                                        [MN ("arg1 = " ++ show t1),
                                         MN ("arg2 = " ++ show t2)]) AssocLeft],
         [binaryOp "+" (\t1, t2 => PApp (PRef $ UN "plus")
                                        [MN ("arg1 = " ++ show t1),
                                         MN ("arg2 = " ++ show t2)]) AssocLeft,
          binaryOp "-" (\t1, t2 => PApp (PRef $ UN "minus")
                                        [MN ("arg1 = " ++ show t1),
                                         MN ("arg2 = " ++ show t2)]) AssocLeft]]


-- mutual
--   mrr1 : Alternative m => m (a -> a -> a)
--                       -> m a
--                       -> (m (a), m (a))
--                       -> Nat
--                       -> m (a -> a)
--   mrr1 rassocOp termP (ambiguousLeft, ambiguousNone) n
--     = if n > 10 then pure id
--            else trace "call mutual " $ (( flip <$> rassocOp) <*>
--             (termP <**> (mrr1 rassocOp termP (ambiguousLeft, ambiguousNone) (n + 1) <|> pure id))

--                           <|> ambiguousLeft
--                           <|> ambiguousNone)

  -- mrr2 : Alternative m => m (a -> a -> a)
  --                     -> m a
  --                     -> (m (a), m (a))
  --                     -> m (a -> a)
  -- mrr2 rassocOp termP (ambiguousLeft, ambiguousNone)
  --   = (mrr1 rassocOp termP (ambiguousLeft, ambiguousNone)) <|> (trace "inf loop?" $ pure id)


-- mutual
--   mrl1 : Alternative m => m (a -> a -> a)
--                       -> m a
--                       -> (m (a), m (a))
--                       -> Nat
--                       -> m (a -> a)
--   mrl1 lassocOp termP (ambiguousRight, ambiguousNone) n
--     = if n > 10 then pure id
--            else trace "call mutual " $ (((flip <$> lassocOp) <*> termP) <**> ((.) <$> ((mrl1 lassocOp termP (ambiguousRight, ambiguousNone) (n + 1)) <|> pure id)))

  -- mrl2 : Alternative m => m (a -> a -> a)
  --                     -> m a
  --                     -> (m (a), m (a))
  --                     -> m (a -> a)
  -- mrl2 lassocOp termP (ambiguousRight, ambiguousNone)
  --   = (mrl1 lassocOp termP (ambiguousRight, ambiguousNone)) <|> pure id




-- buildExpressionParser :  (Alternative m, Applicative m, Parsing m) => OperatorTable m a
--                                  -> m a
--                                  -> m a
-- buildExpressionParser operators accExpression
--   = foldl makeParser accExpression operators
--       where
--         makeParser : (Alternative m, Parsing m) => m a -> List (Operator m a) -> m a
--         makeParser term ops
--           = let

--                 (rassocOps,lassocOps,nassocOps,prefixOps,postfixOps) = foldr splitOps ([],[],[],[],[]) ops

--                 rassocOp   = choice rassocOps
--                 lassocOp   = choice lassocOps
--                 nassocOp   = choice nassocOps
--                 prefixOp   = choice prefixOps
--                 postfixOp  = choice postfixOps


--                 ambiguousRight    = ambiguous "right" rassocOp
--                 ambiguousLeft     = ambiguous "left" lassocOp
--                 ambiguousNone     = ambiguous "non" nassocOp


--                 ambiguous2Right    = ambiguous2 "right" rassocOp
--                 ambiguous2Left     = ambiguous2 "left" lassocOp
--                 ambiguous2None     = ambiguous2 "non" nassocOp




--                 postfixP   = postfixOp <|> pure id

--                 prefixP    = prefixOp <|> pure id

--                 termP      = (prefixP <*> term) <**> postfixP

--                 rassocP  = mrr1 rassocOp termP (ambiguousLeft, ambiguousNone) 0

--                 -- rassocP1 = mrr2 rassocOp termP (ambiguousLeft, ambiguousNone)


--                 lassocP = mrl1 lassocOp termP (ambiguousRight, ambiguousNone) 0

--                 -- lassocP1 = mrl2 lassocOp termP (ambiguousRight, ambiguousNone)

--                 -- nassocP = (flip <$> nassocOp <*> termP)
--                 --              <**> (ambiguous2Right
--                 --               <|> ambiguous2Left
--                 --               <|> ambiguous2None
--                 --               <|> pure id)


--             in trace "created term " termP <**> (rassocP <|> lassocP <|> pure id) -- <?> "operator"
--             where
--               splitOps : Alternative m
--                        => Operator m a
--                        -> ((List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a)), (List $ m (a -> a)))
--                        -> ((List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a)), (List $ m (a -> a)))
--               splitOps (Infix op assoc) (rassoc,lassoc,nassoc,pref,postfix)
--                 = case assoc of
--                     AssocNone  => (rassoc, lassoc, op::nassoc, pref, postfix)
--                     AssocLeft  => trace "got left" (rassoc,op::lassoc,nassoc,pref,postfix)
--                     AssocRight => (op::rassoc,lassoc,nassoc,pref,postfix)
--               splitOps (Prefix op) (rassoc,lassoc,nassoc,pref,postfix)
--                 = trace "Got prefix " (rassoc,lassoc,nassoc,op::pref,postfix)
--               splitOps (Postfix op) (rassoc,lassoc,nassoc,pref,postfix)
--                 = (rassoc,lassoc,nassoc,pref,op::postfix)

--               ambiguous : String -> m (a -> a -> a) -> m (a)
--               ambiguous assoc op =  trace "inside ambiguous" $ op *> empty <?> ("ambiguous use of a " ++ assoc ++ "-associative operator")
--               ambiguous2 : String -> m (a -> a -> a) -> m (a -> a)
--               ambiguous2 assoc op = op *> empty <?> ("ambiguous use of a " ++ assoc ++ "-associative operator")

-- leftops : Monad m => OperatorTable (Parser m) PTerm
-- leftops = 1 `drop` table

-- splitOps : Alternative m
--                        => Operator m a
--                        -> ((List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a)), (List $ m (a -> a)))
--                        -> ((List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a)), (List $ m (a -> a)))
-- splitOps (Infix op assoc) (rassoc,lassoc,nassoc,pref,postfix)
--                 = case assoc of
--                     AssocNone  => (rassoc, lassoc, op::nassoc, pref, postfix)
--                     AssocLeft  => (rassoc,op::lassoc,nassoc,pref,postfix)
--                     AssocRight => (op::rassoc,lassoc,nassoc,pref,postfix)
-- splitOps (Prefix op) (rassoc,lassoc,nassoc,pref,postfix)
--                 = (rassoc,lassoc,nassoc,op::pref,postfix)
-- splitOps (Postfix op) (rassoc,lassoc,nassoc,pref,postfix)
--                 = (rassoc,lassoc,nassoc,pref,op::postfix)


-- test : PTerm -> PTerm
-- test = (\t => PApp (PRef (UN "negate"))
--                                [MN ("arg = " ++ show t)])

-- tm : Monad m => List $ Parser m (PTerm -> PTerm)
-- tm = [(do string "-"
--           pure test)]


-- opp : Monad m => Parser m (PTerm)
-- opp = ((choice tm <|> pure f) <*> natural) <**> (choice postm <|> pure id)

-- oppp : Monad m => Parser m PTerm -> Parser m (PTerm)
-- oppp opp = ((choice postm <|> pure id) <*> opp) <**> (choice postm <|> pure id)

-- opmany : Monad m => Parser m PTerm
-- opmany = oppp $ oppp $ oppp $ oppp opp

-- tmain : Monad m => Parser m PTerm
-- tmain = {-(choice []) <*> -}((choice tm <*> expr) <**> (choice postm))



-- binoperator : Monad m => Operator (Parser m) PTerm
-- binoperator = binaryOp "+" (\t1, t2 => PApp (PRef $ UN "plus")
--                                         [MN ("arg1 = " ++ show t1),
--                                          MN ("arg2 = " ++ show t2)]) AssocLeft

-- plusOp : Monad m => Parser m (PTerm -> PTerm -> PTerm)
-- plusOp = do token (string "+") someSpaces
--             pure (\t1, t2 => PApp (PRef $ UN "plus")
--                                         [MN ("arg1 = " ++ show t1),
--                                          MN ("arg2 = " ++ show t2)])

-- lassocp : Alternative m => m (a -> a -> a)
--                       -> m a
--                       -> Nat
-- --                      -> (m (a), m (a))
--                       -> m (a -> a)
-- lassocp lassocOp termP n -- (ambiguousRight, ambiguousNone)
--     = if n > 10 then pure id
--          else trace "call mutual " $
--               (((flip <$> lassocOp) <*> termP) <**>
--                ((.) <$> ((lassocp lassocOp termP (n + 1)) <|>  pure id)))

-- plusExpr : Monad m => Parser m PTerm
-- plusExpr =  natural <**> (lassocp plusOp natural 0 <|> pure id)






-- --------[Language]-------------------------------------------------------- --

%access export
namespace lang

  pnatural : Monad m => Parser m PTerm
  pnatural = do n <- token natural' manySpaces
                pure $ PRef (UN $ pack n)

  pchar : Monad m => Parser m PTerm
  pchar = do char '\''
             ch <- satisfy (const True)
             char '\''
             pure $ PConstant EChar (cast ch ++ "")

  pstring : Monad m => Parser m PTerm
  pstring = do char '"'
               chs <- many $ satisfy (/= '"')
               char '"'
               pure (PConstant EString $ pack chs)

  -- booleancst : Monad m => Parser m PTerm
  -- booleancst = (do s <- string "True"; pure (PConstant EBoolean "t")) <|>
  --              (do s <- string "False"; pure (PConstant EBoolean "f"))

  valCtor : Monad m => Parser m PTerm
  valCtor = pnatural <|> pstring <|> pchar

  opExpr : Monad m => Parser m PTerm
  opExpr = buildExpressionParser table valCtor

  scopeDecl : Monad m => Parser m PTerm
  scopeDecl = do fp <- upperId
                 rems <- many (do dot; upperId)
                 pure $ PScope (fp :: rems)

  valDef : Monad m => Parser m PTerm
  valDef = do it <- lowerId
              many space
              equals
              many space
              et <- valCtor
              pure $ PDef (UN it) [] et

  printStmt : Monad m => Parser m PTerm
  printStmt = do token (string "print") someSpaces
                 s <- pstring
                 many space
                 pure s

  pmain : Monad m => Parser m (List PTerm)
  pmain = do token (string "main =") someSpaces
             strs <- some $ token printStmt someSpaces
             pure strs

  progParser : Monad m => Parser m (PTerm, List PTerm, List PTerm)
  progParser = do st <- token scopeDecl someSpaces
                  defs <- many $ token valDef someSpaces
                  strs <- pmain
                  pure (st, defs, strs)
