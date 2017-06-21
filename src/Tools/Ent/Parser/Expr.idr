module Tools.Ent.Parser.Expr

import Tools.Ent.Parser.Core
import Tools.Ent.Parser.API

import Debug.Trace

-- ---------------[Operators]------------------------------------------------ --
%access export

public export
data Assoc = AssocLeft | AssocRight | AssocNone

public export
data Operator : (m : Type -> Type) -> a -> Type where
  Infix : (m (a -> a -> a)) -> Assoc -> Operator m a
  Prefix : (m (a -> a)) -> Operator m a
  Postfix : (m (a -> a)) -> Operator m a

public export
OperatorTable : (Type -> Type) -> Type -> Type
OperatorTable m a = List $ List $ Operator m a

mutual
  mrr1 : Alternative m => m (a -> a -> a)
                      -> m a
                      -> (m (a), m (a))
                      -> Nat
                      -> m (a -> a)
  mrr1 rassocOp termP (ambiguousLeft, ambiguousNone) n
    = if n > 10 then pure id
           else trace "call mutual " $ (( flip <$> rassocOp) <*>
            (termP <**> (mrr1 rassocOp termP (ambiguousLeft, ambiguousNone) (n + 1) <|> pure id))

                          <|> ambiguousLeft
                          <|> ambiguousNone)

  -- mrr2 : Alternative m => m (a -> a -> a)
  --                     -> m a
  --                     -> (m (a), m (a))
  --                     -> m (a -> a)
  -- mrr2 rassocOp termP (ambiguousLeft, ambiguousNone)
  --   = (mrr1 rassocOp termP (ambiguousLeft, ambiguousNone)) <|> (trace "inf loop?" $ pure id)


mutual
  mrl1 : Alternative m => m (a -> a -> a)
                      -> m a
                      -> (m (a), m (a))
                      -> Nat
                      -> m (a -> a)
  mrl1 lassocOp termP (ambiguousRight, ambiguousNone) n
    = if n > 10 then pure id
           else trace "call mutual " $ (((flip <$> lassocOp) <*> termP) <**> ((.) <$> ((mrl1 lassocOp termP (ambiguousRight, ambiguousNone) (n + 1)) <|> pure id)))

  -- mrl2 : Alternative m => m (a -> a -> a)
  --                     -> m a
  --                     -> (m (a), m (a))
  --                     -> m (a -> a)
  -- mrl2 lassocOp termP (ambiguousRight, ambiguousNone)
  --   = (mrl1 lassocOp termP (ambiguousRight, ambiguousNone)) <|> pure id




buildExpressionParser :  (Alternative m, Applicative m, Parsing m) => OperatorTable m a
                                 -> m a
                                 -> m a
buildExpressionParser operators accExpression
  = foldl makeParser accExpression operators
      where
        makeParser : (Alternative m, Parsing m) => m a -> List (Operator m a) -> m a
        makeParser term ops
          = let

                (rassocOps,lassocOps,nassocOps,prefixOps,postfixOps) = foldr splitOps ([],[],[],[],[]) ops

                rassocOp   = choice rassocOps
                lassocOp   = choice lassocOps
                nassocOp   = choice nassocOps
                prefixOp   = choice prefixOps
                postfixOp  = choice postfixOps


                ambiguousRight    = ambiguous "right" rassocOp
                ambiguousLeft     = ambiguous "left" lassocOp
                ambiguousNone     = ambiguous "non" nassocOp


                ambiguous2Right    = ambiguous2 "right" rassocOp
                ambiguous2Left     = ambiguous2 "left" lassocOp
                ambiguous2None     = ambiguous2 "non" nassocOp




                postfixP   = postfixOp <|> pure id

                prefixP    = prefixOp <|> pure id

                termP      = (prefixP <*> term) <**> postfixP

                rassocP  = mrr1 rassocOp termP (ambiguousLeft, ambiguousNone) 0

                -- rassocP1 = mrr2 rassocOp termP (ambiguousLeft, ambiguousNone)


                lassocP = mrl1 lassocOp termP (ambiguousRight, ambiguousNone) 0

                -- lassocP1 = mrl2 lassocOp termP (ambiguousRight, ambiguousNone)

                -- nassocP = (flip <$> nassocOp <*> termP)
                --              <**> (ambiguous2Right
                --               <|> ambiguous2Left
                --               <|> ambiguous2None
                --               <|> pure id)


            in trace "created term " termP <**> (rassocP <|> lassocP <|> pure id) -- <?> "operator"
            where
              splitOps : Alternative m
                       => Operator m a
                       -> ((List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a)), (List $ m (a -> a)))
                       -> ((List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a -> a)), (List $ m (a -> a)), (List $ m (a -> a)))
              splitOps (Infix op assoc) (rassoc,lassoc,nassoc,pref,postfix)
                = case assoc of
                    AssocNone  => (rassoc, lassoc, op::nassoc, pref, postfix)
                    AssocLeft  => trace "got left" (rassoc,op::lassoc,nassoc,pref,postfix)
                    AssocRight => (op::rassoc,lassoc,nassoc,pref,postfix)
              splitOps (Prefix op) (rassoc,lassoc,nassoc,pref,postfix)
                = trace "Got prefix " (rassoc,lassoc,nassoc,op::pref,postfix)
              splitOps (Postfix op) (rassoc,lassoc,nassoc,pref,postfix)
                = (rassoc,lassoc,nassoc,pref,op::postfix)

              ambiguous : String -> m (a -> a -> a) -> m (a)
              ambiguous assoc op =  trace "inside ambiguous" $ op *> empty <?> ("ambiguous use of a " ++ assoc ++ "-associative operator")
              ambiguous2 : String -> m (a -> a -> a) -> m (a -> a)
              ambiguous2 assoc op = op *> empty <?> ("ambiguous use of a " ++ assoc ++ "-associative operator")
