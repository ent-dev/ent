module Tools.Ent.Util

%access public export

infixl 4 <$>|

(<$>|) : Functor f => (a -> b) -> Lazy (f a) -> f b
(<$>|) f g = map f (Force g)
