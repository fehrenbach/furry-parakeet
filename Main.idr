module Main

interface Symantics (repr : Type -> Type) where
  int : Int -> repr Int
  bool : Bool -> repr Bool
  string : String -> repr String
  nil : repr (List a)
  not : repr Bool -> repr Bool
  (==) : Eq a => repr a -> repr a -> repr Bool
  (*) : Num a => repr a -> repr a -> repr a
  lam : (repr a -> repr b) -> repr (a -> b)
  app : repr (a -> b) -> repr a -> repr b
  foreach : Lazy (repr (List a)) -> (repr a -> repr (List b)) -> repr (List b)
  where' : repr Bool -> Lazy (repr (List a)) -> repr (List a) 
  yield : repr a -> repr (List a)
  union_all : repr (List a) -> repr (List a) -> repr (List a)

record Product where
  constructor MkProduct
  pid : Int
  name : String
  price : Int

record Order where
  constructor MkOrder
  oid : Int
  opid : Int
  qty : Int
  
record Sale where
  constructor MkSale
  spid : Int
  sname : String
  amount : Int

interface Symantics repr => SymSchema (repr : Type -> Type) where
  product : repr Int -> repr String -> repr Int -> repr Product
  pid : repr Product -> repr Int
  name : repr Product ->  repr String
  price : repr Product -> repr Int
  products : Lazy (repr (List Product))
  
  order : repr Int -> repr Int -> repr Int -> repr Order
  oid : repr Order -> repr Int
  opid : repr Order -> repr Int
  qty : repr Order -> repr Int
  orders : Lazy (repr (List Order))
  
  sale : repr Int -> repr String -> repr Int -> repr Sale

listFive : Symantics r => r (List Int)
listFive = yield (int 5)

-- products
tablet : SymSchema r => r Product
tablet = product (int 1) (string "Tablet") (int 500)
laptop : SymSchema r => r Product
laptop = product (int 2) (string "Laptop") (int 1000)
desktop : SymSchema r => r Product
desktop = product (int 3) (string "Desktop") (int 1000)
router : SymSchema r => r Product
router = product (int 4) (string "Router") (int 150)
hdd : SymSchema r => r Product
hdd = product (int 5) (string "HDD") (int 100)
ssd : SymSchema r => r Product
ssd = product (int 6) (string "SSD") (int 500)

-- orders
o1 : SymSchema r => r Order
o1 = order (int 1) (int 1) (int 5)
o2 : SymSchema r => r Order
o2 = order (int 1) (int 2) (int 5)
o3 : SymSchema r => r Order
o3 = order (int 1) (int 4) (int 2)
o4 : SymSchema r => r Order
o4 = order (int 2) (int 5) (int 10)
o5 : SymSchema r => r Order
o5 = order (int 2) (int 6) (int 20)
o6 : SymSchema r => r Order
o6 = order (int 3) (int 2) (int 50)


data Evaluator a = R a

eval : Evaluator a -> a
eval (R a) = a

Symantics Evaluator where
  int = R
  bool = R
  string = R
  not (R b) = R (not b)
  nil = R []
  (==) (R a) (R b) = R (a == b)
  (*) (R a) (R b) = R (a * b)
  lam f = R (\a => eval (f (R a)))
  app (R f) (R a) = R (f a)
  foreach t f = 
    case eval t of
      []        => R []
      (x :: xs) => R (eval (f (R x)) ++ (eval (foreach (R xs) f)))
  where' (R b) r = if b then r else R []
  yield (R x) = R [x]
  union_all (R as) (R bs) = R (as ++ bs)

Symantics Evaluator => SymSchema Evaluator where
  product (R pid) (R name) (R price) = R (MkProduct pid name price)
  pid (R p) = R (pid p)
  name (R p) = R (name p)
  price (R p) = R (price p)
  products = R (map eval [tablet, laptop, desktop, router, hdd, ssd]) -- yield tablet `union_all` yield laptop

  order (R oid) (R opid) (R qty) = R (MkOrder oid opid qty)
  oid (R o) = R (oid o)
  opid (R o) = R (opid o)
  qty (R o) = R (qty o)
  orders = R (map eval [o1, o2, o3, o4, o5, o6])
  
  sale (R spid) (R sname) (R amount) = R (MkSale spid sname amount)

-- eval (foreach products (\p => yield (pid p)) `union_all` foreach orders (\o => yield (opid o)))

-- Q1
q1 : SymSchema r => r Int -> r (List Order)
q1 xoid = foreach orders $ \o =>
            where' (oid o == xoid) $
              yield o

q1_2 : SymSchema r => r (List Order)
q1_2 = q1 (int 2) -- I'm not using `app` and `lam` anywhere. Is that a problem?

-- eval q1_2

q2 : SymSchema r => r Order -> r (List Sale)
q2 o = foreach products $ \p =>
         where' (not (not (pid p == opid o))) $
           yield $ sale (pid p) (name p) (price p * qty o)

-- eval (q2 (order (int 2) (int 5) (int 10)))
q3 : SymSchema r => r Int -> r (List Sale)
q3 x = foreach (q1 x) $ \y =>
         q2 y
-- Still no app and lam... Oleg et. al. use app, but no lam either

-- eval (q3 (int 2))

data Printer a = P String

print : Printer a -> String
print (P a) = a

Symantics Printer where
  int i = P (show i)
  bool b = P (show b)
  string s = P s
  not (P b) = P ("(NOT " ++ b ++ ")")
  nil = P "[]"
  (==) (P a) (P b) = P (a ++ " == " ++ b)
  (*) (P a) (P b) = P ("(" ++ a ++ " * " ++ b ++ ")")
  lam f = P "lam"
  app (P f) (P a) = P "app"
  foreach t f =
    let ts : String = print t
        fs : String = print (f (P "$arg"))
    in P ("FOREACH (" ++ ts ++ ") " ++ fs)
  where' (P b) r = P ("WHERE " ++ b ++ " " ++ (print r))
  yield (P x) = P ("YIELD " ++ x)
  union_all (P as) (P bs) = P (as ++ " UNION ALL " ++ bs)

Symantics Printer => SymSchema Printer where
  product _ _ _ = P "product"
  pid (P x) = P (x ++ ".pid")
  name (P x) = P (x ++ ".name")
  price (P x) = P (x ++ ".price")
  products = P "products"
  order x y z = P "order"
  oid (P x) = P (x ++ ".oid")
  opid (P x) = P (x ++ ".pid")
  qty (P x) = P (x ++ ".qty")
  orders = P "orders"
  sale x y z = P $ "(MkSale " ++ print x ++ " " ++ print y ++ " " ++ print z ++ ")"

-- λΠ> print (q3 (int 2))
-- "FOREACH (FOREACH (orders) WHERE $arg.oid == 2 YIELD $arg) FOREACH (products) WHERE $arg.pid == $arg.pid YIELD (MkSale $arg.pid $arg.name ($arg.price * $arg.qty))" : String

data ConstantFolder : (repr : Type -> Type) -> (a : Type) -> Type where
  Empty : ConstantFolder repr (List a)
  Unknown : (repr a) -> ConstantFolder repr a

dyn : Symantics repr => ConstantFolder repr a -> repr a
dyn Empty = nil
dyn (Unknown x) = x

Symantics r => Symantics (ConstantFolder r) where
  nil = Empty
  union_all Empty y = y
  union_all (Unknown x) y = Unknown (union_all x (dyn y))
  -- boilerplate
  int x = Unknown (int x)
  bool x = Unknown (bool x)
  string x = Unknown (string x)
  not b = Unknown (not (dyn b))
  lam f = Unknown (lam (\x => dyn (f (Unknown x))))
  app x y = Unknown (app (dyn x) (dyn y))
  foreach t f = Unknown $ foreach (Delay (dyn t)) (\x => dyn (f (Unknown x)))
  where' x y = Unknown (where' (dyn x) (dyn y))
  yield x = Unknown (yield (dyn x))
  (==) x y = Unknown (dyn x == dyn y)
  (*) x y = Unknown (dyn x * dyn y)

SymSchema r => SymSchema (ConstantFolder r) where
-- (Symantics (ConstantFolder r), SymSchema r) => SymSchema (ConstantFolder r) where
  product x y z = Unknown $ product (dyn x) (dyn y) (dyn z)
  pid = pid
  name = name
  price = price
  products = products
  order = order
  oid = oid
  opid = opid
  qty = qty
  orders = Unknown $ Force orders -- not sure I like this Force
  sale = sale

cfp' : ConstantFolder Printer (List Int)
cfp' = union_all nil (yield (int 2))

-- print (dyn (union_all nil (yield (int 2))))

-- From http://okmij.org/ftp/tagless-final/course/RR.hs
-- 
-- {-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

-- -- * Reflection-Reification pair

-- module RR where

-- class RR t repr where
--   fwd :: repr a -> t repr a
--   bwd :: t repr a -> repr a

--   map1 :: (repr a -> repr b) -> (t repr a -> t repr b)
--   map1 f = fwd . f . bwd

--   map2 :: (repr a -> repr b -> repr c) ->
--           (t repr a -> t repr b -> t repr c)
--   map2 f e1 e2 = fwd (f (bwd e1) (bwd e2))


-- -- * fwd is generally not surjective and bwd is not injective
-- -- * bwd . fwd == id,  fwd . bwd /= id

-- -- * QUIZ
-- -- * map1 looks like fmap of a Functor. Can it be defined or related
-- -- * to Functor?

interface RR (t : (Type -> Type) -> Type -> Type) (repr : Type -> Type) where
  fwd : repr a -> t repr a
  bwd : t repr a -> repr a
  
  map1 : (repr a -> repr b) -> (t repr a -> t repr b)
  map1 f = fwd . f . bwd
  
  map2 : (repr a -> repr b -> repr c) -> (t repr a -> t repr b -> t repr c)
  map2 f e1 e2 = fwd (f (bwd e1) (bwd e2))

-- print (q_3 (int 2))

data N2N : (repr : Type -> Type) -> (a : Type) -> Type where
  Unk : repr a -> N2N repr a           -- no annotation
  Neg : repr Bool -> N2N repr Bool     -- it is a negation

-- instance Symantics repr => RR N2N repr where
--   bwd (Unk e) = e
--   bwd (Neg x) = neg x

--   fwd = Unk

Symantics repr => RR N2N repr where
  bwd (Unk e) = e
  bwd (Neg x) = not x
  
  fwd = Unk

-- instance Symantics repr => Symantics (N2N repr) where
--   lit = fwd . lit

--   neg (Unk e) = Neg e                   -- we statically know we negated
--   neg (Neg x) = Unk x

--   -- and e1 e2 = Unk $ and (bwd e1) (bwd e2)
--   and = map2 and
--   or  = map2 or

Symantics repr => Symantics (N2N repr) where
  bool = fwd . bool

  not (Unk e) = Neg e                   -- we statically know we negated
  not (Neg x) = Unk x

  int = fwd . int
  string = fwd . string
  (==) = map2 (==)
  (*) = map2 (*)
  nil = fwd nil
  lam f = fwd (lam (\x => bwd (f (fwd x))))
  app = map2 app
  foreach x f = fwd $ foreach (bwd x) (\x => bwd (f (fwd x)))
  where' x y = fwd $ where' (bwd x) (bwd y)
  yield = map1 yield -- not sure..
  union_all = map2 union_all

-- instance SymInput repr => SymInput (N2N repr) where
--   wireX = fwd wireX
--   wireY = fwd wireY
--   wireZ = fwd wireZ

SymSchema r => SymSchema (N2N r) where
  product x y z = fwd $ product (bwd x) (bwd y) (bwd z)
  pid = map1 pid
  name = map1 name
  price = map1 price
  products = fwd $ Force products
  order x y z = fwd $ order (bwd x) (bwd y) (bwd z)
  oid = map1 oid
  opid = map1 opid
  qty = map1 qty
  orders = fwd $ Force orders
  sale x y z = fwd $ sale (bwd x) (bwd y) (bwd z)

-- -- * Observe the result
-- -- A type-specific version of bwd
-- obsN2N :: Symantics repr => N2N repr a -> repr a
-- obsN2N = bwd
obsN2N : Symantics repr => N2N repr a -> repr a
obsN2N = bwd

-- print (obsN2N (q3 (int 2)))
