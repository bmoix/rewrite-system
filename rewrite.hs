--------------------------------------------------------------------------------
------------------------------   Class Rewrite    ------------------------------
--------------------------------------------------------------------------------

type Signature = [(String, Int)]
type Position = [Int]
type Substitution a = [(a, a)]
type Strategy a = ([(Position, a)] -> [(Position, a)])

class Eq a => Rewrite a where
  getVars :: a -> [a]
  valid :: Signature -> a -> Bool
  match :: a -> a -> [(Position, Substitution a)]
  apply :: a -> Substitution a -> a
  replace :: a -> [(Position, a)] -> a
  evaluate :: a -> a

--------------------------------------------------------------------------------
------------------------------   Rewrite System   ------------------------------
--------------------------------------------------------------------------------

-- generic functions for every type of rewrite system

data Rule a = Rule a a

instance Show a => Show (Rule a) where
  show (Rule x y) = show x ++ " --> " ++ show y 

type RewriteSystem a = [Rule a]

validRule :: Rewrite a => Signature -> Rule a -> Bool
validRule sign (Rule a1 a2) = valid sign a1 && valid sign a2
                              && includes (getVars a2) (getVars a1)

includes :: Eq a => [a] -> [a] -> Bool
includes as bs = all (`elem` bs) as

validRewriteSystem :: Rewrite a => Signature -> RewriteSystem a -> Bool
validRewriteSystem sign = all $ validRule sign

oneStepRewrite :: Rewrite a => RewriteSystem a -> a -> Strategy a -> a
oneStepRewrite rs a str = replace a $ str (concatMap f rs)
  where f (Rule r1 r2) = map (\(p,sub) -> (p, apply r2 sub)) (match r1 a)

rewrite :: Rewrite a => RewriteSystem a -> a -> Strategy a -> a
rewrite rs a str 
  | a == x    = x
  | otherwise = rewrite rs x str
    where x = evaluate $ oneStepRewrite rs a str

nrewrite :: Rewrite a => RewriteSystem a -> a -> Strategy a -> Int -> a
nrewrite rs a str 0 = a
nrewrite rs a str n = nrewrite rs (evaluate (oneStepRewrite rs a str)) str (n-1)


--------------------------------------------------------------------------------
------------------------------       Strings      ------------------------------
--------------------------------------------------------------------------------


data RString = RString String
  deriving Eq

instance Show RString where
  show (RString s) = s

instance Rewrite RString where
  getVars s = []
  
  valid sign s = all (\(RString x) -> elem x (map fst sign)) $ getVars s


  match (RString s1) (RString s2) = stringMatch 0 s1 s2

  apply r [] = r
  apply (RString r) ((_, RString s):sub) = RString $ r ++ s

  replace s [] = s
  replace (RString s) ((p,RString s2):ls) = RString $ take (head p) s ++ s2

  evaluate = id

-- READ --

readRString :: String -> RString
readRString = RString 

readRStringSystem :: [(String, String)] -> RewriteSystem RString
readRStringSystem = map (\x -> Rule (RString (fst x)) (RString (snd x)))

-- STRATEGIES --

leftmost :: Strategy RString
leftmost [] = []
leftmost (l:ls) = [foldr (\x y -> if head (fst x) < head (fst y) then x else y) l ls]

rightmost :: Strategy RString
rightmost [] = []
rightmost (l:ls) = [foldr (\x y -> if head (fst x) > head (fst y) then x else y) l ls]

-- HELPERS --

separeSymbols :: String -> [String]
separeSymbols "" = []
separeSymbols (c:s) = (c : x) : separeSymbols y
  where (x, y) = span isDigit s

isDigit :: Char -> Bool
isDigit c = '0' <= c && c <= '9'

stringMatch :: Int -> String -> String -> [(Position, Substitution RString)]
stringMatch _ _ "" = []
stringMatch n s1 (s:s2)
  | x         = ([n], [(RString s1, RString y)]) : stringMatch (n+1) s1 s2
  | otherwise = stringMatch (n+1) s1 s2
    where (x, y) = stringMatch2 s1 (s:s2)

stringMatch2 :: String -> String -> (Bool, String)
stringMatch2 "" s = (True, s)
stringMatch2 _ "" = (False, "")
stringMatch2 (s:s1) (t:s2)
  | s == t    = stringMatch2 s1 s2
  | otherwise = (False, "")


--------------------------------------------------------------------------------
------------------------------       Trees        ------------------------------
--------------------------------------------------------------------------------


data RTerm = Number Int | Var String | Symbol String [RTerm]
  deriving Eq

instance Show RTerm where
  show (Var s) = s
  show (Number n) = show n
  show (Symbol s []) = s
  show (Symbol s (h:l)) = s ++ "( " ++ show h
                          ++ foldl (\x y -> x ++ " , " ++ show y) "" l ++ " )"

instance Rewrite RTerm where
  getVars (Var s) = [Var s]
  getVars (Number n) = []
  getVars (Symbol s1 l) = foldr (\x y -> getVars x ++ y) [] l

  valid sign (Var _) = True
  valid sign (Number _) = True
  valid sign (Symbol "+" [l, r]) = valid sign l && valid sign r
  valid sign (Symbol "*" [l, r]) = valid sign l && valid sign r
  valid sign (Symbol s l) = elem (s, length l) sign && all (valid sign) l

  match = termMatch []

  apply (Number n) subs = Number n
  apply (Symbol s l) subs = Symbol s $ map (`apply` subs) l 
  apply (Var s) subs = findSubstitution (Var s) subs

  replace = foldl replaceAux

  evaluate t
    | t == x    = t
    | otherwise = evaluate x
      where x = evaluate2 t

-- HELPERS --

termMatch :: Position -> RTerm -> RTerm -> [(Position, Substitution RTerm)]
termMatch p (Var t) t2 = [(p,[(Var t, t2)])]
termMatch p (Number n) t2 = []
termMatch p t1 (Number n) = []
termMatch p t1 (Var t) = []
termMatch p t1 (Symbol s2 t2)
  | x && lastCheck z = (y, z) : l
  | otherwise        = l
    where (x, y, z) = termMatch2 p t1 (Symbol s2 t2)
          l = snd (foldl (\(n,a) b -> (n+1, a ++ termMatch (p++[n]) t1 b)) (0,[]) t2)

termMatch2 :: Position -> RTerm -> RTerm -> (Bool, Position, Substitution RTerm)
termMatch2 p (Var t) t2 = (True, p, [(Var t, t2)])
termMatch2 p (Number n) t2 = (False, p, [])
termMatch2 p t1 (Number n) = (False, p, [])
termMatch2 p t1 (Var t) = (False, p, [])
termMatch2 p (Symbol s1 []) (Symbol s2 []) = (s1 == s2, p, [(Symbol s1 [], Symbol s2 [])])
termMatch2 p (Symbol s1 t1) (Symbol s2 t2)
  | s1 == s2  = foldl (\x (y, z) -> childMatch x (termMatch2 p y z)) (True, p, []) (zip t1 t2)
  | otherwise = (False, p, [])

type BoolPosSubs = (Bool, Position, Substitution RTerm)

childMatch :: BoolPosSubs -> BoolPosSubs -> BoolPosSubs
childMatch (b1, p, s1) (b2, _, s2) = (b1 && b2, p, s1 ++ s2)

lastCheck :: Substitution RTerm -> Bool
lastCheck subs = foldl (\b s -> b && lastCheck2 s subs) True subs

lastCheck2 :: (RTerm, RTerm) -> Substitution RTerm -> Bool
lastCheck2 (t1, t2) = foldl (\b (x, y) -> if t1 == x then b && t2 == y else b) True

findSubstitution :: RTerm -> Substitution RTerm -> RTerm
findSubstitution v subs = snd $ head $ filter (\(x, y) -> x == v) subs

replaceAux :: RTerm -> (Position, RTerm) -> RTerm
replaceAux t1 ([], t2) = t2
replaceAux (Symbol s l) (p:ps, t2) = Symbol s $ snd (foldl f (0,[]) l)
  where f (x, y) z = (x+1, (++) y (if p == x then [replaceAux z (ps, t2)] else [z]))

evaluate2 :: RTerm -> RTerm
evaluate2 (Number n) = Number n
evaluate2 (Var s) = Var s
evaluate2 (Symbol "+" [Number n1, Number n2]) = Number (n1+n2)
evaluate2 (Symbol "*" [Number n1, Number n2]) = Number (n1*n2)
evaluate2 (Symbol s l) = Symbol s $ map evaluate2 l

-- READ --

readRTree :: [(String, Int)] -> RTerm
readRTree l = fst $ readRTreeAux l

readRTreeAux :: [(String, Int)] -> (RTerm, [(String, Int)])
readRTreeAux ((s,-1):l) = (Var s, l)
readRTreeAux ((s,-2):l) = (Number (read s :: Int), l)
readRTreeAux ((s,0):l) = (Symbol s [], l)
readRTreeAux ((s,n):l) = (Symbol s (map fst laux), snd (last laux))
  where laux = readRTreeAux2 n l

readRTreeAux2 :: Int -> [(String, Int)] -> [(RTerm, [(String, Int)])]
readRTreeAux2 0 l = []
readRTreeAux2 n l = (x, y) : readRTreeAux2 (n-1) y 
  where (x, y) = readRTreeAux l

readRTermSystem :: [([(String,Int)],[(String,Int)])] -> RewriteSystem RTerm
readRTermSystem = foldr (\(x, y) z -> Rule (readRTree x) (readRTree y) : z) []

-- STRATEGIES --

parallelinnermost :: Strategy RTerm
parallelinnermost [] = []
parallelinnermost l = foldl (\x (y,z) -> filter (\(p,s) -> isParent p y) x) l l

paralleloutermost :: Strategy RTerm
paralleloutermost [] = []
paralleloutermost l = foldl (\x (y,z) -> filter (\(p,s) -> isParent y p) x) l l

leftmostinnermost :: Strategy RTerm
leftmostinnermost [] = []
leftmostinnermost l = [foldl (\(p1,s1) (p2,s2) -> if left p1 p2 then (p2,s2) else (p1,s1)) i inner]
  where (i:inner) = foldl (\x (y,z) -> filter (\(p,s) -> isMoreInner p y) x) l l

leftmostoutermost :: Strategy RTerm
leftmostoutermost [] = []
leftmostoutermost l = [foldl (\(p1,s1) (p2,s2) -> if left p1 p2 then (p1,s1) else (p2,s2)) o outer]
  where (o:outer) = foldl (\x (y,z) -> filter (\(p,s) -> isMoreInner y p) x) l l

isParent :: Position -> Position -> Bool
isParent p1 p2 = length p1 >= length p2 || not (and $ zipWith (==) p1 p2)

isMoreInner :: Position -> Position -> Bool
isMoreInner p1 p2 = length p1 >= length p2

left :: Position -> Position -> Bool
left p1 p2 = and $ zipWith (<=) p1 p2