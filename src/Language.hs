module Language where

import Data.Char (isAlpha)
import Data.Char (isDigit)
import Data.Char (isLetter)
import Data.Char (isSpace)

data Expr a
  = EVar Name
  | ENum Int
  | EConstr Int
            Int
  | EAp (Expr a)
        (Expr a)
  | ELet IsRec
         [(a,Expr a)]
         (Expr a)
  | ECase (Expr a)
          [Alter a]
  | ELam [a]
         (Expr a)
  deriving (Show)

type CoreExpr = Expr Name
type Name = String
type IsRec = Bool

recursive, nonRecursive :: IsRec
recursive = True
nonRecursive = False

binderOf :: [(a, b)] -> [a]
binderOf defns = [name | (name,rhs) <- defns]

rhssOf :: [(a, b)] -> [b]
rhssOf defns = [rhs | (name,rhs) <- defns]

type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name

isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar v) = True
isAtomicExpr (ENum n) = True
isAtomicExpr e = False

type Program a = [ScDefn a]
type CoreProgram = Program Name

type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name

preludeDefs :: CoreProgram
preludeDefs =
  [("I",["x"],EVar "x")
  ,("K",["x","y"],EVar "x")
  ,("K1",["x","y"],EVar "y")
  ,("S"
   ,["f","g","x"]
   ,EAp (EAp (EVar "f")
             (EVar "x"))
        (EAp (EVar "g")
             (EVar "x")))
  ,("compose"
   ,["f","g","x"]
   ,EAp (EVar "f")
        (EAp (EVar "g")
             (EVar "x")))
  ,("twice"
   ,["f"]
   ,EAp (EAp (EVar "compose")
             (EVar "f"))
        (EVar "f"))]

data Iseq
  = INil
  | IStr String
  | IAppend Iseq
            Iseq
  | IIndent Iseq
  | INewline
  deriving (Show)

iNil :: Iseq
iNil = INil

iStr :: String -> Iseq
iStr str = IStr str

iAppend :: Iseq -> Iseq -> Iseq
iAppend seq1 seq2 = IAppend seq1 seq2

iNewline :: Iseq
iNewline = INewline

iIndent :: Iseq -> Iseq
iIndent s = IIndent s

space :: Int -> String
space n = take n $ repeat ' '

flatten :: Int -> [(Iseq, Int)] -> String
flatten _ [] = ""
flatten col ((INil, _):seqs) = flatten col seqs
flatten col ((IStr s, _) : seqs) = s ++ flatten (col + length s) seqs
flatten col ((IAppend seq1 seq2, n) : seqs) = flatten col ((seq1, n) : (seq2, n) : seqs)
flatten col ((INewline, n) : seqs) = '\n' : (space n) ++ flatten n seqs
flatten col ((IIndent s, _) : seqs) = flatten col ((s, col) : seqs)

iDisplay :: Iseq -> String
iDisplay s = flatten 0 [(s, 0)]

iConcat :: [Iseq] -> Iseq
iConcat [] = iNil
iConcat (x:xs) = x `iAppend` (iConcat xs)

iInterleave :: Iseq -> [Iseq] -> Iseq
iInterleave _ [] = iNil
iInterleave _ [y] = y
iInterleave x (y:ys) = y `iAppend` x `iAppend` (iInterleave x ys)


pprExpr :: CoreExpr -> Iseq
pprExpr (ENum n) = iStr (show n)
pprExpr (EVar v) = iStr v
pprExpr (EAp e1 e2) = (pprExpr e1) `iAppend` (iStr " ") `iAppend` (pprExpr e2)
pprExpr (ELet isrec defns expr) =
  iConcat [iStr keyword
          ,iNewline
          ,iStr "  "
          ,iIndent (pprDefns defns)
          ,iNewline
          ,iStr "in "
          ,pprExpr expr]
  where keyword
          | not isrec = "let"
          | isrec = "letrec"

pprDefns :: [(Name, CoreExpr)] -> Iseq
pprDefns defns = iInterleave s (map pprDefn defns)
  where s = iConcat [ iStr ";", iNewline]

pprDefn :: (Name, CoreExpr) -> Iseq
pprDefn (name, expr) = iConcat [ iStr name, iStr " = ", iIndent (pprExpr expr)]

pprScDefn :: CoreScDefn -> Iseq
pprScDefn (name, vars, expr) = iConcat [ iStr name, iVars, iStr " = ",  pprExpr expr]
  where iVars = (iAddBefore (iStr " ") (map iStr vars))

iAddBefore :: Iseq -> [Iseq] -> Iseq
iAddBefore _ [] = iNil
iAddBefore s (x:xs) = iConcat [s, x, iAddBefore s xs]

pprint :: CoreProgram -> String
pprint p = iDisplay $  iInterleave s (map pprScDefn p)
  where s = iConcat [ iStr ";", iNewline]

aProgram :: CoreProgram
aProgram = [("main",[],EAp (EVar "quadr") (ENum 20)),("quadr",["x"],ELet False [("twice_x",EAp (EAp (EVar "+") (EVar "x")) (EVar "x")),("three",EAp (EAp (EVar "+") (EVar "twice_x")) (EVar "x"))] (EAp (EAp (EVar "+") (EVar "twice_x")) (EVar "twice_x")))]

type Token = (Int, String)

twoCharOps :: [String]
twoCharOps = ["==", "~=", ">=" , "<=", "->"]

clex :: Int -> String -> [Token]
clex line (c:cs)
  | c == '\n' = clex (line+1) cs
  | isSpace c = clex line cs
clex line (c:cs) | isDigit c = (line, num_token) : clex line rest_cs
  where num_token = c : takeWhile isDigit cs
        rest_cs = dropWhile isDigit cs
clex line ('-':'-':cs) = clex line cs_rest
  where cs_rest = dropWhile (\c -> c /= '\n') cs
clex line (c:cs) | isLetter c = (line, var_tok) : clex line rest_cs
  where var_tok = c : takeWhile isIdChar cs
        rest_cs = dropWhile isIdChar cs
clex line (a:b:cs) | elem [a,b] twoCharOps = (line, [a,b]) : clex line cs
clex line (c:cs) = (line, [c]) : clex line cs
clex _ [] = []

isIdChar :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || (c == '_')


type Parser a = [Token] -> [(a, [Token])]

pAlt :: Parser a -> Parser a -> Parser a
pAlt p1 p2 toks = (p1 toks) ++ (p2 toks)

pThen :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
pThen combine p1 p2 toks =
  [(combine v1 v2,toks2) | (v1,toks1) <- p1 toks
                         , (v2,toks2) <- p2 toks1]

pGreeting :: Parser (String, String)
pGreeting = pThen const (pThen (,) pHelloOrGoodbye pVar) (pLit "!")

pHelloOrGoodbye :: Parser String
pHelloOrGoodbye = (pLit "hello") `pAlt` (pLit "goodbye")

pZeroOrMore :: Parser a -> Parser [a]
pZeroOrMore p = (pOneOrMore p) `pAlt` (pEmpty [])

pOneOrMore :: Parser a -> Parser [a]
pOneOrMore p toks =
  [(r : rs,toks2) | (r,toks1) <- p toks
                  , (rs,toks2) <- [head $
                                   pZeroOrMore p toks1]]

pEmpty :: a -> Parser a
pEmpty v toks = [(v, toks)]

toToken :: [String] -> [Token]
toToken = map (\s -> (1,s))

pGreetingN :: Parser Int
pGreetingN = (pZeroOrMore pGreeting) `pApply` length

pApply :: Parser a -> (a -> b) -> Parser b
pApply p f toks = [ (f r, toks1) | (r, toks1) <- p toks]

pOneOrMoreWithSep :: Parser a -> Parser b -> Parser [a]
pOneOrMoreWithSep p sep = pThen (:) p (pRest p sep)

pRest :: Parser a -> Parser b -> Parser [a]
pRest p sep = (pThen (\_ b -> b) sep (pOneOrMoreWithSep p sep)) `pAlt` (pEmpty [])

pSat :: (String -> Bool) -> Parser String
pSat p ((_, tok):toks)
  | p tok = [(tok, toks)]
  | otherwise = []
pSat _ [] = []

pLit :: String -> Parser String
pLit s = pSat (== s)

pVar :: Parser String
pVar = pSat (\s -> (isAlpha . head $ s) && (not $ elem s keywords))

keywords :: [String]
keywords = ["let", "letrec", "case", "in", "of", "Pack"]

pNum :: Parser Int
pNum = pApply (pSat $ and . map isDigit) read

pThen4 :: (a -> b -> c -> d -> e)
       -> Parser a
       -> Parser b
       -> Parser c
       -> Parser d
       -> Parser e
pThen4 f p1 p2 p3 p4 toks =
  [(f r1 r2 r3 r4,toks4) | (r1,toks1) <- p1 toks
                         , (r2,toks2) <- p2 toks1
                         , (r3,toks3) <- p3 toks2
                         , (r4,toks4) <- p4 toks3]

pThen5 :: (a -> b -> c -> d -> e -> f)
       -> Parser a
       -> Parser b
       -> Parser c
       -> Parser d
       -> Parser e
       -> Parser f
pThen5 f p1 p2 p3 p4 p5 toks =
  [(f r1 r2 r3 r4 r5,toks5) | (r1,toks1) <- p1 toks
                            , (r2,toks2) <- p2 toks1
                            , (r3,toks3) <- p3 toks2
                            , (r4,toks4) <- p4 toks3
                            , (r5,toks5) <- p5 toks4]

pThen3 :: (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
pThen3 f p1 p2 p3 toks =
  [(f r1 r2 r3,toks3) | (r1,toks1) <- p1 toks
                      , (r2,toks2) <- p2 toks1
                      , (r3,toks3) <- p3 toks2]

pThen6 :: (a -> b -> c -> d -> e -> f -> g)
       -> Parser a
       -> Parser b
       -> Parser c
       -> Parser d
       -> Parser e
       -> Parser f
       -> Parser g
pThen6 f p1 p2 p3 p4 p5 p6 toks =
  [(f r1 r2 r3 r4 r5 r6,toks6) | (r1,toks1) <- p1 toks
                               , (r2,toks2) <- p2 toks1
                               , (r3,toks3) <- p3 toks2
                               , (r4,toks4) <- p4 toks3
                               , (r5,toks5) <- p5 toks4
                               , (r6,toks6) <- p6 toks5]


syntax :: [Token] -> CoreProgram
syntax = take_first_parse . pProgram
  where take_first_parse ((prog,[]):others) = prog
        take_first_parse (p:others) = take_first_parse others
        take_first_parse _ = error "Syntex error"

pProgram :: Parser CoreProgram
pProgram = pOneOrMoreWithSep pSc (pLit ";")

pSc :: Parser CoreScDefn
pSc = pThen4 mk_sc pVar (pZeroOrMore pVar) (pLit "=") pExpr

mk_sc :: String -> [String] -> String -> CoreExpr -> (String, [String], CoreExpr)
mk_sc a b c d = (a, b, d)

pExpr :: Parser CoreExpr
pExpr = pLet `pAlt` pLetRec `pAlt` pCase `pAlt` pLambda `pAlt` pExpr1

pApp :: Parser CoreExpr
pApp = pApply (pOneOrMore pAExpr) make_ap_chain

make_ap_chain :: [CoreExpr] -> CoreExpr
make_ap_chain [x] = x
make_ap_chain [x,y] = EAp x y
make_ap_chain (x:y:xs) = EAp (EAp x y) (make_ap_chain xs)

pLet :: Parser CoreExpr
pLet = pThen4 makeLet (pLit "let") pDefns (pLit "in") pExpr
  where makeLet a b c d = ELet nonRecursive b d

pDefns :: Parser [(Name, CoreExpr)]
pDefns = pOneOrMoreWithSep pDefn (pLit ";")

pDefn :: Parser (Name, CoreExpr)
pDefn = pThen3 makeDefn pVar (pLit "=") pExpr
  where makeDefn a b c = (a, c)

pLetRec :: Parser CoreExpr
pLetRec = pThen4 makeLetRec (pLit "letrec") pDefns (pLit "in") pExpr
  where makeLetRec a b c d = ELet recursive b d

pCase :: Parser CoreExpr
pCase = pThen4 makeCase (pLit "case") pExpr (pLit "of") pAlters
  where makeCase a b c d = ECase b d

pAlters :: Parser [CoreAlt]
pAlters = pOneOrMoreWithSep pAlter (pLit ";")

pAlter :: Parser CoreAlt
pAlter = pThen6 makeAlter (pLit "<") pNum (pLit ">") (pOneOrMore pVar) (pLit "->") pExpr
  where makeAlter a b c d e f = (b, d, f)

pLambda :: Parser CoreExpr
pLambda = pThen4 makeLambda (pLit "\\") (pOneOrMore pVar) (pLit ".") pExpr
  where makeLambda a b c d = ELam b d

pAExpr :: Parser CoreExpr
pAExpr = (pApply pVar (EVar)) `pAlt` (pApply pNum ENum) `pAlt` pPack `pAlt` (pThen3 (\a b c -> b) (pLit "(") pExpr (pLit ")"))

pPack :: Parser CoreExpr
pPack = pThen6 makePack (pLit "Pack") (pLit "{")  pNum (pLit ",") pNum (pLit "}")
  where makePack a b c d e f = EConstr c e

data PartialExpr = NoOp | FoundOp Name CoreExpr

pExpr1c :: Parser PartialExpr
pExpr1c = (pThen FoundOp (pLit "|") pExpr1) `pAlt` (pEmpty NoOp)

pExpr1 :: Parser CoreExpr
pExpr1 = pThen assembleOp pExpr2 pExpr1c

assembleOp :: CoreExpr -> PartialExpr -> CoreExpr
assembleOp e1 NoOp = e1
assembleOp e1 (FoundOp op e2) = EAp (EAp (EVar op) e1) e2

pExpr2 :: Parser CoreExpr
pExpr2 = pThen assembleOp pExpr3 pExpr2c

pExpr2c :: Parser PartialExpr
pExpr2c = (pThen FoundOp (pLit "&") pExpr2) `pAlt` (pEmpty NoOp)

pExpr3 :: Parser CoreExpr
pExpr3 = pThen assembleOp pExpr4 pExpr3c

pExpr3c :: Parser PartialExpr
pExpr3c = (pThen FoundOp prelop pExpr4) `pAlt` (pEmpty NoOp)

prelop :: Parser String
prelop = (pLit "<") `pAlt` (pLit "<=") `pAlt` (pLit "==") `pAlt` (pLit "~=") `pAlt` (pLit ">=") `pAlt` (pLit ">")

pExpr4 :: Parser CoreExpr
pExpr4 = pThen assembleOp pExpr5 (pExpr4c `pAlt` pExpr4c')

pExpr4c :: Parser PartialExpr
pExpr4c = (pThen FoundOp (pLit "+") pExpr4) `pAlt` (pEmpty NoOp)

pExpr4c' :: Parser PartialExpr
pExpr4c' = (pThen FoundOp (pLit "-") pExpr5) `pAlt` (pEmpty NoOp)

pExpr5 :: Parser CoreExpr
pExpr5 = pThen assembleOp pApp pExpr5c

pExpr5c :: Parser PartialExpr
pExpr5c = (pThen FoundOp ((pLit "*") `pAlt` (pLit "/")) pExpr5) `pAlt` (pEmpty NoOp)

parse :: String -> CoreProgram
parse = syntax . clex 1
