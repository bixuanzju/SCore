module Language where

import Control.Applicative
import Control.Monad (liftM, ap)
import Data.Char (isAlpha, isDigit, isLetter, isSpace)

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

{- Pretty print -}
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
flatten _ ((INewline, n) : seqs) = '\n' : (space n) ++ flatten n seqs
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

iNum :: Int -> Iseq
iNum n = iStr (show n)

iFWNum :: Int -> Int -> Iseq
iFWNum width n =
  iStr (space (width - length digits) ++ digits)
  where digits = show n

iLayn :: [Iseq] -> Iseq
iLayn seqs = iConcat (map lay_item (zip [1..] seqs))
  where lay_item (n, seq) = iConcat [ iFWNum 4 n, iStr ") ", iIndent seq, iNewline ]

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


{- Lexer and Parser -}

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


newtype Parser a = Parser {runParser :: [Token] -> [(a, [Token])]}

instance Monad Parser where
  return a = Parser (\toks -> [(a,toks)])
  p >>= f =
    Parser (\toks ->
              [(r2,toks2) | (r1,toks1) <- runParser p toks
                          , (r2,toks2) <- runParser (f r1) toks1])

instance Applicative Parser where
  pure a = return a
  (<*>) = ap

instance Functor Parser where
  fmap = liftM

pAlt :: Parser a -> Parser a -> Parser a
pAlt p1 p2 =
  Parser (\toks ->
            (runParser p1 toks) ++
            (runParser p2 toks))


pGreeting :: Parser (String, String)
pGreeting =
  do greeting <- pHelloOrGoodbye
     somebody <- pVar
     pLit "!"
     return (greeting,somebody)

pHelloOrGoodbye :: Parser String
pHelloOrGoodbye = (pLit "hello") `pAlt` (pLit "goodbye")

pZeroOrMore :: Parser a -> Parser [a]
pZeroOrMore p = (pOneOrMore p) `pAlt` (return [])

pOneOrMore :: Parser a -> Parser [a]
-- pOneOrMore p = do r <- p
--                   rs <- pZeroOrMore p
--                   return (r:rs)
pOneOrMore p =
  Parser (\toks ->
            [(r : rs,toks2) | (r,toks1) <- runParser p toks
                            , (rs,toks2) <- [head .
                                             runParser (pZeroOrMore p) $
                                             toks1]])

toToken :: [String] -> [Token]
toToken = map (\s -> (1,s))

pGreetingN :: Parser Int
pGreetingN = liftM length (pZeroOrMore pGreeting)

pOneOrMoreWithSep :: Parser a -> Parser b -> Parser [a]
pOneOrMoreWithSep p sep =
  do r <- p
     rs <- pRest p sep
     return (r : rs)

pRest :: Parser a -> Parser b -> Parser [a]
pRest p sep = (sep >> pOneOrMoreWithSep p sep) `pAlt` (return [])

pFail :: Parser a
pFail = Parser (\_ -> [])

pSat :: (String -> Bool) -> Parser String
pSat p = Parser (\toks -> case toks of
                           [] -> []
                           (_, tok):toks' -> if p tok then [(tok, toks')] else [])

pLit :: String -> Parser String
pLit s = pSat (== s)

pVar :: Parser String
pVar = pSat (\s -> (isAlpha . head $ s) && (not $ elem s keywords))

keywords :: [String]
keywords = ["let", "letrec", "case", "in", "of", "Pack"]

pNum :: Parser Int
pNum = liftM read (pSat $ and . map isDigit)

syntax :: [Token] -> CoreProgram
syntax = take_first_parse . runParser pProgram
  where take_first_parse ((prog,[]):others) = prog
        take_first_parse (p:others) = take_first_parse others
        take_first_parse _ = error "Syntex error"

pProgram :: Parser CoreProgram
pProgram = pOneOrMoreWithSep pSc (pLit ";")

pSc :: Parser CoreScDefn
pSc =
  do var <- pVar
     args <- pZeroOrMore pVar
     pLit "="
     expr <- pExpr
     return (var,args,expr)

pExpr :: Parser CoreExpr
pExpr = pLet `pAlt` pLetRec `pAlt` pCase `pAlt` pLambda `pAlt` pExpr1

pApp :: Parser CoreExpr
pApp = liftM  make_ap_chain (pOneOrMore pAExpr)

make_ap_chain :: [CoreExpr] -> CoreExpr
make_ap_chain xs = foldl1 make_ap xs
  where make_ap l r = EAp l r

-- make_ap_chain [x] = x
-- make_ap_chain [x,y] = EAp x y
-- make_ap_chain (x:y:xs) = EAp (EAp x y) (make_ap_chain xs)

pLet :: Parser CoreExpr
pLet =
  do pLit "let"
     defns <- pDefns
     pLit "in"
     expr <- pExpr
     return (ELet nonRecursive defns expr)

pDefns :: Parser [(Name, CoreExpr)]
pDefns = pOneOrMoreWithSep pDefn (pLit ";")

pDefn :: Parser (Name, CoreExpr)
pDefn =
  do var <- pVar
     pLit "="
     expr <- pExpr
     return (var,expr)

pLetRec :: Parser CoreExpr
pLetRec =
  do pLit "letrec"
     defns <- pDefns
     pLit "in"
     expr <- pExpr
     return (ELet recursive defns expr)

pCase :: Parser CoreExpr
pCase =
  do pLit "case"
     expr <- pExpr
     pLit "of"
     alters <- pAlters
     return (ECase expr alters)

pAlters :: Parser [CoreAlt]
pAlters = pOneOrMoreWithSep pAlter (pLit ";")

pAlter :: Parser CoreAlt
pAlter =
  do pLit "<"
     num <- pNum
     pLit ">"
     vars <- pOneOrMore pVar
     pLit "->"
     expr <- pExpr
     return (num,vars,expr)

pLambda :: Parser CoreExpr

pLambda =
  do pLit "\\"
     vars <- pOneOrMore pVar
     pLit "."
     expr <- pExpr
     return (ELam vars expr)

pAExpr :: Parser CoreExpr
pAExpr =
  (liftM EVar pVar) `pAlt`
  (liftM ENum pNum) `pAlt`
  pPack `pAlt`
  (do pLit "("
      expr <- pExpr
      pLit ")"
      return expr)

pPack :: Parser CoreExpr
pPack =
  do pLit "Pack"
     pLit "{"
     num1 <- pNum
     pLit ","
     num2 <- pNum
     pLit "}"
     return (EConstr num1 num2)

data PartialExpr = NoOp | FoundOp Name CoreExpr

pExpr1 :: Parser CoreExpr
pExpr1 =
  do expr <- pExpr2
     expr' <- pExpr1c
     return (assembleOp expr expr')

pExpr1c :: Parser PartialExpr
pExpr1c =
  (do op <- pLit "|"
      expr <- pExpr1
      return (FoundOp op expr)) `pAlt`
  (return NoOp)


assembleOp :: CoreExpr -> PartialExpr -> CoreExpr
assembleOp e1 NoOp = e1
assembleOp e1 (FoundOp op e2) = EAp (EAp (EVar op) e1) e2

pExpr2 :: Parser CoreExpr
pExpr2 =
  do expr <- pExpr3
     expr' <- pExpr2c
     return (assembleOp expr expr')

pExpr2c :: Parser PartialExpr
pExpr2c =
  (do op <- pLit "&"
      expr <- pExpr1
      return (FoundOp op expr)) `pAlt`
  (return NoOp)

pExpr3 :: Parser CoreExpr
pExpr3 =
  do expr <- pExpr4
     expr' <- pExpr3c
     return (assembleOp expr expr')

pExpr3c :: Parser PartialExpr
pExpr3c =
  (do op <- prelop
      expr <- pExpr4
      return (FoundOp op expr)) `pAlt`
  (return NoOp)

prelop :: Parser String
prelop =
  (pLit "<") `pAlt`
  (pLit "<=") `pAlt`
  (pLit "==") `pAlt`
  (pLit "~=") `pAlt`
  (pLit ">=") `pAlt`
  (pLit ">")

pExpr4 :: Parser CoreExpr
pExpr4 =
  do expr <- pExpr5
     expr' <- pExpr4c `pAlt` pExpr4c'
     return (assembleOp expr expr')

pExpr4c :: Parser PartialExpr
pExpr4c =
  (do op <- pLit "+"
      expr <- pExpr4
      return (FoundOp op expr)) `pAlt`
  (return NoOp)

pExpr4c' :: Parser PartialExpr
pExpr4c' =
  (do op <- pLit "-"
      expr <- pExpr5
      return (FoundOp op expr)) `pAlt`
  (return NoOp)

pExpr5 :: Parser CoreExpr
pExpr5 =
  do expr <- pApp
     expr' <- pExpr5c `pAlt` pExpr5c'
     return (assembleOp expr expr')

pExpr5c :: Parser PartialExpr
pExpr5c =
  (do op <- pLit "*"
      expr <- pExpr5
      return (FoundOp op expr)) `pAlt`
  (return NoOp)

pExpr5c' :: Parser PartialExpr
pExpr5c' =
  (do op <- pLit "/"
      expr <- pApp
      return (FoundOp op expr)) `pAlt`
  (return NoOp)

parse :: String -> CoreProgram
parse = syntax . clex 1
