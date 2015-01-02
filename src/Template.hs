module Template where

import Language
import Utils

-- type MultState = (Int,Int,Int,Int) -- (n,m,d,t)

-- evalMult :: MultState -> [MultState]
-- evalMult state =
--   if multFinal state
--      then [state]
--      else state :
--           evalMult (stepMult state)

-- stepMult :: MultState -> MultState
-- stepMult (n,m,d,t)
--   | d > 0 = (n,m,d - 1,t + 1)
--   | d == 0 = (n,m - 1,n,t)

-- multFinal :: MultState -> Bool
-- multFinal (n,m,d,t) = m == 0 && d == 0

-- initState :: MultState
-- initState = (2,4,0,0)


runProg :: String -> String
runProg = showResults . eval . compile . parse

{- Compiler -}
compile :: CoreProgram -> TiState
compile program =
  ([], initialStack, initialTiDump, initialHeap, globals, tiStatInitial)
  where sc_defs = program ++ preludeDefs ++ extraPreludeDefs
        (heap, globals) = buildInitialHeap sc_defs
        initialStack = [addr]
        address_of_print = aLookup globals "printList" (error "printList is not defined")
        address_of_main = aLookup globals "main" (error "main is not defined")
        (initialHeap, addr) = hAlloc heap (NAp address_of_print address_of_main)

extraPreludeDefs :: [CoreScDefn]
extraPreludeDefs =
  [("and"
   ,["x","y","t","f"]
   ,EAp (EAp (EVar "x")
             (EAp (EAp (EVar "y")
                       (EVar "t"))
                  (EVar "f")))
        (EVar "f"))
  ,("or"
   ,["x","y","t","f"]
   ,EAp (EAp (EVar "x")
             (EVar "t"))
        (EAp (EAp (EVar "y")
                  (EVar "t"))
             (EVar "f")))
  ,("not"
   ,["x","t","f"]
   ,EAp (EAp (EVar "x")
             (EVar "f"))
        (EVar "t"))
  ,("xor"
   ,["x","y"]
   ,EAp (EAp (EVar "and")
             (EAp (EAp (EVar "or")
                       (EVar "x"))
                  (EVar "y")))
        (EAp (EVar "not")
             (EAp (EAp (EVar "and")
                       (EVar "x"))
                  (EVar "y"))))
  ,("if",[],EVar "I")
  ,("True",["t","f"],EVar "t")
  ,("False",["t","f"],EVar "f")
  ,("pair"
   ,["a","b","f"]
   ,EAp (EAp (EVar "f")
             (EVar "a"))
        (EVar "b"))
  ,("casePair",[],EVar "I")
  ,("fst"
   ,["p"]
   ,EAp (EVar "p")
        (EVar "K"))
  ,("snd"
   ,["p"]
   ,EAp (EVar "p")
        (EVar "K1"))
  ,("Cons",[],EConstr 2 2)
  ,("Nil",[],EConstr 1 0)
  ,("head"
   ,["xs"]
   ,EAp (EAp (EAp (EVar "caseList")
                  (EVar "xs"))
             (EVar "abort"))
        (EVar "K"))
  ,("tail"
   ,["xs"]
   ,EAp (EAp (EAp (EVar "caseList")
                  (EVar "xs"))
             (EVar "abort"))
        (EVar "K1"))
  ,("printList"
   ,["xs"]
   ,EAp (EAp (EAp (EVar "caseList")
                  (EVar "xs"))
             (EVar "stop"))
        (EVar "printCons"))
  ,("printCons"
   ,["h","t"]
   ,EAp (EAp (EVar "print")
             (EVar "h"))
        (EAp (EVar "printList")
             (EVar "t")))
  ,("sig"
   ,["x"]
   ,EAp (EAp (EVar "Cons")
             (EVar "x"))
        (EVar "Nil"))]

buildInitialHeap :: CoreProgram -> (TiHeap, TiGlobals)
buildInitialHeap sc_defs =
  (heap2, sc_addrs ++ prim_addrs)
  where (heap1, sc_addrs) = mapAccuml allocateSc hInitial sc_defs
        (heap2, prim_addrs) = mapAccuml allocatePrim heap1 primitives

allocatePrim :: TiHeap -> (Name, Primitive) -> (TiHeap, (Name, Addr))
allocatePrim heap (name, prim) = (heap', (name, addr))
  where (heap', addr) = hAlloc heap (NPrim name prim)

primitives :: ASSOC Name Primitive
primitives =
  [("negate",primNeg)
  ,("+",primArith (+))
  ,("-",primArith (-))
  ,("*",primArith (*))
  ,("/",primArith div)
  ,(">",primDyadic (>))
  ,(">=",primDyadic (>=))
  ,("<", primDyadic (<))
  ,("<=", primDyadic (<=))
  ,("==", primDyadic (==))
  ,("~=", primDyadic (/=))
  ,("caseList", primCaseList)
  ,("abort", primAbort)
  ,("print", primPrint)
  ,("stop", primStop)]

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (h, (name, addr))
  where (h, addr) = hAlloc heap (NSupercomb name args body)

{- Evaluator -}
eval :: TiState -> [TiState]
eval state = state : rest_states
  where rest_states | tiFinal state = []
                    | otherwise = eval next_state
        next_state = step state

-- doAdmin :: TiState -> TiState
-- doAdmin = applyToStats tiStatIncSteps

tiFinal :: TiState -> Bool
tiFinal (_, [], [], _, _, _) = True
tiFinal _ = False

isDataNode :: Node -> Bool
isDataNode (NNum _) = True
isDataNode (NData _ _) = True
isDataNode _ = False

step :: TiState -> TiState
step state@(_,stack,_,heap,_,_) =
  dispatch (hLookup heap (head stack))
  where dispatch (NNum n) = numStep state n
        dispatch (NAp a1 a2) = apStep state a1 a2
        dispatch (NSupercomb sc args body) =
          scStep state sc args body
        dispatch (NInd addr) = indStep state addr
        dispatch (NPrim _ prim) =
          primStep state prim
        dispatch (NData _ _) = dataStep state

dataStep :: TiState -> TiState
dataStep (output,stack,dump,heap,globals,stats)
  | not . null $ dump =
    (output,drop (head dump) stack,tail dump,heap,globals,stats)
  | otherwise = error "Impossible happened"

primStep :: TiState -> Primitive -> TiState
primStep state prim = prim state

primStop :: TiState -> TiState
primStop (output, _, _, heap, globals, stats) = (output, [], [], heap, globals, stats)

primPrint :: TiState -> TiState
primPrint (output,stack,dump,heap,globals,stats)
  | isDataNode b1_node =
    let (NNum n) = b1_node
    in (output ++
        [n]
       ,[b2]
       ,dump
       ,heap
       ,globals
       ,stats)
  | otherwise =
    (output,b1 : stack,3 : dump,heap,globals,stats)
  where b1:b2:_ = getArgs heap (tail stack)
        b1_node = hLookup heap b1

primAbort :: TiState -> TiState
primAbort = error "empty list"

primCaseList :: TiState -> TiState
primCaseList (output,stack,dump,heap,globals,stats)
  | isDataNode xs_node =
    case xs_node of
      NData 2 [y,ys] ->
        let (heap',addr) = hAlloc heap (NAp cc y)
        in (output
           ,drop 3 stack
           ,dump
           ,hUpdate heap'
                    (stack !! 3)
                    (NAp addr ys)
           ,globals
           ,stats)
      NData 1 [] ->
        (output
        ,drop 3 stack
        ,dump
        ,hUpdate heap
                 (stack !! 3)
                 (NInd cn)
        ,globals
        ,stats)
      _ -> error "Impossible happened"
  | otherwise =
    (output,xs : stack,4 : dump,heap,globals,stats)
  where xs:cn:cc:_ = getArgs heap (tail stack)
        xs_node = hLookup heap xs

primArith :: (Int -> Int -> Int) -> TiState -> TiState
primArith op (output,stack,dump,heap,globals,stats)
  | isDataNode arg1_node && isDataNode arg2_node =
    let (NNum a) = arg1_node
        (NNum b) = arg2_node
        heap' =
          hUpdate heap
                  (stack !! 2)
                  (NNum (op a b))
    in (output,drop 2 stack,dump,heap',globals,stats)
  | isDataNode arg1_node =
    (output,arg2_addr : stack,3 : dump,heap,globals,stats)
  | otherwise =
    (output,arg1_addr : stack,3 : dump,heap,globals,stats)
  where arg1_addr:arg2_addr:_ =
          getArgs heap (tail stack)
        arg1_node = hLookup heap arg1_addr
        arg2_node = hLookup heap arg2_addr

primDyadic :: (Int -> Int -> Bool) -> TiState -> TiState
primDyadic bop (output,stack,dump,heap,globals,stats)
  | isDataNode arg1_node && isDataNode arg2_node =
    (output
    ,drop 2 stack
    ,dump
    ,hUpdate heap
             (stack !! 2)
             (op arg1_node arg2_node)
    ,globals
    ,stats)
  | isDataNode arg1_node =
    (output,arg2_addr : stack,3 : dump,heap,globals,stats)
  | otherwise =
    (output,arg1_addr : stack,3 : dump,heap,globals,stats)
  where arg1_addr:arg2_addr:_ =
          getArgs heap (tail stack)
        arg1_node = hLookup heap arg1_addr
        arg2_node = hLookup heap arg2_addr
        op = nodify bop globals


nodify :: (Int -> Int -> Bool) -> ASSOC Name Addr -> Node -> Node -> Node
nodify op env a b =
  let (NNum a_val) = a
      (NNum b_val) = b
  in if op a_val b_val
        then NInd (aLookup env "True" (error "True is not defined"))
        else NInd (aLookup env "False" (error "False is not defined"))

primConstr :: Int -> Int -> TiState -> TiState
primConstr tag arity (output,stack,dump,heap,globals,stats) =
  (output
  ,drop arity stack
  ,dump
  ,hUpdate heap
           (stack !! arity)
           (NData tag addrs)
  ,globals
  ,stats)
  where addrs =
          take arity $
          getArgs heap (tail stack)

primNeg :: TiState -> TiState
primNeg (output,stack,dump,heap,globals,stats)
  | isDataNode arg_node =
    let (NNum n) = arg_node
        heap' =
          hUpdate heap
                  (stack !! 1)
                  (NNum (negate n))
    in (output,tail stack,dump,heap',globals,stats)
  | otherwise =
    (output,arg_addr : stack,2 : dump,heap,globals,stats)
  where arg_addr =
          head $
          getArgs heap (tail stack)
        arg_node = hLookup heap arg_addr

indStep :: TiState -> Addr -> TiState
indStep (output, stack, dump, heap, globals, stats) addr =
  (output, addr: tail stack, dump, heap, globals, stats)

numStep :: TiState -> Int -> TiState
numStep (output,stack,dump,heap,globals,stats) _
  | not . null $ dump =
    (output,drop (head dump) stack,tail dump,heap,globals,stats)
  | otherwise =
    error "Number applied as a function"

apStep :: TiState -> Addr -> Addr -> TiState
apStep (output, stack, dump, heap, globals, stats) a1 a2 =
  case hLookup heap a2 of
   (NInd a3) -> (output, stack, dump, hUpdate heap (head stack) (NAp a1 a3), globals, stats)
   _ -> (output, a1:stack, dump, heap, globals, stats)


scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (output, stack, dump, heap, globals, stats) sc_name arg_names body =
  (output, new_stack, dump, new_heap, globals, tiStatIncSteps stats)
  where new_stack = if length arg_names >= length stack
                    then error (sc_name ++ " applied to too few arguments")
                    else drop (length arg_names) stack
        new_heap = instantiateAndUpdate body (stack !! length arg_names) heap env
        env = arg_bindings ++ globals
        arg_bindings = zip arg_names (getArgs heap (tail stack))

getArgs :: TiHeap -> TiStack -> [Addr]
getArgs heap = map get_arg
  where get_arg addr =
          let (NAp _ arg) = hLookup heap addr
          in arg

instantiate :: CoreExpr -> TiHeap -> ASSOC Name Addr -> (TiHeap, Addr)
instantiate (ENum n) heap _ = hAlloc heap (NNum n)
instantiate (EAp e1 e2) heap env = hAlloc heap2 (NAp a1 a2)
  where (heap1, a1) = instantiate e1 heap env
        (heap2, a2) = instantiate e2 heap1 env
instantiate (EVar v) heap env = (heap, aLookup env v (error ("Undefined name " ++ show v)))
instantiate (EConstr tag arity) heap env = instantiateConstr tag arity heap env
instantiate (ELet isrec defs body) heap env = instantiateLet isrec defs body heap env
instantiate (ECase _ _) _ _ = error "Can't instantiate case exprs"
instantiate (ELam _ _) _ _ = error "Haven't implemented yet"

instantiateConstr :: Int -> Int -> TiHeap -> ASSOC Name Addr -> (TiHeap, Addr)
instantiateConstr tag arity heap _ =
  if arity == 0 -- Need to apply it immediately
  then hAlloc heap (NData tag [])
  else hAlloc heap (NPrim "Pack" (primConstr tag arity))

instantiateLet :: IsRec
               -> [(Name,CoreExpr)]
               -> CoreExpr
               -> TiHeap
               -> ASSOC Name Addr
               -> (TiHeap,Addr)
instantiateLet isrec defs body heap env = instantiate body heap1 env'
  where (heap1,bindings) =
          mapAccuml ins_defs heap defs
        ins_defs h (name,expr)
          | isrec == nonRecursive =
            let (h',addr) = instantiate expr h env
            in (h',(name,addr))
          | otherwise =
            let (h',addr) = instantiate expr h env'
            in (h',(name,addr))
        env' = bindings ++ env

instantiateAndUpdate :: CoreExpr -> Addr -> TiHeap -> ASSOC Name Addr -> TiHeap
instantiateAndUpdate (EAp e1 e2) upd_addr heap env =
  hUpdate heap2 upd_addr (NAp a1 a2)
  where (heap1, a1) = instantiate e1 heap env
        (heap2, a2) = instantiate e2 heap1 env
instantiateAndUpdate (EVar v) upd_addr heap env =
  hUpdate heap upd_addr (NInd (aLookup env v (error ("Undefined name " ++ show v))))
instantiateAndUpdate (ENum n) upd_addr heap _ =
  hUpdate heap upd_addr (NNum n)
instantiateAndUpdate (ELet isrec defs body) upd_addr heap env =
  instantiateLetAndUpdate upd_addr isrec defs body heap env
instantiateAndUpdate (ECase _ _) _ _ _ = error "Haven't implemented yet"
instantiateAndUpdate e@(EConstr _ _) upd_addr heap env =
  hUpdate heap' upd_addr (hLookup heap' addr)
  where (heap', addr) = instantiate e heap env
instantiateAndUpdate (ELam _ _) _ _ _ = error "Haven't implemented yet"

instantiateLetAndUpdate :: Addr
                        -> IsRec
                        -> [(Name,CoreExpr)]
                        -> CoreExpr
                        -> TiHeap
                        -> ASSOC Name Addr
                        -> TiHeap
instantiateLetAndUpdate upd_addr isrec defs body heap env =
  instantiateAndUpdate body upd_addr heap1 env'
  where (heap1, bindings) = mapAccuml ins_defs heap defs
        ins_defs h (name, expr)
          | isrec == nonRecursive =
              let (h', addr) = instantiate expr h env
              in (h', (name, addr))
          | otherwise =
              let (h', addr) = instantiate expr h env'
              in (h', (name, addr))
        env' = bindings ++ env

{- Printer -}
showResults :: [TiState] -> String
showResults states =
  iDisplay $
  iConcat [iLayn (map showState states),showStats (last states)]

showState :: TiState -> Iseq
showState (_, stack,_,heap,_,_) =
  iConcat [showStack heap stack,iNewline]

showHeap :: TiHeap -> Iseq
showHeap heap =
  iConcat [iStr "Hep ["
          ,iIndent (iInterleave iNewline
                                (map show_heap_item (hAddresses heap)))
          ,iStr " ]"]
  where show_heap_item addr =
          iConcat [showFWAddr addr,iStr ": ",showNode (hLookup heap addr)]

showStack :: TiHeap -> TiStack -> Iseq
showStack heap stack =
  iConcat [iStr "Stk ["
          ,iIndent (iInterleave iNewline
                                (map show_stack_item stack))
          ,iStr " ]"]
  where show_stack_item addr =
          iConcat [showFWAddr addr
                  ,iStr ": "
                  ,showStkNode heap
                               (hLookup heap addr)]

showStkNode :: TiHeap -> Node -> Iseq
showStkNode heap (NAp fun arg) =
  iConcat [ iStr "NAp ", showFWAddr fun,
            iStr " ", showFWAddr arg, iStr " (",
            showNode (hLookup heap arg), iStr ")"]
showStkNode _ node = showNode node

showNode :: Node -> Iseq
showNode (NAp a1 a2) = iConcat [ iStr "NAp ", showAddr a1,
                                 iStr " ", showAddr a2]
showNode (NSupercomb name _ _) = iStr ("NSupercomb " ++ name)
showNode (NNum n) = iStr "NNum " `iAppend` iNum n
showNode (NInd addr) = iStr "NInd " `iAppend` showAddr addr
showNode (NPrim name _) = iStr ("NPrim " ++ name)
showNode (NData tag addrs) = iConcat [iStr ("NData <" ++ show tag ++ "> "),
                                      iInterleave (iStr " ") (map showAddr addrs)]

showAddr :: Addr -> Iseq
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> Iseq
showFWAddr addr = iStr (space (4 - length str) ++ str)
  where str = show addr

showStats :: TiState -> Iseq
showStats (output,_,_,heap,_,stats) =
  iConcat [iNewline
          ,iNewline
          ,iStr "The outcome = ["
          ,iInterleave (iStr ",")
                       (map iNum output)
          ,iStr "]"
          ,iNewline
          ,iStr "Total number of SC reductions = "
          ,iNum (tiStatGetSteps stats)
          ,iNewline
          ,iStr "Heap size = "
          ,iNum (hSize heap)]

type TiState = (Output, TiStack, TiDump, TiHeap, TiGlobals, TiStats)

type Output = [Int]

type TiStack = [Addr]

type TiDump = [Int]

initialTiDump :: TiDump
initialTiDump = []

type TiHeap = Heap Node

data Node = NAp Addr Addr
          | NSupercomb Name [Name] CoreExpr
          | NNum Int
          | NInd Addr
          | NPrim Name Primitive
          | NData Int [Addr]

type Primitive = TiState -> TiState

type TiGlobals = ASSOC Name Addr

type TiStats = Int

tiStatInitial :: TiStats
tiStatInitial = 0

tiStatIncSteps :: TiStats -> TiStats
tiStatIncSteps = (+1)

tiStatGetSteps :: TiStats -> Int
tiStatGetSteps = id

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats stats_fun (output,stack,dump,heap,sc_defs,stats) =
  (output, stack,dump,heap,sc_defs,stats_fun stats)
