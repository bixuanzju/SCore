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
  (initialStack, initialTiDump, initialHeap, globals, tiStatInitial)
  where sc_defs = program ++ preludeDefs ++ extraPreludeDefs
        (initialHeap, globals) = buildInitialHeap sc_defs
        initialStack = [address_of_main]
        address_of_main = aLookup globals "main" (error "main is not defined")

extraPreludeDefs :: [CoreScDefn]
extraPreludeDefs = []

buildInitialHeap :: CoreProgram -> (TiHeap, TiGlobals)
buildInitialHeap = mapAccuml allocateSc hInitial

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) = (h, (name, addr))
  where (h, addr) = hAlloc heap (NSupercomb name args body)

{- Evaluator -}
eval :: TiState -> [TiState]
eval state = state : rest_states
  where rest_states | tiFinal state = []
                    | otherwise = eval next_state
        next_state = doAdmin (step state)

doAdmin :: TiState -> TiState
doAdmin = applyToStats tiStatIncSteps

tiFinal :: TiState -> Bool
tiFinal ([sole_addr], _, heap, _, _) =
  isDataNode (hLookup heap sole_addr)
tiFinal ([], _, _, _, _) = error "Empty stack!"
tiFinal _ = False

isDataNode :: Node -> Bool
isDataNode (NNum _) = True
isDataNode _ = False

step :: TiState -> TiState
step state@(stack, _, heap, _, _) = dispatch (hLookup heap (head stack))
  where dispatch (NNum n) = numStep state n
        dispatch (NAp a1 a2) = apStep state a1 a2
        dispatch (NSupercomb sc args body) = scStep state sc args body
        dispatch (NInd addr) = indStep state addr

indStep :: TiState -> Addr -> TiState
indStep (stack, dump, heap, globals, stats) addr =
  (addr:(tail stack), dump, heap, globals, stats)

numStep :: TiState -> Int -> TiState
numStep _ _ = error "Number applied as a function"

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, stats) a1 _ =
  (a1:stack, dump, heap, globals, stats)

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack, dump, heap, globals, stats) sc_name arg_names body =
  (new_stack, dump, new_heap, globals, stats)
  where new_stack = if (length arg_names) >= (length stack)
                    then error (sc_name ++ " applied to too few arguments")
                    else (drop (length arg_names) stack)
        new_heap = instantiateAndUpdate body (stack !! (length arg_names)) heap env
        env = arg_bindings ++ globals
        arg_bindings = zip arg_names (getargs heap (tail stack))

getargs :: TiHeap -> TiStack -> [Addr]
getargs heap stack = map get_arg stack
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
instantiate (ECase e alts) heap env = error "Can't instantiate case exprs"


instantiateConstr tag arity heap env = error "Can't instantiate constructors yet"

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
showState (stack,_,heap,_,_) =
  iConcat [showStack heap stack,iNewline,showHeap heap,iNewline]

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
showNode (NNum n) = (iStr "NNum ") `iAppend` (iNum n)
showNode (NInd addr) = (iStr "NInd ") `iAppend` (showAddr addr)

showAddr :: Addr -> Iseq
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> Iseq
showFWAddr addr = iStr (space (4 - length str) ++ str)
  where str = show addr

showStats :: TiState -> Iseq
showStats (_, _, heap, _, stats) =
  iConcat [ iNewline, iNewline, iStr "Total number of steps = ",
            iNum (tiStatGetSteps stats), iNewline,
            iStr "Heap size = ", iNum (hSize heap)]

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)

type TiStack = [Addr]

data TiDump = DummyTiDump

initialTiDump :: TiDump
initialTiDump = DummyTiDump

type TiHeap = Heap Node

data Node = NAp Addr Addr
          | NSupercomb Name [Name] CoreExpr
          | NNum Int
          | NInd Addr
          deriving Show

type TiGlobals = ASSOC Name Addr

type TiStats = Int

tiStatInitial :: TiStats
tiStatInitial = 0

tiStatIncSteps :: TiStats -> TiStats
tiStatIncSteps = (+1)

tiStatGetSteps :: TiStats -> Int
tiStatGetSteps = id

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats stats_fun (stack,dump,heap,sc_defs,stats) =
  (stack,dump,heap,sc_defs,stats_fun stats)
