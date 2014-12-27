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

mapAccuml :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccuml _ acc [] = (acc, [])
mapAccuml f acc (x:xs) = (acc2,x' : xs')
  where (acc1,x') = f acc x
        (acc2,xs') = mapAccuml f acc1 xs

eval :: TiState -> [TiState]
eval state = state : rest_states
  where rest_states | tiFinal state = []
                    | otherwise = eval next_state
        next_state = doAdmin (step state)

doAdmin :: TiState -> TiState
doAdmin = applyToStats tiStatIncSteps

tiFinal :: TiState -> Bool
tiFinal ([sole_addr], dump, heap, globals, stats) =
  isDataNode (hLookup heap sole_addr)
tiFinal ([], dump, heap, globals, stats) = error "Empty stack!"
tiFinal state = False

isDataNode :: Node -> Bool
isDataNode (NNum _) = True
isDataNode node = False

step :: TiState -> TiState
step state@(stack, dump, heap, globals, stats) = dispatch (hLookup heap (head stack))
  where dispatch (NNum n) = numStep state n
        dispatch (NAp a1 a2) = apStep state a1 a2
        dispatch (NSupercomb sc args body) = scStep state sc args body

numStep :: TiState -> Int -> TiState
numStep state n = error "Number applied as a function"

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, stats) a1 a2 =
  (a1:stack, dump, heap, globals, stats)

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack, dump, heap, globals, stats) sc_name arg_names body =
  (new_stack, dump, new_heap, globals, stats)
  where new_stack = result_addr : (drop (length arg_names + 1) stack)
        (new_heap, result_addr) = instantiate body heap env
        env = arg_bindings ++ globals
        arg_bindings = zip arg_names (getargs heap (tail stack))

getargs :: TiHeap -> TiStack -> [Addr]
getargs heap stack = map get_arg stack
  where get_arg addr = arg
          where (NAp fun arg) = hLookup heap addr

instantiate :: CoreExpr -> TiHeap -> ASSOC Name Addr -> (TiHeap, Addr)
instantiate (ENum n) heap env = hAlloc heap (NNum n)
instantiate (EAp e1 e2) heap env = hAlloc heap2 (NAp a1 a2)
  where (heap1, a1) = instantiate e1 heap env
        (heap2, a2) = instantiate e2 heap1 env
instantiate (EVar v) heap env = (heap, aLookup env v (error ("Undefined name " ++ show v)))
instantiate (EConstr tag arity) heap env = instantiateConstr tag arity heap env
instantiate (ELet isrec defs body) heap env = instantiateLet isrec defs body heap env
instantiate (ECase e alts) heap env = error "Can't instantiate case exprs"

instantiateConstr tag arity heap env = error "Can't instantiate constructors yet"
instantiateLet isrec defs body heap env = error "Can't instantiate let(rec)s yet"

showResults :: [TiState] -> String
showResults states = iDisplay (iConcat [ iLayn (map showState states),
                               showStats (last states)])

showState :: TiState -> Iseq
showState (stack, dump, heap, globals, stats) = iConcat [ showStack heap stack, iNewline ]

showStack :: TiHeap -> TiStack -> Iseq
showStack heap stack =
  iConcat [ iStr "Stk [",
            iIndent (iInterleave iNewline (map show_stack_item stack)),
            iStr " ]"]
  where show_stack_item addr = iConcat [ showFWAddr addr, iStr ": ",
                                         showStkNode heap (hLookup heap addr)]

showStkNode :: TiHeap -> Node -> Iseq
showStkNode heap (NAp fun arg) =
  iConcat [ iStr "NAp ", showFWAddr fun,
            iStr " ", showFWAddr arg, iStr " (",
            showNode (hLookup heap arg), iStr ")"]
showStkNode heap node = showNode node

showNode :: Node -> Iseq
showNode (NAp a1 a2) = iConcat [ iStr "NAp ", showAddr a1,
                                 iStr " ", showAddr a2]
showNode (NSupercomb name args body) = iStr ("NSupercomb " ++ name)
showNode (NNum n) = (iStr "NNum ") `iAppend` (iNum n)

showAddr :: Addr -> Iseq
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> Iseq
showFWAddr addr = iStr (space (4 - length str) ++ str)
  where str = show addr

showStats :: TiState -> Iseq
showStats (stack, dump, heap, globals, stats) =
  iConcat [ iNewline, iNewline, iStr "Total number of steps = ",
            iNum (tiStatGetSteps stats)]

type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)

type TiStack = [Addr]

data TiDump = DummyTiDump

initialTiDump :: TiDump
initialTiDump = DummyTiDump

type TiHeap = Heap Node

data Node = NAp Addr Addr
          | NSupercomb Name [Name] CoreExpr
          | NNum Int
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
