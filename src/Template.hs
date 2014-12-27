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
eval = undefined

showResults :: [TiState] -> String
showResults = undefined

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
