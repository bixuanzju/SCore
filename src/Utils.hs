module Utils where


{- Heap representation -}
type Heap a = (Int, [Int], [(Int, a)])
type Addr = Int

hInitial :: Heap a
hInitial = (0, [1..], [])

hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc (size, (next:free), cts) n = ((size + 1, free, (next, n):cts), next)

hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (size, free, cts) a n = (size, free, (a, n):(remove cts a))

hFree :: Heap a -> Addr -> Heap a
hFree (size, free, cts) a = (size-1, a:free, remove cts a)

hLookup :: Heap a -> Addr -> a
hLookup (size, free, cts) a = aLookup cts a (error $ "can't find node " ++ showaddr a ++ " in the heap")

hAddresses :: Heap a -> [Addr]
hAddresses (size, free, cts) = [addr | (addr, node) <- cts]

hNull :: Addr
hNull = 0

hIsNull :: Addr -> Bool
hIsNull = (== 0)

showaddr :: Addr -> String
showaddr a = "#" ++ show a

remove :: [(Int, a)] -> Addr -> [(Int, a)]
remove [] a = error ("Attempt to update or free nonexistent address " ++ showaddr a)
remove (n@(addr1,_):cts) addr2 =
  if addr1 == addr2
     then cts
     else n : (remove cts addr2)

{- Association list representation-}

type ASSOC a b = [(a, b)]

aLookup :: Eq a => [(a, t)] -> a -> t -> t
aLookup [] _  def = def
aLookup ((addr, n):cts') a def = if addr == a then n else aLookup cts' a def

aDomain :: ASSOC a b -> [a]
aDomain alist = [key | (key, val) <- alist]

aRange :: ASSOC a b -> [b]
aRange alist = [val | (key, val) <- alist]

aEmpty :: ASSOC a b
aEmpty = []
