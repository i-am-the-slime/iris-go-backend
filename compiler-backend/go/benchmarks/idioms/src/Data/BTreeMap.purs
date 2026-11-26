-- | A persistent B-tree with ordered-collections' Data.Map interface: wide nodes of keys and
-- | values in flat arrays, so a lookup touches a few arrays and a map of a million entries is a
-- | handful of levels deep. Every write copies the arrays on the path from the root.
module Data.BTreeMap
  ( Map
  , empty
  , singleton
  , isEmpty
  , size
  , lookup
  , member
  , insert
  , insertWith
  , delete
  , alter
  , update
  , foldlWithKey
  , foldrWithKey
  , toArray
  , toUnfoldable
  , keys
  , values
  , fromFoldable
  , fromFoldableWith
  , fromAscending
  , unionWith
  , union
  , maxKeys
  ) where

import Prelude

import Control.Monad.ST as ST
import Data.Array ((..))
import Data.Array as Array
import Data.Array.ST as STArray
import Data.Foldable (class Foldable, foldMapDefaultL)
import Data.FoldableWithIndex (class FoldableWithIndex, foldMapWithIndexDefaultL, foldlWithIndex, foldrWithIndex)
import Data.FunctorWithIndex (class FunctorWithIndex)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Unfoldable (class Unfoldable)
import Partial.Unsafe (unsafePartial)

-- | The number of entries and the root.
data Map k v = Map Int (Node k v)

-- | Keys and values side by side, and the children between them; a leaf has no children.
data Node k v = Node (Array k) (Array v) (Array (Node k v))

maxKeys :: Int
maxKeys = 16

minKeys :: Int
minKeys = maxKeys / 2

empty :: forall k v. Map k v
empty = Map 0 (Node [] [] [])

singleton :: forall k v. k -> v -> Map k v
singleton key value = Map 1 (Node [ key ] [ value ] [])

isEmpty :: forall k v. Map k v -> Boolean
isEmpty (Map count _) = count == 0

size :: forall k v. Map k v -> Int
size (Map count _) = count

lookup :: forall k v. Ord k => k -> Map k v -> Maybe v
lookup key (Map _ root) = go root
  where
  go (Node nodeKeys nodeValues children) = do
    let { index, found } = search key nodeKeys
    if found then Just (at nodeValues index)
    else if Array.null children then Nothing
    else go (at children index)

member :: forall k v. Ord k => k -> Map k v -> Boolean
member key m = case lookup key m of
  Just _ -> true
  Nothing -> false

insert :: forall k v. Ord k => k -> v -> Map k v -> Map k v
insert = insertWith \_ new -> new

-- | `insertWith combine key value`: an existing value becomes `combine old value`, and the key
-- | replaces the stored one, as in Data.Map.
insertWith :: forall k v. Ord k => (v -> v -> v) -> k -> v -> Map k v -> Map k v
insertWith combine key value (Map count root) = case insertInto root of
  Inserted added node -> Map (if added then count + 1 else count) (grow node)
  where
  insertInto (Node nodeKeys nodeValues children) = do
    let { index, found } = search key nodeKeys
    if found then
      Inserted false (Node (setAt index key nodeKeys) (setAt index (combine (at nodeValues index) value) nodeValues) children)
    else if Array.null children then
      Inserted true (Node (insertAt index key nodeKeys) (insertAt index value nodeValues) children)
    else case insertInto (at children index) of
      Inserted added child
        | overfull child -> Inserted added (splitChild index child (Node nodeKeys nodeValues children))
        | otherwise -> Inserted added (Node nodeKeys nodeValues (setAt index child children))

data Inserted k v = Inserted Boolean (Node k v)

delete :: forall k v. Ord k => k -> Map k v -> Map k v
delete key m@(Map count root)
  | member key m = Map (count - 1) (shrink (deleteFrom key root))
  | otherwise = m

alter :: forall k v. Ord k => (Maybe v -> Maybe v) -> k -> Map k v -> Map k v
alter change key m = case change (lookup key m) of
  Nothing -> delete key m
  Just value -> insert key value m

update :: forall k v. Ord k => (v -> Maybe v) -> k -> Map k v -> Map k v
update change key m = case lookup key m of
  Nothing -> m
  Just old -> case change old of
    Nothing -> delete key m
    Just value -> insert key value m

-- | Entries in ascending key order.
foldlWithKey :: forall k v a. (k -> a -> v -> a) -> a -> Map k v -> a
foldlWithKey step start (Map _ root) = go start root
  where
  go accumulated (Node nodeKeys nodeValues children)
    | Array.null children = foldlWithIndex (\index acc value -> step (at nodeKeys index) acc value) accumulated nodeValues
    | otherwise = do
        let before = foldlWithIndex (\index acc value -> step (at nodeKeys index) (go acc (at children index)) value) accumulated nodeValues
        go before (at children (Array.length nodeKeys))

-- | Entries in descending key order, the greatest combined first.
foldrWithKey :: forall k v a. (k -> v -> a -> a) -> a -> Map k v -> a
foldrWithKey step start (Map _ root) = go root start
  where
  go (Node nodeKeys nodeValues children) accumulated
    | Array.null children = foldrWithIndex (\index value acc -> step (at nodeKeys index) value acc) accumulated nodeValues
    | otherwise = do
        let after = go (at children (Array.length nodeKeys)) accumulated
        foldrWithIndex (\index value acc -> go (at children index) (step (at nodeKeys index) value acc)) after nodeValues

toArray :: forall k v. Map k v -> Array (k /\ v)
toArray (Map _ root) = STArray.run do
  out <- STArray.new
  pushEntries out root
  pure out

pushEntries :: forall h k v. STArray.STArray h (k /\ v) -> Node k v -> ST.ST h Unit
pushEntries out (Node nodeKeys nodeValues children) = do
  ST.for 0 (Array.length nodeKeys) \index -> do
    when (not (Array.null children)) (pushEntries out (at children index))
    void (STArray.push (at nodeKeys index /\ at nodeValues index) out)
  when (not (Array.null children)) (pushEntries out (at children (Array.length nodeKeys)))

toUnfoldable :: forall f k v. Unfoldable f => Map k v -> f (k /\ v)
toUnfoldable = toArray >>> Array.toUnfoldable

keys :: forall k v. Map k v -> Array k
keys = foldrWithKey (\key _ rest -> Array.cons key rest) []

values :: forall k v. Map k v -> Array v
values = foldrWithKey (\_ value rest -> Array.cons value rest) []

-- | Later entries win. Entries already in strictly ascending key order build in O(n).
fromFoldable :: forall f k v. Ord k => Foldable f => f (k /\ v) -> Map k v
fromFoldable = fromFoldableWith \new _ -> new

-- | A repeated key keeps `combine new old`, as Data.Map's fromFoldableWith.
fromFoldableWith :: forall f k v. Ord k => Foldable f => (v -> v -> v) -> f (k /\ v) -> Map k v
fromFoldableWith combine entries = built
  where
  built
    | ascending = fromAscending (entryArray <#> fst') (entryArray <#> snd')
    | otherwise = Array.foldl (\m (key /\ value) -> insertWith (flip combine) key value m) empty entryArray
  entryArray = Array.fromFoldable entries
  ascending = ascendingFrom 0
  ascendingFrom index
    | index + 1 >= Array.length entryArray = true
    | fst' (at entryArray index) < fst' (at entryArray (index + 1)) = ascendingFrom (index + 1)
    | otherwise = false
  fst' (key /\ _) = key
  snd' (_ /\ value) = value

-- | The map of keys in strictly ascending order, built bottom up.
fromAscending :: forall k v. Array k -> Array v -> Map k v
fromAscending entryKeys entryValues
  | Array.null entryKeys = empty
  | otherwise = Map (Array.length entryKeys) (build entryKeys entryValues (heightFor 0))
  where
  heightFor height
    | capacity height >= Array.length entryKeys = height
    | otherwise = heightFor (height + 1)

-- | Entries of both; where both have a key, the right map's key and `combine left right`.
unionWith :: forall k v. Ord k => (v -> v -> v) -> Map k v -> Map k v -> Map k v
unionWith combine left right
  | isEmpty left = right
  | isEmpty right = left
  | otherwise = do
      let merged = mergeAscending combine (toArray left) (toArray right)
      fromAscending (merged <#> \(key /\ _) -> key) (merged <#> \(_ /\ value) -> value)

mergeAscending :: forall k v. Ord k => (v -> v -> v) -> Array (k /\ v) -> Array (k /\ v) -> Array (k /\ v)
mergeAscending combine ls rs = STArray.run do
    out <- STArray.new
    let
      go i j
        | i >= Array.length ls = ST.for j (Array.length rs) \index -> push (at rs index) out
        | j >= Array.length rs = ST.for i (Array.length ls) \index -> push (at ls index) out
        | otherwise = do
            let (lk /\ lv) = at ls i
            let (rk /\ rv) = at rs j
            case compare lk rk of
              LT -> push (lk /\ lv) out *> go (i + 1) j
              GT -> push (rk /\ rv) out *> go i (j + 1)
              EQ -> push (rk /\ combine lv rv) out *> go (i + 1) (j + 1)
    go 0 0
    pure out
  where
  push :: forall h. (k /\ v) -> STArray.STArray h (k /\ v) -> ST.ST h Unit
  push entry out = void (STArray.push entry out)

union :: forall k v. Ord k => Map k v -> Map k v -> Map k v
union = unionWith const

instance (Show k, Show v) => Show (Map k v) where
  show m = "(fromFoldable " <> show (toArray m) <> ")"

instance (Eq k, Eq v) => Eq (Map k v) where
  eq left right = size left == size right && toArray left == toArray right

instance (Ord k, Ord v) => Ord (Map k v) where
  compare left right = compare (toArray left) (toArray right)

instance Functor (Map k) where
  map change (Map count root) = Map count (go root)
    where
    go (Node nodeKeys nodeValues children) = Node nodeKeys (nodeValues <#> change) (children <#> go)

instance FunctorWithIndex k (Map k) where
  mapWithIndex change (Map count root) = Map count (go root)
    where
    go (Node nodeKeys nodeValues children) =
      Node nodeKeys (Array.mapWithIndex (\index value -> change (at nodeKeys index) value) nodeValues) (children <#> go)

instance Foldable (Map k) where
  foldl step = foldlWithKey \_ acc value -> step acc value
  foldr step = foldrWithKey \_ value acc -> step value acc
  foldMap = foldMapDefaultL

instance FoldableWithIndex k (Map k) where
  foldlWithIndex step = foldlWithKey step
  foldrWithIndex step = foldrWithKey step
  foldMapWithIndex = foldMapWithIndexDefaultL

-- | The index of the first key not less than `key`, and whether it is `key`.
search :: forall k. Ord k => k -> Array k -> { index :: Int, found :: Boolean }
search key nodeKeys = go 0 (Array.length nodeKeys)
  where
  go low high
    | low < high = do
        let middle = (low + high) / 2
        if at nodeKeys middle < key then go (middle + 1) high else go low middle
    | otherwise = { index: low, found: low < Array.length nodeKeys && at nodeKeys low == key }

overfull :: forall k v. Node k v -> Boolean
overfull (Node nodeKeys _ _) = Array.length nodeKeys > maxKeys

grow :: forall k v. Node k v -> Node k v
grow root
  | overfull root = splitChild 0 root (Node [] [] [ root ])
  | otherwise = root

-- | Splits the parent's overfull child at `index` around its middle entry.
splitChild :: forall k v. Int -> Node k v -> Node k v -> Node k v
splitChild index (Node childKeys childValues grandchildren) (Node nodeKeys nodeValues children) =
  Node (insertAt index (at childKeys middle) nodeKeys) (insertAt index (at childValues middle) nodeValues)
    (insertAt (index + 1) right (setAt index left children))
  where
  middle = Array.length childKeys / 2
  left = Node (Array.take middle childKeys) (Array.take middle childValues) (Array.take (middle + 1) grandchildren)
  right = Node (Array.drop (middle + 1) childKeys) (Array.drop (middle + 1) childValues) (Array.drop (middle + 1) grandchildren)

-- | Removes `key`, which the subtree holds. The result may hold fewer than minKeys keys, which
-- | its parent repairs.
deleteFrom :: forall k v. Ord k => k -> Node k v -> Node k v
deleteFrom key (Node nodeKeys nodeValues children) = deleted
  where
  deleted
    | Array.null children = Node (removeAt index nodeKeys) (removeAt index nodeValues) children
    | found = case deleteLast (at children index) of
        Popped lastKey lastValue child ->
          repair index (Node (setAt index lastKey nodeKeys) (setAt index lastValue nodeValues) (setAt index child children))
    | otherwise = repair index (Node nodeKeys nodeValues (setAt index (deleteFrom key (at children index)) children))
  searched = search key nodeKeys
  index = searched.index
  found = searched.found

data Popped k v = Popped k v (Node k v)

deleteLast :: forall k v. Node k v -> Popped k v
deleteLast (Node nodeKeys nodeValues children) = popped
  where
  popped
    | Array.null children = Popped (at nodeKeys last) (at nodeValues last) (Node (Array.take last nodeKeys) (Array.take last nodeValues) children)
    | otherwise = case deleteLast (at children (last + 1)) of
        Popped key value child -> Popped key value (repair (last + 1) (Node nodeKeys nodeValues (setAt (last + 1) child children)))
  last = Array.length nodeKeys - 1

-- | Gives the child at `index` at least minKeys keys, borrowing from a sibling or merging with one.
repair :: forall k v. Int -> Node k v -> Node k v
repair index parent@(Node nodeKeys nodeValues children) = repaired
  where
  repaired
    | keyCount (at children index) >= minKeys = parent
    | index > 0 && keyCount (at children (index - 1)) > minKeys = borrowFromLeft index
    | index + 1 < Array.length children && keyCount (at children (index + 1)) > minKeys = borrowFromRight index
    | index + 1 < Array.length children = merge index
    | otherwise = merge (index - 1)
  keyCount (Node ks _ _) = Array.length ks
  borrowFromLeft index = do
    let Node childKeys childValues grandchildren = at children index
    let Node leftKeys leftValues leftChildren = at children (index - 1)
    let last = Array.length leftKeys - 1
    let child = Node (Array.cons (at nodeKeys (index - 1)) childKeys) (Array.cons (at nodeValues (index - 1)) childValues)
          (if Array.null leftChildren then grandchildren else Array.cons (at leftChildren (last + 1)) grandchildren)
    let left = Node (Array.take last leftKeys) (Array.take last leftValues) (Array.take (last + 1) leftChildren)
    Node (setAt (index - 1) (at leftKeys last) nodeKeys) (setAt (index - 1) (at leftValues last) nodeValues)
      (setAt (index - 1) left (setAt index child children))
  borrowFromRight index = do
    let Node childKeys childValues grandchildren = at children index
    let Node rightKeys rightValues rightChildren = at children (index + 1)
    let child = Node (Array.snoc childKeys (at nodeKeys index)) (Array.snoc childValues (at nodeValues index))
          (if Array.null rightChildren then grandchildren else Array.snoc grandchildren (at rightChildren 0))
    let right = Node (Array.drop 1 rightKeys) (Array.drop 1 rightValues) (Array.drop 1 rightChildren)
    Node (setAt index (at rightKeys 0) nodeKeys) (setAt index (at rightValues 0) nodeValues)
      (setAt index child (setAt (index + 1) right children))
  merge leftIndex = do
    let Node leftKeys leftValues leftChildren = at children leftIndex
    let Node rightKeys rightValues rightChildren = at children (leftIndex + 1)
    let merged = Node (leftKeys <> [ at nodeKeys leftIndex ] <> rightKeys) (leftValues <> [ at nodeValues leftIndex ] <> rightValues)
          (leftChildren <> rightChildren)
    Node (removeAt leftIndex nodeKeys) (removeAt leftIndex nodeValues) (removeAt (leftIndex + 1) (setAt leftIndex merged children))

shrink :: forall k v. Node k v -> Node k v
shrink root@(Node nodeKeys _ children)
  | Array.null nodeKeys && not (Array.null children) = at children 0
  | otherwise = root

-- | The most entries a subtree of this height holds.
capacity :: Int -> Int
capacity height
  | height <= 0 = maxKeys
  | capacity (height - 1) > 100000000 = capacity (height - 1)
  | otherwise = capacity (height - 1) * (maxKeys + 1) + maxKeys

build :: forall k v. Array k -> Array v -> Int -> Node k v
build entryKeys entryValues height
  | height == 0 = Node entryKeys entryValues []
  | otherwise = buildBranch entryKeys entryValues height

-- | A node of this height above the entries: about equal children, each built the same way.
buildBranch :: forall k v. Array k -> Array v -> Int -> Node k v
buildBranch entryKeys entryValues height = Node separators separatorValues children
  where
  below = capacity (height - 1)
  childCount = max 2 ((Array.length entryKeys + 1 + below) / (below + 1))
  entries = Array.length entryKeys - (childCount - 1)
  sizeOf child = entries / childCount + (if child < entries `mod` childCount then 1 else 0)
  startOf child = child * (entries / childCount) + min child (entries `mod` childCount) + child
  children = (0 .. (childCount - 1)) <#> \child -> do
    let start = startOf child
    let end = start + sizeOf child
    build (Array.slice start end entryKeys) (Array.slice start end entryValues) (height - 1)
  separatorAt child = startOf child + sizeOf child
  separators = (0 .. (childCount - 2)) <#> \child -> at entryKeys (separatorAt child)
  separatorValues = (0 .. (childCount - 2)) <#> \child -> at entryValues (separatorAt child)

at :: forall a. Array a -> Int -> a
at elements index = unsafePartial (Array.unsafeIndex elements index)

setAt :: forall a. Int -> a -> Array a -> Array a
setAt index value elements = Array.updateAt index value elements # fromMaybe elements

insertAt :: forall a. Int -> a -> Array a -> Array a
insertAt index value elements = Array.insertAt index value elements # fromMaybe elements

removeAt :: forall a. Int -> Array a -> Array a
removeAt index elements = Array.deleteAt index elements # fromMaybe elements
