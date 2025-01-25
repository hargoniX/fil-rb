import Filrb.Basic

instance : Preorder UInt32 where
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_le := sorry

-- Park Miller LCG
@[inline]
def rand (x : UInt32) : UInt32 :=
  let product := x.toUInt64 * 48271
  let x := ((product &&& (0x7fffffff : UInt64)) + (product >>> 31)).toUInt32
  (x &&& (0x7fffffff : UInt32)) + (x >>> 31)

partial def buildRandomTree (seed : UInt32) (count : UInt32) : IO (Filrb.Set UInt32) := do
  let t1 ← IO.monoNanosNow
  let tree := go Filrb.Set.empty seed count
  let t2 ← IO.monoNanosNow
  IO.println s!"random-insert {t2 - t1}"
  return tree
where
  go (t : Filrb.Set UInt32) (seed : UInt32) (count : UInt32) : Filrb.Set UInt32 :=
    if count != 0 then
      let next := rand seed
      go (t.insert next) next (count - 1)
    else
      t

partial def searchRandomTree (t : Filrb.Set UInt32) (seed : UInt32) (count : UInt32) : IO Unit := do
  let t1 ← IO.monoNanosNow
  let found := go t seed count 0
  let t2 ← IO.monoNanosNow
  assert! count == found
  IO.println s!"random-search {t2 - t1}"
where
  go (t : Filrb.Set UInt32) (seed : UInt32) (count : UInt32) (found : UInt32) : UInt32 :=
    if count != 0 then
      let next := rand seed
      if t.contains next then
        go t next (count - 1) (found + 1)
      else
        go t next (count - 1) found
    else
      found

def benchRandomTree (seed : UInt32) (count : UInt32) : IO Unit := do
  let tree ← buildRandomTree seed count
  searchRandomTree tree seed count


partial def buildSequentialTree (count : UInt32) : IO (Filrb.Set UInt32) := do
  let t1 ← IO.monoNanosNow
  let tree := go Filrb.Set.empty count
  let t2 ← IO.monoNanosNow
  IO.println s!"sequential-insert {t2 - t1}"
  return tree
where
  go (t : Filrb.Set UInt32) (count : UInt32) : Filrb.Set UInt32 :=
    if count != 0 then
      go (t.insert count) (count - 1)
    else
      t

partial def searchSequentialTree (t : Filrb.Set UInt32) (count : UInt32) : IO Unit := do
  let t1 ← IO.monoNanosNow
  let found := go t count 0
  let t2 ← IO.monoNanosNow
  assert! count == found
  IO.println s!"sequential-search {t2 - t1}"
where
  go (t : Filrb.Set UInt32) (count : UInt32) (found : UInt32) : UInt32 :=
    if count != 0 then
      if t.contains count then
        go t (count - 1) (found + 1)
      else
        go t (count - 1) found
    else
      found

def benchSequentialTree (count : UInt32) : IO Unit := do
  let tree ← buildSequentialTree count
  searchSequentialTree tree count


def main (args : List String) : IO UInt32 := do
  if args.length < 2 then
    IO.println "Please provide more arguments"
    return 1
  let seed := String.toNat! args[0]! |>.toUInt32
  let count := String.toNat! args[1]! |>.toUInt32
  benchRandomTree seed count
  benchSequentialTree count
  return 0


