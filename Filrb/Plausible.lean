import Filrb.Basic
import Plausible

namespace Filrb

open Plausible

instance Set.sampleableExt {α : Type u} [SampleableExt α] [Ord α] [Preorder α] [LawfulOrd α] :
    SampleableExt (Set α) where
  proxy := List (SampleableExt.proxy α)
  sample := SampleableExt.sample (α := List α)
  interp xs := xs.foldl (init := .empty) (fun tree x => tree.insert (SampleableExt.interp x))

end Filrb
