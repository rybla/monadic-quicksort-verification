# Monadic Quicksort Verification in Liquid Haskell


A Liquid Haskell verification of Mu and Chiang's _[Deriving Monadic Quicksort][Mu S, Chiang T - Declarative Pearl- Deriving Monadic Quicksort]_.

## Tasks


- [ ] types synonyms (and predicates)
  - [x] collection of type synonyms and predicates relating to reasoning about functions (`Function.hs`)
  - [x] collection of type synonyms and predicates relating to reasoning about relations (functions that return `Bool`) (`Relation.hs`)
- [x] data classes:
  - [x] semigroup (`VSemigrou.hs`)
  - [x] functor (`VFunctor.hs`)
  - [x] group (`VGroup.hs`)
  - [x] monad (`VMonad.hs`)
    - [ ] monadic sequence right-identity (`vseq_identity_right`)
  - [ ] plus-monad, used for monadic nondeterminism (`VMonadPlus.hs`)
    - [x] implement
    - [x] plus-monadic refinement (`RefinesPlusMonadic` and `RefinesPlusMonadicF`)
    - [ ] plus-monadic refinement is monotic in monadic binding (`vbind_monotonic_refinement`)
    - [ ] guarding monad-commutes with other monad elements (that have just (monadic) effect)
    - [ ] guarding a conjunction is the same as the sequence of guarding each conjunct (`mguard_and_vseq`)
    - [ ] guarding the plus-monadic sum of two monad sequence terms with head elements are guarding on disjoint conditions plus-monad refines a top-level branching by the boolean over the sequence tails (`mguard_disjoint_branch`)
  - [ ] array-monad, used for monadic array interface (`VMonadArray.hs`)
    - [x] implement
    - [ ] array-monad writing the append of two lists is the same as the sequence of array-monad writing the first list and then array-monad writing the second list ofset by the length of the first list
  - [x] ordered (set) (`VOrdered.hs`)
- [ ] data
  - [x] identity functor (`VIdentity.hs`)
  - [x] list (`VList.hs`)
  - [x] natural numbers (`VNat.hs`)
- [x] SlowSort (`SlowSort.hs`)
  - [x] filter (nondeterministic) (`vfilter`)
  - [x] predicate for "sorted" (`isSorted`)
  - [x] permutation (nondeterministic) (`permute`)
  - [x] split (nondeterministic) (`split`)
- [ ] QuickSort (`QuickSort.hs`)
  - [x] specify partition function (as function predicate)
  - [x] implement `partition`
  - [ ] prove correctness of `partition` implementation
  - [ ] prove "divide and conquer" property (`divide_and_conquer`)



<!-- References -->

[Mu S, Chiang T - Declarative Pearl- Deriving Monadic Quicksort]: https://scm.iis.sinica.edu.tw/pub/2020-monadic-sort.pdf
