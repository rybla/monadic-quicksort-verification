# Monadic Quicksort Verification in Liquid Haskell

A Liquid Haskell verification of Mu and Chiang's _[Deriving Monadic
Quicksort][mu s, chiang t - declarative pearl- deriving monadic quicksort]_.

## Tasks

- [ ] types synonyms (and predicates)
  - [x] collection of type synonyms and predicates relating to reasoning about
        functions (`Function.hs`)
  - [x] collection of type synonyms and predicates relating to reasoning about
        relations (functions that return `Bool`) (`Relation.hs`)
- [x] data classes:
  - [x] semigroup (`VSemigroup.hs`)
  - [x] functor (`VFunctor.hs`)
  - [x] group (`VGroup.hs`)
  - [x] monad (`VMonad.hs`)
    - [ ] monadic sequence right-identity (`vseq_identity_right`)
  - [ ] plus-monad, used for monadic nondeterminism (`VMonadPlus.hs`)
    - [x] implement
    - [x] plus-monadic refinement (`RefinesPlusMonadic` and
          `RefinesPlusMonadicF`)
    - [x] plus-monadic refinement is monotic in monadic binding
          (`vbind_monotonic_refinement`)
    - [ ] guarding monad-commutes with other monad elements (that have just
          (monadic) effect)
    - [ ] guarding a conjunction is the same as the sequence of guarding each
          conjunct (`guard_and_vseq`)
    - [ ] guarding the plus-monadic sum of two monad sequence terms with head
          elements are guarding on disjoint conditions plus-monad refines a
          top-level branching by the boolean over the sequence tails
          (`guard_disjoint_branch`)
  - [ ] array-monad, used for monadic array interface (`VMonadArray.hs`)
    - [x] implement
    - [ ] array-monad writing the append of two lists is the same as the
          sequence of array-monad writing the first list and then array-monad
          writing the second list ofset by the length of the first list
  - [x] ordered (set) (`VOrdered.hs`)
- [ ] data
  - [x] identity functor (`VIdentity.hs`)
  - [x] list (`VList.hs`)
  - [x] natural numbers (`VNat.hs`)
- [ ] SlowSort List (`SlowSort.hs`)
  - [x] filter (nondeterministic) (`vfilter`)
  - [x] predicate for "is sorted" (`isSorted`)
  - [x] permutation (nondeterministic) (`permute`)
  - [x] split (nondeterministic) (`split`)
  - [ ] `slowsort` termination
  - [ ] `permute` termination
  - [ ] lift of a list plus-monadically refines permutations of itself
        (`identity_refines_permute`)
  - [ ] `isSorted` termination
  - [ ] `split` termination
- [ ] QuickSort List (`QuickSortList.hs`)
  - [ ] `partition_correct`
  - [ ] "divide and conquer" property (`divide_and_conquer`)
- [ ] Partition Array (`PartitionArray.hs`)
  - [ ] what's the main theorem of this module?
  - [x] mark corresponding terms in paper
  - [ ] `partl_correct`
  - [ ] `partl_generalizes_partition`
  - [ ] `ipartl_specification1_correct`
  - [ ] decide how to handle (get rid of / name) commented-out implementation
        for `partl'` that is given in paper but then overriden
  - [ ] `ipartl_specification2_correct`
  - [ ] `ipartl_VCons_specification3_correct`
  - [ ] `ipartl_VCons_then_specification4_correct`
  - [ ] `ipartl_VCons_else_specification4_correct`
  - [ ] `refinement11`
  - [ ] `ipartl_VCons_specification5_correct`
- [ ] QuickSort Array (`QuickSortArray.hs`)
  - [ ] `iqsort_specification1_correct`
  - [ ] `iqsort_specification2_correct`
  - [ ] `refinement13`
  - [ ] `iqsort_specification3_correct`

<!-- old -->

- [ ] QuickSort List (`QuickSort.hs`)
  - [x] specify partition function (as function predicate)
  - [x] implement `partition`
  - [ ] prove correctness of `partition` implementation
  - [ ] prove "divide and conquer" property (`divide_and_conquer`)

<!-- References -->

[mu s, chiang t - declarative pearl- deriving monadic quicksort]:
  https://scm.iis.sinica.edu.tw/pub/2020-monadic-sort.pdf
