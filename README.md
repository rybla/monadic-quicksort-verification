# Monadic Quicksort Verification in Liquid Haskell

A Liquid Haskell verification of Mu and Chiang's _[Deriving Monadic
Quicksort][mu s, chiang t - declarative pearl- deriving monadic quicksort]_.

## Tasks

`Placeholder.M`:

- [ ] prove `kleisli_associativity`

`Sort.List`:

- [ ] prove termination `permute`
- [ ] use auxes for `divide_and_conquer_lemma1_aux`
- [ ] prove `divide_and_conquer_lemma1`:
  - [ ] several `bind_associativity`
  - [ ] several `guard_and`
  - [ ] rearrange `guard`s
  - [ ] uses auxes to box `divide_and_conquer_lemma1_aux`
- [ ] use auxes for `divide_and_conquer_aux`
- [ ] prove `divide_and_conquer`
- [ ] prove `divide_and_conquer_lemma2` in `Cons` case
  - [ ] progress with `guard` properties
- [ ] prove `quicksort_refines_slowsort` in `Cons` case

`Sort.Array`:

- [ ] prove `ipartl_spec_lemma1`
- [ ] prove `ipartl_spec_lemma2`
- [ ] prove `ipartl_spec_lemma3_aux1_Nil`
- [ ] prove `ipartl_spec_lemma3_aux2_Nil`
- [ ] prove `ipartl_spec_lemma3_aux1_Cons`
- [ ] prove `ipartl_spec_lemma3_aux2_Cons`
- [ ] prove `ipartl_spec_lemma3`
- [x] prove `ipartl_spec_steps1to3`
  - [ ] prove `ipartl_spec_steps1to3_lemma`
- [ ] prove `ipartl_spec_steps3Ato4`
- [ ] prove `permute_kleisli_permute` in `Cons` case
  - [ ] prove `permute_kleisli_permute_lemma` in `Cons` case
- [ ] prove termination `iqsort`
- [ ] prove `ipartl_spec_steps4to7`
  - [ ] prove `ipartl_spec_steps4to5`
    - [x] prove `ipartl_spec_steps4to5_lemma1`
    - [ ] prove `ipartl_spec_steps4to5_lemma2`
  - [ ] prove `ipartl_spec_steps5to6`
  - [ ] prove `ipartl_spec_steps6to7`
  - [x] prove `ipartl_spec_steps4to7_lemma1`
  - [x] prove `ipartl_spec_steps4to7_lemma2`

<!-- References -->

[mu s, chiang t - declarative pearl- deriving monadic quicksort]:
  https://scm.iis.sinica.edu.tw/pub/2020-monadic-sort.pdf
