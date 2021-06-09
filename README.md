# Monadic Quicksort Verification in Liquid Haskell

A Liquid Haskell verification of Mu and Chiang's _[Deriving Monadic
Quicksort][mu s, chiang t - declarative pearl- deriving monadic quicksort]_.

## Tasks

- [ ] try `--fast` option

`Placeholder.M`:

- [ ] implement `interpretM`
- [x] prove `kleisli_associativity`
- [x] prove `bind_if`
- [x] prove `seq_bind_associativity`
- [x] prove `bind_associativity4`
- [x] prove `seq_associativity4`
- [x] prove `seq_pure_bind`
- [x] prove `seq_if_bind`
- [x] prove `pure_kleisli`
- [ ] prove `refinesplus_equalprop`
- [x] prove `refinesplus_reflexivity`
- [x] prove `refinesplus_transitivity`
- [ ] prove `refinesplus_substitutability`
- [x] prove `writeList_append`
- [x] prove `writeList_redundancy`
- [ ] prove `writeList_commutativity`

`Sort.List`:

- [ ] prove termination `permute`
- [ ] prove `pure_refines_permute`
- [ ] prove `permute_preserves_length`
- [ ] prove `bind_seq_associativity_with_permute_preserved_length`
- [ ] prove `divide_and_conquer`
  - [ ] use auxes for `divide_and_conquer_aux`
  - [ ] prove `divide_and_conquer_lemma1`:
    - [ ] use auxes for `divide_and_conquer_lemma1_aux`
    - [ ] several `bind_associativity`
    - [ ] several `guard_and`
    - [ ] rearrange `guard`s
    - [ ] uses auxes to box `divide_and_conquer_lemma1_aux`
  - [ ] prove `divide_and_conquer_lemma2`
    - [ ] prove `Cons` case
    - [ ] progress with `guard` properties
- [ ] prove `quicksort_refines_slowsort`
  - [ ] prove `Cons` case

`Sort.Array`:

- [ ] prove `permute_kleisli_permute` in `Cons` case
  - [ ] prove `permute_kleisli_permute_lemma` in `Cons` case
- [x] prove `ipartl_spec`
  - [ ] prove `dispatch_preserves_length_append_ys_zs`
    - [ ] formalize
  - [ ] prove `dispatch_commutativity_seq_bind`
  - [x] prove `ipartl_spec_lemma1`
    - [x] prove `ipartl_spec_lemma1_step1`
    - [x] prove `ipartl_spec_lemma1_step1`
    - [x] prove `ipartl_spec_lemma1_step1`
  - [x] prove `ipartl_spec_lemma2`
    - [x] prove `ipartl_spec_lemma2_step1`
    - [x] prove `ipartl_spec_lemma2_step2`
    - [x] prove `ipartl_spec_lemma2_step3`
  - [x] prove `ipartl_spec_lemma3`
    - [x] prove `ipartl_spec_lemma3_aux1_Nil`
    - [x] prove `ipartl_spec_lemma3_aux2_Nil`
    - [ ] case `Cons`
    - [x] prove `ipartl_spec_lemma3_aux1_Cons`
    - [ ] prove `ipartl_spec_lemma3_aux2_Cons`
  - [x] prove `ipartl_spec_steps1to3`
    - [x] prove `ipartl_spec_steps1to3_lemma`
  - [ ] prove `ipartl_spec_steps3Ato4`
  - [x] prove `ipartl_spec_steps4to7`
    - [x] prove `ipartl_spec_steps4to7_lemma1`
    - [x] prove `ipartl_spec_steps4to7_lemma2`
    - [x] prove `ipartl_spec_steps4to5`
      - [x] prove `ipartl_spec_steps4to5_lemma1`
      - [x] prove `ipartl_spec_steps4to5_lemma2`
    - [x] prove `ipartl_spec_steps5to6`
    - [x] prove `ipartl_spec_steps6to7`
  - [x] prove `ipartl_spec_steps7to8`
    - [x] prove `ipartl_spec_steps7to8_lemma`
  - [x] prove `ipartl_spec_steps8to9`
  - [x] prove `ipartl_spec_steps`
- [ ] prove termination `iqsort`
- [x] prove `iqsort_spec`
  - [ ] outlined proofs
  - [ ] prove `iqsort_spec_lemma1`
  - [ ] prove `iqsort_spec_lemma2`
  - [ ] prove `iqsort_spec_lemma3`
  - [ ] prove `iqsort_spec_lemma4`

<!-- References -->

[mu s, chiang t - declarative pearl- deriving monadic quicksort]:
  https://scm.iis.sinica.edu.tw/pub/2020-monadic-sort.pdf
