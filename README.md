# Propositional Equality for Refinement Types 

## How to run 

```
# install the propositional equality library 
cd propositional-equality
stack install 

# run the tests/ examples in the paper 
stack test 

# run the case study 
cd .. 
stack install 
```


# EDITS

old src:                      & new src                            & paper  
PropositionalEquality         & Relation.Equality.Prop             & 
PEqProperties                 & Relation.Equality.Prop             &  
EqRT                          & EqualProp                          & 
EqT                           & EqualityProp                       & 

Reflexivity                   & Redefined as empty                 & 
refl                          & reflexivity                        & 
Transitivity                  & Transitivity'                      & 
trans                         & transitivity'                      & 
toSMT                         & concreteness                       & 
EqCtx                         & substitutability (+ flip args)     & 
eqRTCtx                       & same 
EqSMT                         & reflexivity
EqFun                         & extensionality
eqSMT                         & eqSMT'            


- Reverse.hs requires importing refined unit :(


# TODO 
Some restructuring could help. Maybe make them both top level dirsctories? 


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
- [x] prove `refinesplus_equalprop`
- [x] prove `refinesplus_reflexivity`
- [x] prove `refinesplus_transitivity`
- [x] prove `refinesplus_substitutability`
- [x] prove `writeList_append`
- [x] prove `writeList_redundancy`
- [x] prove `writeList_commutativity`

`Sort.List`:

- [ ] prove termination `permute`
- [x] prove `pure_refines_permute`
- [x] prove `permute_preserves_length`
- [x] prove `bind_seq_associativity_with_permute_preserved_length`
- [x] prove `divide_and_conquer`
  - [x] use auxes for `divide_and_conquer_aux`
  - [x] prove `divide_and_conquer_lemma1`:
    - [x] use auxes for `divide_and_conquer_lemma1_aux`
    - [x] several `bind_associativity`
    - [x] several `guard_and`
    - [x] rearrange `guard`s
    - [x] uses auxes to box `divide_and_conquer_lemma1_aux`
  - [x] prove `divide_and_conquer_lemma2`
    - [x] prove `Cons` case
    - [x] progress with `guard` properties
- [x] prove `quicksort_refines_slowsort`
  - [x] prove `Cons` case

`Sort.Array`:

- [x] prove `permute_kleisli_permute` in `Cons` case
  - [x] prove `permute_kleisli_permute_lemma` in `Cons` case
- [x] prove `ipartl_spec`
  - [x] prove `dispatch_preserves_length_append_ys_zs`
  - [x] prove `dispatch_commutativity_seq_bind`
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
    - [x] case `Cons`
    - [x] prove `ipartl_spec_lemma3_aux1_Cons`
    - [x] prove `ipartl_spec_lemma3_aux2_Cons`
  - [x] prove `ipartl_spec_steps1to3`
    - [x] prove `ipartl_spec_steps1to3_lemma`
  - [x] prove `ipartl_spec_steps3Ato4`
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
  - [x] prove `iqsort_step1`
  - [x] prove `iqsort_step2`
  - [x] prove `iqsort_step3`
  - [x] prove `iqsort_step4`

<!-- References -->

[mu s, chiang t - declarative pearl- deriving monadic quicksort]:
  https://scm.iis.sinica.edu.tw/pub/2020-monadic-sort.pdf
