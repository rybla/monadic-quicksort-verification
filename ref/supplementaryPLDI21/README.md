# Supplementary matterial for PLDI'21 submission #190: Function Equality in Refinement Types 

- `proofs-and-definitions.pdf` contains the type derivation of thmEq in section 2 and the missing definitions and proofs from section 3. 

- `code` contains the code from sections 2, 4, and 5.
   To use Liquid Haskell to check all the code, run `stack build`. 
   The files check in the build are, as specified in `propositional-equality.cabal`: 

```
      -- section 2: unsound client
      Unsoundness.hs  

      -- section 4: library definitions and classy induction  
      PropositionalEquality.hs
      PEqProperties.hs 

      -- section 5: examples 
      5.1 Reverse.hs 
      5.2 RefinedDomains.hs 
      5.3 Map.hs
      5.4 Folds.hs
      5.5 RunTimeCheck.hs
      5.6 Readers.hs
      5.7 Endofunctors.hs
```