# LiquidHaskell Feedback

## Namespaces

### Records

Records often don't like the record field to appear in the Haskell definition.
For example, I've ended up having to define records in this way:

```haskell
{-@
data R a b c = R
  { x :: a,
    y :: b,
    z :: c
  }
@-}
data R a b c = R a b c

-- not lifted, as to not clash with refinement definition of `R`
x :: R a b c -> a
x (R x _ _) = x
-- and so on for `y` and `z`
```

### Type Synonyms

Refinement-level type synonyms seem to be declared globally. So I can't redefine
a type synonym in another module, even if the other module with the same-named
type synonym is imported qualified.

### Infixed Operations

Infixed-operations defined in one file cannot be used in the refinements of
another file, even with proper importing and hiding.

## Features

### Lambdas in Refinements

LH doesn't seem to handle these well.
