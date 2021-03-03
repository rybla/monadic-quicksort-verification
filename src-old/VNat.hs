module VNat where

import Function
import Language.Haskell.Liquid.ProofCombinators

-- Data. The natural numbers.
{-@
data VNat = Zero | Suc VNat
@-}
data VNat = Zero | Suc VNat

{-@ inline vzero @-}
vzero :: VNat
vzero = Zero

{-@ inline vone @-}
vone :: VNat
vone = Suc Zero

{-@ inline vtwo @-}
vtwo :: VNat
vtwo = Suc vone

-- Function. Addition.
{-@ reflect vadd @-}
vadd :: Op2 VNat
vadd Zero n = n
vadd (Suc m) n = Suc (vadd m n)

-- Lemma. Additive right-identity i.e. n + 0 = n.
{-@ automatic-instances vadd_identity_right @-}
{-@
vadd_identity_right :: n:VNat -> {vadd n Zero = n}
@-}
vadd_identity_right :: VNat -> Proof
vadd_identity_right Zero = ()
-- vadd Zero Zero
--   === Zero
--   *** QED
vadd_identity_right (Suc n) =
  vadd (Suc n) Zero
    === Suc (vadd n Zero)
    === (Suc n ? vadd_identity_right n)
    *** QED

-- Lemma. Addition with successor on the right i.e. m + S n = S (m + n).
{-@
vadd_Suc_right :: m:VNat -> n:VNat -> {vadd m (Suc n) = Suc (vadd m n)}
@-}
vadd_Suc_right :: VNat -> VNat -> Proof
vadd_Suc_right Zero n =
  vadd Zero (Suc n)
    === Suc n ? vadd_identity_right (Suc n)
    === (Suc (vadd Zero n) ? vadd_identity_right n)
    *** QED
vadd_Suc_right (Suc m) n =
  vadd (Suc m) (Suc n)
    === Suc (vadd m (Suc n))
    === (Suc (Suc (vadd m n)) ? vadd_Suc_right m n)
    === Suc (vadd (Suc m) n)
    *** QED

-- Lemma. Additive left-identity i.e. 0 + n = n.
{-@ automatic-instances vadd_identity_left @-}
{-@
vadd_identity_left:: n:VNat -> {IsIdentityLeft vadd Zero n}
@-}
vadd_identity_left :: VNat -> Proof
vadd_identity_left _ = ()

-- Lemma. Additive identity i.e. n + 0 = 0 + n = n.
{-@ automatic-instances vadd_identity @-}
{-@
vadd_identity :: n:VNat -> {IsIdentity vadd Zero n}
@-}
vadd_identity :: VNat -> Proof
vadd_identity n = vadd_identity_right n

-- Lemma. Addition is commutative i.e. m + n = n + m.
{-@
vadd_commutative :: m:VNat -> n:VNat -> {IsCommutative vadd m n}
@-}
vadd_commutative :: VNat -> VNat -> Proof
vadd_commutative Zero n =
  vadd Zero n
    === n ? vadd_identity n
    === vadd n Zero ? vadd_identity n
    *** QED
vadd_commutative (Suc m) n =
  vadd (Suc m) n
    === Suc (vadd m n)
    === (Suc (vadd n m) ? vadd_commutative m n)
    === (vadd n (Suc m) ? vadd_Suc_right n m)
    *** QED

-- Lemma. Addition is associative i.e. l + (m + n) = (l + m) + n.
{-@
vadd_associative :: l:VNat -> m:VNat -> n:VNat -> {IsAssociative vadd l m n}
@-}
vadd_associative :: VNat -> VNat -> VNat -> Proof
vadd_associative Zero m n =
  vadd Zero (vadd m n)
    === (vadd m n ? vadd_identity (vadd m n))
    === (vadd (vadd Zero m) n ? vadd_identity m)
    *** QED
vadd_associative (Suc l) m n =
  vadd (Suc l) (vadd m n)
    === Suc (vadd l (vadd m n))
    === (Suc (vadd (vadd l m) n) ? vadd_associative l m n)
    === vadd (Suc (vadd l m)) n
    === vadd (vadd (Suc l) m) n
    *** QED

-- Function. Multiplication
{-@ reflect vmul @-}
vmul :: Op2 VNat
vmul Zero _ = Zero
vmul (Suc m) n = vadd n (vmul m n)

-- Lemma. Multiplicative identity i.e. 1 * n = n.
{-@ automatic-instances vmul_identity @-}
{-@ vmul_identity :: n:VNat -> {IsIdentity vmul vone n} @-}
vmul_identity :: VNat -> Proof
vmul_identity Zero = trivial
vmul_identity (Suc n) = vmul_identity n

-- Lemma. Multiplicative zero i.e. 0 * n = n * 0 = 0.
{-@ automatic-instances vmul_zero @-}
{-@ vmul_zero :: n:VNat -> {IsZero vmul Zero n} @-}
vmul_zero :: VNat -> Proof
vmul_zero Zero = ()
vmul_zero (Suc n) = vmul_zero n

-- TODO: prove
-- Lemma. Multiplicative commutativity i.e. m * n = n * m.
{-@
assume vmul_commutative :: m:VNat -> n:VNat ->
  {IsCommutative vmul m n}
@-}
vmul_commutative :: VNat -> VNat -> Proof
vmul_commutative Zero n = vmul_zero n
vmul_commutative m Zero = vmul_zero m
vmul_commutative (Suc m) (Suc n) = ()

-- TODO: proof in progress
-- vmul (Suc m) (Suc n)
--   === vadd (Suc n) (vmul m (Suc n))
--   === Suc (vadd n (vmul m (Suc n)))
--   === (Suc (vadd n (vmul (Suc n) m)) ? vmul_commutative m (Suc n))
--   === Suc (vadd n (vadd m (vmul n m)))
--   === (Suc (vadd n (vadd m (vmul m n))) ? vadd_commutative n m)
--   === (Suc (vadd (vadd n m) (vmul m n)) ? vadd_associative n m (vmul m n))
--   === (Suc (vadd (vadd m n) (vmul m n)) ? vadd_commutative m n)
--   === (Suc (vadd m (vadd n (vmul m n))) ? vadd_associative m n (vmul m n))
--   === Suc (vadd m (vmul (Suc m) n))
--   === (Suc (vadd m (vmul n (Suc m))) ? vmul_commutative (Suc m) n)
--   === vadd (Suc m) (vmul n (Suc m))
--   === vmul (Suc n) (Suc m)
--   *** QED

-- TODO: prove
-- Lemma. Distribution of vmultiplication over vaddition i.e.
-- l * (m + n) = (l * m) + (l * n).
{-@ assume vmul_distributive :: l:VNat -> m:VNat -> n:VNat ->
  {IsDistributive vmul vadd l m n} @-}
vmul_distributive :: VNat -> VNat -> VNat -> Proof
vmul_distributive l m n = ()

-- TODO: proof in progress
-- vmul_distributive Zero    m n = ()
-- vmul_distributive (Suc l) m n
--   =   vmul (Suc l) (vadd m n)
--   === vadd (vadd m n) (vmul l (vadd m n))
--   === (vadd (vadd m n) (vadd (vmul l m) (vmul l n)) ? vmul_distributive l m n)
--   ===
--   === vadd (vmul (Suc l) m) (vmul (Suc l) n)
--   *** QED
