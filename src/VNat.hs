module VNat where

import Function
import Liquid.ProofCombinators

-- Data. The natural numbers.
{-@
data VNat = Zero | Suc VNat
@-}
data VNat = Zero | Suc VNat

{-@ reflect vzero @-}
vzero :: VNat
vzero = Zero

{-@ reflect vone @-}
vone :: VNat
vone = Suc Zero

{-@ reflect vtwo @-}
vtwo :: VNat
vtwo = Suc vone

-- Function. Addition.
{-@ reflect vadd @-}
vadd :: Op2 VNat
vadd Zero n = n
vadd (Suc m) n = Suc (vadd m n)

-- Lemma. Additive identity.
{-@
vadd_identity :: n:VNat ->
  {IsIdentity vadd Zero n}
@-}
vadd_identity :: VNat -> Proof
vadd_identity Zero = ()
vadd_identity (Suc n) = vadd_identity n

{-@
vadd_m_Sn :: m:VNat -> n:VNat ->
  {vadd m (Suc n) = Suc (vadd m n)}
@-}
vadd_m_Sn :: VNat -> VNat -> Proof
vadd_m_Sn Zero n = ()
vadd_m_Sn (Suc m) n =
  vadd (Suc m) (Suc n)
    ==. Suc (vadd m (Suc n))
    ==. Suc (Suc (vadd m n))
    ? vadd_m_Sn m n
    ==. Suc (vadd (Suc m) n)
    *** QED

-- {-@
-- vadd_Sm_n :: m:VNat -> n:VNat ->
--   {vadd (Suc m) n = Suc (vadd m n)}
-- @-}
-- vadd_Sm_n :: VNat -> VNat -> Proof
-- vadd_Sm_n m n = ()

-- Lemma. Addition is commutative.
{-@
vadd_commutative :: m:VNat -> n:VNat ->
  {IsCommutative vadd m n}
@-}
vadd_commutative :: VNat -> VNat -> Proof
vadd_commutative Zero n = vadd_identity n
vadd_commutative (Suc m) n =
  vadd (Suc m) n
    ==. Suc (vadd m n)
    ==. Suc (vadd n m)
    ? vadd_commutative m n
    ==. vadd n (Suc m)
    ? vadd_m_Sn n m
    *** QED

-- Lemma. Addition is associative.
{-@
vadd_associative :: l:VNat -> m:VNat -> n:VNat ->
  {IsAssociative vadd l m n}
@-}
vadd_associative :: VNat -> VNat -> VNat -> Proof
vadd_associative Zero m n = ()
vadd_associative (Suc l) m n =
  vadd (Suc l) (vadd m n)
    ==. Suc (vadd l (vadd m n))
    ==. Suc (vadd (vadd l m) n)
    ? vadd_associative l m n
    ==. vadd (Suc (vadd l m)) n
    ==. vadd (vadd (Suc l) m) n
    *** QED

-- Function. Multiplication
{-@ reflect vmul @-}
vmul :: Op2 VNat
vmul Zero _ = Zero
vmul (Suc m) n = vadd n (vmul m n)

-- Lemma. Multiplicative identity.
{-@ vmul_identity :: n:VNat -> {IsIdentity vmul vone n} @-}
vmul_identity :: VNat -> Proof
vmul_identity Zero = ()
vmul_identity (Suc n) = vmul_identity n

-- Lemma. Multiplicative annihilator.
{-@ vmul_annihilator :: n:VNat -> {IsZero vmul Zero n} @-}
vmul_annihilator :: VNat -> Proof
vmul_annihilator Zero = ()
vmul_annihilator (Suc n) = vmul_annihilator n

{-@
assume vmul_commutative :: m:VNat -> n:VNat ->
  {IsCommutative vmul m n}
@-}
vmul_commutative :: VNat -> VNat -> Proof
vmul_commutative Zero n = vmul_annihilator n
vmul_commutative m Zero = vmul_annihilator m
vmul_commutative (Suc m) (Suc n) =
  vmul (Suc m) (Suc n)
    ==. vadd (Suc n) (vmul m (Suc n))
    ==. Suc (vadd n (vmul m (Suc n)))
    ==. Suc (vadd n (vmul (Suc n) m))
    ? vmul_commutative m (Suc n)
    ==. Suc (vadd n (vadd m (vmul n m)))
    ==. Suc (vadd n (vadd m (vmul m n)))
    ? vadd_commutative n m
    ==. Suc (vadd (vadd n m) (vmul m n))
    ? vadd_associative n m (vmul m n)
    ==. Suc (vadd (vadd m n) (vmul m n))
    ? vadd_commutative m n
    ==. Suc (vadd m (vadd n (vmul m n)))
    ? vadd_associative m n (vmul m n)
    ==. Suc (vadd m (vmul (Suc m) n))
    ==. Suc (vadd m (vmul n (Suc m)))
    ? vmul_commutative (Suc m) n
    ==. vadd (Suc m) (vmul n (Suc m))
    ==. vmul (Suc n) (Suc m)
    *** QED

-- Lemma. Distribution of vmultiplication over vaddition.
{-@ assume vmul_distributive :: l:VNat -> m:VNat -> n:VNat ->
  {IsDistributive vmul vadd l m n} @-}
vmul_distributive :: VNat -> VNat -> VNat -> Proof
vmul_distributive l m n = ()

-- vmul_distributive Zero    m n = ()
-- vmul_distributive (Suc l) m n
--   =   vmul (Suc l) (vadd m n)
--   ==. vadd (vadd m n) (vmul l (vadd m n))
--   ==. vadd (vadd m n) (vadd (vmul l m) (vmul l n)) ? vmul_distributive l m n
--   ==.
--   ==. vadd (vmul (Suc l) m) (vmul (Suc l) n)
--   *** QED
