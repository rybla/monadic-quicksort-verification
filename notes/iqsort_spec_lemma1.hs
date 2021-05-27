iqsort_spec_lemma1

{-@
iqsort_spec_lemma1 ::
  Equality (M ()) =>
  p:Int -> i:Natural -> xs:List Int ->
  EqualProp (M ())
    {iqsort_spec_lemma1_aux p i xs}
    {iqsort_spec_aux2 i (Cons p xs)}
@-}
iqsort_spec_lemma1 :: Equality (M ()) => Int -> Natural -> List Int -> EqualityProp (M ())
iqsort_spec_lemma1 = undefined -- TODO: this seems hard



iqsort_spec_lemma1_aux p i xs
-- defn iqsort_spec_lemma1_aux
partl' p (Nil, Nil, xs) >>= 
  iqsort_spec_lemma1_aux_aux p i
-- defn iqsort_spec_lemma1_aux_aux
partl' p (Nil, Nil, xs) >>= \(ys, zs) ->
  permute ys >>= 
    iqsort_spec_lemma1_aux_aux_aux p i ys zs
-- defn iqsort_spec_lemma1_aux_aux_aux
partl' p (Nil, Nil, xs) >>= \(ys, zs) ->
  permute ys >>= \ys' ->
    writeList i (ys' ++ Cons p Nil ++ zs) >>
      iqsort i (length ys) >>
        iqsort (S (i + length ys)) (length zs)
-- writeList_append
partl' p (Nil, Nil, xs) >>= \(ys, zs) ->
  permute ys >>= \ys' ->
    writeList i (ys' ++ Cons p Nil) >>
      writeList (i + length (ys' ++ Cons p Nil)) zs >>
        iqsort i (length ys) >>
          iqsort (S (i + length ys)) (length zs)
-- length_snoc, add_S_right
partl' p (Nil, Nil, xs) >>= \(ys, zs) ->
  permute ys >>= \ys' ->
    writeList i (ys' ++ Cons p Nil) >>
      writeList (S i + length ys') zs >>
        iqsort i (length ys) >>
          iqsort (S (i + length ys)) (length zs)
-- permute_preserves_length
partl' p (Nil, Nil, xs) >>= \(ys, zs) ->
  permute ys >>= \ys' ->
    writeList i (ys' ++ Cons p Nil) >>
      writeList (S (i + length ys)) zs >>
        iqsort i (length ys) >>
          iqsort (S (i + length ys)) (length zs)
-- permute_commutativity with writeList somehow?
partl' p (Nil, Nil, xs) >>= \(ys, zs) ->
  permute ys >>= \ys' ->
    writeList i (ys' ++ Cons p Nil) >>
      iqsort i (length ys) >>
        writeList (S (i + length ys)) zs >>
          iqsort (S (i + length ys)) (length zs)
-- (refine) [ref 12]
partl' p (Nil, Nil, xs) >>= \(ys, zs) ->
  permute ys >>= \ys' ->
    writeList i (ys' ++ Cons p Nil) >>
      iqsort i (length ys) >>
        slowsort zs >>=
          writeList (S (i + length ys))




-- writeList_append
partl' p (Nil, Nil, xs) >>= \(ys, zs) ->
  permute ys >>= \ys' ->
    writeList i ys' >>
      writeList (i + length ys') (Cons p Nil) >>
        iqsort i (length ys) >>
          slowsort zs >>=
            writeList (S (i + length ys))
-- writeList_commutativity
partl' p (Nil, Nil, xs) >>= \(ys, zs) ->
  permute ys >>= \ys' ->
    writeList (i + length ys') (Cons p Nil) >>
      writeList i ys' >>
        iqsort i (length ys) >>
          slowsort zs >>=
            writeList (S (i + length ys))
-- 
partl' p (Nil, Nil, xs) >>= \(ys, zs) ->
  permute ys >>= \ys' ->
    writeList (i + length ys') (Cons p Nil) >>
      writeList i ys' >>
        iqsort i (length ys) >>
          slowsort zs >>=
            writeList (S (i + length ys))
-- 





-- ... refines ...


-- 
( pure (partition x xs) >>= \(ys, zs) ->
    permute ys >>= slowsort >>= \ys' ->
      permute zs >>= slowsort >>= \zs' ->
        pure (ys' ++ Cons x Nil ++ zs')
) >>
  writeList i
-- 
( pure (partition x xs) >>= \(ys, zs) ->
    kleisli permute slowsort ys >>= \ys' ->
      kleisli permute slowsort zs >>= \zs' ->
        pure (ys' ++ Cons x Nil ++ zs')
) >>
  writeList i
-- kleisli permute slowsort
( pure (partition x xs) >>= \(ys, zs) ->
    slowsort ys >>= \ys' ->
      slowsort zs >>= \zs' ->
        pure (ys' ++ Cons x Nil ++ zs')
) >>
  writeList i
--
slowsort (Cons p xs) >>= 
  writeList i
--
iqsort_spec_aux2 i (Cons p xs)




-- 
-- 
-- 

pure (partition x xs) >>= \(ys, zs) ->
  slowsort ys >>= \ys' ->
    slowsort zs >>= \zs' ->
      pure (ys' ++ Cons x Nil ++ zs')
-- refines
slowsort (Cons x xs)