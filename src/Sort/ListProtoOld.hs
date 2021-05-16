--
-- ! OLD
--

{-@ reflect ipartl_spec_steps_4_to_7_lemma3_aux1 @-}
ipartl_spec_steps_4_to_7_lemma3_aux1 :: Int -> Natural -> (List Int, List Int, List Int) -> M (Natural, Natural)
ipartl_spec_steps_4_to_7_lemma3_aux1 p i (ys', zs', xs) =
  writeList i (ys' ++ zs')
    >> writeList (i + length (ys' ++ zs')) xs
    >> ipartl p i (length ys', length zs', length xs)

{-@ reflect ipartl_spec_steps_4_to_7_lemma3_aux2 @-}
ipartl_spec_steps_4_to_7_lemma3_aux2 :: Int -> Natural -> (List Int, List Int, List Int) -> M (Natural, Natural)
ipartl_spec_steps_4_to_7_lemma3_aux2 p i (ys', zs', xs) =
  ( writeListToLength3 i
      >=> ipartl p i
  )
    (ys', zs', xs)

{-@
ipartl_spec_steps_4_to_7_lemma3 ::
  (Equality (M (Natural, Natural)), Equality (M (Natural, Natural, Natural)), Eq (M ())) =>
  p:Int -> i:Natural -> ys'_zs'_xs:(List Int, List Int, List Int) ->
  EqualProp (M (Natural, Natural))
    {ipartl_spec_steps_4_to_7_lemma3_aux1 p i ys'_zs'_xs}
    {ipartl_spec_steps_4_to_7_lemma3_aux2 p i ys'_zs'_xs}
@-}
ipartl_spec_steps_4_to_7_lemma3 :: (Equality (M (Natural, Natural)), Equality (M (Natural, Natural, Natural)), Eq (M ())) => Int -> Natural -> (List Int, List Int, List Int) -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps_4_to_7_lemma3 p i (ys', zs', xs) = undefined

{- -- * in progress
  [eqpropchain|
      ipartl_spec_steps_4_to_7_lemma3_aux1 p i (ys', zs', xs)

    %==
      %-- step6
      writeList i (ys' ++ zs') >>
        writeList (i + length (ys' ++ zs')) xs >>
          ipartl p i (length ys', length zs', length xs)

      %by %reflexivity

    %==
      writeList i ys' >>
        writeList (add i (length ys')) zs' >>
          writeList (i + length (ys' ++ zs')) xs >>
            ipartl p i (length ys', length zs', length xs)

      %by undefined

    %==
      writeList i ys' >>
        writeList (add i (length ys')) zs' >>
          ipartl p i (length ys', length zs', length xs)

        %by undefined
        %-- TODO: not sure...

    %==
      writeList i ys' >>
        writeList (add i (length ys')) zs' >>
          ( pure (length ys', length zs', length xs) >>=
              ipartl p i
          )

        %by %rewrite ipartl p i (length ys', length zs', length xs)
                 %to pure (length ys', length zs', length xs) >>= ipartl p i
        %by %symmetry
        %by pure_bind (length ys', length zs', length xs) (ipartl p i)

    %==
      writeList i ys' >>
        writeList (add i (length ys')) zs' >>
          pure (length ys', length zs', length xs) >>=
            ipartl p i

        %by seq_pure_bind (writeList i ys' >> writeList (add i (length ys')) zs') (length ys', length zs', length xs) (ipartl p i)

    %==
      writeList i (ys' ++ zs') >>
        pure (length ys', length zs', length xs) >>=
          ipartl p i

        %by %rewrite writeList i ys' >> writeList (add i (length ys')) zs'
                 %to writeList i (ys' ++ zs')
        %by %symmetry
        %by writeList_append i ys' zs'

    %==
      writeListToLength3 i (ys', zs', xs) >>=
        ipartl p i

        %by %rewrite writeList i (ys' ++ zs') >> pure (length ys', length zs', length xs)
                 %to writeListToLength3 i (ys', zs', xs)
        %by %symmetry
        %by %reflexivity

    %==
      ( writeListToLength3 i >=>
        ipartl p i
      ) (ys', zs', xs)

        %by %symmetry
        %by %reflexivity

    %==
      ipartl_spec_steps_4_to_7_lemma3_aux1 p i (ys', zs', xs)

        %by %symmetry
        %by %reflexivity
  |]
-}

{-@ reflect ipartl_spec_steps_4_to_7_lemma2_aux2 @-}
ipartl_spec_steps_4_to_7_lemma2_aux2 :: Int -> Natural -> Int -> List Int -> List Int -> List Int -> M (Natural, Natural)
ipartl_spec_steps_4_to_7_lemma2_aux2 p i x xs ys zs =
  permute (zs ++ Cons x Nil)
    >>= dispatch_aux2 xs ys
    >>= ipartl_spec_step5_aux p i

{-@
ipartl_spec_steps_4_to_7_lemma2 ::
  (Equality (M (Natural, Natural)), Equality (M (List Int, List Int, List Int))) =>
    p:Int -> i:Natural -> x:Int -> xs:List Int -> ys:List Int -> zs:List Int ->
    EqualProp (M (Natural, Natural))
      {ipartl_spec_lemma1_aux2 p i x xs ys zs}
      {ipartl_spec_steps_4_to_7_lemma2_aux2 p i x xs ys zs}
@-}
ipartl_spec_steps_4_to_7_lemma2 :: (Equality (M (Natural, Natural)), Equality (M (List Int, List Int, List Int))) => Int -> Natural -> Int -> List Int -> List Int -> List Int -> EqualityProp (M (Natural, Natural))
ipartl_spec_steps_4_to_7_lemma2 p i x xs ys zs = undefined -- TODO

{- -- * correct
  [eqpropchain|
      ipartl_spec_lemma1_aux2 p i x xs ys zs

    %==
      permute (zs ++ Cons x Nil) >>=
        ipartl_spec_lemma1_aux2_aux i p ys xs

    %==
      permute (zs ++ Cons x Nil) >>= \zs' ->
        writeList i (ys ++ zs') >>
          ipartl p i (length ys, length zs', length xs)

        %by undefined
        %{- -- ! LH reject
        %by %rewrite ipartl_spec_lemma1_aux2_aux i p ys xs
                 %to \zs' -> writeList i (ys ++ zs') >> ipartl p i (length ys, length zs', length xs)
        %by %reflexivity
        -}%

    %==
      permute (zs ++ Cons x Nil) >>= \zs' ->
        ipartl_spec_step5_aux p i (ys, zs', xs)

        %by %rewrite \zs' -> writeList i (ys ++ zs') >> ipartl p i (length ys, length zs', length xs)
                 %to \zs' -> ipartl_spec_step5_aux p i (ys, zs', xs)
        %by %extend zs'
        %by %symmetry
        %by %reflexivity

    %==
      permute (zs ++ Cons x Nil) >>= \zs' ->
        (pure (ys, zs', xs) >>=
          ipartl_spec_step5_aux p i)

    %==
      permute (zs ++ Cons x Nil) >>= \zs' ->
        (dispatch_aux2 xs ys zs' >>=
          ipartl_spec_step5_aux p i)

        %by %rewrite \zs' -> (pure (ys, zs', xs) >>= ipartl_spec_step5_aux p i)
                 %to \zs' -> (dispatch_aux2 xs ys zs' >>= ipartl_spec_step5_aux p i)
        %by %extend zs'
        %by %rewrite pure (ys, zs', xs)
                 %to dispatch_aux2 xs ys zs'
        %by %symmetry
        %by %reflexivity

    %==
      permute (zs ++ Cons x Nil) >>= \zs' ->
        ( dispatch_aux2 xs ys >=>
          ipartl_spec_step5_aux p i)
        zs'

        %by %rewrite \zs' -> (dispatch_aux2 xs ys zs' >>= ipartl_spec_step5_aux p i)
                 %to \zs' -> (dispatch_aux2 xs ys >=> ipartl_spec_step5_aux p i) zs'
        %by %extend zs'
        %by %symmetry
        %by %reflexivity

    %==
      permute (zs ++ Cons x Nil) >>=
        ( dispatch_aux2 xs ys >=>
          ipartl_spec_step5_aux p i)

        %by %rewrite \zs' -> (dispatch_aux2 xs ys >=> ipartl_spec_step5_aux p i) zs'
                 %to (dispatch_aux2 xs ys >=> ipartl_spec_step5_aux p i)
        %by %extend zs'
        %by %reflexivity

    %==
      permute (zs ++ Cons x Nil) >>=
        dispatch_aux2 xs ys >>=
          ipartl_spec_step5_aux p i

        %by %symmetry
        %by bind_associativity (permute (zs ++ Cons x Nil)) (dispatch_aux2 xs ys) (ipartl_spec_step5_aux p i)

    %==
      ipartl_spec_steps_4_to_7_lemma2_aux2 p i x xs ys zs

        %by %symmetry
        %by %reflexivity
  |]
-}
