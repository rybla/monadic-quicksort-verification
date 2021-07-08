    %== split xs >>= apply (\(ys, zs) ->
          liftM2 (permute_aux2 x) (permute ys) (permute zs) >>=
          apply (\xs -> pure (length xs))
        )
      %by undefined
      %-- TODO: permute_preserves_length_lemma1

    %== split xs >>= apply (\(ys, zs) ->
          apply (\(ys, zs) -> liftM2 (permute_aux2 x) (permute ys) (permute zs)) (ys, zs) >>=
          apply (\xs -> pure (length xs))
        )
      %by undefined
      %-- TODO: subst_cont; extend

    %== split xs >>= apply (\(ys, zs) ->
        ( apply (\(ys, zs) -> liftM2 (permute_aux2 x) (permute ys) (permute zs)) >=>
          apply (\xs -> pure (length xs))
        ) (ys, zs))
      %by undefined
      %-- TODO: subst_cont; extend

    %== split xs >>=
        ( apply (\(ys, zs) -> liftM2 (permute_aux2 x) (permute ys) (permute zs)) >=>
          apply (\xs -> pure (length xs))
        )
      %by undefined

    %== split xs >>=
        apply (\(ys, zs) -> liftM2 (permute_aux2 x) (permute ys) (permute zs)) >>=
        apply (\xs -> pure (length xs))
      %by undefined
      %-- TODO: bind_associativity

    %== split xs >>= permute_aux1 x >>= apply (\xs -> pure (length xs))
      %by %rewrite split xs >>= (apply (\(ys, zs) -> liftM2 (apply (\ys' zs' -> ys' ++ Cons x Nil ++ zs')) (permute ys) (permute zs)))
                   %to split xs >>= permute_aux1 x
      %by %symmetry
      %by %reflexivity
