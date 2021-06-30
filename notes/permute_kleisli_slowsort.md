{-@ permute_kleisli_slowsort :: (Equality (M (List Int)), Equality (List Int ->
M (List Int))) => xs:List Int -> EqualProp (M (List Int)) {(permute >=>
slowsort) xs} {slowsort xs} @-} permute_kleisli_slowsort :: (Equality (M (List
Int)), Equality (List Int -> M (List Int))) => List Int -> EqualityProp (M (List
Int)) permute_kleisli_slowsort xs = [eqpropchain| (permute >=> slowsort) xs %==
(permute >=> (permute >=> guardBy sorted)) xs %by %rewrite slowsort %to permute
>=> guardBy sorted %by %extend ys %by %reflexivity %== ((permute >=> permute)
>=> (guardBy sorted)) xs %by kleisli_associativity permute permute sorted xs %==
(permute >=> guardBy sorted) xs %by %rewrite permute >=> permute %to permute %by
%extend ys %by permute_kleisli_permute ys %== slowsort xs |]
