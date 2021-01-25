-- slowsort_VCons_expansion_correct
slowsort_ (VCons p xs)
=
split_ xs >>= slowsort_VCons_expansion_aux1_ p
-- proof
slowsort_ (VCons p xs)
=== -- [def] slowsort
(permute_ >=> guardBy_ isSorted_) (VCons p xs)
=== -- [def] >=>
permute_ (VCons p xs) >>= guardBy_ isSorted_
=== -- [def] permute on VCons
(split_ xs >>= permute_aux1_ p) >>= guardBy_ isSorted_
=== -- [lem] vbind_associative
split_ xs >>= (permute_aux1_ p >=> guardBy_ isSorted_)
=== -- [def] tmp_aux1
split_ xs >>= tmp_aux1_ p
=== -- [lem] tmp_lem1
split_ xs >>= slowsort_VCons_expansion_aux1_ p

--------------------------------------------------------------------------------

-- tmp_aux1
tmp_aux1 p = permute_aux1_ p >=> guardBy_ isSorted_

-- tmp_lem1
tmp_aux1_ p
=
slowsort_VCons_expansion_aux1_ p
-- proof
tmp_aux1 p (ys, zs)
=== -- [def] tmp_aux1
(permute_aux1_ p >=> guardBy_ isSorted_) (ys, zs)
=== -- [def] >=>
permute_aux1_ p (ys, zs) >>= guardBy isSorted_ 
=== -- [def] permute_aux1
vmapM2_ (permute_aux2 p) (permute_ ys) (permute_ zs) >>= guardBy isSorted_
=== -- [def] vmapM2, tmp_aux2
(permute_ ys >>= tmp_aux2_ p zs) >>= guardBy isSorted_
===
(permute_ ys >>= tmp_aux2_ p zs) >>= guardBy isSorted_
...
===
(guard_ (isSortedBetween_ p ys zs))
  >> ( (permute_ ys >>= guardBy_ isSorted_)
          >>= slowsort_VCons_expansion_aux2_ p zs
      )
=== -- [def] slowsort_VCons_expansion_aux1
slowsort_VCons_expansion_aux1_ p (ys, zs)

--------------------------------------------------------------------------------

-- tmp_aux2
tmp_aux2 x zs ys' = permute_ zs >>= tmp_aux3_ x


-- TODO
tmp_aux2 x zs ys'
===
permute_ zs >>= tmp_aux3_ x ys' 
===
  ...

--------------------------------------------------------------------------------

tmp_aux3 x ys' zs' = vlift_ (permute_aux2 x ys' zs')

