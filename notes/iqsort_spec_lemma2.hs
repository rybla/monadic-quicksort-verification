iqsort_spec_lemma2

--

seq (writeList i (concat (Cons p Nil) ys)) (swap i (add i (length ys)))

-- infix
writeList i (Cons p Nil ++ ys)
  >> swap i (i + length ys)

--
permute ys >>= \ys' ->
  writeList i (ys' ++ Cons p Nil)

--
permute ys
  >>= iqsort_spec_lemma2_aux2 p i

-- defn iqsort_spec_lemma2_aux1
iqsort_spec_lemma2_aux1 p i ys
