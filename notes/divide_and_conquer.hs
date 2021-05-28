pure (partition x' (x : xs)) 
  <+> (split (x : xs) >>= guardBy (\(ys', zs') -> all (<= x') ys' && all (x' <=) zs'))

% def partition

pure (if x <= x' then (x : ys, zs) else (ys, x : zs)) 
  <+> (split (x : xs) >>= guardBy (\(ys', zs') -> all (<= x') ys' && all (x' <=) zs'))

%def split

pure (if x <= x' then (x : ys, zs) else (ys, x : zs)) 
  <+> ((split xs >>= \(ys, zs) -> pure (x : ys, zs) <+> pure (ys, x : zs)) 
        >>= guardBy (\(ys', zs') -> all (<= x') ys' && all (x' <=) zs'))



...

split (x : xs) >>= guardBy (\(ys', zs') -> all (<= x') ys' && all (x' <=) zs')