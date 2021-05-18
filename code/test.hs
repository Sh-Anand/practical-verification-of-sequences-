module Project where

groupBy :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _ [] = []
groupBy f (x : xs) = (x : ys) : groupBy f zs
  where tu = span (f x) xs
        ys = fst tu
        zs = snd tu

