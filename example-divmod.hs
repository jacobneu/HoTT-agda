import Control.Arrow

infix /%
(/%) :: Int -> Int -> (Int,Int)
n /% d = 
    if n < d
    then (0,n)
    else incFst ((n-d)/%d) where
        incFst :: (Int,Int) -> (Int,Int)
        incFst (q,r) = (q+1,r)
