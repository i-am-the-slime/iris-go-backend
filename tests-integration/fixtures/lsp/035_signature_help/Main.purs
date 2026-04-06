module Main where

data Maybe a = Just a | Nothing

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe _ (Just a) = a
fromMaybe a Nothing = a

map :: forall a b. (a -> b) -> Array a -> Array b
map _ _ = []

life :: Int
life = 42

-- cursor on first arg
check :: Int
check = fromMaybe life Nothing
--               &

-- cursor on second arg
check2 :: Int
check2 = fromMaybe life Nothing
--                      &

-- cursor on function name in application
check3 :: Int
check3 = fromMaybe life Nothing
--        &

-- cursor on first arg of map
check4 :: Array Int
check4 = map life []
--           &

-- standalone function, cursor on name
check5 = fromMaybe
--            &

-- cursor on space after first arg
check6 :: Int
check6 = fromMaybe life Nothing
--                       &

-- cursor between function and first arg
check7 :: Int
check7 = fromMaybe life Nothing
--                &

-- cursor after space past standalone function (real typing scenario)
check8 = fromMaybe
--                 &

-- cursor after space in operator chain (VS Code real case)
check9 = Just 12 # fromMaybe
--                          &

-- trailing space after fromMaybe (exactly what VS Code sends)
check10 = fromMaybe
--                  &

-- last line with no newline, cursor past fromMaybe
check11 = fromMaybe
--               &
