-- https://en.wikipedia.org/wiki/Continuation-passing_style

-- Direct-style definition

pow2 :: Float -> Float
pow2 x = x ** 2

add :: Float -> Float -> Float
add x y = x + y

pyth :: Float -> Float -> Float
pyth x y = sqrt (add (pow2 x) (pow2 y))

-- CPS definition

pow2' :: Float -> (Float -> a) -> a
pow2' x cont = cont (x ** 2)

add' :: Float -> Float -> (Float -> a) -> a
add' x y cont = cont (x + y)

sqrt' :: Float -> (Float -> a) -> a
sqrt' x = \cont -> cont (sqrt x)

pyth' :: Float -> Float -> (Float -> a) -> a
pyth' x y cont = pow2' x (\x2 -> pow2' y (\y2 -> add' x2 y2 (\anb -> sqrt' anb cont)))

-- (f' x) cont = cont (f x)

-- sDS :: Stm -> State -> State
-- SCS :: Stm -> State -> (State -> a) -> a
-- SCS :: Stm -> State -> (State -> State) -> State
-- SCS :: Stm -> (State -> State) -> State -> State
-- Cont = State -> State
-- SCS :: Stm -> Cont -> Cont
