module High_Order exposing (..)

import Main exposing (println, m_int)


-- ASSIGNMENT 10    (higher order functions)
repeatUntil : (a -> Bool) -> (a -> a) -> a -> a
repeatUntil con func x = if con x then x else repeatUntil con func (func x)

collatz : List Int -> List Int
collatz x =
    case x of
        [] -> []
        y :: _ -> (if (modBy 2 y) > 0 then 3 * y + 1 else y // 2) :: x


-- VIEW
main = println [
        String.fromInt(repeatUntil (\x -> x > 100) ((*) 2) 7),
        String.fromInt(repeatUntil (\x -> x > 100) ((+) 1) 42),
        String.fromInt(repeatUntil (\x -> 3 ^ x > 100) ((+) 1) 0),
        "[" ++ String.join ", " (
            List.map String.fromInt (repeatUntil (\x -> m_int (List.head x) == 1) collatz [19])
        ) ++ "]"
    ]