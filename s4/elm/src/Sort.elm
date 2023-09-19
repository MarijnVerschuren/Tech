module Sort exposing (..)

import Main exposing (println)


-- ASSIGNMENT 8     (sorting)
split : List comparable -> (List comparable, List comparable)
split lst = split_helper lst True [] []

split_helper : List comparable -> Bool -> List comparable -> List comparable -> (List comparable, List comparable)
split_helper lst add_a a b =
    case lst of
        [] -> (a, b)
        first :: rest -> if add_a
            then split_helper rest (not add_a) (first :: a) b
            else split_helper rest (not add_a) a (first :: b)

merge : List comparable -> List comparable -> List comparable
merge a b =
    case (a, b) of
        (_, []) -> a
        ([], _) -> b
        (fa :: ra, fb :: rb) -> if fa < fb
            then fa :: merge ra b
            else fb :: merge a rb

msort: List comparable -> List comparable
msort lst =
    case lst of
        [] -> []        -- empty list
        [_] -> lst      -- single element
        _ -> let (halfOne, halfTwo) = split lst in merge (msort halfOne) (msort halfTwo)


-- VIEW
list: List Int
list = [
        34,
        6,
        23,
        3,
        1
    ]
list_s: List Int
list_s = msort list

main = println [
       "[" ++ String.join ", " (List.map (\t -> String.fromInt t) list) ++ "]",
       "[" ++ String.join ", " (List.map (\t -> String.fromInt t) list_s) ++ "]"
   ]