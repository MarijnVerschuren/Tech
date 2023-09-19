module Pythagoras exposing (main)

import Main exposing (..)
import Html exposing (text)


-- ASSIGNMENT 3    (pythagoras pt1)
isTripleTuple : (Int, Int, Int) -> Bool
isTripleTuple (x, y, z) = x > 0 && y > 0 && z > 0 && (x ^ 2 + y ^ 2 == z ^ 2)

leg1 : Int -> Int -> Int
leg1 x y = x ^ 2 - y ^ 2
leg2 : Int -> Int -> Int
leg2 x y = 2 * x * y
hyp : Int -> Int -> Int
hyp x y = x ^ 2 + y ^ 2

pythTriple : (Int, Int) -> (Int, Int, Int)
pythTriple (x, y) = (leg1 x y, leg2 x y, hyp x y)


-- ASSIGNMENT 5     (pythagoras pt2)
pythTriplesMap : List (Int, Int) -> List (Int, Int, Int)
pythTriplesMap list = List.map (\t -> pythTriple t) list
pythTriplesRec : List (Int, Int) -> List (Int, Int, Int)
pythTriplesRec list =
    case list of
        [] -> []
        first :: rest -> [pythTriple first] ++ pythTriplesRec rest
arePythTriplesFilter : List (Int, Int, Int) -> List (Int, Int, Int)
arePythTriplesFilter list = List.filter isTripleTuple list
arePythTriplesRec : List (Int, Int, Int) -> List (Int, Int, Int)
arePythTriplesRec list =
    case list of
        [] -> []
        first :: rest -> (if (isTripleTuple first) then [first] else []) ++ arePythTriplesRec rest



-- DISPLAY
main = text (String.join ",\n" [
       string_from_bool(isTripleTuple(pythTriple(8, 6))),
       string_from_multi_tuple_3i(pythTriplesMap [(5,4), (2,1), (35,7)]),
       string_from_multi_tuple_3i(pythTriplesRec [(5,4), (2,1), (35,7)]),
       string_from_multi_tuple_3i(arePythTriplesFilter [(9, 40, 41), (3, 4, 6), (1176, 490, 1274)]),
       string_from_multi_tuple_3i(arePythTriplesRec [(9, 40, 41), (3, 4, 5), (1176, 491, 1274)])
   ])