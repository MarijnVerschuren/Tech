module Main exposing (..)

import Html exposing (text)
import String


-- Use correct function names / types

-- HELPERS
string_from_bool : Bool -> String
string_from_bool x = if x then "True" else "False"
string_from_tuple_3i : (Int, Int, Int) -> String
string_from_tuple_3i (x, y, z) = "(" ++ String.fromInt(x) ++ ", " ++ String.fromInt(y) ++ ", " ++ String.fromInt(z) ++ ")"
string_from_multi_tuple_3i : List (Int, Int, Int) -> String
string_from_multi_tuple_3i x = "[" ++ String.join ", " (List.map (\t -> string_from_tuple_3i t) x) ++ "]"
string_from_tuple_1i1s : (Int, String) -> String
string_from_tuple_1i1s (i, s) = "(" ++ String.fromInt(i) ++ ", " ++ s ++ ")"
string_from_multi_tuple_1i1s : List (Int, String) -> String
string_from_multi_tuple_1i1s x = "[" ++ String.join ", " (List.map (\t -> string_from_tuple_1i1s t) x) ++ "]"

main = text "main"