module Main exposing (..)

import Html exposing (Html, text)
import String


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

to_div x = Html.div [] x
println : List String -> Html msg
println x = to_div (List.map (\y -> to_div [Html.text y]) x)


foldl_rec : (a -> b -> b) -> b -> List a -> b
foldl_rec func acc lst =
    case lst of
        [] -> acc
        a :: rest -> foldl_rec func (func a acc) rest

foldr_rec : (a -> b -> b) -> b -> List a -> b
foldr_rec func acc lst =
    case lst of
        [] -> acc
        a :: rest -> func a (foldr_rec func acc rest)


m_int : Maybe Int -> Int
m_int = Maybe.withDefault 0


-- VIEW
main = text "main"