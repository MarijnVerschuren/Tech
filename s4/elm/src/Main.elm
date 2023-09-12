module Main exposing (main)
import Html exposing (text)
import Char exposing (isAlpha)
import String exposing (filter)

-- HELPERS
string_from_bool : Bool -> String
string_from_bool x = if x then "True" else "False"
string_from_tuple_3i : (Int, Int, Int) -> String
string_from_tuple_3i (x, y, z) = "(" ++ String.fromInt(x) ++ ", " ++ String.fromInt(y) ++ ", " ++ String.fromInt(z) ++ ")"
string_from_multi_tuple_3i : List (Int, Int, Int) -> String
string_from_multi_tuple_3i x = "[" ++ String.join ", " (List.map (\t -> string_from_tuple_3i t) x) ++ "]"


-- ASSIGNMENT 2
encode : Int -> Char -> Char
encode offset char = if Char.toCode(char) >= 97
    then Char.fromCode((modBy 26 ((Char.toCode(char) - 97) + offset)) + 97)  -- lower case
    else Char.fromCode((modBy 26 ((Char.toCode(char) - 65) + offset)) + 65)  -- upper case

decode : Int -> Char -> Char
decode offset char = if Char.toCode(char) >= 97
    then Char.fromCode((modBy 26 ((Char.toCode(char) - 71) - offset)) + 97)  -- lower case
    else Char.fromCode((modBy 26 ((Char.toCode(char) - 39) - offset)) + 65)  -- upper case


-- ASSIGNMENT 3
is_triple : (Int, Int, Int) -> Bool
is_triple (x, y, z) = x > 0 && y > 0 && z > 0 && (x ^ 2 + y ^ 2 == z ^ 2)

side_a : Int -> Int -> Int
side_a x y = x ^ 2 - y ^ 2
side_b : Int -> Int -> Int
side_b x y = 2 * x * y
side_c : Int -> Int -> Int
side_c x y = x ^ 2 + y ^ 2

gen_triple : (Int, Int) -> (Int, Int, Int)
gen_triple (x, y) = (side_a x y, side_b x y, side_c x y)


-- ASSIGNMENT 4
normalize : String -> String
normalize msg = filter isAlpha msg
encrypt : Int -> String -> String
encrypt offset msg = String.map (\c -> encode offset c)(normalize msg)
decrypt : Int -> String -> String
decrypt offset msg = String.map (\c -> decode offset c)(normalize msg)


-- ASSIGNMENT 5
gen_triple_map : List (Int, Int) -> List (Int, Int, Int)
gen_triple_map list = List.map (\t -> gen_triple t) list
gen_triple_rec : List (Int, Int) -> List (Int, Int, Int)
gen_triple_rec list =
    case list of
        [] -> []
        first :: rest -> [gen_triple first] ++ gen_triple_rec rest
is_triple_fil : List (Int, Int, Int) -> List (Int, Int, Int)
is_triple_fil list = List.filter is_triple list
is_triple_rec : List (Int, Int, Int) -> List (Int, Int, Int)
is_triple_rec list =
    case list of
        [] -> []
        first :: rest -> (if (is_triple first) then [first] else []) ++ is_triple_rec rest


-- DISPLAY
print : List String
print = [
    String.fromChar(encode 4 'Y'),
    String.fromChar(decode 4 'c'),
    string_from_bool(is_triple(gen_triple(8, 6))),
    (encrypt 7 "Hello World"),
    (decrypt 7 "OlssvDvysk"),
    string_from_multi_tuple_3i(gen_triple_map [(5,4), (2,1), (35,7)]),
    string_from_multi_tuple_3i(gen_triple_rec [(5,4), (2,1), (35,7)]),
    string_from_multi_tuple_3i(is_triple_fil [(9, 40, 41), (3, 4, 6), (1176, 490, 1274)]),
    string_from_multi_tuple_3i(is_triple_rec [(9, 40, 41), (3, 4, 5), (1176, 491, 1274)])]
main = text (String.join ",\n" print)