module Caesar exposing (main)

import Main exposing (println, string_from_multi_tuple_1i1s)
import Char exposing (isAlpha)


-- ASSIGNMENT 2     (caesar pt1)
encode : Int -> Char -> Char
encode offset char = if Char.isLower char
    then Char.fromCode((modBy 26 (Char.toCode char - Char.toCode 'a' + offset)) + Char.toCode 'a')  -- lower case
    else Char.fromCode((modBy 26 (Char.toCode char - Char.toCode 'A' + offset)) + Char.toCode 'A')  -- upper case

decode : Int -> Char -> Char
decode offset char = encode (offset * -1) char


-- ASSIGNMENT 4     (caesar pt2)
normalize : String -> String
normalize msg = String.filter isAlpha msg
encrypt : Int -> String -> String
encrypt offset msg = String.map (\c -> encode offset c)(normalize msg)
decrypt : Int -> String -> String
decrypt offset msg = String.map (\c -> decode offset c)(normalize msg)


-- ASSIGNMENT 6     (caesar pt3)
decrypt_check: List String -> Int -> String -> Bool
decrypt_check keywords offset msg =
    case keywords of
        [] -> False
        first :: rest ->
            if (String.contains (String.toUpper first) (String.toUpper (decrypt offset msg)))
            then True else decrypt_check rest offset msg
candidates: List String -> String -> List (Int, String)
candidates keywords msg = List.map (\i -> (i, decrypt i msg)) (List.filter (\i -> decrypt_check keywords i msg) (List.range 1 25))


-- VIEW
main = println [
       String.fromChar(encode 4 'Y'),
       String.fromChar(decode 4 'c'),
       (encrypt 7 "hey hello hi"),
       (decrypt 7 "OlssvDvysk"),
       string_from_multi_tuple_1i1s(candidates ["Hey", "Hello", "H"] "OlfOlssvOp")
   ]