module Propositions exposing (..)

import Main exposing (println)


-- ASSIGNMENT 9     (propositions pt1)
type Proposition
    = Or    Proposition Proposition
    | And   Proposition Proposition
    | Impl  Proposition Proposition
    | Bi    Proposition Proposition
    | Not   Proposition
    | Var   String

encapsulate : String -> String -> String -> String
encapsulate a b x = a ++ x ++ b
bracket = encapsulate "(" ")"

switcheroo: Proposition -> Proposition
switcheroo x =
    case x of
        Or a b ->   Or (switcheroo a) (switcheroo b)
        And a b ->  And (switcheroo a) (switcheroo b)
        Impl a b -> Or (Not (switcheroo a)) (switcheroo b)
        Bi a b ->   switcheroo (And
                (Impl
                    (switcheroo a)
                    (switcheroo b)
                )
                (Impl
                    (switcheroo b)
                    (switcheroo a)
                )
            )
        Not a -> Not (switcheroo a)
        Var a -> Var a

print : Proposition -> String
print x =
    case x of
        Or a b ->   bracket(print(a) ++ " or " ++   print(b))
        And a b ->  bracket(print(a) ++ " and " ++  print(b))
        Impl a b -> bracket(print(a) ++ " => " ++   print(b))
        Bi a b ->   bracket(print(a) ++ " <=> " ++  print(b))
        Not a ->    "not " ++ print(a)
        Var a ->    a


-- ASSIGNMENT 11    (propositions pt2)
members_rec : List String -> Proposition -> List String
members_rec lst x =
    case x of
        Or a b ->   members_rec (members_rec lst a) b
        And a b ->  members_rec (members_rec lst a) b
        Impl a b -> members_rec (members_rec lst a) b
        Bi a b ->   members_rec (members_rec lst a) b
        Not a ->    members_rec lst a
        Var a ->    if List.member a lst then lst else a :: lst
members : Proposition -> List String
members = members_rec []

demorgan: Proposition -> Proposition
demorgan x =
    case x of
        Not (And a b) ->    Or (Not (demorgan a)) (Not (demorgan b))
        Not (Or a b) ->     And (Not (demorgan a)) (Not (demorgan b))
        Or a b ->           Or (demorgan a) (demorgan b)
        And a b ->          And (demorgan a) (demorgan b)
        Impl a b ->         Impl (demorgan a) (demorgan b)
        Bi a b ->           Bi (demorgan a) (demorgan b)
        Not a ->            Not (demorgan a)
        Var a ->            Var a



-- VIEW
main = println [
        print (Not (And (Var "A") (Or (Impl (Var "B") (Var "C")) (Bi (Var "D") (Var "E"))))),
        print (switcheroo (Or (Impl (Var "B") (Not (Var "C"))) (Bi (Not (Var "D")) (Var "E")))),
        "[" ++ String.join ", " (members (Not (And (Var "A") (Or (Impl (Var "B") (Var "C")) (Bi (Var "D") (Var "E")))))) ++ "]",
        print (demorgan (Not (Or (Var "A") (Var "B"))))
    ]
