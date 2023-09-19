module Propositions exposing (..)

import Main exposing (println)


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


main = println [
        print (Not (And (Var "A") (Or (Impl (Var "B") (Var "C")) (Bi (Var "D") (Var "E"))))),
        print (switcheroo (Or (Impl (Var "B") (Not (Var "C"))) (Bi (Not (Var "D")) (Var "E"))))
    ]
