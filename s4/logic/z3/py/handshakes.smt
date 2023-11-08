; handshaking ***
; a set of 5 couples (10 people) have shook x amount of hands
; each person has shook a different amount of hands
; find out how many handshakes a given person has given and how many solutions there are


(declare-const Handshakes (Array Int Int))

; make sure that all answer are different and that everyone's hand has been shaken
(assert
	(forall ((i Int))
		(=>
			(and
				(>= i 0)
				(<= i 4)
			)
			(=
				(+
					(select Handshakes i)
					(select Handshakes (- 9 i))
				)
				8
			)
		)
	)
)
; filter for all answers in range: [0, 8] because 10 people - 1 themselves -1 their husband or wife
(assert
	(forall ((i Int))
		(=>
			(and
				(>= i 0)
				(<= i 9)
			)
			(and
				(<= (select Handshakes i) 8)
				(>= (select Handshakes i) 0)
			)
		)
	)
)

; check answer 1
(push)
(check-sat)
(echo "Handshakes:")
(eval (select Handshakes 9))
(pop)

; add rule to exclude answer 1
(assert (not (= (select Handshakes 9) 4 ) ) )
(push)
; check answer 2
(check-sat)  ; if sat another solution is found
(eval (select Handshakes 9))
(pop)

; add rule to exclude answer 2
(assert (not (= (select Handshakes 9) 1 ) ) )
(push)
; check answer 3
(check-sat)  ; if sat another solution is found
(eval (select Handshakes 9))
(pop)

; add rule to exclude answer 3
(assert (not (= (select Handshakes 9) 0 ) ) )
(push)
; check answer 4
(check-sat)  ; if sat another solution is found
(eval (select Handshakes 9))
(pop)

; add rule to exclude answer 4
(assert (not (= (select Handshakes 9) 3 ) ) )
(push)
; check answer 5
(check-sat)  ; if sat another solution is found
(eval (select Handshakes 9))
(pop)

; add rule to exclude answer 5
(assert (not (= (select Handshakes 9) 2 ) ) )
(push)
; check answer 6
(check-sat)  ; if sat another solution is found
(eval (select Handshakes 9))
(pop)

; add rule to exclude answer 6
(assert (not (= (select Handshakes 9) 8 ) ) )
(push)
; check answer 7
(check-sat)  ; if sat another solution is found
(eval (select Handshakes 9))
(pop)

; add rule to exclude answer 7
(assert (not (= (select Handshakes 9) 5 ) ) )
(push)
; check answer 8
(check-sat)  ; if sat another solution is found
(eval (select Handshakes 9))
(pop)

; add rule to exclude answer 8
(assert (not (= (select Handshakes 9) 6 ) ) )
(push)
; check answer 9
(check-sat)  ; if sat another solution is found
(eval (select Handshakes 9))
(pop)

; add rule to exclude answer 9
(assert (not (= (select Handshakes 9) 7 ) ) )
(push)
; check answer 10
(check-sat)  ; if sat another solution is found
(eval (select Handshakes 9))
(pop)