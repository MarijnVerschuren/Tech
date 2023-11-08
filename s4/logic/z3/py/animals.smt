; animals **

; rules:
;   you must spend exactly 400 euro whilst buying exactly 100 animals
;   you must buy at least one of each!
;   a dog costs:    60 euro
;   a cat costs:    4 euro ?
;   a mouse costs:  1 euro

(declare-const dogs Int)
(declare-const cats Int)
(declare-const mice Int)


; make sure that the sum of the price for all dogs, cats and mouses is exactly 400
(assert
	(=
		(+
			(* dogs 60)
			(* cats 4)
			(* mice 1)
		)
		400
	)
)
; make sure that there are exactly 100 animals
(assert
	(=
		(+
			dogs
			cats
			mice
		)
		100
	)
)
; make sure that there are at least one of each
(assert
	(and
		(> dogs 0)
		(> cats 0)
		(> mice 0)
	)
)

(check-sat)
(get-value (dogs))
(get-value (cats))
(get-value (mice))