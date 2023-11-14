; Tweedledum and Tweedledee ***

; Tweedledum lies on:
; * monday
; * tuesday
; * wednesday
;
; Tweedledee lies on:
; * thursday
; * friday
; * saturday


(declare-const dum Int)
(declare-const dee Int)
(assert (distinct dum dee))

(define-const monday Int 0)
(define-const tuesday Int 1)
(define-const wednesday Int 2)
(define-const thursday Int 3)
(define-const friday Int 4)
(define-const saturday Int 5)
(define-const sunday Int 6)

(declare-fun lies (Int Int) Bool)

(assert (and
	(= (lies dum monday) true)
	(= (lies dum tuesday) true)
	(= (lies dum wednesday) true)
	(= (lies dum thursday) false)
	(= (lies dum friday) false)
	(= (lies dum saturday) false)
	(= (lies dum sunday) false)

	(= (lies dee monday) false)
	(= (lies dee tuesday) false)
	(= (lies dee wednesday) false)
	(= (lies dee thursday) true)
	(= (lies dee friday) true)
	(= (lies dee saturday) true)
	(= (lies dee sunday) false)
))


; A: I will lie tomorrow
; B: I lied yesterday, and i will lie tomorrow
(declare-const QA1 Bool)
(declare-const QB1 Bool)
(assert (and
	(= QA1
		(or
			(and (not (lies dum monday)) (lies dum tuesday))
			(and (not (lies dee monday)) (lies dee tuesday))

			(and (not (lies dum tuesday)) (lies dum wednesday))
			(and (not (lies dee tuesday)) (lies dee wednesday))

			(and (not (lies dum wednesday)) (lies dum thursday))
			(and (not (lies dee wednesday)) (lies dee thursday))

			(and (not (lies dum thursday)) (lies dum friday))
			(and (not (lies dee thursday)) (lies dee friday))

			(and (not (lies dum friday)) (lies dum saturday))
			(and (not (lies dee friday)) (lies dee saturday))

			(and (not (lies dum saturday)) (lies dum sunday))
			(and (not (lies dee saturday)) (lies dee sunday))
		)
	)
	(= QB1
		(or
			(and
				(lies dum monday)
				(not (lies dum tuesday))
				(lies dum wednesday)
			)
			(and
				(lies dee monday)
				(not (lies dee tuesday))
				(lies dee wednesday)
			)

			(and
				(lies dum tuesday)
				(not (lies dum wednesday))
				(lies dum thursday)
			)
			(and
				(lies dee tuesday)
				(not (lies dee wednesday))
				(lies dee thursday)
			)

			(and
				(lies dum wednesday)
				(not (lies dum thursday))
				(lies dum friday)
			)
			(and
				(lies dee wednesday)
				(not (lies dee thursday))
				(lies dee friday)
			)

			(and
				(lies dum thursday)
				(not (lies dum friday))
				(lies dum saturday)
			)
			(and
				(lies dee thursday)
				(not (lies dee friday))
				(lies dee saturday)
			)

			(and
				(lies dum friday)
				(not (lies dum saturday))
				(lies dum sunday)
			)
			(and
				(lies dee friday)
				(not (lies dee saturday))
				(lies dee sunday)
			)
		)
	)
))
; TODO: day? who is A and B




(check-sat)
(get-model)
(echo "A: I will lie tomorrow")
(echo "B: I lied yesterday, and i will lie tomorrow")
(get-value (QA1 QB1))