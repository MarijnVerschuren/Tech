; counterfeit coins *****

; we have 12 coins with one counterfeit among them
; we can find the counterfeit by looking at its weight
; we are only allowed 3 weight comparisons
; i will assume that i can weigh all groups within a step since i need to find out whether the counterfeit is heavier or lighter


; method:
; * step-1: split the 12 coins in three groups of 4: A, B, C
;           if A != norm then:      A
;           elif B != norm then:    B
;           else:                   C
; * step-2: split the set of 4 containing the counterfeit into groups of 2: xL, xH
;           if xL == norm then:     xH
;           else                    xL
; * step-3: split the set of 2 containing the counterfeit into 2 elements: X, Y
;           if X != norm then:      X is counterfeit
;           else:                   Y is counterfeit

; constants
(declare-const c1 Int)
(declare-const c2 Int)
(declare-const c3 Int)
(declare-const c4 Int)
(declare-const c5 Int)
(declare-const c6 Int)
(declare-const c7 Int)
(declare-const c8 Int)
(declare-const c9 Int)
(declare-const c10 Int)
(declare-const c11 Int)
(declare-const c12 Int)

(declare-const AL Int)      ; c1, c2
(declare-const BL Int)      ; c5, c6
(declare-const CL Int)      ; c9, c10

(declare-const A Int)       ; c1 - c4
(declare-const B Int)       ; c5 - c8
(declare-const C Int)       ; c9 - c12


; define the possible weights for the coins (normal, heavy, light)
(define-fun normal () Int 0)
(define-fun heavy () Int 1)
(define-fun light () Int -1)

; set counterfeit coin
(assert
	(and
		(= c1 normal)
		(= c2 normal)
		(= c3 normal)
		(= c4 normal)
		(= c5 normal)
		(= c6 normal)
		(= c7 normal)
		(= c8 normal)
		(= c9 light)
		(= c10 normal)
		(= c11 normal)
		(= c12 normal)
	)
)

(assert
	(and
		(= AL (+ c1 c2))
		(= BL (+ c5 c6))
		(= CL (+ c9 c10))
	)
)

(assert
	(and
		(= A (+ AL c3 c4))
		(= B (+ BL c7 c8))
		(= C (+ CL c11 c12))
	)
)


(check-sat)

; weighing rounds
(eval
	; weighing round 1
	(ite (= A normal)
	(ite (= B normal)
	(ite (= C normal)  ; checking C is not needed but is added to filter out situations where all coins are normal
	; C - weighing round 2
		"all normal"
		(ite (= CL normal)
			; CH - weighing round 3
			(ite (= c11 normal)
				"C12 is counterfeit"
				"C11 is counterfeit"
			)
			; CL - weighing round 3
			(ite (= c9 normal)
				"C10 is counterfeit"
				"C9 is counterfeit"
			)
		)
	)
	; B - weighing round 2
		(ite (= BL normal)
			; BH - weighing round 3
			(ite (= c7 normal)
				"C8 is counterfeit"
				"C7 is counterfeit"
			)
			; BL - weighing round 3
			(ite (= c5 normal)
				"C6 is counterfeit"
				"C5 is counterfeit"
			)
		)
	)
	; A - weighing round 2
		(ite (= AL normal)
			; AH - weighing round 3
			(ite (= c3 normal)
				"C4 is counterfeit"
				"C3 is counterfeit"
			)
			; AL - weighing round 3
			(ite (= c1 normal)
				"C2 is counterfeit"
				"C1 is counterfeit"
			)
		)
	)
)

(eval
(ite (< (+ A B C) normal)
	"Too light"
	"Too heavy"
)
)