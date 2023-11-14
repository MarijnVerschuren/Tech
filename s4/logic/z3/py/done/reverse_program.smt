; reverse program **

; find the values for 'a' and 'b' such that the value at the end is 'a = 1000' and 'b = 999'
; for i = 1; i <= 10; i++
;   if a > b then:
;       b *= 2
;       a -= 3
;   else:
;       a *= 2
;       b -= 5


(declare-fun a (Int) Int)
(declare-fun b (Int) Int)


(assert
	(and
		(= (a 1) (ite (> (a 0) (b 0)) (- (a 0) 3) (* (a 0) 2)))
		(= (b 1) (ite (> (a 0) (b 0)) (* (b 0) 2) (- (b 0) 5)))

		(= (a 2) (ite (> (a 1) (b 1)) (- (a 1) 3) (* (a 1) 2)))
		(= (b 2) (ite (> (a 1) (b 1)) (* (b 1) 2) (- (b 1) 5)))

		(= (a 3) (ite (> (a 2) (b 2)) (- (a 2) 3) (* (a 2) 2)))
		(= (b 3) (ite (> (a 2) (b 2)) (* (b 2) 2) (- (b 2) 5)))

		(= (a 4) (ite (> (a 3) (b 3)) (- (a 3) 3) (* (a 3) 2)))
		(= (b 4) (ite (> (a 3) (b 3)) (* (b 3) 2) (- (b 3) 5)))

		(= (a 5) (ite (> (a 4) (b 4)) (- (a 4) 3) (* (a 4) 2)))
		(= (b 5) (ite (> (a 4) (b 4)) (* (b 4) 2) (- (b 4) 5)))

		(= (a 6) (ite (> (a 5) (b 5)) (- (a 5) 3) (* (a 5) 2)))
		(= (b 6) (ite (> (a 5) (b 5)) (* (b 5) 2) (- (b 5) 5)))

		(= (a 7) (ite (> (a 6) (b 6)) (- (a 6) 3) (* (a 6) 2)))
		(= (b 7) (ite (> (a 6) (b 6)) (* (b 6) 2) (- (b 6) 5)))

		(= (a 8) (ite (> (a 7) (b 7)) (- (a 7) 3) (* (a 7) 2)))
		(= (b 8) (ite (> (a 7) (b 7)) (* (b 7) 2) (- (b 7) 5)))

		(= (a 9) (ite (> (a 8) (b 8)) (- (a 8) 3) (* (a 8) 2)))
		(= (b 9) (ite (> (a 8) (b 8)) (* (b 8) 2) (- (b 8) 5)))

		(= (a 10) (ite (> (a 9) (b 9)) (- (a 9) 3) (* (a 9) 2)))
		(= (b 10) (ite (> (a 9) (b 9)) (* (b 9) 2) (- (b 9) 5)))
	)
)

(assert
	(and
		(= (a 10) 1000)
		(= (b 10) 999)
	)
)

(check-sat)
(get-model)
(get-value ((a 0) (b 0)))