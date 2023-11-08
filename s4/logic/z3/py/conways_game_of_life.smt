; conways game of life ***

; define a 6x6 grid as an array of arrays
(declare-const grid0 (Array Int (Array Int Bool)))
(declare-const grid1 (Array Int (Array Int Bool)))
(declare-const grid2 (Array Int (Array Int Bool)))
(declare-const grid3 (Array Int (Array Int Bool)))
(declare-const grid4 (Array Int (Array Int Bool)))


; function to count live neighbors
(define-fun count-live-neighbors ((grid (Array Int (Array Int Bool))) (x Int) (y Int)) Int
	(let
		(
			(xm1 (if (> x 0) (- x 1) 5))
			(xp1 (if (< x 5) (+ x 1) 0))
			(ym1 (if (> y 0) (- y 1) 5))
			(yp1 (if (< y 5) (+ y 1) 0))
		)
		(+
			(if (select (select grid xm1) ym1) 1 0)
			(if (select (select grid x) ym1) 1 0)
			(if (select (select grid xp1) ym1) 1 0)
			(if (select (select grid xm1) y) 1 0)
			(if (select (select grid xp1) y) 1 0)
			(if (select (select grid xm1) yp1) 1 0)
			(if (select (select grid x) yp1) 1 0)
			(if (select (select grid xp1) yp1) 1 0)
		)
	)
)
; function to calculate the next state of a cell
(define-fun next-state ((grid (Array Int (Array Int Bool))) (x Int) (y Int)) Bool
	(let
		(
			(alive
				(select (select grid x) y)
			)
		)
		(let
			(
				(neighbors (count-live-neighbors grid x y))
			)
			(or
				(and
					alive
					(or
						(= neighbors 2)
						(= neighbors 3)
					)
				)
				(and
					(not alive)
					(= neighbors 3)
				)
			)
		)
	)
)


; The rest of your function definitions remain the same

; Transition rules for each cell for each generation
(assert
	(forall ((x Int) (y Int))
		(=>
			(and (>= x 0) (< x 6) (>= y 0) (< y 6))
			(=
				(select (select grid1 x) y)
				(next-state grid0 x y)
			)
		)
	)
)
(assert
	(forall ((x Int) (y Int))
		(=>
			(and (>= x 0) (< x 6) (>= y 0) (< y 6))
			(=
				(select (select grid2 x) y)
				(next-state grid1 x y)
			)
		)
	)
)



; Oscillation check for period 2
(assert
	(forall ((x Int) (y Int))
		(=>
			(and (>= x 0) (< x 6) (>= y 0) (< y 6))
			(=
				(select (select grid0 x) y)
				(select (select grid2 x) y)
			)
		)
	)
)
;; Oscillation check for period 4
;(assert
;	(forall ((x Int) (y Int))
;		(=>
;			(and (>= x 0) (< x 6) (>= y 0) (< y 6))
;			(=
;				(select (select grid0 x) y)
;				(select (select grid4 x) y)
;			)
;		)
;	)
;)


; check for a solution and print it
(check-sat)
(get-model)

(get-value (select (select grid0 0) 0))
(get-value (select (select grid0 1) 0))
(get-value (select (select grid0 2) 0))
(get-value (select (select grid0 3) 0))
(get-value (select (select grid0 4) 0))
(get-value (select (select grid0 5) 0))

(get-value (select (select grid0 0) 1))
(get-value (select (select grid0 1) 1))
(get-value (select (select grid0 2) 1))
(get-value (select (select grid0 3) 1))
(get-value (select (select grid0 4) 1))
(get-value (select (select grid0 5) 1))

(get-value (select (select grid0 0) 2))
(get-value (select (select grid0 1) 2))
(get-value (select (select grid0 2) 2))
(get-value (select (select grid0 3) 2))
(get-value (select (select grid0 4) 2))
(get-value (select (select grid0 5) 2))

(get-value (select (select grid0 0) 3))
(get-value (select (select grid0 1) 3))
(get-value (select (select grid0 2) 3))
(get-value (select (select grid0 3) 3))
(get-value (select (select grid0 4) 3))
(get-value (select (select grid0 5) 3))

(get-value (select (select grid0 0) 4))
(get-value (select (select grid0 1) 4))
(get-value (select (select grid0 2) 4))
(get-value (select (select grid0 3) 4))
(get-value (select (select grid0 4) 4))
(get-value (select (select grid0 5) 4))

(get-value (select (select grid0 0) 5))
(get-value (select (select grid0 1) 5))
(get-value (select (select grid0 2) 5))
(get-value (select (select grid0 3) 5))
(get-value (select (select grid0 4) 5))
(get-value (select (select grid0 5) 5))