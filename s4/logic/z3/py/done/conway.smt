; conways game of life ***

(set-option :random-seed 345166437)

(declare-const SIZE Int)
(declare-const GEN Int)


; grid function: (x, y, gen) -> alive
(declare-fun grid (Int Int Int) Bool)
(define-fun neighbors ((x Int) (y Int) (g Int)) Int
	(+
		(grid (- x 1) (- y 1) g)
		(grid (- x 1) y g)
		(grid (- x 1) (+ y 1) g)
		(grid x (- y 1) g)
		(grid x (+ y 1) g)
		(grid (+ x 1) (- y 1) g)
		(grid (+ x 1) y g)
		(grid (+ x 1) (+ y 1) g)
    )
)
(define-fun next ((x Int) (y Int) (g Int)) Bool
	(ite
		(or
			(and
				(grid x y g)
				(= (neighbors x y g) 2)
			)
			(= (neighbors x y g) 3)
		)
		true
		false
	)
)


(assert
	(and
		(= SIZE 6)
		(= GEN 10)
	)
)


(assert
	(and
		(= (grid 0 0 1) (next 0 0 0)) (= (grid 1 0 1) (next 1 0 0)) (= (grid 2 0 1) (next 2 0 0)) (= (grid 3 0 1) (next 3 0 0)) (= (grid 4 0 1) (next 4 0 0)) (= (grid 5 0 1) (next 5 0 0))
		(= (grid 0 1 1) (next 0 1 0)) (= (grid 1 1 1) (next 1 1 0)) (= (grid 2 1 1) (next 2 1 0)) (= (grid 3 1 1) (next 3 1 0)) (= (grid 4 1 1) (next 4 1 0)) (= (grid 5 1 1) (next 5 1 0))
		(= (grid 0 2 1) (next 0 2 0)) (= (grid 1 2 1) (next 1 2 0)) (= (grid 2 2 1) (next 2 2 0)) (= (grid 3 2 1) (next 3 2 0)) (= (grid 4 2 1) (next 4 2 0)) (= (grid 5 2 1) (next 5 2 0))
		(= (grid 0 3 1) (next 0 3 0)) (= (grid 1 3 1) (next 1 3 0)) (= (grid 2 3 1) (next 2 3 0)) (= (grid 3 3 1) (next 3 3 0)) (= (grid 4 3 1) (next 4 3 0)) (= (grid 5 3 1) (next 5 3 0))
		(= (grid 0 4 1) (next 0 4 0)) (= (grid 1 4 1) (next 1 4 0)) (= (grid 2 4 1) (next 2 4 0)) (= (grid 3 4 1) (next 3 4 0)) (= (grid 4 4 1) (next 4 4 0)) (= (grid 5 4 1) (next 5 4 0))
		(= (grid 0 5 1) (next 0 5 0)) (= (grid 1 5 1) (next 1 5 0)) (= (grid 2 5 1) (next 2 5 0)) (= (grid 3 5 1) (next 3 5 0)) (= (grid 4 5 1) (next 4 5 0)) (= (grid 5 5 1) (next 5 5 0))

		(= (grid 0 0 2) (next 0 0 1)) (= (grid 1 0 2) (next 1 0 1)) (= (grid 2 0 2) (next 2 0 1)) (= (grid 3 0 2) (next 3 0 1)) (= (grid 4 0 2) (next 4 0 1)) (= (grid 5 0 2) (next 5 0 1))
		(= (grid 0 1 2) (next 0 1 1)) (= (grid 1 1 2) (next 1 1 1)) (= (grid 2 1 2) (next 2 1 1)) (= (grid 3 1 2) (next 3 1 1)) (= (grid 4 1 2) (next 4 1 1)) (= (grid 5 1 2) (next 5 1 1))
		(= (grid 0 2 2) (next 0 2 1)) (= (grid 1 2 2) (next 1 2 1)) (= (grid 2 2 2) (next 2 2 1)) (= (grid 3 2 2) (next 3 2 1)) (= (grid 4 2 2) (next 4 2 1)) (= (grid 5 2 2) (next 5 2 1))
		(= (grid 0 3 2) (next 0 3 1)) (= (grid 1 3 2) (next 1 3 1)) (= (grid 2 3 2) (next 2 3 1)) (= (grid 3 3 2) (next 3 3 1)) (= (grid 4 3 2) (next 4 3 1)) (= (grid 5 3 2) (next 5 3 1))
		(= (grid 0 4 2) (next 0 4 1)) (= (grid 1 4 2) (next 1 4 1)) (= (grid 2 4 2) (next 2 4 1)) (= (grid 3 4 2) (next 3 4 1)) (= (grid 4 4 2) (next 4 4 1)) (= (grid 5 4 2) (next 5 4 1))
		(= (grid 0 5 2) (next 0 5 1)) (= (grid 1 5 2) (next 1 5 1)) (= (grid 2 5 2) (next 2 5 1)) (= (grid 3 5 2) (next 3 5 1)) (= (grid 4 5 2) (next 4 5 1)) (= (grid 5 5 2) (next 5 5 1))

		(= (grid 0 0 3) (next 0 0 2)) (= (grid 1 0 3) (next 1 0 2)) (= (grid 2 0 3) (next 2 0 2)) (= (grid 3 0 3) (next 3 0 2)) (= (grid 4 0 3) (next 4 0 2)) (= (grid 5 0 3) (next 5 0 2))
		(= (grid 0 1 3) (next 0 1 2)) (= (grid 1 1 3) (next 1 1 2)) (= (grid 2 1 3) (next 2 1 2)) (= (grid 3 1 3) (next 3 1 2)) (= (grid 4 1 3) (next 4 1 2)) (= (grid 5 1 3) (next 5 1 2))
		(= (grid 0 2 3) (next 0 2 2)) (= (grid 1 2 3) (next 1 2 2)) (= (grid 2 2 3) (next 2 2 2)) (= (grid 3 2 3) (next 3 2 2)) (= (grid 4 2 3) (next 4 2 2)) (= (grid 5 2 3) (next 5 2 2))
		(= (grid 0 3 3) (next 0 3 2)) (= (grid 1 3 3) (next 1 3 2)) (= (grid 2 3 3) (next 2 3 2)) (= (grid 3 3 3) (next 3 3 2)) (= (grid 4 3 3) (next 4 3 2)) (= (grid 5 3 3) (next 5 3 2))
		(= (grid 0 4 3) (next 0 4 2)) (= (grid 1 4 3) (next 1 4 2)) (= (grid 2 4 3) (next 2 4 2)) (= (grid 3 4 3) (next 3 4 2)) (= (grid 4 4 3) (next 4 4 2)) (= (grid 5 4 3) (next 5 4 2))
		(= (grid 0 5 3) (next 0 5 2)) (= (grid 1 5 3) (next 1 5 2)) (= (grid 2 5 3) (next 2 5 2)) (= (grid 3 5 3) (next 3 5 2)) (= (grid 4 5 3) (next 4 5 2)) (= (grid 5 5 3) (next 5 5 2))

		(= (grid 0 0 4) (next 0 0 3)) (= (grid 1 0 4) (next 1 0 3)) (= (grid 2 0 4) (next 2 0 3)) (= (grid 3 0 4) (next 3 0 3)) (= (grid 4 0 4) (next 4 0 3)) (= (grid 5 0 4) (next 5 0 3))
		(= (grid 0 1 4) (next 0 1 3)) (= (grid 1 1 4) (next 1 1 3)) (= (grid 2 1 4) (next 2 1 3)) (= (grid 3 1 4) (next 3 1 3)) (= (grid 4 1 4) (next 4 1 3)) (= (grid 5 1 4) (next 5 1 3))
		(= (grid 0 2 4) (next 0 2 3)) (= (grid 1 2 4) (next 1 2 3)) (= (grid 2 2 4) (next 2 2 3)) (= (grid 3 2 4) (next 3 2 3)) (= (grid 4 2 4) (next 4 2 3)) (= (grid 5 2 4) (next 5 2 3))
		(= (grid 0 3 4) (next 0 3 3)) (= (grid 1 3 4) (next 1 3 3)) (= (grid 2 3 4) (next 2 3 3)) (= (grid 3 3 4) (next 3 3 3)) (= (grid 4 3 4) (next 4 3 3)) (= (grid 5 3 4) (next 5 3 3))
		(= (grid 0 4 4) (next 0 4 3)) (= (grid 1 4 4) (next 1 4 3)) (= (grid 2 4 4) (next 2 4 3)) (= (grid 3 4 4) (next 3 4 3)) (= (grid 4 4 4) (next 4 4 3)) (= (grid 5 4 4) (next 5 4 3))
		(= (grid 0 5 4) (next 0 5 3)) (= (grid 1 5 4) (next 1 5 3)) (= (grid 2 5 4) (next 2 5 3)) (= (grid 3 5 4) (next 3 5 3)) (= (grid 4 5 4) (next 4 5 3)) (= (grid 5 5 4) (next 5 5 3))

		(= (grid 0 0 5) (next 0 0 4)) (= (grid 1 0 5) (next 1 0 4)) (= (grid 2 0 5) (next 2 0 4)) (= (grid 3 0 5) (next 3 0 4)) (= (grid 4 0 5) (next 4 0 4)) (= (grid 5 0 5) (next 5 0 4))
		(= (grid 0 1 5) (next 0 1 4)) (= (grid 1 1 5) (next 1 1 4)) (= (grid 2 1 5) (next 2 1 4)) (= (grid 3 1 5) (next 3 1 4)) (= (grid 4 1 5) (next 4 1 4)) (= (grid 5 1 5) (next 5 1 4))
		(= (grid 0 2 5) (next 0 2 4)) (= (grid 1 2 5) (next 1 2 4)) (= (grid 2 2 5) (next 2 2 4)) (= (grid 3 2 5) (next 3 2 4)) (= (grid 4 2 5) (next 4 2 4)) (= (grid 5 2 5) (next 5 2 4))
		(= (grid 0 3 5) (next 0 3 4)) (= (grid 1 3 5) (next 1 3 4)) (= (grid 2 3 5) (next 2 3 4)) (= (grid 3 3 5) (next 3 3 4)) (= (grid 4 3 5) (next 4 3 4)) (= (grid 5 3 5) (next 5 3 4))
		(= (grid 0 4 5) (next 0 4 4)) (= (grid 1 4 5) (next 1 4 4)) (= (grid 2 4 5) (next 2 4 4)) (= (grid 3 4 5) (next 3 4 4)) (= (grid 4 4 5) (next 4 4 4)) (= (grid 5 4 5) (next 5 4 4))
		(= (grid 0 5 5) (next 0 5 4)) (= (grid 1 5 5) (next 1 5 4)) (= (grid 2 5 5) (next 2 5 4)) (= (grid 3 5 5) (next 3 5 4)) (= (grid 4 5 5) (next 4 5 4)) (= (grid 5 5 5) (next 5 5 4))

		(= (grid 0 0 6) (next 0 0 5)) (= (grid 1 0 6) (next 1 0 5)) (= (grid 2 0 6) (next 2 0 5)) (= (grid 3 0 6) (next 3 0 5)) (= (grid 4 0 6) (next 4 0 5)) (= (grid 5 0 6) (next 5 0 5))
		(= (grid 0 1 6) (next 0 1 5)) (= (grid 1 1 6) (next 1 1 5)) (= (grid 2 1 6) (next 2 1 5)) (= (grid 3 1 6) (next 3 1 5)) (= (grid 4 1 6) (next 4 1 5)) (= (grid 5 1 6) (next 5 1 5))
		(= (grid 0 2 6) (next 0 2 5)) (= (grid 1 2 6) (next 1 2 5)) (= (grid 2 2 6) (next 2 2 5)) (= (grid 3 2 6) (next 3 2 5)) (= (grid 4 2 6) (next 4 2 5)) (= (grid 5 2 6) (next 5 2 5))
		(= (grid 0 3 6) (next 0 3 5)) (= (grid 1 3 6) (next 1 3 5)) (= (grid 2 3 6) (next 2 3 5)) (= (grid 3 3 6) (next 3 3 5)) (= (grid 4 3 6) (next 4 3 5)) (= (grid 5 3 6) (next 5 3 5))
		(= (grid 0 4 6) (next 0 4 5)) (= (grid 1 4 6) (next 1 4 5)) (= (grid 2 4 6) (next 2 4 5)) (= (grid 3 4 6) (next 3 4 5)) (= (grid 4 4 6) (next 4 4 5)) (= (grid 5 4 6) (next 5 4 5))
		(= (grid 0 5 6) (next 0 5 5)) (= (grid 1 5 6) (next 1 5 5)) (= (grid 2 5 6) (next 2 5 5)) (= (grid 3 5 6) (next 3 5 5)) (= (grid 4 5 6) (next 4 5 5)) (= (grid 5 5 6) (next 5 5 5))

		(= (grid 0 0 7) (next 0 0 6)) (= (grid 1 0 7) (next 1 0 6)) (= (grid 2 0 7) (next 2 0 6)) (= (grid 3 0 7) (next 3 0 6)) (= (grid 4 0 7) (next 4 0 6)) (= (grid 5 0 7) (next 5 0 6))
		(= (grid 0 1 7) (next 0 1 6)) (= (grid 1 1 7) (next 1 1 6)) (= (grid 2 1 7) (next 2 1 6)) (= (grid 3 1 7) (next 3 1 6)) (= (grid 4 1 7) (next 4 1 6)) (= (grid 5 1 7) (next 5 1 6))
		(= (grid 0 2 7) (next 0 2 6)) (= (grid 1 2 7) (next 1 2 6)) (= (grid 2 2 7) (next 2 2 6)) (= (grid 3 2 7) (next 3 2 6)) (= (grid 4 2 7) (next 4 2 6)) (= (grid 5 2 7) (next 5 2 6))
		(= (grid 0 3 7) (next 0 3 6)) (= (grid 1 3 7) (next 1 3 6)) (= (grid 2 3 7) (next 2 3 6)) (= (grid 3 3 7) (next 3 3 6)) (= (grid 4 3 7) (next 4 3 6)) (= (grid 5 3 7) (next 5 3 6))
		(= (grid 0 4 7) (next 0 4 6)) (= (grid 1 4 7) (next 1 4 6)) (= (grid 2 4 7) (next 2 4 6)) (= (grid 3 4 7) (next 3 4 6)) (= (grid 4 4 7) (next 4 4 6)) (= (grid 5 4 7) (next 5 4 6))
		(= (grid 0 5 7) (next 0 5 6)) (= (grid 1 5 7) (next 1 5 6)) (= (grid 2 5 7) (next 2 5 6)) (= (grid 3 5 7) (next 3 5 6)) (= (grid 4 5 7) (next 4 5 6)) (= (grid 5 5 7) (next 5 5 6))

		(= (grid 0 0 8) (next 0 0 7)) (= (grid 1 0 8) (next 1 0 7)) (= (grid 2 0 8) (next 2 0 7)) (= (grid 3 0 8) (next 3 0 7)) (= (grid 4 0 8) (next 4 0 7)) (= (grid 5 0 8) (next 5 0 7))
		(= (grid 0 1 8) (next 0 1 7)) (= (grid 1 1 8) (next 1 1 7)) (= (grid 2 1 8) (next 2 1 7)) (= (grid 3 1 8) (next 3 1 7)) (= (grid 4 1 8) (next 4 1 7)) (= (grid 5 1 8) (next 5 1 7))
		(= (grid 0 2 8) (next 0 2 7)) (= (grid 1 2 8) (next 1 2 7)) (= (grid 2 2 8) (next 2 2 7)) (= (grid 3 2 8) (next 3 2 7)) (= (grid 4 2 8) (next 4 2 7)) (= (grid 5 2 8) (next 5 2 7))
		(= (grid 0 3 8) (next 0 3 7)) (= (grid 1 3 8) (next 1 3 7)) (= (grid 2 3 8) (next 2 3 7)) (= (grid 3 3 8) (next 3 3 7)) (= (grid 4 3 8) (next 4 3 7)) (= (grid 5 3 8) (next 5 3 7))
		(= (grid 0 4 8) (next 0 4 7)) (= (grid 1 4 8) (next 1 4 7)) (= (grid 2 4 8) (next 2 4 7)) (= (grid 3 4 8) (next 3 4 7)) (= (grid 4 4 8) (next 4 4 7)) (= (grid 5 4 8) (next 5 4 7))
		(= (grid 0 5 8) (next 0 5 7)) (= (grid 1 5 8) (next 1 5 7)) (= (grid 2 5 8) (next 2 5 7)) (= (grid 3 5 8) (next 3 5 7)) (= (grid 4 5 8) (next 4 5 7)) (= (grid 5 5 8) (next 5 5 7))

		(= (grid 0 0 9) (next 0 0 8)) (= (grid 1 0 9) (next 1 0 8)) (= (grid 2 0 9) (next 2 0 8)) (= (grid 3 0 9) (next 3 0 8)) (= (grid 4 0 9) (next 4 0 8)) (= (grid 5 0 9) (next 5 0 8))
		(= (grid 0 1 9) (next 0 1 8)) (= (grid 1 1 9) (next 1 1 8)) (= (grid 2 1 9) (next 2 1 8)) (= (grid 3 1 9) (next 3 1 8)) (= (grid 4 1 9) (next 4 1 8)) (= (grid 5 1 9) (next 5 1 8))
		(= (grid 0 2 9) (next 0 2 8)) (= (grid 1 2 9) (next 1 2 8)) (= (grid 2 2 9) (next 2 2 8)) (= (grid 3 2 9) (next 3 2 8)) (= (grid 4 2 9) (next 4 2 8)) (= (grid 5 2 9) (next 5 2 8))
		(= (grid 0 3 9) (next 0 3 8)) (= (grid 1 3 9) (next 1 3 8)) (= (grid 2 3 9) (next 2 3 8)) (= (grid 3 3 9) (next 3 3 8)) (= (grid 4 3 9) (next 4 3 8)) (= (grid 5 3 9) (next 5 3 8))
		(= (grid 0 4 9) (next 0 4 8)) (= (grid 1 4 9) (next 1 4 8)) (= (grid 2 4 9) (next 2 4 8)) (= (grid 3 4 9) (next 3 4 8)) (= (grid 4 4 9) (next 4 4 8)) (= (grid 5 4 9) (next 5 4 8))
		(= (grid 0 5 9) (next 0 5 8)) (= (grid 1 5 9) (next 1 5 8)) (= (grid 2 5 9) (next 2 5 8)) (= (grid 3 5 9) (next 3 5 8)) (= (grid 4 5 9) (next 4 5 8)) (= (grid 5 5 9) (next 5 5 8))
 	)
)

(assert
	(and
		(or
			(and
				(= (grid 0 0 0) (grid 0 0 2)) (= (grid 1 0 0) (grid 1 0 2)) (= (grid 2 0 0) (grid 2 0 2)) (= (grid 3 0 0) (grid 3 0 2)) (= (grid 4 0 0) (grid 4 0 2)) (= (grid 5 0 0) (grid 5 0 2))
				(= (grid 0 1 0) (grid 0 1 2)) (= (grid 1 1 0) (grid 1 1 2)) (= (grid 2 1 0) (grid 2 1 2)) (= (grid 3 1 0) (grid 3 1 2)) (= (grid 4 1 0) (grid 4 1 2)) (= (grid 5 1 0) (grid 5 1 2))
				(= (grid 0 2 0) (grid 0 2 2)) (= (grid 1 2 0) (grid 1 2 2)) (= (grid 2 2 0) (grid 2 2 2)) (= (grid 3 2 0) (grid 3 2 2)) (= (grid 4 2 0) (grid 4 2 2)) (= (grid 5 2 0) (grid 5 2 2))
				(= (grid 0 3 0) (grid 0 3 2)) (= (grid 1 3 0) (grid 1 3 2)) (= (grid 2 3 0) (grid 2 3 2)) (= (grid 3 3 0) (grid 3 3 2)) (= (grid 4 3 0) (grid 4 3 2)) (= (grid 5 3 0) (grid 5 3 2))
				(= (grid 0 4 0) (grid 0 4 2)) (= (grid 1 4 0) (grid 1 4 2)) (= (grid 2 4 0) (grid 2 4 2)) (= (grid 3 4 0) (grid 3 4 2)) (= (grid 4 4 0) (grid 4 4 2)) (= (grid 5 4 0) (grid 5 4 2))
				(= (grid 0 5 0) (grid 0 5 2)) (= (grid 1 5 0) (grid 1 5 2)) (= (grid 2 5 0) (grid 2 5 2)) (= (grid 3 5 0) (grid 3 5 2)) (= (grid 4 5 0) (grid 4 5 2)) (= (grid 5 5 0) (grid 5 5 2))
			)
			(and
				(= (grid 0 0 0) (grid 0 0 4)) (= (grid 1 0 0) (grid 1 0 4)) (= (grid 2 0 0) (grid 2 0 4)) (= (grid 3 0 0) (grid 3 0 4)) (= (grid 4 0 0) (grid 4 0 4)) (= (grid 5 0 0) (grid 5 0 4))
				(= (grid 0 1 0) (grid 0 1 4)) (= (grid 1 1 0) (grid 1 1 4)) (= (grid 2 1 0) (grid 2 1 4)) (= (grid 3 1 0) (grid 3 1 4)) (= (grid 4 1 0) (grid 4 1 4)) (= (grid 5 1 0) (grid 5 1 4))
				(= (grid 0 2 0) (grid 0 2 4)) (= (grid 1 2 0) (grid 1 2 4)) (= (grid 2 2 0) (grid 2 2 4)) (= (grid 3 2 0) (grid 3 2 4)) (= (grid 4 2 0) (grid 4 2 4)) (= (grid 5 2 0) (grid 5 2 4))
				(= (grid 0 3 0) (grid 0 3 4)) (= (grid 1 3 0) (grid 1 3 4)) (= (grid 2 3 0) (grid 2 3 4)) (= (grid 3 3 0) (grid 3 3 4)) (= (grid 4 3 0) (grid 4 3 4)) (= (grid 5 3 0) (grid 5 3 4))
				(= (grid 0 4 0) (grid 0 4 4)) (= (grid 1 4 0) (grid 1 4 4)) (= (grid 2 4 0) (grid 2 4 4)) (= (grid 3 4 0) (grid 3 4 4)) (= (grid 4 4 0) (grid 4 4 4)) (= (grid 5 4 0) (grid 5 4 4))
				(= (grid 0 5 0) (grid 0 5 4)) (= (grid 1 5 0) (grid 1 5 4)) (= (grid 2 5 0) (grid 2 5 4)) (= (grid 3 5 0) (grid 3 5 4)) (= (grid 4 5 0) (grid 4 5 4)) (= (grid 5 5 0) (grid 5 5 4))
			)

			(and
				(= (grid 0 0 1) (grid 0 0 3)) (= (grid 1 0 1) (grid 1 0 3)) (= (grid 2 0 1) (grid 2 0 3)) (= (grid 3 0 1) (grid 3 0 3)) (= (grid 4 0 1) (grid 4 0 3)) (= (grid 5 0 1) (grid 5 0 3))
				(= (grid 0 1 1) (grid 0 1 3)) (= (grid 1 1 1) (grid 1 1 3)) (= (grid 2 1 1) (grid 2 1 3)) (= (grid 3 1 1) (grid 3 1 3)) (= (grid 4 1 1) (grid 4 1 3)) (= (grid 5 1 1) (grid 5 1 3))
				(= (grid 0 2 1) (grid 0 2 3)) (= (grid 1 2 1) (grid 1 2 3)) (= (grid 2 2 1) (grid 2 2 3)) (= (grid 3 2 1) (grid 3 2 3)) (= (grid 4 2 1) (grid 4 2 3)) (= (grid 5 2 1) (grid 5 2 3))
				(= (grid 0 3 1) (grid 0 3 3)) (= (grid 1 3 1) (grid 1 3 3)) (= (grid 2 3 1) (grid 2 3 3)) (= (grid 3 3 1) (grid 3 3 3)) (= (grid 4 3 1) (grid 4 3 3)) (= (grid 5 3 1) (grid 5 3 3))
				(= (grid 0 4 1) (grid 0 4 3)) (= (grid 1 4 1) (grid 1 4 3)) (= (grid 2 4 1) (grid 2 4 3)) (= (grid 3 4 1) (grid 3 4 3)) (= (grid 4 4 1) (grid 4 4 3)) (= (grid 5 4 1) (grid 5 4 3))
				(= (grid 0 5 1) (grid 0 5 3)) (= (grid 1 5 1) (grid 1 5 3)) (= (grid 2 5 1) (grid 2 5 3)) (= (grid 3 5 1) (grid 3 5 3)) (= (grid 4 5 1) (grid 4 5 3)) (= (grid 5 5 1) (grid 5 5 3))
			)
			(and
				(= (grid 0 0 1) (grid 0 0 5)) (= (grid 1 0 1) (grid 1 0 5)) (= (grid 2 0 1) (grid 2 0 5)) (= (grid 3 0 1) (grid 3 0 5)) (= (grid 4 0 1) (grid 4 0 5)) (= (grid 5 0 1) (grid 5 0 5))
				(= (grid 0 1 1) (grid 0 1 5)) (= (grid 1 1 1) (grid 1 1 5)) (= (grid 2 1 1) (grid 2 1 5)) (= (grid 3 1 1) (grid 3 1 5)) (= (grid 4 1 1) (grid 4 1 5)) (= (grid 5 1 1) (grid 5 1 5))
				(= (grid 0 2 1) (grid 0 2 5)) (= (grid 1 2 1) (grid 1 2 5)) (= (grid 2 2 1) (grid 2 2 5)) (= (grid 3 2 1) (grid 3 2 5)) (= (grid 4 2 1) (grid 4 2 5)) (= (grid 5 2 1) (grid 5 2 5))
				(= (grid 0 3 1) (grid 0 3 5)) (= (grid 1 3 1) (grid 1 3 5)) (= (grid 2 3 1) (grid 2 3 5)) (= (grid 3 3 1) (grid 3 3 5)) (= (grid 4 3 1) (grid 4 3 5)) (= (grid 5 3 1) (grid 5 3 5))
				(= (grid 0 4 1) (grid 0 4 5)) (= (grid 1 4 1) (grid 1 4 5)) (= (grid 2 4 1) (grid 2 4 5)) (= (grid 3 4 1) (grid 3 4 5)) (= (grid 4 4 1) (grid 4 4 5)) (= (grid 5 4 1) (grid 5 4 5))
				(= (grid 0 5 1) (grid 0 5 5)) (= (grid 1 5 1) (grid 1 5 5)) (= (grid 2 5 1) (grid 2 5 5)) (= (grid 3 5 1) (grid 3 5 5)) (= (grid 4 5 1) (grid 4 5 5)) (= (grid 5 5 1) (grid 5 5 5))
			)

			(and
				(= (grid 0 0 2) (grid 0 0 4)) (= (grid 1 0 2) (grid 1 0 4)) (= (grid 2 0 2) (grid 2 0 4)) (= (grid 3 0 2) (grid 3 0 4)) (= (grid 4 0 2) (grid 4 0 4)) (= (grid 5 0 2) (grid 5 0 4))
				(= (grid 0 1 2) (grid 0 1 4)) (= (grid 1 1 2) (grid 1 1 4)) (= (grid 2 1 2) (grid 2 1 4)) (= (grid 3 1 2) (grid 3 1 4)) (= (grid 4 1 2) (grid 4 1 4)) (= (grid 5 1 2) (grid 5 1 4))
				(= (grid 0 2 2) (grid 0 2 4)) (= (grid 1 2 2) (grid 1 2 4)) (= (grid 2 2 2) (grid 2 2 4)) (= (grid 3 2 2) (grid 3 2 4)) (= (grid 4 2 2) (grid 4 2 4)) (= (grid 5 2 2) (grid 5 2 4))
				(= (grid 0 3 2) (grid 0 3 4)) (= (grid 1 3 2) (grid 1 3 4)) (= (grid 2 3 2) (grid 2 3 4)) (= (grid 3 3 2) (grid 3 3 4)) (= (grid 4 3 2) (grid 4 3 4)) (= (grid 5 3 2) (grid 5 3 4))
				(= (grid 0 4 2) (grid 0 4 4)) (= (grid 1 4 2) (grid 1 4 4)) (= (grid 2 4 2) (grid 2 4 4)) (= (grid 3 4 2) (grid 3 4 4)) (= (grid 4 4 2) (grid 4 4 4)) (= (grid 5 4 2) (grid 5 4 4))
				(= (grid 0 5 2) (grid 0 5 4)) (= (grid 1 5 2) (grid 1 5 4)) (= (grid 2 5 2) (grid 2 5 4)) (= (grid 3 5 2) (grid 3 5 4)) (= (grid 4 5 2) (grid 4 5 4)) (= (grid 5 5 2) (grid 5 5 4))
			)
			(and
				(= (grid 0 0 2) (grid 0 0 6)) (= (grid 1 0 2) (grid 1 0 6)) (= (grid 2 0 2) (grid 2 0 6)) (= (grid 3 0 2) (grid 3 0 6)) (= (grid 4 0 2) (grid 4 0 6)) (= (grid 5 0 2) (grid 5 0 6))
				(= (grid 0 1 2) (grid 0 1 6)) (= (grid 1 1 2) (grid 1 1 6)) (= (grid 2 1 2) (grid 2 1 6)) (= (grid 3 1 2) (grid 3 1 6)) (= (grid 4 1 2) (grid 4 1 6)) (= (grid 5 1 2) (grid 5 1 6))
				(= (grid 0 2 2) (grid 0 2 6)) (= (grid 1 2 2) (grid 1 2 6)) (= (grid 2 2 2) (grid 2 2 6)) (= (grid 3 2 2) (grid 3 2 6)) (= (grid 4 2 2) (grid 4 2 6)) (= (grid 5 2 2) (grid 5 2 6))
				(= (grid 0 3 2) (grid 0 3 6)) (= (grid 1 3 2) (grid 1 3 6)) (= (grid 2 3 2) (grid 2 3 6)) (= (grid 3 3 2) (grid 3 3 6)) (= (grid 4 3 2) (grid 4 3 6)) (= (grid 5 3 2) (grid 5 3 6))
				(= (grid 0 4 2) (grid 0 4 6)) (= (grid 1 4 2) (grid 1 4 6)) (= (grid 2 4 2) (grid 2 4 6)) (= (grid 3 4 2) (grid 3 4 6)) (= (grid 4 4 2) (grid 4 4 6)) (= (grid 5 4 2) (grid 5 4 6))
				(= (grid 0 5 2) (grid 0 5 6)) (= (grid 1 5 2) (grid 1 5 6)) (= (grid 2 5 2) (grid 2 5 6)) (= (grid 3 5 2) (grid 3 5 6)) (= (grid 4 5 2) (grid 4 5 6)) (= (grid 5 5 2) (grid 5 5 6))
			)

			(and
				(= (grid 0 0 3) (grid 0 0 5)) (= (grid 1 0 3) (grid 1 0 5)) (= (grid 2 0 3) (grid 2 0 5)) (= (grid 3 0 3) (grid 3 0 5)) (= (grid 4 0 3) (grid 4 0 5)) (= (grid 5 0 3) (grid 5 0 5))
				(= (grid 0 1 3) (grid 0 1 5)) (= (grid 1 1 3) (grid 1 1 5)) (= (grid 2 1 3) (grid 2 1 5)) (= (grid 3 1 3) (grid 3 1 5)) (= (grid 4 1 3) (grid 4 1 5)) (= (grid 5 1 3) (grid 5 1 5))
				(= (grid 0 2 3) (grid 0 2 5)) (= (grid 1 2 3) (grid 1 2 5)) (= (grid 2 2 3) (grid 2 2 5)) (= (grid 3 2 3) (grid 3 2 5)) (= (grid 4 2 3) (grid 4 2 5)) (= (grid 5 2 3) (grid 5 2 5))
				(= (grid 0 3 3) (grid 0 3 5)) (= (grid 1 3 3) (grid 1 3 5)) (= (grid 2 3 3) (grid 2 3 5)) (= (grid 3 3 3) (grid 3 3 5)) (= (grid 4 3 3) (grid 4 3 5)) (= (grid 5 3 3) (grid 5 3 5))
				(= (grid 0 4 3) (grid 0 4 5)) (= (grid 1 4 3) (grid 1 4 5)) (= (grid 2 4 3) (grid 2 4 5)) (= (grid 3 4 3) (grid 3 4 5)) (= (grid 4 4 3) (grid 4 4 5)) (= (grid 5 4 3) (grid 5 4 5))
				(= (grid 0 5 3) (grid 0 5 5)) (= (grid 1 5 3) (grid 1 5 5)) (= (grid 2 5 3) (grid 2 5 5)) (= (grid 3 5 3) (grid 3 5 5)) (= (grid 4 5 3) (grid 4 5 5)) (= (grid 5 5 3) (grid 5 5 5))
			)
			(and
				(= (grid 0 0 3) (grid 0 0 7)) (= (grid 1 0 3) (grid 1 0 7)) (= (grid 2 0 3) (grid 2 0 7)) (= (grid 3 0 3) (grid 3 0 7)) (= (grid 4 0 3) (grid 4 0 7)) (= (grid 5 0 3) (grid 5 0 7))
				(= (grid 0 1 3) (grid 0 1 7)) (= (grid 1 1 3) (grid 1 1 7)) (= (grid 2 1 3) (grid 2 1 7)) (= (grid 3 1 3) (grid 3 1 7)) (= (grid 4 1 3) (grid 4 1 7)) (= (grid 5 1 3) (grid 5 1 7))
				(= (grid 0 2 3) (grid 0 2 7)) (= (grid 1 2 3) (grid 1 2 7)) (= (grid 2 2 3) (grid 2 2 7)) (= (grid 3 2 3) (grid 3 2 7)) (= (grid 4 2 3) (grid 4 2 7)) (= (grid 5 2 3) (grid 5 2 7))
				(= (grid 0 3 3) (grid 0 3 7)) (= (grid 1 3 3) (grid 1 3 7)) (= (grid 2 3 3) (grid 2 3 7)) (= (grid 3 3 3) (grid 3 3 7)) (= (grid 4 3 3) (grid 4 3 7)) (= (grid 5 3 3) (grid 5 3 7))
				(= (grid 0 4 3) (grid 0 4 7)) (= (grid 1 4 3) (grid 1 4 7)) (= (grid 2 4 3) (grid 2 4 7)) (= (grid 3 4 3) (grid 3 4 7)) (= (grid 4 4 3) (grid 4 4 7)) (= (grid 5 4 3) (grid 5 4 7))
				(= (grid 0 5 3) (grid 0 5 7)) (= (grid 1 5 3) (grid 1 5 7)) (= (grid 2 5 3) (grid 2 5 7)) (= (grid 3 5 3) (grid 3 5 7)) (= (grid 4 5 3) (grid 4 5 7)) (= (grid 5 5 3) (grid 5 5 7))
			)

			(and
				(= (grid 0 0 4) (grid 0 0 6)) (= (grid 1 0 4) (grid 1 0 6)) (= (grid 2 0 4) (grid 2 0 6)) (= (grid 3 0 4) (grid 3 0 6)) (= (grid 4 0 4) (grid 4 0 6)) (= (grid 5 0 4) (grid 5 0 6))
				(= (grid 0 1 4) (grid 0 1 6)) (= (grid 1 1 4) (grid 1 1 6)) (= (grid 2 1 4) (grid 2 1 6)) (= (grid 3 1 4) (grid 3 1 6)) (= (grid 4 1 4) (grid 4 1 6)) (= (grid 5 1 4) (grid 5 1 6))
				(= (grid 0 2 4) (grid 0 2 6)) (= (grid 1 2 4) (grid 1 2 6)) (= (grid 2 2 4) (grid 2 2 6)) (= (grid 3 2 4) (grid 3 2 6)) (= (grid 4 2 4) (grid 4 2 6)) (= (grid 5 2 4) (grid 5 2 6))
				(= (grid 0 3 4) (grid 0 3 6)) (= (grid 1 3 4) (grid 1 3 6)) (= (grid 2 3 4) (grid 2 3 6)) (= (grid 3 3 4) (grid 3 3 6)) (= (grid 4 3 4) (grid 4 3 6)) (= (grid 5 3 4) (grid 5 3 6))
				(= (grid 0 4 4) (grid 0 4 6)) (= (grid 1 4 4) (grid 1 4 6)) (= (grid 2 4 4) (grid 2 4 6)) (= (grid 3 4 4) (grid 3 4 6)) (= (grid 4 4 4) (grid 4 4 6)) (= (grid 5 4 4) (grid 5 4 6))
				(= (grid 0 5 4) (grid 0 5 6)) (= (grid 1 5 4) (grid 1 5 6)) (= (grid 2 5 4) (grid 2 5 6)) (= (grid 3 5 4) (grid 3 5 6)) (= (grid 4 5 4) (grid 4 5 6)) (= (grid 5 5 4) (grid 5 5 6))
			)
			(and
				(= (grid 0 0 4) (grid 0 0 8)) (= (grid 1 0 4) (grid 1 0 8)) (= (grid 2 0 4) (grid 2 0 8)) (= (grid 3 0 4) (grid 3 0 8)) (= (grid 4 0 4) (grid 4 0 8)) (= (grid 5 0 4) (grid 5 0 8))
				(= (grid 0 1 4) (grid 0 1 8)) (= (grid 1 1 4) (grid 1 1 8)) (= (grid 2 1 4) (grid 2 1 8)) (= (grid 3 1 4) (grid 3 1 8)) (= (grid 4 1 4) (grid 4 1 8)) (= (grid 5 1 4) (grid 5 1 8))
				(= (grid 0 2 4) (grid 0 2 8)) (= (grid 1 2 4) (grid 1 2 8)) (= (grid 2 2 4) (grid 2 2 8)) (= (grid 3 2 4) (grid 3 2 8)) (= (grid 4 2 4) (grid 4 2 8)) (= (grid 5 2 4) (grid 5 2 8))
				(= (grid 0 3 4) (grid 0 3 8)) (= (grid 1 3 4) (grid 1 3 8)) (= (grid 2 3 4) (grid 2 3 8)) (= (grid 3 3 4) (grid 3 3 8)) (= (grid 4 3 4) (grid 4 3 8)) (= (grid 5 3 4) (grid 5 3 8))
				(= (grid 0 4 4) (grid 0 4 8)) (= (grid 1 4 4) (grid 1 4 8)) (= (grid 2 4 4) (grid 2 4 8)) (= (grid 3 4 4) (grid 3 4 8)) (= (grid 4 4 4) (grid 4 4 8)) (= (grid 5 4 4) (grid 5 4 8))
				(= (grid 0 5 4) (grid 0 5 8)) (= (grid 1 5 4) (grid 1 5 8)) (= (grid 2 5 4) (grid 2 5 8)) (= (grid 3 5 4) (grid 3 5 8)) (= (grid 4 5 4) (grid 4 5 8)) (= (grid 5 5 4) (grid 5 5 8))
			)

			(and
				(= (grid 0 0 5) (grid 0 0 7)) (= (grid 1 0 5) (grid 1 0 7)) (= (grid 2 0 5) (grid 2 0 7)) (= (grid 3 0 5) (grid 3 0 7)) (= (grid 4 0 5) (grid 4 0 7)) (= (grid 5 0 5) (grid 5 0 7))
				(= (grid 0 1 5) (grid 0 1 7)) (= (grid 1 1 5) (grid 1 1 7)) (= (grid 2 1 5) (grid 2 1 7)) (= (grid 3 1 5) (grid 3 1 7)) (= (grid 4 1 5) (grid 4 1 7)) (= (grid 5 1 5) (grid 5 1 7))
				(= (grid 0 2 5) (grid 0 2 7)) (= (grid 1 2 5) (grid 1 2 7)) (= (grid 2 2 5) (grid 2 2 7)) (= (grid 3 2 5) (grid 3 2 7)) (= (grid 4 2 5) (grid 4 2 7)) (= (grid 5 2 5) (grid 5 2 7))
				(= (grid 0 3 5) (grid 0 3 7)) (= (grid 1 3 5) (grid 1 3 7)) (= (grid 2 3 5) (grid 2 3 7)) (= (grid 3 3 5) (grid 3 3 7)) (= (grid 4 3 5) (grid 4 3 7)) (= (grid 5 3 5) (grid 5 3 7))
				(= (grid 0 4 5) (grid 0 4 7)) (= (grid 1 4 5) (grid 1 4 7)) (= (grid 2 4 5) (grid 2 4 7)) (= (grid 3 4 5) (grid 3 4 7)) (= (grid 4 4 5) (grid 4 4 7)) (= (grid 5 4 5) (grid 5 4 7))
				(= (grid 0 5 5) (grid 0 5 7)) (= (grid 1 5 5) (grid 1 5 7)) (= (grid 2 5 5) (grid 2 5 7)) (= (grid 3 5 5) (grid 3 5 7)) (= (grid 4 5 5) (grid 4 5 7)) (= (grid 5 5 5) (grid 5 5 7))
			)
			(and
				(= (grid 0 0 5) (grid 0 0 9)) (= (grid 1 0 5) (grid 1 0 9)) (= (grid 2 0 5) (grid 2 0 9)) (= (grid 3 0 5) (grid 3 0 9)) (= (grid 4 0 5) (grid 4 0 9)) (= (grid 5 0 5) (grid 5 0 9))
				(= (grid 0 1 5) (grid 0 1 9)) (= (grid 1 1 5) (grid 1 1 9)) (= (grid 2 1 5) (grid 2 1 9)) (= (grid 3 1 5) (grid 3 1 9)) (= (grid 4 1 5) (grid 4 1 9)) (= (grid 5 1 5) (grid 5 1 9))
				(= (grid 0 2 5) (grid 0 2 9)) (= (grid 1 2 5) (grid 1 2 9)) (= (grid 2 2 5) (grid 2 2 9)) (= (grid 3 2 5) (grid 3 2 9)) (= (grid 4 2 5) (grid 4 2 9)) (= (grid 5 2 5) (grid 5 2 9))
				(= (grid 0 3 5) (grid 0 3 9)) (= (grid 1 3 5) (grid 1 3 9)) (= (grid 2 3 5) (grid 2 3 9)) (= (grid 3 3 5) (grid 3 3 9)) (= (grid 4 3 5) (grid 4 3 9)) (= (grid 5 3 5) (grid 5 3 9))
				(= (grid 0 4 5) (grid 0 4 9)) (= (grid 1 4 5) (grid 1 4 9)) (= (grid 2 4 5) (grid 2 4 9)) (= (grid 3 4 5) (grid 3 4 9)) (= (grid 4 4 5) (grid 4 4 9)) (= (grid 5 4 5) (grid 5 4 9))
				(= (grid 0 5 5) (grid 0 5 9)) (= (grid 1 5 5) (grid 1 5 9)) (= (grid 2 5 5) (grid 2 5 9)) (= (grid 3 5 5) (grid 3 5 9)) (= (grid 4 5 5) (grid 4 5 9)) (= (grid 5 5 5) (grid 5 5 9))
			)
		)
		(> (+
			(grid 0 0 9) (grid 1 0 9) (grid 2 0 9) (grid 3 0 9) (grid 4 0 9) (grid 5 0 9)
			(grid 0 1 9) (grid 1 1 9) (grid 2 1 9) (grid 3 1 9) (grid 4 1 9) (grid 5 1 9)
			(grid 0 2 9) (grid 1 2 9) (grid 2 2 9) (grid 3 2 9) (grid 4 2 9) (grid 5 2 9)
			(grid 0 3 9) (grid 1 3 9) (grid 2 3 9) (grid 3 3 9) (grid 4 3 9) (grid 5 3 9)
			(grid 0 4 9) (grid 1 4 9) (grid 2 4 9) (grid 3 4 9) (grid 4 4 9) (grid 5 4 9)
			(grid 0 5 9) (grid 1 5 9) (grid 2 5 9) (grid 3 5 9) (grid 4 5 9) (grid 5 5 9)
		) 2)  ; at least 3 alive cells
	)
)


(check-sat)
(get-model)
(get-value (
	(grid 0 0 0) (grid 1 0 0) (grid 2 0 0) (grid 3 0 0) (grid 4 0 0) (grid 5 0 0)
	(grid 0 1 0) (grid 1 1 0) (grid 2 1 0) (grid 3 1 0) (grid 4 1 0) (grid 5 1 0)
	(grid 0 2 0) (grid 1 2 0) (grid 2 2 0) (grid 3 2 0) (grid 4 2 0) (grid 5 2 0)
	(grid 0 3 0) (grid 1 3 0) (grid 2 3 0) (grid 3 3 0) (grid 4 3 0) (grid 5 3 0)
	(grid 0 4 0) (grid 1 4 0) (grid 2 4 0) (grid 3 4 0) (grid 4 4 0) (grid 5 4 0)
	(grid 0 5 0) (grid 1 5 0) (grid 2 5 0) (grid 3 5 0) (grid 4 5 0) (grid 5 5 0)
))