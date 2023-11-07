; trucks **
; each truck (1 - 6) can carry at most 8 pallets with a max weight of 8000kg
; the pallets (nuzzles prittles skipples crottles dupples) have different counts, weights and rules:
; nuzzles:
;   count:  4
;   weight: 800kg
;   rule:
;       nuzzles are valuable so to mitigate the risk of loss,
;       no two pallets may be in one truck
; prittles:
;   count:  x
;   weight: 1300kg
; skipples:
;   count:  8
;   weight: 1000kg
;   rule:
;       skipples need to be cooled only two of the six trucks
;       poses the ability to cool payload
; crottles:
;   count:  8
;   weight: 1500kg
; dupples:
;   count:  12
;   weight: 400kg


(declare-datatypes () ((Truck truck_1 truck_2 truck_3 truck_4 truck_5 truck_6)))
(declare-datatypes () ((Pallet nuzzles prittles skipples crottles dupples)))

; count of each pallet type in each truck
(declare-fun count (Truck Pallet) Int)


; make sure that each truck is not allowed to carry more than 8 pallets
; and that the combination doesnt weigh more than 8000kg
(assert
	(forall ((t Truck))
		(and
			(<  ; count of all pallets in each truc must not exceed 9
				(+
					(count t nuzzles)
					(count t prittles)
					(count t skipples)
					(count t crottles)
					(count t dupples)
				)
				9
			)
			(<  ; weight of the combination of pallets must not exceed 8001kg
				(+
					(* 800 (count t nuzzles))
					(* 1300 (count t prittles))
					(* 1000 (count t skipples))
					(* 1500 (count t crottles))
					(* 400 (count t dupples))
				)
				8001
			)
			(forall ((p Pallet))    ; there must not be negative pallets of any kind in each truck
				(>=
					(count t p)
					0
				)
			)
		)
	)
)

; check if skipples are distributed over no more than 2 strucks
(assert
	(<
		(+
			(> (count truck_1 skipples) 0)
			(> (count truck_2 skipples) 0)
			(> (count truck_3 skipples) 0)
			(> (count truck_4 skipples) 0)
			(> (count truck_5 skipples) 0)
			(> (count truck_6 skipples) 0)
		)
		3
	)
)

; check if all deliverables are delivered
(assert ; check if all four nuzzles pallets are in trucks
	(=
		(+
			(count truck_1 nuzzles)
			(count truck_2 nuzzles)
			(count truck_3 nuzzles)
			(count truck_4 nuzzles)
			(count truck_5 nuzzles)
			(count truck_6 nuzzles)
		)
		4
	)
)
(assert ; check if all eight skipples pallets are in trucks
	(=
		(+
			(count truck_1 skipples)
			(count truck_2 skipples)
			(count truck_3 skipples)
			(count truck_4 skipples)
			(count truck_5 skipples)
			(count truck_6 skipples)
		)
		8
	)
)
(assert ; check if all eight crottles pallets are in trucks
	(=
		(+
			(count truck_1 crottles)
			(count truck_2 crottles)
			(count truck_3 crottles)
			(count truck_4 crottles)
			(count truck_5 crottles)
			(count truck_6 crottles)
		)
		8
	)
)
(assert ; check if all twelve dupples pallets are in trucks
	(=
		(+
			(count truck_1 dupples)
			(count truck_2 dupples)
			(count truck_3 dupples)
			(count truck_4 dupples)
			(count truck_5 dupples)
			(count truck_6 dupples)
		)
		12
	)
)
(assert ; check if at least one prittles pallet is in a truck
	(>
		(+
			(count truck_1 prittles)
			(count truck_2 prittles)
			(count truck_3 prittles)
			(count truck_4 prittles)
			(count truck_5 prittles)
			(count truck_6 prittles)
		)
		0
	)
)
(assert ; check if no two nuzzles boxes are in one truck
	(forall ((t Truck))
		(<= (count t nuzzles) 1)
	)
)
(assert
	(or
		(and
			(> (count truck_1 skipples) 0)
			(> (count truck_2 skipples) 0)
			(= (count truck_3 skipples) 0)
			(= (count truck_4 skipples) 0)
			(= (count truck_5 skipples) 0)
			(= (count truck_6 skipples) 0)
		)
		(and
			(> (count truck_1 skipples) 0)
			(> (count truck_3 skipples) 0)
			(= (count truck_2 skipples) 0)
			(= (count truck_4 skipples) 0)
			(= (count truck_5 skipples) 0)
			(= (count truck_6 skipples) 0)
		)
		(and
			(> (count truck_1 skipples) 0)
			(> (count truck_4 skipples) 0)
			(= (count truck_2 skipples) 0)
			(= (count truck_3 skipples) 0)
			(= (count truck_5 skipples) 0)
			(= (count truck_6 skipples) 0)
		)
		(and
			(> (count truck_1 skipples) 0)
			(> (count truck_5 skipples) 0)
			(= (count truck_2 skipples) 0)
			(= (count truck_3 skipples) 0)
			(= (count truck_4 skipples) 0)
			(= (count truck_6 skipples) 0)
		)
		(and
			(> (count truck_1 skipples) 0)
			(> (count truck_6 skipples) 0)
			(= (count truck_2 skipples) 0)
			(= (count truck_3 skipples) 0)
			(= (count truck_4 skipples) 0)
			(= (count truck_5 skipples) 0)
		)
		(and
			(> (count truck_2 skipples) 0)
			(> (count truck_3 skipples) 0)
			(= (count truck_1 skipples) 0)
			(= (count truck_4 skipples) 0)
			(= (count truck_5 skipples) 0)
			(= (count truck_6 skipples) 0)
		)
		(and
			(> (count truck_2 skipples) 0)
			(> (count truck_4 skipples) 0)
			(= (count truck_1 skipples) 0)
			(= (count truck_3 skipples) 0)
			(= (count truck_5 skipples) 0)
			(= (count truck_6 skipples) 0)
		)
		(and
			(> (count truck_2 skipples) 0)
			(> (count truck_5 skipples) 0)
			(= (count truck_1 skipples) 0)
			(= (count truck_3 skipples) 0)
			(= (count truck_4 skipples) 0)
			(= (count truck_6 skipples) 0)
		)
		(and
			(> (count truck_2 skipples) 0)
			(> (count truck_6 skipples) 0)
			(= (count truck_1 skipples) 0)
			(= (count truck_3 skipples) 0)
			(= (count truck_4 skipples) 0)
			(= (count truck_5 skipples) 0)
		)
		(and
			(> (count truck_3 skipples) 0)
			(> (count truck_4 skipples) 0)
			(= (count truck_1 skipples) 0)
			(= (count truck_2 skipples) 0)
			(= (count truck_5 skipples) 0)
			(= (count truck_6 skipples) 0)
		)
		(and
			(> (count truck_3 skipples) 0)
			(> (count truck_5 skipples) 0)
			(= (count truck_1 skipples) 0)
			(= (count truck_2 skipples) 0)
			(= (count truck_4 skipples) 0)
			(= (count truck_6 skipples) 0)
		)
		(and
			(> (count truck_3 skipples) 0)
			(> (count truck_6 skipples) 0)
			(= (count truck_1 skipples) 0)
			(= (count truck_2 skipples) 0)
			(= (count truck_4 skipples) 0)
			(= (count truck_5 skipples) 0)
		)
		(and
			(> (count truck_4 skipples) 0)
			(> (count truck_5 skipples) 0)
			(= (count truck_1 skipples) 0)
			(= (count truck_2 skipples) 0)
			(= (count truck_3 skipples) 0)
			(= (count truck_6 skipples) 0)
		)
		(and
			(> (count truck_4 skipples) 0)
			(> (count truck_6 skipples) 0)
			(= (count truck_1 skipples) 0)
			(= (count truck_2 skipples) 0)
			(= (count truck_3 skipples) 0)
			(= (count truck_5 skipples) 0)
		)
		(and
			(> (count truck_5 skipples) 0)
			(> (count truck_6 skipples) 0)
			(= (count truck_1 skipples) 0)
			(= (count truck_2 skipples) 0)
			(= (count truck_3 skipples) 0)
			(= (count truck_4 skipples) 0)
		)
	)
)

; check satisfied and print solution
(check-sat)
(get-value
	(
		(count truck_1 nuzzles)
		(count truck_1 prittles)
		(count truck_1 skipples)
		(count truck_1 crottles)
		(count truck_1 dupples)
	)
)
(get-value
	(
		(count truck_2 nuzzles)
		(count truck_2 prittles)
		(count truck_2 skipples)
		(count truck_2 crottles)
		(count truck_2 dupples)
	)
)
(get-value
	(
		(count truck_3 nuzzles)
		(count truck_3 prittles)
		(count truck_3 skipples)
		(count truck_3 crottles)
		(count truck_3 dupples)
	)
)
(get-value
	(
		(count truck_4 nuzzles)
		(count truck_4 prittles)
		(count truck_4 skipples)
		(count truck_4 crottles)
		(count truck_4 dupples)
	)
)
(get-value
	(
		(count truck_5 nuzzles)
		(count truck_5 prittles)
		(count truck_5 skipples)
		(count truck_5 crottles)
		(count truck_5 dupples)
	)
)
(get-value
	(
		(count truck_6 nuzzles)
		(count truck_6 prittles)
		(count truck_6 skipples)
		(count truck_6 crottles)
		(count truck_6 dupples)
	)
)
