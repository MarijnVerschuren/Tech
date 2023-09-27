[bits 64]
section .text
	global bubble_sort



; analysis:
;	the bubble_sort function implementation can be divided up into two main parts:
;	the 'max' function and the 'reverse' function these are both implemented with a time complexity of O(1):
;	max function:
;		mov r8, [rax + rcx * 8]				; array[i] is loaded into R8
;		mov r9, [rax + (rcx - 1) * 8]		; array[i - 1] is loaded into R9
;		cmp r9, r8							; R8 and R9 are compared to set the comparison status registers that are used in the reverse function
;	reverse function:
;		cmovg r8, r9						; conditionally move R9 into R8 if R9 > R8
;		cmovg r9, [rax + rcx * 8]			; conditionally load array[i] into R8 if R9 > R8
;		mov [rax + (rcx - 1) * 8], r9		; store R9 back to array[i - 1]
;		mov [rax + rcx * 8], r8				; store R8 back to array[i]
;	i did not find a way to conditionally store the data which would be a lot faster
;
;	time complexity of the max function:			O(1)
;	time complexity of the reverse function:		O(1)
;
;	time complexity of the bubble_sort function:	O(n^2)


; time tests (s):
; time was measured on an array of 100000 random int64_t's to
; determine what implementation of the reverse function is best
;
; |				times				|					implementation						|
; |	6.964624, 6.866957, 6.970855	|	reverse function:	r8 -> r10, r9 -> r8, r10 -> r9	|
; |	6.003875, 6.141479, 5.944625	|	reverse function:	r9 -> r8, mem -> r9				|
; |	23.055041, 22.518016, 22.471222	|	C - implementation									|


; rax	->	array
; rbx	->	j
; rcx	->	i
; rdx	->	length	->	length - j
; rsi	->	length
; r8	->	array[i]
; r9	->	array[i-1]


bubble_sort:
	xor rbx, rbx			; uint64_t j = 0;

	loop_0:
	mov rcx, 1				; uint64_t i = 1;
	mov rdx, rsi			; move the array length into rdx
	sub rdx, rbx			; calculate		(length - j)

	loop_1:
	mov r8, [rax + rcx * 8]
	mov r9, [rax + (rcx - 1) * 8]
	cmp r9, r8

	cmovg r8, r9
	cmovg r9, [rax + rcx * 8]
    mov [rax + (rcx - 1) * 8], r9
	mov [rax + rcx * 8], r8

	inc rcx					; i++
	cmp rcx, rdx			; compare (i) and (length - j)
	jl loop_1				; jump only if (i) is less than (length - j)

	inc rbx					; j++
	cmp rbx, rsi			; compare (j) and (length)
	jl loop_0				; jump only of (j) is less than (length)

	ret
