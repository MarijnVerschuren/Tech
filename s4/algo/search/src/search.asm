[bits 64]
section .text
	global linear_count
	global binary_count


; rdi	->	words		-> cmp func a
; rsi	->	size		-> cmp func b
; rdx	->	word
; rcx	->	cmp function

; rax	->	cmp return
; rbx	->	i
; r8	->	words
; r9	->	size
; r10	->	flag
; r11	->	count
linear_count:
	xor rbx, rbx			; set i to 0
	xor r11, r11			; set count to 0
	xor r10, r10			; set the rest of the flag register to 0
	mov r8, rdi				; move word array into r8
	mov r9, rsi				; move size into r9
	mov rsi, rdx			; move word into rsi

	test r9, r9
	jz lc_end

	lc_loop:
	mov rdi, [r8 + 8 * rbx]	; load words[i] into rdi

	call rcx				; call compare words on rdi, rsi
	test rax, rax			; test rax
	setz r10b				; conditionally set r10 to 1
	add r11, r10			; add r10 to the count

	inc rbx					; increment i
	cmp rbx, r9				; test i < size
	jl lc_loop
	lc_end:

	mov rax, r11			; move count into rax
	ret



; rdi	->	words		-> cmp func a
; rsi	->	size		-> cmp func b
; rdx	->	word
; rcx	->	cmp function

; rax	->	cmp return
; rbx	->	i
; r8	->	words
; r9	->	size
; r10	->	lower_bound
; r11	->	upper_bound
; r12	->	upper_bound copy
binary_count:
	xor rax, rax			; clear return value
	mov r8, rdi				; word array
	mov r9, rsi				; word array size
	xor r10, r10			; clear r10
	mov r11, r9				; mov size into r11
	dec r11					; calculate size - 1
	mov rsi, rdx			; word a

	test r9, r9				; check if there are elements in the word array
	jz bc_end				; return if not

	bc_loop:
	mov rbx, r10			; move the lower_bound into rbx
	add rbx, r11			; add the upperbound to rbx
	shr rbx, 1				; divide rbx by 2

	mov rdi, [r8 + 8 * rbx]	; load words[i] into rdi
	call rcx				; call compare words on rdi, rsi
	test rax, rax			; test rax

	jz bc_hit				; jump to hit subroutine if words match
	cmovp r10, rbx			; move on parity even (-1 -> 0b11111111)
	cmovnp r11, rbx			; move on parity odd (-1 -> 0b11111111)

	; TODO: improve compare
	mov r12, r11			; copy upper_bound to r12
	sub r12, r10			; subtract lower_bound
	cmp r12, 1				; check if the difference is greater than 1
	jg bc_loop

	xor rax, rax			; clear return value if the word was not found
	ret

	bc_hit:
	mov r10, rbx			; move the hit location into lower_bound

	bc_hit_loop_low:
	dec r10					; decrement lower_bound
	test r10, r10			; check if lower_bound is still greater than 0
	js bc_hit_loop_low_end	; jump to loop end if not
	mov rdi, [r8 + 8 * r10]	; load words[i] into rdi
	call rcx				; call compare words on rdi, rsi
	test rax, rax			; test rax
	jz bc_hit_loop_low
	bc_hit_loop_low_end:

	mov r11, rbx			; move the hit location into upper_bound

	bc_hit_loop_high:
	inc r11					; increment upper_bound
	cmp r11, r9				; compare upper_bound to array size
	je bc_hit_loop_high_end	; jump to loop end if they are equal
	mov rdi, [r8 + 8 * r11]	; load words[i] into rdi
	call rcx				; call compare words on rdi, rsi
	test rax, rax			; test rax
	jz bc_hit_loop_high
	bc_hit_loop_high_end:

	mov rax, r11			; move upper_bound into return value
	sub rax, r10			; subtract lower_bound from return value
	dec rax					; decrement return value to correct for offset

	bc_end:
	ret