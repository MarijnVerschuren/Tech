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
binary_count:
	xor rax, rax
	mov r8, rdi
	mov r9, rsi
	xor r10, r10			; clear r10
	mov r11, r9				; mov size into r11
	dec r11					; calculate size - 1
	mov rsi, rdx			; word a

	test r9, r9
	jz bc_end

	bc_loop:
	mov rbx, r10
	add rbx, r11
	shr rbx, 1

	mov rdi, [r8 + 8 * rbx]	; load words[i] into rdi
	call rcx				; call compare words on rdi, rsi
	test rax, rax			; test rax

	jz bc_hit
	cmovp r10, rbx			; move on parity even (-1 -> 0b11111111)
	cmovnp r11, rbx			; move on parity odd (-1 -> 0b11111111)

	cmp r10, r11
	jne bc_loop

	xor rax, rax
	ret

	bc_hit:
	mov r10, rbx

	bc_hit_loop_low:
	dec r10
	test r10, r10
	js bc_hit_loop_low_end
	mov rdi, [r8 + 8 * r10]	; load words[i] into rdi
	call rcx				; call compare words on rdi, rsi
	test rax, rax			; test rax
	jz bc_hit_loop_low
	bc_hit_loop_low_end:

	mov r11, rbx

	bc_hit_loop_high:
	inc r11
	cmp r11, r9
	je bc_hit_loop_high_end
	mov rdi, [r8 + 8 * r11]	; load words[i] into rdi
	call rcx				; call compare words on rdi, rsi
	test rax, rax			; test rax
	jz bc_hit_loop_high
	bc_hit_loop_high_end:

	mov rax, r11
	sub rax, r10
	dec rax

	bc_end:
	ret