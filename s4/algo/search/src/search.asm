[bits 64]
section .text
	global linear_count
	global linear_count_a
	global binary_count_a
	extern compare_words



; rdi	->	text
; rsi	->	word
linear_count:
	xor rax, rax			; occurrence counter

	xor rbx, rbx			; 0 constant
	xor cl, cl				; char from text
	xor dl, dl				; char from word
	xor r8, r8				; word index
	xor r9, r9				; conditional additive

	lc_loop:
	mov cl, [rdi]			; current char from text
	mov dl, [rsi + r8]		; current char from word

	inc r8					; increment the word index
	cmp cl, dl
	cmovne r9, r8
	cmovne r8, rbx			; reset word index if chars are not the same

	cmp r9, 1
	setg r9b
	sub rdi, r9

	test dl, dl
	setz r9b
	add rax, r9
	sub rdi, r9

	inc rdi
	test cl, cl
	jnz lc_loop

	ret



; rdi	->	words		-> cmp func a
; rsi	->	size		-> cmp func b
; rdx	->	word

; rax	->	cmp return
; rbx	->	i
; rcx	->	count
; r8	->	words
; r9	->	size
; r10
linear_count_a:
	xor rbx, rbx			; set i to 0
	xor rcx, rcx			; set count to 0
	mov r8, rdi				; move word array into r8
	mov r9, rsi				; move size into r9
	mov rsi, rdx			; move word into rsi

	lca_loop:
	mov rdi, [r8 + 8 * rbx]	; load words[i] into rdi

	call compare_words		; call compare words on rdi, rsi
	test rax, rax			; test rax
	setz r10b				; conditionally set r10 to 1
	add rcx, r10			; add r10 to the count

	inc rbx					; increment i
	cmp rbx, r9				; test i < size
	jl lca_loop

	mov rax, rcx			; move count into rax
	ret



; rdi	->	words		-> cmp func a
; rsi	->	size		-> cmp func b
; rdx	->	word
binary_count_a:
	xor rax, rax
	ret