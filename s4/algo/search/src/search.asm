[bits 64]
section .text
	global linear_search
	global binary_search



; rdi	->	text
; rsi	->	word
linear_search:
	xor rax, rax			; occurrence counter

	xor rbx, rbx			; 0 constant
	xor cl, cl				; char from text
	xor dl, dl				; char from word
	xor r8, r8				; word index
	xor r9, r9				; conditional additive

	loop_0:
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
	jnz loop_0

	ret



; rdi	->	tree
; rsi	->	word
binary_search:
	xor rax, rax
	ret