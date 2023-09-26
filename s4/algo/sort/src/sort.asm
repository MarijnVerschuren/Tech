[bits 64]
section .text
	global sort


;mov [rax], rsi
;mov [rax + 16], rsi
;mov [rax + 32], rsi
;mov [rax + 48], rsi
;mov [rax + 64], rsi

sort:
	xor rbx, rbx			; uint64_t j = 0;
	mov rcx, 1				; uint64_t i = 1;
	mov rdx, rsi			; move the array length into rdx

	loop_0:
	add qword [rax], 1

	loop_1:
	add qword [rax + 8], 1

	; for (; i < length - j; i++)
	inc rcx
	sub rdx, rbx			; calculate		(length - j)
	cmp rcx, rdx			; compare (i) and (length - j)
	jl loop_1				; jump only if (i) is less than (length - j)
	; for (; j < length; j++)
	inc rbx
	cmp rbx, rsi			; compare (j) and (length)
	jl loop_0				; jump only of (j) is less than (length)

	ret