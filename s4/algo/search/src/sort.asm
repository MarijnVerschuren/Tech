[bits 64]
section .text
	global sort
	global cmp_words


; rax	->	ret from cmp
; rbx	->	j
; rcx	->	i
; rdx	->	cmp function 				-> unused
; rsi	->	arg 1 for cmp (array[i])
; rdi	->	arg 0 for cmp (array[i-1])
; r8	->	array
; r9	->	length
; r10	->	length - j
; r11	->	cmp function (rbx is cleared after calling cmp function)
sort:
	mov r8, rax				; move array to r8
	mov r9, rsi				; move length into r9
	mov r11, rdx			; move cmp function into r11
	xor rbx, rbx			; uint64_t j = 0;

	loop_0:
	mov rcx, 1				; uint64_t i = 1;
	mov r10, r9				; move the array length into rdi
	sub r10, rbx			; calculate		(length - j)

	loop_1:
	mov rdi, [r8 + rcx * 8]
	mov rsi, [r8 + (rcx - 1) * 8]
	call r11
	test rax, rax

	cmovp rdi, rsi					; move on parity even (-1 -> 0b11111111)
	cmovp rsi, [r8 + rcx * 8]		; move on parity even (-1 -> 0b11111111)
    mov [r8 + (rcx - 1) * 8], rsi
	mov [r8 + rcx * 8], rdi

	inc rcx					; i++
	cmp rcx, r10			; compare (i) and (length - j)
	jl loop_1				; jump only if (i) is less than (length - j)

	inc rbx					; j++
	cmp rbx, r9				; compare (j) and (length)
	jl loop_0				; jump only of (j) is less than (length)

	ret


; rax	->
; rdi	->	a
; rsi	->	b
cmp_words:
	vmovdqu ymm0, [rdi]
	vmovdqu ymm1, [rsi]
	vpminub ymm2, ymm0, ymm1
	vpcmpeqb ymm0, ymm0, ymm2
	vpcmpeqb ymm1, ymm1, ymm2
	vpsubb ymm0, ymm0, ymm1
	; vectorized code...
	movq rax, xmm0
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8

	pextrq rax, xmm0, 1
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8

	vextracti128 xmm0, ymm0, 1
	movq rax, xmm0
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8

	pextrq rax, xmm0, 1
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8
	test al, al
	jnz cmp_loop_end
	shr rax, 8

	cmp_loop_end:
	and rax, 0xff
	ret