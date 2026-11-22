// Entry and exit templates of the native arm64 co-simulation harness (see harness.c).
// Both are copied into the executable code page, around the instructions under test:
//
//   CODE + 0     entry_tmpl  (called from C as void entry(struct ctx *); ends with a `b` to TEST,
//                             patched by the harness)
//   TEST         the instructions under test (fall through to EXIT at the end)
//   EXIT         exit_tmpl   (its literal `exit_ctx` is patched with the address of the context)
//
// struct ctx (all 8-byte words): x[0..30] at 0, sp at 248, nzcv at 256, host sp at 264,
// host tpidr_el0 at 272, host x19..x30 at 280..375.
        .text
        .global entry_tmpl, entry_tmpl_end, exit_tmpl, exit_tmpl_lit, exit_tmpl_end
        .p2align 2
entry_tmpl:
        stp     x19, x20, [x0, #280]
        stp     x21, x22, [x0, #296]
        stp     x23, x24, [x0, #312]
        stp     x25, x26, [x0, #328]
        stp     x27, x28, [x0, #344]
        stp     x29, x30, [x0, #360]
        mov     x1, sp
        str     x1, [x0, #264]
        mrs     x1, tpidr_el0
        str     x1, [x0, #272]
        ldr     x1, [x0, #256]
        msr     nzcv, x1
        ldr     x1, [x0, #248]
        mov     sp, x1
        ldp     x1, x2, [x0, #8]
        ldp     x3, x4, [x0, #24]
        ldp     x5, x6, [x0, #40]
        ldp     x7, x8, [x0, #56]
        ldp     x9, x10, [x0, #72]
        ldp     x11, x12, [x0, #88]
        ldp     x13, x14, [x0, #104]
        ldp     x15, x16, [x0, #120]
        ldp     x17, x18, [x0, #136]
        ldp     x19, x20, [x0, #152]
        ldp     x21, x22, [x0, #168]
        ldp     x23, x24, [x0, #184]
        ldp     x25, x26, [x0, #200]
        ldp     x27, x28, [x0, #216]
        ldp     x29, x30, [x0, #232]
        ldr     x0, [x0]
        b       .               // patched: b TEST
entry_tmpl_end:

        .p2align 3
exit_tmpl:
        msr     tpidr_el0, x0
        ldr     x0, exit_tmpl_lit
        stp     x1, x2, [x0, #8]
        stp     x3, x4, [x0, #24]
        stp     x5, x6, [x0, #40]
        stp     x7, x8, [x0, #56]
        stp     x9, x10, [x0, #72]
        stp     x11, x12, [x0, #88]
        stp     x13, x14, [x0, #104]
        stp     x15, x16, [x0, #120]
        stp     x17, x18, [x0, #136]
        stp     x19, x20, [x0, #152]
        stp     x21, x22, [x0, #168]
        stp     x23, x24, [x0, #184]
        stp     x25, x26, [x0, #200]
        stp     x27, x28, [x0, #216]
        stp     x29, x30, [x0, #232]
        mrs     x1, tpidr_el0
        str     x1, [x0]
        mov     x1, sp
        str     x1, [x0, #248]
        mrs     x1, nzcv
        str     x1, [x0, #256]
        ldr     x1, [x0, #264]
        mov     sp, x1
        ldr     x1, [x0, #272]
        msr     tpidr_el0, x1
        ldp     x19, x20, [x0, #280]
        ldp     x21, x22, [x0, #296]
        ldp     x23, x24, [x0, #312]
        ldp     x25, x26, [x0, #328]
        ldp     x27, x28, [x0, #344]
        ldp     x29, x30, [x0, #360]
        ret
        .p2align 3
exit_tmpl_lit:
        .quad   0
exit_tmpl_end:
        .section .note.GNU-stack,"",@progbits
