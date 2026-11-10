/* Shared layout; link_flash.ld / link_sram.ld define MEMORY and BENCHMEM. */
_estack = ORIGIN(RAM) + LENGTH(RAM);

SECTIONS
{
    .isr_vector : { KEEP(*(.isr_vector)) } > FLASH

    /* The functions under test and the harness. Each object starts on a
       64-byte boundary, so every function has the same address mod 64 as in
       the ELF that aiT analyzed (where each object was linked at 0x08000000). */
    .bench : ALIGN(64) {
        _sbench = .;
        . = ALIGN(64); KEEP(*cache.o(.text .text.*))
        . = ALIGN(64); KEEP(*while_true_break.o(.text .text.*))
        . = ALIGN(64); KEEP(*arraysearch.o(.text .text.*))
        . = ALIGN(64); KEEP(*collatz.o(.text .text.*))
        . = ALIGN(64); KEEP(*linked_list.o(.text .text.*))
        . = ALIGN(64); KEEP(*harness.o(.text .text.*))
        . = ALIGN(4);
        _ebench = .;
    } > BENCHMEM AT > FLASH
    _sibench = LOADADDR(.bench);

    .text : {
        *(.text*)
        *(.rodata*)
        . = ALIGN(4);
    } > FLASH

    .data : {
        _sdata = .;
        *(.data*)
        . = ALIGN(4);
        _edata = .;
    } > RAM AT > FLASH
    _sidata = LOADADDR(.data);

    .bss (NOLOAD) : {
        _sbss = .;
        *(.bss*)
        *(COMMON)
        . = ALIGN(4);
        _ebss = .;
    } > RAM

    /* keep 1 KiB for the stack */
    ASSERT(_ebss + 1024 <= _estack, "RAM overflow")

    /DISCARD/ : { *(.ARM.exidx*) *(.ARM.attributes) }
}
