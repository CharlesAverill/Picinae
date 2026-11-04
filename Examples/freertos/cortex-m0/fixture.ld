/* Generic extraction memory map, not a claim of support for a particular board. */
ENTRY(Reset_Handler)
MEMORY {
    FLASH (rx)  : ORIGIN = 0x00000000, LENGTH = 256K
    RAM   (rwx) : ORIGIN = 0x20000000, LENGTH = 64K
}
_estack = ORIGIN(RAM) + LENGTH(RAM);
SECTIONS {
    .isr_vector : { KEEP(*(.isr_vector)) } > FLASH
    .text : { *(.text .text.*) *(.rodata .rodata.*) . = ALIGN(4); } > FLASH
    .ARM.extab : { *(.ARM.extab*) } > FLASH
    .ARM.exidx : { *(.ARM.exidx*) } > FLASH
    .data : {
        . = ALIGN(8); _sdata = .; *(.data .data.*) . = ALIGN(8); _edata = .;
    } > RAM AT> FLASH
    _sidata = LOADADDR(.data);
    .bss (NOLOAD) : {
        . = ALIGN(8); _sbss = .; *(.bss .bss.* COMMON) . = ALIGN(8); _ebss = .;
    } > RAM
    ASSERT(_ebss + 4096 <= _estack, "Insufficient main stack reserve")
    /DISCARD/ : { *(.note.GNU-stack) }
}
