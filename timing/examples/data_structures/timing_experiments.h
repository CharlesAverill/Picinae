#include <stdint.h>
#include <stdio.h>
#include <neorv32.h>

#define BAUD_RATE 19200
#define puts neorv32_uart0_puts

#define START_TIMER \
	{ neorv32_cpu_csr_write(CSR_MCYCLE, 0); }

#define PRINT_TIMER { \
	uint32_t cycles_low = neorv32_cpu_csr_read(CSR_MCYCLE); \
	uint32_t cycles_high = neorv32_cpu_csr_read(CSR_MCYCLEH); \
	uint64_t cycles = ((uint64_t)cycles_high << 32) | cycles_low; \
	char cycles_str[128]; \
	itoa(cycles, cycles_str, 10); \
	puts("Cycle count read: "); \
	puts(cycles_str); \
	puts("\n"); \
	neorv32_cpu_csr_write(CSR_MCYCLE, cycles); \
}
