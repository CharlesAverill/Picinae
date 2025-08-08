#include <neorv32.h>
#include <stdint.h>

#define N_TRIALS 10
#define DELAY_CYCLES 2000000000ULL
#define BAUD_RATE 19200

#define printf neorv32_uart0_printf

uint64_t read_clock(void) {
	int cycles_low = neorv32_cpu_csr_read(CSR_MCYCLE);\
	int cycles_high = neorv32_cpu_csr_read(CSR_MCYCLEH);\
	return ((uint64_t)cycles_high << 32) | cycles_low;
}

int main(void) {
	neorv32_rte_setup();
	neorv32_uart0_setup(BAUD_RATE, 0);
	printf("NEORV32 Clock Frequency Measurement\n");

	// Do several trials
	for(int i = 0; i < N_TRIALS; i++) {
		printf("READY\n");

		// Delay
		neorv32_cpu_csr_write(CSR_MCYCLE, 0);
		neorv32_cpu_csr_write(CSR_MCYCLEH, 0);
		while(read_clock() < DELAY_CYCLES);

		printf("END\n");
	}
}
