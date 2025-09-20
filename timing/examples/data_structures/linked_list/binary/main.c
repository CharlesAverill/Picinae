#include "linked_list.h"

int main() {
    neorv32_rte_setup();
    neorv32_uart0_setup(BAUD_RATE, 0);

    insert_after_pos_in_list(NULL, NULL, 0);
    find_in_list(NULL, 0);
    insert_in_sorted_list(NULL, NULL);

    return 0;
}

