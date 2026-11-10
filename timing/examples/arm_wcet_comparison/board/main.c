/*
 * On-board driver for measuring the arm_wcet_comparison functions on the
 * STM32F072B-DISCO.
 *
 * The board's ST-LINK/V2 has no virtual COM port, so the host talks to this
 * program through RAM over SWD (see run_on_board.py): it fills in `mbox` and
 * bumps cmd_seq, this program measures inputs [start, start+count) of one
 * benchmark into `recs`, then sets done_seq = cmd_seq.
 *
 * Input i of each benchmark is a deterministic function of i, so a batch can
 * be rerun on its own. Each input is measured `reps` times, rebuilding any
 * state the function mutates before every repetition, and min/max cycles are
 * recorded; min != max flags interference (none is expected: interrupts are
 * off, there is no DMA, and nothing else touches the bus except SWD reads).
 *
 * Clock: the reset default, 8 MHz HSI, flash at 0 wait states. This is the
 * configuration CortexM0NoWait.v describes (SYSCLK <= 24 MHz).
 */
#include <stdint.h>
#include <stddef.h>

/* ---------------- functions under test (unmodified objects) ---------------- */

typedef struct list_node {
    uint32_t value;
    struct list_node *next;
} list_node;

int sum(int *arr, uint32_t size);
uint32_t while_true_break(uint32_t n);
uint16_t find(uint64_t *arr, uint16_t size, uint64_t key);
uint32_t collatz(uint16_t n);
list_node *find_in_list(list_node *l, uint32_t key);
void insert_after_pos_in_list(list_node *l, list_node *value, uint32_t position);
void insert_in_sorted_list(list_node *l, list_node *value);

/* cache.c's stuff() is linked but never run; it references rand(). */
int rand(void) { return 0; }

/* ---------------- harness.S ---------------- */

struct call { uint32_t fn, r0, r1, r2, r3, ret; };
uint32_t measure_call(struct call *c);
extern char measure_call_ret[];

void stub_bx(void), stub_nop1(void), stub_nop8(void), stub_ldr(void),
     stub_str(void), stub_ldm1(void), stub_ldr_pc(void), stub_muls(void),
     stub_uxth(void), stub_b(void), stub_beq_taken(void),
     stub_beq_not_taken(void), stub_push_pop2(void), stub_push_pop3(void),
     stub_bl(void);

/* ---------------- registers ---------------- */

#define REG(a) (*(volatile uint32_t *)(a))
#define SYST_CSR   REG(0xE000E010)
#define SYST_RVR   REG(0xE000E014)
#define SYST_CVR   REG(0xE000E018)
#define SYST_CALIB REG(0xE000E01C)
#define FLASH_ACR  REG(0x40022000)
#define RCC_CR     REG(0x40021000)
#define RCC_CFGR   REG(0x40021004)
#define DBGMCU_IDCODE REG(0x40015800)

/* ---------------- host interface ---------------- */

#define MAGIC   0x54494D45u  /* "TIME" */
#define VERSION 1u
#define MAXREC  128
#define NBENCH  8

enum { B_CALIB, B_SUM, B_WTB, B_FIND, B_COLLATZ, B_FIND_IN_LIST,
       B_INSERT_AFTER_POS, B_INSERT_IN_SORTED };

enum { ST_IDLE, ST_OK, ST_BAD_BENCH, ST_BAD_RANGE, ST_BASE_UNSTABLE };

struct mailbox {
    uint32_t magic, version;
    uint32_t cmd_seq, done_seq;           /* host bumps cmd_seq; we echo it */
    uint32_t bench, start, count, reps;   /* the command */
    uint32_t status;
    uint32_t base_min, base_max;          /* baseline delta seen so far */
    uint32_t maxrec, nbench;
    uint32_t counts[NBENCH];              /* number of inputs per benchmark */
    uint32_t fn_addr[NBENCH];             /* entry addresses, for checking */
    uint32_t flash_acr, rcc_cr, rcc_cfgr, syst_calib, idcode;
    uint32_t code_in_sram;
};

/* One measured input. in0..in2 are the parameters the timing model needs. */
struct record {
    uint32_t in0, in1, in2;
    uint32_t ret;     /* the function's return value (or a derived value) */
    uint32_t ok;      /* 1 if the result/side effect matched a C reference */
    uint32_t cmin, cmax;
};

volatile struct mailbox mbox;
volatile struct record recs[MAXREC];

/* ---------------- benchmark data (one shared area) ---------------- */

#define MAXLEN 1000
#define INT_MAX_U 0x7FFFFFFFu

static union {
    int      ints[MAXLEN];
    uint64_t u64[MAXLEN];
    list_node nodes[MAXLEN + 3];
} data;

static const uint32_t flash_word = 0xCAFEF00Du;
static uint32_t ram_word = 0x600DF00Du;

/* ---------------- deterministic inputs ---------------- */

static uint32_t mix(uint32_t x)
{
    x ^= x >> 16; x *= 0x7feb352du;
    x ^= x >> 15; x *= 0x846ca68bu;
    x ^= x >> 16;
    return x;
}

static uint32_t H(uint32_t i, uint32_t salt)
{
    return mix(i * 0x9E3779B9u ^ mix(salt + 0x51ED270Bu));
}

/* Unsigned modulo without __aeabi_uidivmod taking part in anything timed. */
static uint32_t umod(uint32_t a, uint32_t m) { return a % m; }

/* ---------------- measurement core ---------------- */

static uint32_t base_cycles;

static uint32_t measure_base(void)
{
    struct call c = { (uint32_t)measure_call_ret | 1u, 0, 0, 0, 0, 0 };
    return measure_call(&c);
}

/* Measure `fn` `reps` times; setup() (if any) restores state before each. */
static void measure(volatile struct record *r, void *fn,
                    uint32_t a0, uint32_t a1, uint32_t a2, uint32_t a3,
                    void (*setup)(void), uint32_t reps)
{
    uint32_t cmin = 0xFFFFFFFFu, cmax = 0;
    struct call c;
    for (uint32_t k = 0; k < reps; k++) {
        if (setup) setup();
        c.fn = (uint32_t)fn; c.r0 = a0; c.r1 = a1; c.r2 = a2; c.r3 = a3;
        uint32_t d = measure_call(&c) - base_cycles;
        if (d < cmin) cmin = d;
        if (d > cmax) cmax = d;
    }
    r->ret = c.ret;
    r->cmin = cmin;
    r->cmax = cmax;
}

/* ---------------- 0: calibration stubs ---------------- */

struct stub { void (*fn)(void); uint32_t r0, r1; };

static const struct stub stubs[] = {
    { stub_bx,            0, 0 },
    { stub_nop1,          0, 0 },
    { stub_nop8,          0, 0 },
    { stub_ldr,           (uint32_t)&ram_word, 0 },
    { stub_ldr,           (uint32_t)&flash_word, 0 },
    { stub_str,           (uint32_t)&ram_word, 0x600DF00Du },
    { stub_ldm1,          (uint32_t)&ram_word, 0 },
    { stub_ldr_pc,        0, 0 },
    { stub_muls,          0x12345, 0x6789 },
    { stub_uxth,          0x12345, 0 },
    { stub_b,             0, 0 },
    { stub_beq_taken,     0, 0 },
    { stub_beq_not_taken, 0, 0 },
    { stub_push_pop2,     0, 0 },
    { stub_push_pop3,     0, 0 },
    { stub_bl,            0, 0 },
};
#define NSTUBS (sizeof stubs / sizeof stubs[0])

static void run_calib(uint32_t i, volatile struct record *r, uint32_t reps)
{
    r->in0 = i; r->in1 = 0; r->in2 = 0;
    measure(r, (void *)stubs[i].fn, stubs[i].r0, stubs[i].r1, 0, 0, 0, reps);
    r->ok = 1;
}

/* ---------------- 1: sum ---------------- */

static void run_sum(uint32_t i, volatile struct record *r, uint32_t reps)
{
    uint32_t size = i;
    int ref = 0;
    for (uint32_t j = 0; j < size; j++) {
        data.ints[j] = (int)H(j, 1);
        ref += data.ints[j];
    }
    r->in0 = size; r->in1 = 0; r->in2 = 0;
    measure(r, (void *)sum, (uint32_t)data.ints, size, 0, 0, 0, reps);
    r->ok = (r->ret == (uint32_t)ref);
}

/* ---------------- 2: while_true_break ---------------- */

static void run_wtb(uint32_t i, volatile struct record *r, uint32_t reps)
{
    uint32_t n = i, ref = n;
    while (!(ref + ref >= ref * ref)) ref--;
    r->in0 = n; r->in1 = 0; r->in2 = 0;
    measure(r, (void *)while_true_break, n, 0, 0, 0, 0, reps);
    r->ok = (r->ret == ref);
}

/* ---------------- 3: find (uint64_t array) ----------------
 * i -> len = i/2, found = (i odd && len > 0). Element j has a unique high
 * word (low 10 bits = j); a not-found key's high word ends in 1023. Some
 * elements before the stopping point get the key's low word (partial matches,
 * which cost extra cycles); 1 input in 8 gets all of them.
 */
#define FIND_COUNT (2 * MAXLEN + 2)

static void run_find(uint32_t i, volatile struct record *r, uint32_t reps)
{
    uint32_t len = i >> 1;
    int found = (i & 1) && len > 0;
    for (uint32_t j = 0; j < len; j++) {
        uint32_t hi = (H(j, 31) & ~0x3FFu) | j;
        uint32_t lo = H(j, 32);
        data.u64[j] = ((uint64_t)hi << 32) | lo;
    }
    uint32_t idx = found ? umod(H(i, 33), len) : 0xFFFFFFFFu;
    uint64_t key = found ? data.u64[idx]
                         : ((uint64_t)((H(i, 34) & ~0x3FFu) | 1023u) << 32) | H(i, 35);
    uint32_t klo = (uint32_t)key;
    uint32_t stop = found ? idx : len;
    if (stop > 0) {
        if (umod(H(i, 37), 8) == 0) {
            for (uint32_t j = 0; j < stop; j++)
                data.u64[j] = (data.u64[j] & 0xFFFFFFFF00000000ull) | klo;
        } else {
            uint32_t np = umod(H(i, 36), (stop < 16 ? stop : 16) + 1);
            for (uint32_t k = 0; k < np; k++) {
                uint32_t p = umod(H(i, 40 + k), stop);
                data.u64[p] = (data.u64[p] & 0xFFFFFFFF00000000ull) | klo;
            }
        }
    }
    uint32_t pm = 0;
    for (uint32_t j = 0; j < stop; j++)
        if ((uint32_t)data.u64[j] == klo) pm++;

    r->in0 = len; r->in1 = idx; r->in2 = pm;
    measure(r, (void *)find, (uint32_t)data.u64, len,
            (uint32_t)key, (uint32_t)(key >> 32), 0, reps);
    r->ok = (r->ret == (found ? idx : 0xFFFFu));
}

/* ---------------- 4: collatz ---------------- */

static void run_collatz(uint32_t i, volatile struct record *r, uint32_t reps)
{
    uint16_t n = (uint16_t)i;
    uint32_t k;
    for (k = 0; k < 55000; k++) {
        n = (n % 2 == 0) ? (uint16_t)(n / 2) : (uint16_t)(3 * n + 1);
        if (n == 1) break;
    }
    uint32_t ref = (n == 1) ? k : 0;
    r->in0 = i; r->in1 = 0; r->in2 = 0;
    measure(r, (void *)collatz, i, 0, 0, 0, 0, reps);
    r->ok = (r->ret == ref);
}

/* ---------------- linked lists ---------------- */

static uint32_t ll_len;          /* nodes in the list under test */
static list_node *ll_value;      /* node being inserted */

static void build_list(uint32_t len)
{
    for (uint32_t j = 0; j < len; j++)
        data.nodes[j].next = (j + 1 < len) ? &data.nodes[j + 1] : NULL;
}

/* 5: find_in_list. i -> len = i/2 nodes with unique values, key found
 * (i odd, len > 0) at a pseudo-random index or absent. len 0 is NULL. */
#define FIL_COUNT (2 * MAXLEN + 2)

static void run_find_in_list(uint32_t i, volatile struct record *r, uint32_t reps)
{
    uint32_t len = i >> 1;
    int found = (i & 1) && len > 0;
    for (uint32_t j = 0; j < len; j++)
        data.nodes[j].value = (H(j, 51) & ~0x3FFu) | j;
    build_list(len);
    uint32_t idx = found ? umod(H(i, 52), len) : 0xFFFFFFFFu;
    uint32_t key = found ? data.nodes[idx].value : ((H(i, 53) & ~0x3FFu) | 1023u);
    list_node *head = len ? &data.nodes[0] : NULL;

    r->in0 = len; r->in1 = idx; r->in2 = 0;
    measure(r, (void *)find_in_list, (uint32_t)head, key, 0, 0, 0, reps);
    list_node *want = found ? &data.nodes[idx] : NULL;
    r->ok = (r->ret == (uint32_t)want);
    r->ret = r->ret ? (uint32_t)((list_node *)r->ret - data.nodes) : 0xFFFFFFFFu;
}

/* 6: insert_after_pos_in_list. i = 0: l = NULL; i = 1: value = NULL;
 * otherwise len = 1..1000 nodes, with pos = 0, in [1, len-1], len-1, or
 * >= len (sometimes 0xFFFFFFFF). */
#define IAP_COUNT (2 + 4 * MAXLEN)

static void setup_iap(void)
{
    build_list(ll_len);
    ll_value->value = 9999;
    ll_value->next = NULL;
}

static void run_insert_after_pos(uint32_t i, volatile struct record *r, uint32_t reps)
{
    uint32_t len, pos, kind;
    if (i < 2) {
        kind = i + 1; len = (i == 0) ? 0 : 1; pos = 0;
    } else {
        uint32_t j = i - 2, v = j & 3;
        kind = 0; len = j / 4 + 1;
        if (v == 0)      pos = 0;
        else if (v == 1) pos = len > 1 ? 1 + umod(H(i, 61), len - 1) : 1;
        else if (v == 2) pos = len - 1;
        else             pos = umod(H(i, 62), 8) == 0 ? 0xFFFFFFFFu
                                                       : len + umod(H(i, 63), 1000);
    }
    for (uint32_t j = 0; j < len; j++) data.nodes[j].value = j;
    ll_len = len;
    ll_value = &data.nodes[MAXLEN + 1];
    list_node *l = (kind == 1) ? NULL : &data.nodes[0];
    list_node *value = (kind == 2) ? NULL : ll_value;

    r->in0 = len; r->in1 = pos; r->in2 = kind;
    measure(r, (void *)insert_after_pos_in_list, (uint32_t)l, (uint32_t)value,
            pos, 0, setup_iap, reps);

    /* check the list after the last repetition */
    int ok = 1;
    if (kind != 0) {
        for (uint32_t j = 0; j < len; j++)
            ok &= data.nodes[j].next == ((j + 1 < len) ? &data.nodes[j + 1] : NULL);
    } else {
        uint32_t at = pos < len - 1 ? pos : len - 1;
        list_node *after = (at + 1 < len) ? &data.nodes[at + 1] : NULL;
        ok = data.nodes[at].next == ll_value && ll_value->next == after;
    }
    r->ok = ok;
    r->ret = 0;
}

/* 7: insert_in_sorted_list. A head node, k nodes with values 4, 8, .., 4k,
 * and an INT_MAX sentinel. i = 0: value is INT_MAX (the skip branch);
 * otherwise k = 0..1000, value pseudo-random in [0, 4k+8) or 4k+100. */
#define IIS_COUNT (1 + 2 * (MAXLEN + 1))

static void setup_iis(void)
{
    build_list(ll_len);
    ll_value->next = NULL;
}

static void run_insert_in_sorted(uint32_t i, volatile struct record *r, uint32_t reps)
{
    uint32_t k, val;
    if (i == 0) {
        k = 10; val = INT_MAX_U;
    } else {
        uint32_t j = i - 1;
        k = j / 2;
        val = (j & 1) ? 4 * k + 100 : umod(H(i, 71), 4 * k + 8);
    }
    uint32_t len = k + 2;
    data.nodes[0].value = 0;
    for (uint32_t m = 1; m <= k; m++) data.nodes[m].value = 4 * m;
    data.nodes[k + 1].value = INT_MAX_U;
    ll_len = len;
    ll_value = &data.nodes[MAXLEN + 2];
    ll_value->value = val;

    build_list(len);
    uint32_t d = 0;
    list_node *it = &data.nodes[0];
    if (val != INT_MAX_U)
        while (it->next->value <= val) { it = it->next; d++; }

    r->in0 = k; r->in1 = val; r->in2 = d;
    measure(r, (void *)insert_in_sorted_list, (uint32_t)&data.nodes[0],
            (uint32_t)ll_value, 0, 0, setup_iis, reps);

    list_node *after = &data.nodes[d + 1];
    r->ok = data.nodes[d].next == ll_value && ll_value->next == after;
    r->ret = 0;
}

/* ---------------- dispatch ---------------- */

typedef void (*runner)(uint32_t, volatile struct record *, uint32_t);

static const runner runners[NBENCH] = {
    run_calib, run_sum, run_wtb, run_find, run_collatz, run_find_in_list,
    run_insert_after_pos, run_insert_in_sorted,
};

static const uint32_t counts[NBENCH] = {
    NSTUBS, MAXLEN + 1, 1000, FIND_COUNT, 65536, FIL_COUNT, IAP_COUNT, IIS_COUNT,
};

/* Measure the baseline n times; returns 0 if it varied. */
static int check_base(uint32_t n)
{
    int stable = 1;
    for (uint32_t k = 0; k < n; k++) {
        uint32_t b = measure_base();
        if (b != base_cycles) stable = 0;
        if (b < mbox.base_min) mbox.base_min = b;
        if (b > mbox.base_max) mbox.base_max = b;
    }
    return stable;
}

static uint32_t run_batch(void)
{
    uint32_t b = mbox.bench, start = mbox.start, count = mbox.count;
    uint32_t reps = mbox.reps ? mbox.reps : 1;
    if (b >= NBENCH) return ST_BAD_BENCH;
    if (count > MAXREC || start > counts[b] || count > counts[b] - start)
        return ST_BAD_RANGE;
    if (!check_base(8)) return ST_BASE_UNSTABLE;
    for (uint32_t k = 0; k < count; k++)
        runners[b](start + k, &recs[k], reps);
    if (!check_base(8)) return ST_BASE_UNSTABLE;
    return ST_OK;
}

extern char _sibench[], _sbench[];

int main(void)
{
    __asm volatile ("cpsid i" ::: "memory");

    SYST_CSR = 0;
    SYST_RVR = 0x00FFFFFFu;
    SYST_CVR = 0;
    SYST_CSR = 0x5;   /* core clock, enabled, no interrupt */

    base_cycles = measure_base();
    mbox.base_min = 0xFFFFFFFFu;
    mbox.base_max = 0;
    check_base(64);

    mbox.version = VERSION;
    mbox.maxrec = MAXREC;
    mbox.nbench = NBENCH;
    for (int b = 0; b < NBENCH; b++) mbox.counts[b] = counts[b];
    mbox.fn_addr[B_CALIB] = (uint32_t)measure_call_ret;
    mbox.fn_addr[B_SUM] = (uint32_t)sum;
    mbox.fn_addr[B_WTB] = (uint32_t)while_true_break;
    mbox.fn_addr[B_FIND] = (uint32_t)find;
    mbox.fn_addr[B_COLLATZ] = (uint32_t)collatz;
    mbox.fn_addr[B_FIND_IN_LIST] = (uint32_t)find_in_list;
    mbox.fn_addr[B_INSERT_AFTER_POS] = (uint32_t)insert_after_pos_in_list;
    mbox.fn_addr[B_INSERT_IN_SORTED] = (uint32_t)insert_in_sorted_list;
    mbox.flash_acr = FLASH_ACR;
    mbox.rcc_cr = RCC_CR;
    mbox.rcc_cfgr = RCC_CFGR;
    mbox.syst_calib = SYST_CALIB;
    mbox.idcode = DBGMCU_IDCODE;
    mbox.code_in_sram = ((uintptr_t)_sibench != (uintptr_t)_sbench);
    mbox.status = ST_IDLE;
    mbox.done_seq = mbox.cmd_seq;
    mbox.magic = MAGIC;

    for (;;) {
        while (mbox.cmd_seq == mbox.done_seq) { }
        uint32_t seq = mbox.cmd_seq;
        mbox.status = run_batch();
        mbox.done_seq = seq;
    }
}
