"""Measure the arm_wcet_comparison functions on an STM32F072B-DISCO.

    python3 run_on_board.py [--mem flash|sram] [--flash] [--reps 3] [--bench NAME ...]

Plug the board in by CN1 (ST-LINK); needs OpenOCD (apt install openocd).
With --flash this builds the firmware (make MEM=...), checks it against the
analyzed ELFs and programs it; otherwise it resets the board and uses whatever
is already on it.

The board's ST-LINK/V2 has no serial port, so the host talks to the firmware
through RAM over SWD, using OpenOCD's Tcl RPC port; its memory accesses don't
halt the core. The host writes a command into `mbox`, waits for the firmware
to echo it, and reads back `recs`. Results go to results/<mem>/<bench>.csv, then compare.py summarizes
them against the Rocq models and aiT in results/<mem>/summary.txt.
"""
import argparse
import csv
import json
import socket
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path

import compare

HERE = Path(__file__).resolve().parent

BENCH_NAMES = ['calib', 'sum', 'while_true_break', 'find', 'collatz', 'find_in_list',
               'insert_after_pos_in_list', 'insert_in_sorted_list']
FN_SYMBOLS = ['measure_call_ret', 'sum', 'while_true_break', 'find', 'collatz',
              'find_in_list', 'insert_after_pos_in_list', 'insert_in_sorted_list']

MAGIC, VERSION = 0x54494D45, 1
STATUS = {0: 'idle', 1: 'ok', 2: 'bad bench', 3: 'bad range', 4: 'baseline unstable'}

# struct mailbox in main.c, as 32-bit words
MB_FIELDS = (['magic', 'version', 'cmd_seq', 'done_seq', 'bench', 'start', 'count', 'reps',
              'status', 'base_min', 'base_max', 'maxrec', 'nbench']
             + [f'counts{i}' for i in range(8)] + [f'fn_addr{i}' for i in range(8)]
             + ['flash_acr', 'rcc_cr', 'rcc_cfgr', 'syst_calib', 'idcode', 'code_in_sram'])
MB = {name: 4 * i for i, name in enumerate(MB_FIELDS)}
REC_WORDS = 7  # in0, in1, in2, ret, ok, cmin, cmax


def symbols(elf):
    out = subprocess.run(['arm-none-eabi-nm', elf], check=True, capture_output=True,
                         text=True).stdout
    return {p[2]: int(p[0], 16) for p in (l.split() for l in out.splitlines()) if len(p) == 3}


class OpenOCD:
    """An OpenOCD server for the board, driven over its Tcl RPC port."""

    PORT = 6666

    def __init__(self, log_path):
        # Log to a file: a pipe nobody reads fills up and blocks OpenOCD
        self.log_path = log_path
        self.log = open(log_path, 'w')
        self.proc = subprocess.Popen(
            ['openocd', '-f', 'interface/stlink.cfg', '-f', 'target/stm32f0x.cfg',
             '-c', f'tcl_port {self.PORT}', '-c', 'gdb_port disabled',
             '-c', 'telnet_port disabled'],
            stdout=self.log, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL)
        end = time.monotonic() + 10
        while True:
            try:
                self.sock = socket.create_connection(('127.0.0.1', self.PORT), timeout=60)
                break
            except OSError:
                if self.proc.poll() is not None or time.monotonic() > end:
                    self.close()
                    sys.exit(f'could not start OpenOCD:\n{Path(self.log_path).read_text()}')
                time.sleep(0.1)
        self.buf = b''

    def cmd(self, command):
        self.sock.sendall(command.encode() + b'\x1a')
        while b'\x1a' not in self.buf:
            chunk = self.sock.recv(65536)
            if not chunk:
                sys.exit('OpenOCD closed the connection')
            self.buf += chunk
        reply, _, self.buf = self.buf.partition(b'\x1a')
        return reply.decode().strip()

    def read_words(self, addr, n):
        words = []
        while len(words) < n:   # in chunks, to keep replies small
            k = min(1024, n - len(words))
            reply = self.cmd(f'read_memory 0x{addr + 4 * len(words):08x} 32 {k}')
            try:
                words += [int(w, 16) for w in reply.split()]
            except ValueError:
                sys.exit(f'OpenOCD read failed: {reply}')
        return words

    def write_word(self, addr, value):
        reply = self.cmd(f'write_memory 0x{addr:08x} 32 {{0x{value:08x}}}')
        if reply:
            sys.exit(f'OpenOCD write failed: {reply}')

    def close(self):
        try:
            self.cmd('shutdown')
        except Exception:
            pass
        try:
            self.proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self.proc.kill()
            self.proc.wait()
        self.log.close()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()


class Board:
    def __init__(self, ocd, mbox, recs):
        self.ocd = ocd
        self.mbox, self.recs = mbox, recs

    def read(self, field):
        return self.ocd.read_words(self.mbox + MB[field], 1)[0]

    def write(self, field, value):
        self.ocd.write_word(self.mbox + MB[field], value)

    def mailbox(self):
        return dict(zip(MB_FIELDS, self.ocd.read_words(self.mbox, len(MB_FIELDS))))

    def wait_ready(self, timeout=5.0):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            if self.read('magic') == MAGIC:
                return
            time.sleep(0.05)
        sys.exit('firmware did not start (no mailbox magic); is timing.bin flashed?')

    def run_batch(self, bench, start, count, reps, expect_s):
        self.write('bench', bench)
        self.write('start', start)
        self.write('count', count)
        self.write('reps', reps)
        seq = (self.read('cmd_seq') + 1) & 0xFFFFFFFF
        self.write('cmd_seq', seq)
        # Don't poll while the batch is likely still running: SWD reads share
        # the bus with the core. (Any stall would show up as cmin != cmax.)
        time.sleep(expect_s)
        deadline = time.monotonic() + 60 + 10 * expect_s
        while self.read('done_seq') != seq:
            if time.monotonic() > deadline:
                sys.exit(f'batch {BENCH_NAMES[bench]}[{start}:{start + count}] timed out')
            time.sleep(0.01)
        status = self.read('status')
        if status != 1:
            sys.exit(f'batch {BENCH_NAMES[bench]}[{start}:{start + count}] failed: '
                     f'{STATUS.get(status, status)}')
        words = self.ocd.read_words(self.recs, REC_WORDS * count)
        return [words[i:i + REC_WORDS] for i in range(0, len(words), REC_WORDS)]


def check_config(mb, syms, mem):
    problems = []
    if mb['version'] != VERSION:
        problems.append(f'firmware version {mb["version"]}, expected {VERSION}')
    for i, sym in enumerate(FN_SYMBOLS):
        if mb[f'fn_addr{i}'] & ~1 != syms[sym] & ~1:
            problems.append(f'{sym} is at 0x{mb[f"fn_addr{i}"]:08x} on the board but '
                            f'0x{syms[sym]:08x} in the ELF (stale firmware? use --flash)')
    if mb['code_in_sram'] != (mem == 'sram'):
        problems.append(f'board firmware runs code from {"SRAM" if mb["code_in_sram"] else "flash"}')
    if mb['flash_acr'] & 0x7 != 0:
        problems.append(f'flash latency is {mb["flash_acr"] & 7} wait states, expected 0')
    if (mb['rcc_cfgr'] >> 2) & 0x3 != 0:
        problems.append('SYSCLK is not the 8 MHz HSI')
    if mb['base_min'] != mb['base_max']:
        problems.append(f'baseline varies: {mb["base_min"]}..{mb["base_max"]}')
    if problems:
        sys.exit('board check failed:\n  ' + '\n  '.join(problems))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--mem', choices=['flash', 'sram'], default='flash',
                    help='where the measured code runs (default flash)')
    ap.add_argument('--flash', action='store_true', help='build, verify and flash first')
    ap.add_argument('--reps', type=int, default=3, help='repetitions per input (default 3)')
    ap.add_argument('--bench', nargs='+', choices=BENCH_NAMES, default=BENCH_NAMES)
    ap.add_argument('--out', type=Path, help='output directory (default results/<mem>)')
    args = ap.parse_args()

    elf = HERE / 'build' / args.mem / 'timing.elf'
    if args.flash:
        subprocess.run(['make', '-C', str(HERE), f'MEM={args.mem}', 'all', 'verify'],
                       check=True)
    elif not elf.exists():
        sys.exit(f'{elf} not found; run with --flash')
    syms = symbols(elf)
    out = args.out or HERE / 'results' / args.mem
    out.mkdir(parents=True, exist_ok=True)

    with OpenOCD(out / 'openocd.log') as ocd:
        if args.flash:
            reply = ocd.cmd(f'if {{[catch {{program {elf} verify}} e]}} '
                            f'{{return "FAILED: $e"}} else {{return OK}}')
            if reply != 'OK':
                sys.exit(f'programming failed: {reply}')
            print(f'programmed {elf.relative_to(HERE)}')
        board = Board(ocd, syms['mbox'], syms['recs'])
        # RAM survives reset: clear the old magic so we wait for the new boot
        ocd.cmd('halt')
        board.write('magic', 0)
        ocd.cmd('reset run')
        board.wait_ready()
        mb = board.mailbox()
        check_config(mb, syms, args.mem)
        base = mb['base_min']
        print(f'board ok: IDCODE 0x{mb["idcode"]:08x}, FLASH_ACR 0x{mb["flash_acr"]:08x}, '
              f'RCC_CFGR 0x{mb["rcc_cfgr"]:08x}, code in {args.mem}, '
              f'baseline {base} cycles')

        meta = {'date': datetime.now().isoformat(timespec='seconds'), 'mem': args.mem,
                'reps': args.reps, 'baseline_cycles': base,
                **{k: mb[k] for k in ('idcode', 'flash_acr', 'rcc_cr', 'rcc_cfgr',
                                      'syst_calib')}}
        for name in args.bench:
            b = BENCH_NAMES.index(name)
            total, maxrec = mb[f'counts{b}'], mb['maxrec']
            rows, t0, expect = [], time.monotonic(), 0.0
            for start in range(0, total, maxrec):
                count = min(maxrec, total - start)
                t = time.monotonic()
                rows += board.run_batch(b, start, count, args.reps, expect)
                # Next time, sleep for ~90% of this batch's duration before polling
                expect = 0.9 * (time.monotonic() - t)
                print(f'\r{name}: {len(rows)}/{total}', end='', flush=True)
            print(f'  ({time.monotonic() - t0:.1f} s)')
            with open(out / f'{name}.csv', 'w', newline='') as f:
                w = csv.writer(f)
                w.writerow(['in0', 'in1', 'in2', 'ret', 'ok', 'cmin', 'cmax'])
                w.writerows(rows)

        mb = board.mailbox()
        meta['baseline_min'], meta['baseline_max'] = mb['base_min'], mb['base_max']
        (out / 'meta.json').write_text(json.dumps(meta, indent=2) + '\n')
        if mb['base_min'] != mb['base_max']:
            print(f'WARNING: baseline varied during the run: {mb["base_min"]}..{mb["base_max"]}')

    print()
    print(compare.summarize(out))


if __name__ == '__main__':
    main()
