#!/usr/bin/env python3
"""Upload a program to a NEORV32 board through its UART bootloader, run it,
and capture its UART output to a log file.

Example (binary search experiment, from its directory):

    python3 ../../../neorv32/run_on_board.py binary/neorv32_exe.bin measurements.txt \
        --build --stop-regex '^Len: ' --stop-count 1000

The board must be running the bootloader (or be at its auto-boot countdown).
If it is running some other program, press the board's reset button when
prompted. Requires pyserial (`pip install pyserial`).
"""

import argparse
import re
import subprocess
import sys
import time
from pathlib import Path

import serial

DEFAULT_PORT = '/dev/ttyUSB0'
DEFAULT_BAUD = 19200  # Must match BAUD_RATE in timing_experiments.h and the bootloader


class Board:
    def __init__(self, port, baud, verbose):
        self.ser = serial.Serial(port, baud, timeout=0.1)
        self.verbose = verbose
        self.pending = ''  # received text after the last read_until match

    def close(self):
        self.ser.close()

    def send(self, data):
        self.ser.write(data)
        self.ser.flush()

    def read_until(self, patterns, timeout, on_text=None):
        """Read until the received text contains one of `patterns`. Returns the
        matching pattern, or None on timeout. `on_text(buf)` is called on each
        new chunk and may send input to the board (e.g. to abort auto-boot).
        Text received after the match is kept for the next call."""
        buf, self.pending = self.pending, ''
        deadline = time.monotonic() + timeout
        while True:
            hits = [(buf.find(p), p) for p in patterns if p in buf]
            if hits:
                pos, p = min(hits)
                self.pending = buf[pos + len(p):]
                return p
            if time.monotonic() >= deadline:
                return None
            chunk = self.ser.read(256).decode(errors='replace')
            if not chunk:
                continue
            if self.verbose:
                sys.stdout.write(chunk)
                sys.stdout.flush()
            buf += chunk
            if on_text is not None:
                on_text(buf)


def enter_bootloader_console(board, timeout):
    """Get the bootloader to its `CMD:>` prompt."""
    aborted = [False]

    def abort_autoboot(buf):
        if not aborted[0] and 'Press any key' in buf:
            board.send(b' ')
            aborted[0] = True

    # 'r' restarts the bootloader if it is sitting at its prompt, and aborts the
    # auto-boot countdown if it is in that phase. Either way we end at CMD:>.
    board.ser.reset_input_buffer()
    board.pending = ''
    board.send(b'r')
    if board.read_until(['CMD:>'], 5, abort_autoboot):
        return
    print('\nBootloader not responding; press the reset button on the board.', file=sys.stderr)
    if not board.read_until(['CMD:>'], timeout, abort_autoboot):
        sys.exit('Timed out waiting for the bootloader prompt (check port, baud rate and cabling).')


def upload(board, image):
    data = Path(image).read_bytes()
    board.send(b'u')
    if not board.read_until(['Awaiting neorv32_exe.bin'], 5):
        sys.exit('Bootloader did not accept the upload command.')
    print(f'Uploading {image} ({len(data)} bytes)...', file=sys.stderr)
    for i in range(0, len(data), 128):
        board.send(data[i:i + 128])
    # Transfer time at 10 bits per byte plus margin
    wait = len(data) * 10 / board.ser.baudrate + 10
    result = board.read_until(['OK', 'ERROR_SIGNATURE', 'ERROR_DEVICE', 'ERROR_CHECKSUM'], wait)
    if result != 'OK':
        sys.exit(f'Upload failed: {result or "no response from bootloader"}')
    if not board.read_until(['CMD:>'], 5):
        sys.exit('Bootloader did not return to its prompt after upload.')


def run_and_capture(board, log_path, stop_regex, stop_count, idle_timeout, total_timeout, echo, stop_on_trap):
    board.pending = ''  # only the prompt's trailing space can be left here
    board.send(b'e')
    # The bootloader echoes the command and a newline before jumping to the
    # program; drop that echo from the head of the stream without discarding
    # any program output that arrives in the same read.
    echo_re = re.compile(r'^\s*e\r?\n')
    head = ''

    stop_re = re.compile(stop_regex) if stop_regex else None
    matches = 0
    n_lines = 0
    partial = ''
    start = last_rx = time.monotonic()
    reason = None
    trapped = False

    with open(log_path, 'w') as log:
        try:
            while True:
                chunk = board.ser.read(4096).decode(errors='replace')
                now = time.monotonic()
                if head is not None and chunk:
                    head += chunk
                    if '\n' not in head:
                        last_rx = now
                        continue
                    chunk, head = echo_re.sub('', head, count=1), None
                if chunk:
                    last_rx = now
                    log.write(chunk)
                    log.flush()
                    if echo:
                        sys.stdout.write(chunk)
                        sys.stdout.flush()
                    partial += chunk
                    *lines, partial = partial.split('\n')
                    n_lines += len(lines)
                    if stop_on_trap and any('<NEORV32-RTE>' in l for l in lines):
                        reason = 'program trapped (see <NEORV32-RTE> message in the log)'
                        trapped = True
                        break
                    if stop_re is not None:
                        matches += sum(1 for l in lines if stop_re.search(l.rstrip('\r')))
                        if matches >= stop_count:
                            reason = f'matched {stop_regex!r} {matches} times'
                            break
                elif idle_timeout and now - last_rx > idle_timeout:
                    reason = f'no output for {idle_timeout}s'
                    break
                if total_timeout and now - start > total_timeout:
                    reason = f'total timeout of {total_timeout}s reached'
                    break
        except KeyboardInterrupt:
            reason = 'interrupted'
        if head:  # output stopped before the first newline
            log.write(head)

    print(f'\nStopped ({reason}). Wrote {n_lines} lines to {log_path}.', file=sys.stderr)
    if trapped:
        return 2
    if stop_re is not None and matches < stop_count:
        print(f'Warning: expected {stop_count} lines matching {stop_regex!r}, saw {matches}.', file=sys.stderr)
        return 1
    return 0


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('image', help='Executable image to upload (neorv32_exe.bin)')
    p.add_argument('log_file', help='File to write the program\'s UART output to')
    p.add_argument('--port', default=DEFAULT_PORT, help=f'Serial port (default {DEFAULT_PORT})')
    p.add_argument('--baud', type=int, default=DEFAULT_BAUD, help=f'Baud rate (default {DEFAULT_BAUD})')
    p.add_argument('--build', action='store_true',
                   help='Run build.sh in the image\'s directory before uploading')
    p.add_argument('--stop-regex', help='Stop capturing once enough output lines match this regex')
    p.add_argument('--stop-count', type=int, default=1, help='Number of --stop-regex matches to wait for (default 1)')
    p.add_argument('--idle-timeout', type=float, default=30,
                   help='Stop after this many seconds without output; 0 disables (default 30)')
    p.add_argument('--timeout', type=float, default=0, help='Overall capture time limit in seconds; 0 disables')
    p.add_argument('--reset-timeout', type=float, default=60,
                   help='How long to wait for a manual board reset (default 60)')
    p.add_argument('--allow-traps', action='store_true',
                   help='Keep capturing after the runtime environment reports a trap/exception')
    p.add_argument('--quiet', action='store_true', help='Do not echo UART traffic to the terminal')
    args = p.parse_args()

    image = Path(args.image)
    if args.build:
        print(f'Building in {image.parent}...', file=sys.stderr)
        subprocess.run(['bash', './build.sh'], cwd=image.parent, check=True)
    if not image.is_file():
        sys.exit(f'{image} does not exist (build it first, or pass --build).')

    board = Board(args.port, args.baud, verbose=not args.quiet)
    try:
        enter_bootloader_console(board, args.reset_timeout)
        upload(board, image)
        print('Starting program, capturing output...', file=sys.stderr)
        rc = run_and_capture(board, args.log_file, args.stop_regex, args.stop_count,
                             args.idle_timeout, args.timeout, echo=not args.quiet,
                             stop_on_trap=not args.allow_traps)
    finally:
        board.close()
    sys.exit(rc)


if __name__ == '__main__':
    main()
