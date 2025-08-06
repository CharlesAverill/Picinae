import serial
import time
import statistics
import subprocess

# Configuration
SERIAL_PORT = '/dev/ttyUSB0'  # Update to your serial port
BAUD_RATE = 19200
N_TRIALS = 10
DELAY_CYCLES = 2_000_000_000  # Must match the firmware constant
UPLOAD_SCRIPT = "~/bin/minicom_bin_upload"
UPLOAD_SCRIPT = subprocess.check_output(['bash', '-c', f'echo {UPLOAD_SCRIPT}']).decode().strip()
BINARY_FILE = "./neorv32_exe.bin"

# Build program
print("Building test program")
subprocess.run(["bash", "./build.sh"])

# Open serial connection
ser = serial.Serial(SERIAL_PORT, BAUD_RATE, timeout=20)

# Send space to get out of auto-boot
print("Breaking out of auto-boot")
ser.write(b'r')
time.sleep(1)
ser.write(b' ')

# Start program upload
line = ""
while "e: Start executable" not in line:
    print(f"[{line}]")
    line = ser.readline().decode(errors='ignore').strip()
time.sleep(1)
print("Starting program upload")
ser.write(b'u')
time.sleep(1)
print(f"[{ser.readline().decode(errors='ignore').strip()}]")
subprocess.run([UPLOAD_SCRIPT, '-i', BINARY_FILE, '-o', SERIAL_PORT], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

frequencies = []

trial = 0
start_time = None

# Start program execution
print("Upload complete, starting test")
time.sleep(1)
ser.write(b'e')

while trial < N_TRIALS:
    try:
        line = ser.readline().decode(errors='ignore').strip()
    except UnicodeDecodeError:
        continue  # Skip garbage bytes

    if not line:
        continue

    print(f"[{trial+1}] > {line}")

    if "READY" in line:
        start_time = time.perf_counter()

    elif "END" in line and start_time is not None:
        end_time = time.perf_counter()
        duration = end_time - start_time
        freq = DELAY_CYCLES / duration
        frequencies.append(freq)
        print(f"[{trial+1}] Duration: {duration:.6f} s | Frequency: {freq:.2f} Hz\n")
        start_time = None
        trial += 1

# Final summary
if frequencies:
    avg_freq = statistics.mean(frequencies)
    min_freq = min(frequencies)
    max_freq = max(frequencies)
    stdev_freq = statistics.stdev(frequencies) if len(frequencies) > 1 else 0.0

    print("=== Frequency Estimation Summary ===")
    print(f"Trials        : {N_TRIALS}")
    print(f"Avg Frequency : {avg_freq:.2f} Hz")
    print(f"Min Frequency : {min_freq:.2f} Hz")
    print(f"Max Frequency : {max_freq:.2f} Hz")
    print(f"Stdev         : {stdev_freq:.2f} Hz")
else:
    print("No trials completed. Check UART output or connection.")

