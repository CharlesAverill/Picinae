Burning and serial setup:
0. Set up USB BLASTER driver https://www.intel.com/content/www/us/en/support/programmable/support-resources/download/dri-usb-b-lnx.html
1. Put USB blaster into USB BLASTER serial port on board
2. Set SW11 to RUN
3. Compile CPU in quartus prime
4. Open Programmer, select board, burn chip onto board
5. Remove USB blaster from USB BLASTER serial port and place into UART TO USB port
6. `sudo minicom -s -D /dev/ttyUSB0 -b 19200`
7. Set Serial Port Setup > Hardware Flow Control to No
8. Save to configuration "neorv32", can ignore -s flag for minicom now if you provide neorv32 after baudrate

For compiling neorv32 example programs:
1. Download gcc from https://github.com/xpack-dev-tools/riscv-none-elf-gcc-xpack/releases
2. `make exe RISCV_PREFIX=<path-to-download/bin/riscv-none-elf-`

Uploading via minicom:
1. Select 'u' option at bootloader menu
2. Follow this procedure: https://www.dannysung.com/articles/linux/tips/sending-binary-files-via-minicom/ (copy available in clock_freq_measurement)
3. Ctrl-A S, select neorv32_exe.bin, upload
4. After upload, select 'e' option to execute

Uploading, running and logging automatically (instead of minicom):
1. Burn the CPU and connect the UART TO USB port as above (close minicom, it holds the port)
2. `pip install pyserial`
3. `python3 run_on_board.py <path/to/neorv32_exe.bin> <log file> [--build] [--port /dev/ttyUSB0]`
   The script gets the bootloader to its prompt (asks you to press reset if a program is
   running), uploads the image, starts it, and writes its UART output to the log file.
   Capture stops after --stop-count lines matching --stop-regex, or after --idle-timeout
   seconds without output (default 30). Example, from data_structures/array/binary_search:
     python3 ../../../neorv32/run_on_board.py binary/neorv32_exe.bin measurements.txt \
         --build --stop-regex '^Len: ' --stop-count 1000
     python3 compare_experiment_expected.py measurements.txt
