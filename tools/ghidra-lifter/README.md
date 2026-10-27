# pcode2coq

## Setup
0. Install Ghidra 11.4+; previous versions of Ghidra require pyhidra. For those instructions see past versions of the README.
1. Clone this project or extract the released tarball
2. Launch Ghidra through the support/pyghidraRun script in Ghidra's directory.
3. Add this project's path to Ghidra's script manager like so: Display Script Manager > Manage Script Directories > Add (plus button)
    * Optional: Bind hotkey in script manager for running pcode2coq (ex: Ctrl-Shift-P)
4. pcode2coq.py will appear in your Script Manager (under Scripts/PCode)

## Usage
We assume the user is familiar with Ghidra.

1. Import and analyze the binary in Ghidra
2. Click on any line within the target function
3. Run pcode2coq.py from the Script Manager
4. Answer the prompts (unless using saved defaults)
5. Result(s) can be found in `<path to project>/output/<lifted binary>.v`
6. Done! Load the new rocq program (.v) with Picinae
    * You might have to move the .v file to the same directory as Picinae.

You can run it headlessly with Ghidra using the pyghidraRun script.  This makes it easier to iterate, as the GUI only refreshes the entry file.  It does not update the dependencies while it is running.  E.g., if you add a new architecture in translationConstants.py, you need to close and reopen Ghidra before lifting to it.

Below is an example of running the headless script headlessly to extract a few functions from an already analyzed libgmp.so.  Change the paths as necessary for your system.

```
~/ghidra_12.0_PUBLIC/support/pyghidraRun --headless \
  ~/ghidra_projects my_lifting_project \
  -process libgmp.so.10.5.0 \
  -noanalysis \
  -scriptPath "$HOME/pcode2coq" \
  -postScript pcode2coq_headless.py \
    --functionRegex '(mpn_(add|sub)_nc|copyi|add_n_sub_n)' \
    --typeCheck \
    --globalAddressing \
    --outputDir "$HOME/pcode2coq/output/libgmp"
```
```
```

## Troubleshooting

### ebpf binaries don't load in Ghidra
Disable "Perform Symbol Relocations" in the Import Options

## Example Lift Screenshots
![alt text](screenshots/scriptdir.png "Script Manager")
![alt text](screenshots/running1.png "Prompt 1")
![alt text](screenshots/running2.png "Prompt 2")
![alt text](screenshots/consoleresult.png "Result")
