---
name: Ghidra-to-Picinae-lifter
description: Uses the Ghidra reverse engineering platform to lift binary code to a Picinae program.
---

To lift binary code to a Picinae program that can be analyzed and verified, use the pcode2coq_headless.py script.  Let `Picinae` be the top level directory containing the project.  The script is `Picinae/tools/ghidra-lifter/pcode2coq_headless.py`.

To run the script you must use Ghidra's support tool `pyghidraRun`.  Typically, the system's Ghidra installation will be configured by the environment variable `GHIDRA_INSTALL_DIR` and the script will be `$GHIDRA_INSTALL_DIR/support/pyghidraRun`.  If it is not, you can find it using `find $HOME -name pyghidraRun`.

Binaries/functions should always be lifted with `--global-addressing` so they can compose and be used together to reason about caller-callee relationships.

For each binary you lift from, create a new file and name the lifted file after the function that is lifted---exclude the binary name from the file.

A typical invocation will look like so:


```
$GHIDRA_INSTALL_DIR/support/pyghidraRun --headless \
  ~/research/ghidra_projects mass_lifting \
  -process libgmp.so.10.5.0 \
  -noanalysis \
  -scriptPath "Picinae/tools/ghidra-lifter" \
  -postScript pcode2coq_headless.py \
    --functionRegex '(mpn_(add|sub)_nc|copyi|add_n_sub_n)' \
    --typeCheck \
    --globalAddressing \
    --outputDir "Picinae/Examples/libgmp.so.10.5.0"
```

  Where `mass_lifting` is the user's pre-existing project for mass lifting, located in their ghidra_projects directory.  The binary to lift from is given by `-process`, e.g., `libgmp.so.10.5.0` in this case. `-noanalysis` is useful if you know the binary has already been analyzed in the project, otherwise omit it to allow Ghidra to disassemble it.  The `-scriptPath` needs to point to the script and may change depending on where Picinae is located on the user's system.  `--functionRegex` is useful for lifting multiple functions at once, saving time.  It gets compiled by Python's `re` module.  And the `outputDir` should be a subdir of Examples named after the binary the functions came from.

The `--prependProgName` and `--interleave` flags are available should the user request them, but are unset by default.


If Ghidra lifts a new architecture element that is not in the corresponding architecture's architecture specification, i.e., it has no `var` constructor, then you will need to add that constructor and its associated bitwidth in the typctx of the architecture file.  Make sure to mark it as a Ghidra compatibility `var`.  Its bitwidth should be the bitwidth of the first expression assigned to it.  The variable then needs to be added to the file `translationConstants.py` in the appropriate architecture to be recognized by the lifter.


