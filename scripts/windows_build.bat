@SET coqc="C:\Coq\bin\coqc.exe"
@IF NOT EXIST %coqc% (
  @ECHO Error: %coqc% does not exist.
  @ECHO Please edit the first line of this batch file to point to coqc.exe.
  @GOTO ErrorExit
)
@SET coqc=%coqc% -R . Picinae
%coqc% Picinae_core.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_theory.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_statics.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_finterp.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_simplifier_base.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_simplifier_v0.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_simplifier_v1_1.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_ISA.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_i386.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_armv7.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_riscv.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_amd64.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Picinae_armv8_pcode.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
@ECHO Picinae build succeeded!
@GOTO Done
:ErrorExit
@ECHO Script failed with errors. Aborting.
:Done
@PAUSE
