@SET coqc="C:\Coq\bin\coqc.exe"
@IF NOT EXIST %coqc% (
  @ECHO Error: %coqc% does not exist.
  @ECHO Please edit the first line of this batch file to point to coqc.exe.
  @GOTO ErrorExit
)
@SET coqc=%coqc% -R .. Picinae

%coqc% i386_strcmp.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% i386_strlen.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% arm7_strlen.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% i386_wcsspn.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% arm7_memset.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% arm8_strcasecmp.v
@IF ERRORLEVEL 1 GOTO :ErrorExit

%coqc% i386_strcmp_proof.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% i386_strlen_proof.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% arm7_strlen_proof.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% i386_wcsspn_proof.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% arm7_memset_proof.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% arm8_strcasecmp_proof.v
@IF ERRORLEVEL 1 GOTO :ErrorExit

@ECHO Picinae tests succeeded!
@GOTO Done
:ErrorExit
@ECHO Script failed with errors. Aborting.
:Done
@PAUSE
