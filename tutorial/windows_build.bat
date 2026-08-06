@SET coqc="C:\Coq\bin\coqc.exe"
@SET coqdoc="C:\Coq\bin\coqdoc.exe"
@IF NOT EXIST %coqc% (
  @ECHO Error: %coqc% does not exist.
  @ECHO Please edit the first line of this batch file to point to coqc.exe.
  @GOTO ErrorExit
)
@IF NOT EXIST %coqdoc% (
  @ECHO Error: %coqdoc% does not exist.
  @ECHO Please edit the second line of this batch file to point to coqdoc.exe.
  @GOTO ErrorExit
)
@SET coqc=%coqc% -R .. Picinae
@SET coqdoc=%coqdoc% -R .. Picinae
%coqc% AbsAndPracs.v
%coqdoc% AbsAndPracs.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% BasicLoops.v
%coqdoc% BasicLoops.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Basics.v
%coqdoc% Basics.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Foundation.v
%coqdoc% Foundation.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% PicinaeAuto.v
%coqdoc% PicinaeAuto.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
%coqc% Preface.v
%coqdoc% Preface.v
@IF ERRORLEVEL 1 GOTO :ErrorExit
@ECHO Picinae build succeeded!
@GOTO Done
:ErrorExit
@ECHO Script failed with errors. Aborting.
:Done
@PAUSE
