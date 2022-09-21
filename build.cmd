@echo off
for %%i in (".", "Basics", "BackwardProofs") do (
   call :processFolder %%i
)

goto :build
:processFolder
for %%i in (%1\*.lean) do (
   if not "%%i" == ".\lakefile.lean" (
      echo ==================== %%i
      echo alectryon --frontend lean4+markup %%i --backend webpage --lake lakefile.lean -o %%i.md
      alectryon.exe --frontend lean4+markup %%i --backend webpage --lake lakefile.lean -o %%i.md
   )
)
goto :eof

:build
mdbook build
rem start docs\index.html