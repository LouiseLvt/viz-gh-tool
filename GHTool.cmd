@echo off
rem GHTool launcher: double-click this file (GHTool.ps1 must be in the same folder).
title GHTool - Viz Graphic Hub
powershell.exe -NoLogo -NoProfile -ExecutionPolicy Bypass -File "%~dp0GHTool.ps1" %*
if errorlevel 1 (
  echo.
  echo GHTool stopped with an error. Copy the message above.
  pause
)
