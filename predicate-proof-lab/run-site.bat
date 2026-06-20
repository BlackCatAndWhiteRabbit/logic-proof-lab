@echo off
cd /d "%~dp0"

set "NODE_CMD="
set "CODEX_NODE=%USERPROFILE%\.cache\codex-runtimes\codex-primary-runtime\dependencies\node\bin\node.exe"

where node >nul 2>nul
if %errorlevel%==0 set "NODE_CMD=node"

if not defined NODE_CMD (
  if exist "%CODEX_NODE%" set "NODE_CMD=%CODEX_NODE%"
)

if defined NODE_CMD (
  echo Predicate Proof Lab running at http://127.0.0.1:5600/
  "%NODE_CMD%" server.js
) else (
  echo Node.js was not found. Opening index.html directly instead.
  start "" "%~dp0index.html"
)

pause
