param([string]$Distro = "Ubuntu-24.04")
$ErrorActionPreference = "Stop"
$Root = (Resolve-Path (Join-Path $PSScriptRoot '..\..')).Path
Get-Content (Join-Path $Root 'MANIFEST.sha256') | ForEach-Object {
  if ($_ -match '^([0-9a-f]{64})  (.+)$') {
    $actual = (Get-FileHash -Algorithm SHA256 (Join-Path $Root $Matches[2])).Hash.ToLowerInvariant()
    if ($actual -ne $Matches[1]) { throw "manifest mismatch: $($Matches[2])" }
  }
}
Write-Output 'SGH_MANIFEST_VERIFIED=true'
if ($Root -notmatch '^([A-Za-z]):\\(.*)$') { throw "Expected an absolute Windows path: $Root" }
$Drive = $Matches[1].ToLowerInvariant()
$Rest = $Matches[2].Replace('\', '/')
$RootWsl = "/mnt/$Drive/$Rest"
$ToolPath = "/home/f4verify/.elan/toolchains/leanprover--lean4---v4.31.0/bin:" +
            "/home/f4verify/.opam/easycrypt/bin:" +
            "/home/f4verify/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin:" +
            "/usr/local/bin:/usr/bin:/bin"
$Run = "cd '$RootWsl' && bash audit/F4/replay_public_v1.sh"
& wsl.exe -d $Distro -- env HOME=/home/f4verify "PATH=$ToolPath" bash -lc $Run
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
