param(
    [string]$NativeCheckout = "C:\Users\Raphael\AppData\Local\Temp\linka-f4-hax-current-20261119",
    [string]$Distro = "Ubuntu-24.04"
)

$ErrorActionPreference = "Stop"
function Convert-ToWslPath([string]$WindowsPath) {
    $Resolved = (Resolve-Path $WindowsPath).Path
    if ($Resolved -notmatch '^([A-Za-z]):\\(.*)$') {
        throw "Expected an absolute Windows drive path: $Resolved"
    }
    $Drive = $Matches[1].ToLowerInvariant()
    $Rest = $Matches[2].Replace('\', '/')
    return "/mnt/$Drive/$Rest"
}

$ProofWsl = Convert-ToWslPath (Join-Path $PSScriptRoot "..\..")
$NativeWsl = Convert-ToWslPath $NativeCheckout

$ToolPath = "/home/f4verify/.elan/toolchains/leanprover--lean4---v4.31.0/bin:" +
            "/home/f4verify/.opam/easycrypt/bin:" +
            "/home/f4verify/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin:" +
            "/usr/local/bin:/usr/bin:/bin"
$Run = "cd '$ProofWsl' && F4_GIT='/mnt/c/Program Files/Git/cmd/git.exe' " +
       "bash audit/F4/replay_global_v1.sh '$NativeWsl'"

& wsl.exe -d $Distro -- env `
    HOME=/home/f4verify `
    CARGO_HOME=/home/f4verify/.cargo `
    CARGO_TARGET_DIR=/home/f4verify/.cache/f4-current-target `
    "PATH=$ToolPath" `
    bash -lc $Run

if ($LASTEXITCODE -ne 0) {
    exit $LASTEXITCODE
}
