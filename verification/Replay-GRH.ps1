[CmdletBinding()]
param(
    [Parameter(Mandatory)] [string] $CertificateDirectory,
    [Parameter(Mandatory)] [string] $Checker,
    [Parameter(Mandatory)] [string] $Zstd,
    [int] $Jobs = 8
)
$ErrorActionPreference = 'Stop'
$checkerPath = (Resolve-Path -LiteralPath $Checker).Path
$zstdPath = (Resolve-Path -LiteralPath $Zstd).Path
$base = (Resolve-Path -LiteralPath $CertificateDirectory).Path

# Source and checker revision are recorded beside this script in results.json.
$inputs = @(
    [pscustomobject]@{
        Name = 'challenge.ndjson'
        Long = 27
        CompressedHash = 'c24ef99dab3556a52c7fb886e03cf22a242f3b96f82ae4cc40539e5d2f678ac6'
        Hash = 'bd484ac9886a96f26b1d9a7a59ebd45b7a70d102c015d4f31f9302bbdd6ab2b9'
    }
    [pscustomobject]@{
        Name = 'solution.ndjson'
        Long = 30
        CompressedHash = '61a8938ad5f5e57397c1c0e3b954916af546d9004ade01c3555744a681b05381'
        Hash = '5ea74b912147c5c93cc2b6d70cc727cf908df2f62ac6a20480a3fa02f6be244e'
    }
)
foreach ($entry in $inputs) {
    $unpacked = Join-Path $base $entry.Name
    $packed = "$unpacked.zst"
    if ((Get-FileHash -LiteralPath $packed -Algorithm SHA256).Hash -ne $entry.CompressedHash) {
        throw "Compressed certificate checksum mismatch for $packed"
    }
    if (-not (Test-Path -LiteralPath $unpacked -PathType Leaf)) {
        & $zstdPath -q -d "--long=$($entry.Long)" $packed -o $unpacked
        if ($LASTEXITCODE -ne 0) { throw "Decompression failed for $packed" }
    }
    if ((Get-FileHash -LiteralPath $unpacked -Algorithm SHA256).Hash -ne $entry.Hash) {
        throw "Certificate checksum mismatch for $unpacked"
    }
    Write-Output "$($entry.Name) SHA256 $($entry.Hash)"
}
& python (Join-Path $PSScriptRoot 'check-axioms.py') (Join-Path $base $inputs[1].Name)
if ($LASTEXITCODE -ne 0) { throw 'Unexpected axiom in the GRH solution export.' }
& $checkerPath --verified "--jobs=$Jobs" '--progress=5%' --compare (Join-Path $base $inputs[0].Name) (Join-Path $base $inputs[1].Name)
if ($LASTEXITCODE -ne 0) { throw "GRH proof or statement check failed with exit code $LASTEXITCODE" }

