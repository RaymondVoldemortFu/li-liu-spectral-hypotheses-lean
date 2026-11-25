$ErrorActionPreference = 'Stop'
$projectRoot = $PSScriptRoot
$portable = Join-Path (Split-Path -Parent $projectRoot) '.environment'
$bin = Join-Path $portable 'lean-4.36.0-windows\bin'
$lake = Join-Path $bin 'lake.exe'
if (-not (Test-Path -LiteralPath $lake)) {
    throw "Expected the portable Lean 4.36.0 toolchain under $portable."
}

$env:PATH = "$bin;$env:PATH"
$env:TEMP = Join-Path $portable 'tmp'
$env:TMP = $env:TEMP
$env:ELAN_HOME = Join-Path $portable 'elan'
$env:XDG_CACHE_HOME = Join-Path $portable 'cache'
$env:MATHLIB_CACHE_DIR = Join-Path $portable 'cache\mathlib'
$env:LAKE_CACHE_DIR = Join-Path $portable 'cache\lake'
$env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
New-Item -ItemType Directory -Force -Path $env:TEMP | Out-Null

Push-Location -LiteralPath $projectRoot
try {
    & $lake build
    if ($LASTEXITCODE -ne 0) { throw 'Lake build failed.' }
    $sources = @(Get-ChildItem -Path 'SpectralTests' -Filter '*.lean' | Sort-Object Name | ForEach-Object FullName)
    foreach ($source in ($sources + 'SpectralTests.lean')) {
        & $lake env lean -DwarningAsError=true $source
        if ($LASTEXITCODE -ne 0) { throw "Lean rejected $source." }
    }
    & $lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Audit.olean Audit.lean
    if ($LASTEXITCODE -ne 0) { throw 'The independent statement or the axiom check failed.' }
    $outputDir = Join-Path $projectRoot '.lake\build'
    $export = Join-Path $outputDir 'Audit.ndjson'
    $targets = @('GoldbachSpectral.unconditional_shift', 'GoldbachSpectral.arithmetic_one_shift', 'GoldbachSpectral.arithmetic_obstruction', 'GoldbachSpectral.arithmetic_real_zeros', 'GoldbachSpectral.arithmetic_prescribed', 'GoldbachSpectral.Audit.as_printed', 'GoldbachSpectral.spectral_conclusions', 'GoldbachSpectral.prescribed_admissible', 'GoldbachSpectral.slow_compatibility', 'GoldbachSpectral.buchstab_drop', 'GoldbachSpectral.beta_samples_cancel', 'GoldbachSpectral.gap_cube', 'GoldbachSpectral.window_thresholds', 'GoldbachSpectral.factorial_window', 'GoldbachSpectral.checked_window', 'GoldbachSpectral.separated_spectrum', 'GoldbachSpectral.BandSieve.inclusion_exclusion', 'GoldbachSpectral.BandSieve.extra_layer', 'GoldbachSpectral.BandSieve.residue_discrepancy', 'GoldbachSpectral.BandSieve.weighted_discrepancy', 'GoldbachSpectral.BandSieve.prime_mass_windows', 'GoldbachSpectral.BandSieve.layer_population', 'GoldbachSpectral.BandSieve.signed_matrix_lower', 'GoldbachSpectral.BandSieve.transpose', 'GoldbachSpectral.BandSieve.row_tests', 'GoldbachSpectral.BandSieve.growing_rows', 'GoldbachSpectral.BandSieve.wheel_small', 'GoldbachSpectral.residue_row_witness', 'GoldbachSpectral.reflectedBeta_mass', 'GoldbachSpectral.reflectedBeta_support', 'GoldbachSpectral.real_zeros_from_gain', 'GoldbachSpectral.some_width_iff_decay')
    $exportArgs = @('env', 'leanexport', 'Audit', '--') + $targets
    $process = Start-Process -FilePath $lake -ArgumentList $exportArgs -WindowStyle Hidden -Wait -PassThru -RedirectStandardOutput $export
    if ($process.ExitCode -ne 0 -or (Get-Item -LiteralPath $export).Length -eq 0) {
        throw 'Proof export failed.'
    }
    & (Join-Path $bin 'leanchecker.exe') --from-export $export
    if ($LASTEXITCODE -ne 0) { throw 'Lean kernel replay failed.' }
    & (Join-Path $bin 'lean4lean.exe') --import $export
    if ($LASTEXITCODE -ne 0) { throw 'lean4lean replay failed.' }
    & (Join-Path $bin 'con-leche.exe') --verified $export
    if ($LASTEXITCODE -ne 0) { throw 'con-leche replay failed.' }

    $configPath = Join-Path $outputDir 'nanoda.json'
    $config = @{
        export_file_path = $export
        permitted_axioms = @('propext', 'Classical.choice', 'Quot.sound')
        unpermitted_axiom_hard_error = $true
        nat_extension = $true
        string_extension = $true
        num_threads = 4
    }
    [IO.File]::WriteAllText($configPath, ($config | ConvertTo-Json))
    & (Join-Path $bin 'nanoda_bin.exe') $configPath
    if ($LASTEXITCODE -ne 0) { throw 'nanoda replay failed.' }
    Write-Output ((Get-FileHash -Algorithm SHA256 -LiteralPath $export).Hash)
    Write-Output 'Lean, lean4lean, con-leche and nanoda accepted the same export.'
} finally {
    Pop-Location
}
