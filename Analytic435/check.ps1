$ErrorActionPreference = 'Stop'
$projectRoot = $PSScriptRoot
$portable = Join-Path (Split-Path -Parent (Split-Path -Parent $projectRoot)) '.environment'
$bin = Join-Path $portable 'lean-4.35.0-windows/bin'
$checkers = Join-Path $portable 'lean-4.36.0-windows/bin'
$env:PATH = "$bin;$env:PATH"
$env:ELAN_HOME = Join-Path $portable 'elan'
$env:TEMP = Join-Path $portable 'tmp'
$env:TMP = $env:TEMP
$env:LAKE_CACHE_DIR = Join-Path $portable 'cache/lake435'
$env:MATHLIB_CACHE_DIR = Join-Path $portable 'cache/mathlib435'
$env:XDG_CACHE_HOME = Join-Path $portable 'cache'
$env:MATHLIB_NO_CACHE_ON_UPDATE = '1'
$lake = Join-Path $bin 'lake.exe'
Push-Location -LiteralPath $projectRoot
try {
    & $lake --wfail build AnalyticAudit
    if ($LASTEXITCODE -ne 0) { throw 'Analytic proof build failed.' }
    foreach ($source in (Get-ChildItem -LiteralPath $projectRoot -Filter '*.lean' | Sort-Object Name)) {
        & $lake env lean -DwarningAsError=true $source.FullName
        if ($LASTEXITCODE -ne 0) { throw "Lean rejected $($source.Name)." }
    }
    $targets = @('some_actual_S_iff', 'broad_projection', 'half_cross_vanish', 'smooth_class_bound',
                 'character_gram', 'mixed_kernel_norms', 'doubled_quadratic', 'actual_transfer', 'cofinal_prime_lower',
                 'physical_AP', 'R_forces_shifts', 'S_forces_shifts', 'large_shift', 'cofinal_growth',
                 'refute_R', 'refute_S', 'prescribed_failure', 'all_local_of_primitive',
                 'norm_lower_on_original', 'cofinal_original_zeros', 'primitive_GRH_spectral_consequences', 'common_zero_sequence',
                 'guaranteed_width_and_log_gap', 'no_admissible_S_iff', 'arbitrarily_large_test',
                 'arithmeticH_admissible', 'arithmetic_width_decay', 'arithmetic_width_refuted',
                 'paper_GRH_iff', 'paper_spectral_consequences')
    $targets = @($targets | ForEach-Object { "GoldbachSpectral435.$_" })
    $targets += @('signed_matrix_lower', 'transpose', 'row_tests', 'sample_data', 'variation_bound', 'growing_rows') | ForEach-Object { "GoldbachSpectral.BandSieve.$_" }
    $export = Join-Path $projectRoot '.lake/build/AnalyticAudit.ndjson'
    $arguments = @('env', 'leanexport', 'AnalyticAudit', '--') + $targets
    $exportLog = Join-Path $projectRoot '.lake/build/AnalyticAudit-export.log'
    $process = Start-Process -FilePath $lake -ArgumentList $arguments -WindowStyle Hidden -Wait -PassThru -RedirectStandardOutput $export -RedirectStandardError $exportLog
    if ($process.ExitCode -ne 0 -or (Get-Item -LiteralPath $export).Length -eq 0) {
        throw "Proof export failed with exit code $($process.ExitCode). $(Get-Content -LiteralPath $exportLog -Raw)"
    }
    & (Join-Path $checkers 'leanchecker.exe') --from-export $export
    if ($LASTEXITCODE -ne 0) { throw 'Kernel replay failed.' }
    & (Join-Path $checkers 'lean4lean.exe') --import $export
    if ($LASTEXITCODE -ne 0) { throw 'lean4lean replay failed.' }
    & (Join-Path $checkers 'con-leche.exe') --verified $export
    if ($LASTEXITCODE -ne 0) { throw 'con-leche replay failed.' }
    $config = Join-Path $projectRoot '.lake/build/nanoda.json'
    [IO.File]::WriteAllText($config, (@{export_file_path = $export; permitted_axioms = @('propext','Classical.choice','Quot.sound');
        unpermitted_axiom_hard_error = $true; nat_extension = $true; string_extension = $true; num_threads = 4} | ConvertTo-Json))
    & (Join-Path $checkers 'nanoda_bin.exe') $config
    if ($LASTEXITCODE -ne 0) { throw 'nanoda replay failed.' }
    Write-Output ((Get-FileHash -LiteralPath $export -Algorithm SHA256).Hash)
    Write-Output 'Lean, lean4lean, con-leche and nanoda accepted the same export.'
} finally {
    Pop-Location
}

