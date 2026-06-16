# Analyze all sorries in the PF/ directory
# Categorize them for systematic elimination

Write-Host "=== PRINCIPIA FRACTALIS SORRY ANALYSIS ===" -ForegroundColor Cyan
Write-Host ""

$totalSorries = 0
$files = @{}

Get-ChildItem -Path "PF" -Filter "*.lean" -Recurse | ForEach-Object {
    $filePath = $_.FullName
    $fileName = $_.Name
    $content = Get-Content $filePath -Raw
    
    if ($content -match 'sorry') {
        $sorries = Select-String -Path $filePath -Pattern "\bsorry\b" -Context 3,1
        $count = $sorries.Count
        $totalSorries += $count
        
        $files[$fileName] = @{
            Path = $filePath
            Count = $count
            Sorries = $sorries
        }
    }
}

# Sort by count
$sortedFiles = $files.GetEnumerator() | Sort-Object { $_.Value.Count }

foreach ($file in $sortedFiles) {
    $name = $file.Key
    $data = $file.Value
    $count = $data.Count
    
    Write-Host "[$count] $name" -ForegroundColor Yellow
    
    foreach ($sorry in $data.Sorries) {
        $lineNum = $sorry.LineNumber
        $context = $sorry.Context.PreContext -join " "
        
        # Categorize
        $category = "COMPLEX"
        if ($context -match "numerical|certified|100\+ digits") {
            $category = "NUMERICAL"
        } elseif ($context -match "empirical|clinical|patient|observ") {
            $category = "EMPIRICAL"
        } elseif ($context -match "trivial|elementary|simple|algebraic") {
            $category = "SIMPLE"
        } elseif ($context -match "framework|operator|spectral theory") {
            $category = "FRAMEWORK"
        } elseif ($context -match "definition|placeholder|infrastructure") {
            $category = "DEFINITION"
        }
        
        $preview = $context -replace '\s+', ' ' | Select-Object -First 60
        Write-Host "  L$lineNum [$category]: $preview" -ForegroundColor Gray
    }
    Write-Host ""
}

Write-Host "=== SUMMARY ===" -ForegroundColor Cyan
Write-Host "Total files with sorries: $($files.Count)"
Write-Host "Total sorries: $totalSorries"
Write-Host ""

# Categorize by type
$numerical = 0
$empirical = 0
$simple = 0
$framework = 0
$definition = 0
$complex = 0

foreach ($file in $files.Values) {
    foreach ($sorry in $file.Sorries) {
        $context = $sorry.Context.PreContext -join " "
        if ($context -match "numerical|certified|100\+ digits") { $numerical++ }
        elseif ($context -match "empirical|clinical|patient|observ") { $empirical++ }
        elseif ($context -match "trivial|elementary|simple|algebraic") { $simple++ }
        elseif ($context -match "framework|operator|spectral theory") { $framework++ }
        elseif ($context -match "definition|placeholder|infrastructure") { $definition++ }
        else { $complex++ }
    }
}

Write-Host "Category Breakdown:" -ForegroundColor Green
Write-Host "  NUMERICAL (external cert): $numerical"
Write-Host "  EMPIRICAL (measurements): $empirical"
Write-Host "  SIMPLE (easy proofs): $simple"
Write-Host "  FRAMEWORK (theory): $framework"
Write-Host "  DEFINITION (computational): $definition"
Write-Host "  COMPLEX (needs work): $complex"
