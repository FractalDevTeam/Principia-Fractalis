# File Organization Script
# Cleans up the root directory by moving files to appropriate subdirectories

Write-Host "🗂️  Organizing Principia Fractalis submission folder..." -ForegroundColor Cyan

# Turing Machine files
$turingFiles = @(
    "TURING_MACHINE_*.md",
    "VERIFICATION_ASSESSMENT_TURING_COMPLETENESS.md",
    "COMPLETE_CLAIMS.md",
    "REVIEW_RESPONSE.md",
    "BOOK_UPDATES_REQUIRED.md",
    "ERRATA_DEFINITION_21_1.tex",
    "COMPLETION_SUMMARY_NOV_19_2025.md",
    "RIGOR_ENHANCEMENTS.md"
)

foreach ($pattern in $turingFiles) {
    Get-ChildItem -Path . -Filter $pattern -File | ForEach-Object {
        Move-Item $_.FullName -Destination "docs\turing-machine\" -Force
        Write-Host "  ✓ Moved $($_.Name) to docs/turing-machine/" -ForegroundColor Green
    }
}

# Verification files
$verificationFiles = @(
    "VERIFICATION_*.md",
    "BUILD_STATUS_*.md",
    "FINAL_STATUS_*.md",
    "FINAL_VERIFICATION_*.md",
    "COMPREHENSIVE_VERIFICATION*",
    "COMPLETION_STATUS.txt",
    "TRUE_STATUS_*.md",
    "REAL_STATUS_*.md"
)

foreach ($pattern in $verificationFiles) {
    Get-ChildItem -Path . -Filter $pattern -File | ForEach-Object {
        Move-Item $_.FullName -Destination "docs\verification\" -Force
        Write-Host "  ✓ Moved $($_.Name) to docs/verification/" -ForegroundColor Green
    }
}

# Axiom files
$axiomFiles = @(
    "*AXIOM*.md",
    "*_AXIOMS_*.md",
    "EXTERNAL_NUMERICAL_CERTIFICATION.md",
    "EMPIRICAL_DATA_SOURCES.md"
)

foreach ($pattern in $axiomFiles) {
    Get-ChildItem -Path . -Filter $pattern -File | ForEach-Object {
        Move-Item $_.FullName -Destination "docs\axioms\" -Force
        Write-Host "  ✓ Moved $($_.Name) to docs/axioms/" -ForegroundColor Green
    }
}

# Millennium Problems
$millenniumFiles = @(
    "RH_*.md",
    "BSD_*.md",
    "YM_*.md",
    "PNP_*.md",
    "PROBLEMS143_*.md"
)

foreach ($pattern in $millenniumFiles) {
    Get-ChildItem -Path . -Filter $pattern -File | ForEach-Object {
        Move-Item $_.FullName -Destination "docs\millennium-problems\" -Force
        Write-Host "  ✓ Moved $($_.Name) to docs/millennium-problems/" -ForegroundColor Green
    }
}

# Progress/Session files
$progressFiles = @(
    "SESSION_*.md",
    "PROGRESS_*.md",
    "WAVE_*.md",
    "*_SESSION_*.md",
    "STAGE_C_*.md",
    "IMPLEMENTATION_SUMMARY.md",
    "COMPLETION_ROADMAP.md"
)

foreach ($pattern in $progressFiles) {
    Get-ChildItem -Path . -Filter $pattern -File | ForEach-Object {
        Move-Item $_.FullName -Destination "docs\progress\" -Force
        Write-Host "  ✓ Moved $($_.Name) to docs/progress/" -ForegroundColor Green
    }
}

# Old status/attack files (archive)
$archiveFiles = @(
    "ATTACK_*.md",
    "AGENT_*.md",
    "HONEST_STATUS_*.md",
    "SORRY_*.md",
    "STATUS_*.md",
    "INCOMPLETE_ITEMS_*.md",
    "CIRCULARITY_*.md",
    "RESTORATION_*.md",
    "TIMESTAMP_PROOF.txt"
)

foreach ($pattern in $archiveFiles) {
    Get-ChildItem -Path . -Filter $pattern -File | ForEach-Object {
        Move-Item $_.FullName -Destination "archive\old-status\" -Force
        Write-Host "  ✓ Moved $($_.Name) to archive/old-status/" -ForegroundColor Yellow
    }
}

# Additional doc files
$miscDocs = @(
    "ACADEMIC_REVIEW_*.md",
    "*_INDEX.md",
    "FILE_ORGANIZATION_GUIDE.md",
    "LEAN_PROOF_*.md",
    "PROOF_*.md",
    "LATEX_READING_NOTES.md",
    "MASTER_*.md",
    "README_FOR_AI_AGENTS.md",
    "THEOREM_CODE_SNIPPETS.md",
    "WORK_BREAKDOWN_STRUCTURE.md",
    "QUIPU_VALIDATION_CRITICAL.md",
    "COLLATZ_FRACTAL_RESONANCE_APPROACH.md",
    "RADIX_ECONOMY_PROOFS_COMPLETED.md"
)

foreach ($pattern in $miscDocs) {
    Get-ChildItem -Path . -Filter $pattern -File | ForEach-Object {
        Move-Item $_.FullName -Destination "docs\" -Force
        Write-Host "  ✓ Moved $($_.Name) to docs/" -ForegroundColor Cyan
    }
}

Write-Host "`n✅ File organization complete!" -ForegroundColor Green
Write-Host "📁 Root directory is now clean" -ForegroundColor Green
Write-Host "📖 Check INDEX.md for navigation" -ForegroundColor Cyan
