#!/bin/bash
# Principia Fractalis Branch Cleanup Script
# Generated: November 30, 2025
#
# This script cleans up redundant branches and archives stale ones as tags.
# Review each section before running. All operations are logged.
#
# USAGE:
#   chmod +x BRANCH_CLEANUP.sh
#   ./BRANCH_CLEANUP.sh
#
# NOTE: This script uses GitHub API via 'gh' CLI. Ensure you're authenticated.

set -e

REPO="FractalDevTeam/Principia-Fractalis"
LOG_FILE="branch_cleanup_$(date +%Y%m%d_%H%M%S).log"

echo "=== Principia Fractalis Branch Cleanup ===" | tee -a "$LOG_FILE"
echo "Repository: $REPO" | tee -a "$LOG_FILE"
echo "Date: $(date)" | tee -a "$LOG_FILE"
echo "" | tee -a "$LOG_FILE"

# ========================================
# SECTION 1: DELETE REDUNDANT BRANCHES
# These branches are duplicates or already merged
# ========================================

echo "--- SECTION 1: Deleting redundant branches ---" | tee -a "$LOG_FILE"

REDUNDANT_BRANCHES=(
    "zero-sorries-complete"       # Same as PF_CANONICAL
    "merge-turing-machine-final"  # Same as turing-machine-complete
    "merge-all-updates"           # Same as final-publication-ready
    "main"                        # Orphaned, conflicts with master
)

for branch in "${REDUNDANT_BRANCHES[@]}"; do
    echo "Deleting branch: $branch" | tee -a "$LOG_FILE"
    # Uncomment the next line to actually delete:
    # gh api -X DELETE "repos/$REPO/git/refs/heads/$branch" 2>/dev/null && echo "  ✓ Deleted" || echo "  ✗ Failed or not found"
    echo "  [DRY RUN] Would delete $branch" | tee -a "$LOG_FILE"
done

echo "" | tee -a "$LOG_FILE"

# ========================================
# SECTION 2: ARCHIVE STALE BRANCHES AS TAGS
# These branches have historical value but are no longer active
# ========================================

echo "--- SECTION 2: Archiving stale branches as tags ---" | tee -a "$LOG_FILE"

declare -A ARCHIVE_BRANCHES
ARCHIVE_BRANCHES=(
    ["security-hardening"]="archive/security-hardening-2025-11-13"
    ["millennium-bridges"]="archive/millennium-bridges-2025-11-16"
    ["pf-skeleton-2025-11-21"]="archive/pf-skeleton-2025-11-21"
)

for branch in "${!ARCHIVE_BRANCHES[@]}"; do
    tag="${ARCHIVE_BRANCHES[$branch]}"
    echo "Archiving branch '$branch' as tag '$tag'" | tee -a "$LOG_FILE"

    # Get the SHA of the branch
    # SHA=$(gh api "repos/$REPO/git/refs/heads/$branch" --jq '.object.sha' 2>/dev/null)
    # if [ -n "$SHA" ]; then
    #     # Create tag
    #     gh api "repos/$REPO/git/refs" -f ref="refs/tags/$tag" -f sha="$SHA"
    #     # Delete branch
    #     gh api -X DELETE "repos/$REPO/git/refs/heads/$branch"
    #     echo "  ✓ Archived as $tag"
    # else
    #     echo "  ✗ Branch not found"
    # fi

    echo "  [DRY RUN] Would archive $branch as $tag" | tee -a "$LOG_FILE"
done

echo "" | tee -a "$LOG_FILE"

# ========================================
# SECTION 3: BRANCHES TO KEEP
# These are the active, important branches
# ========================================

echo "--- SECTION 3: Branches to KEEP (no action) ---" | tee -a "$LOG_FILE"

KEEP_BRANCHES=(
    "master"                       # Default branch, most recent
    "coq-millennium-verification"  # Active Coq development
    "PF_CANONICAL"                 # Lean complete formalization
    "final-publication-ready"      # Has LICENSE/CITATION (merged to master)
)

for branch in "${KEEP_BRANCHES[@]}"; do
    echo "  ✓ Keeping: $branch" | tee -a "$LOG_FILE"
done

echo "" | tee -a "$LOG_FILE"

# ========================================
# SECTION 4: BRANCHES TO EVALUATE
# These need manual review
# ========================================

echo "--- SECTION 4: Branches requiring manual evaluation ---" | tee -a "$LOG_FILE"

EVALUATE_BRANCHES=(
    "axiom-elimination-complete"   # 18 commits ahead of PF_CANONICAL
    "final-zero-sorries"           # 18 commits ahead of PF_CANONICAL
    "complete-100-percent-coverage" # 1 commit ahead of PF_CANONICAL
    "turing-machine-complete"      # 7 commits ahead of PF_CANONICAL
)

for branch in "${EVALUATE_BRANCHES[@]}"; do
    echo "  ? Evaluate: $branch" | tee -a "$LOG_FILE"
    # You can check with:
    # gh api "repos/$REPO/compare/PF_CANONICAL...$branch" --jq '{ahead: .ahead_by, behind: .behind_by}'
done

echo "" | tee -a "$LOG_FILE"

# ========================================
# SECTION 5: ADD REPOSITORY TOPICS
# ========================================

echo "--- SECTION 5: Adding repository topics ---" | tee -a "$LOG_FILE"

TOPICS="formal-verification,lean4,coq,mathematics,millennium-problems,proof-assistant,spectral-theory"

echo "Adding topics: $TOPICS" | tee -a "$LOG_FILE"
# Uncomment to add topics:
# gh repo edit "$REPO" --add-topic formal-verification --add-topic lean4 --add-topic coq --add-topic mathematics --add-topic millennium-problems --add-topic proof-assistant --add-topic spectral-theory
echo "  [DRY RUN] Would add topics" | tee -a "$LOG_FILE"

echo "" | tee -a "$LOG_FILE"

# ========================================
# SUMMARY
# ========================================

echo "=== SUMMARY ===" | tee -a "$LOG_FILE"
echo "" | tee -a "$LOG_FILE"
echo "This was a DRY RUN. To execute:" | tee -a "$LOG_FILE"
echo "1. Review this script and uncomment the actual API calls" | tee -a "$LOG_FILE"
echo "2. Run: ./BRANCH_CLEANUP.sh" | tee -a "$LOG_FILE"
echo "" | tee -a "$LOG_FILE"
echo "Actions that would be taken:" | tee -a "$LOG_FILE"
echo "  - Delete ${#REDUNDANT_BRANCHES[@]} redundant branches" | tee -a "$LOG_FILE"
echo "  - Archive ${#ARCHIVE_BRANCHES[@]} stale branches as tags" | tee -a "$LOG_FILE"
echo "  - Keep ${#KEEP_BRANCHES[@]} important branches" | tee -a "$LOG_FILE"
echo "  - Evaluate ${#EVALUATE_BRANCHES[@]} branches manually" | tee -a "$LOG_FILE"
echo "  - Add repository topics" | tee -a "$LOG_FILE"
echo "" | tee -a "$LOG_FILE"
echo "Log saved to: $LOG_FILE" | tee -a "$LOG_FILE"
echo "" | tee -a "$LOG_FILE"
echo "=== DONE ===" | tee -a "$LOG_FILE"
