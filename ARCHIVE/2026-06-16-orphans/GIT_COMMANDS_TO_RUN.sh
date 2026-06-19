#!/bin/bash
# GitHub Update Script - Run this to update your GitHub repository
# Make executable with: chmod +x GIT_COMMANDS_TO_RUN.sh
# Run with: ./GIT_COMMANDS_TO_RUN.sh

set -e  # Exit on any error

echo "========================================="
echo " PRINCIPIA FRACTALIS - GITHUB UPDATE"
echo "========================================="
echo ""

# Step 1: Check we're in the right directory
CURRENT_DIR=$(basename "$PWD")
if [[ "$CURRENT_DIR" != "PRINCIPIA_FRACTALIS_GITHUB_READY_2025-11-15" ]]; then
    echo "ERROR: Not in the correct directory!"
    echo "Please run: cd '/home/xluxx/pablo_context/PRINCIPIA_FRACTALIS_GITHUB_READY_2025-11-15'"
    exit 1
fi

echo "✅ Step 1: In correct directory"
echo ""

# Step 2: Initialize git if needed
if [ ! -d ".git" ]; then
    echo "📦 Step 2: Initializing git repository..."
    git init
    echo "✅ Git initialized"
else
    echo "✅ Step 2: Git already initialized"
fi
echo ""

# Step 3: Create .gitignore
echo "📝 Step 3: Creating .gitignore..."
cat > .gitignore << 'GITIGNORE'
# Lean build artifacts
.lake/
build/
lake-packages/
*.olean
*.trace

# System files
.DS_Store
*~
.vscode/
GITIGNORE
echo "✅ .gitignore created"
echo ""

# Step 4: Add remote (you need to edit this!)
echo "🔗 Step 4: Setting up GitHub remote..."
echo ""
echo "BEFORE CONTINUING, YOU MUST:"
echo "1. Create a repository on GitHub (https://github.com/new)"
echo "2. Copy the repository URL"
echo "3. Edit this script and replace YOUR_USERNAME and YOUR_REPO below"
echo ""

# ⚠️ EDIT THIS LINE WITH YOUR GITHUB INFO:
GITHUB_REPO="https://github.com/YOUR_USERNAME/YOUR_REPO.git"

# Check if user edited the URL
if [[ "$GITHUB_REPO" == *"YOUR_USERNAME"* ]]; then
    echo "❌ ERROR: You haven't set your GitHub repository URL yet!"
    echo ""
    echo "Please edit this file and replace:"
    echo "  GITHUB_REPO=\"https://github.com/YOUR_USERNAME/YOUR_REPO.git\""
    echo "with your actual GitHub repository URL."
    echo ""
    echo "Example:"
    echo "  GITHUB_REPO=\"https://github.com/xluxx/principia-fractalis.git\""
    echo ""
    exit 1
fi

# Add or update remote
if git remote | grep -q "origin"; then
    echo "Updating existing remote..."
    git remote set-url origin "$GITHUB_REPO"
else
    echo "Adding new remote..."
    git remote add origin "$GITHUB_REPO"
fi
echo "✅ Remote set to: $GITHUB_REPO"
echo ""

# Step 5: Add all files
echo "📂 Step 5: Adding all files to git..."
git add .
echo "✅ Files added"
echo ""

# Step 6: Create commit
echo "💾 Step 6: Creating commit..."
git commit -m "fix: Address circular reasoning in P≠NP formalization

CRITICAL UPDATE - Resolves Lean community feedback:

✅ Circular axiom 'spectral_gap_positive' REMOVED
   - Now documented as framework claim
   - See CIRCULARITY_FIX_REPORT.md for details

✅ Scientific honesty maintained
   - Clear separation: proven vs framework axioms
   - Realistic timeline: 12-18 months for completion

✅ Documentation added
   - README.md with honest claims
   - Axiom status clearly documented
   - Build verified

PACKAGE STATUS:
- Build: SUCCESS
- Circular reasoning: ELIMINATED
- Framework: DOCUMENTED
- Lean version: 4.24.0-rc1

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>"
echo "✅ Commit created"
echo ""

# Step 7: Push to GitHub
echo "🚀 Step 7: Pushing to GitHub..."
echo ""
echo "This will OVERWRITE your GitHub repository with this version."
echo "Press ENTER to continue, or Ctrl+C to cancel..."
read

git branch -M main
git push -u origin main --force

echo ""
echo "========================================="
echo " ✅ GITHUB UPDATE COMPLETE!"
echo "========================================="
echo ""
echo "Your repository is now live at:"
echo "$GITHUB_REPO"
echo ""
echo "Next steps:"
echo "1. Visit your GitHub repository in a web browser"
echo "2. Verify all files are there"
echo "3. Check that README.md displays correctly"
echo ""
echo "You're done! 🎉"
echo ""
