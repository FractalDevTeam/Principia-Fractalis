#!/usr/bin/env python3
"""
Generate visual diagram of proof structure and mathematical gaps
"""

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
import numpy as np

def create_proof_structure_diagram():
    """Create comprehensive proof structure diagram"""

    fig, ax = plt.subplots(1, 1, figsize=(14, 10))
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 10)
    ax.axis('off')

    # Title
    ax.text(5, 9.5, 'Operator-Theoretic Proof Structure: P ≠ NP',
            ha='center', va='top', fontsize=16, fontweight='bold')

    # Color scheme
    color_established = '#90EE90'  # Light green
    color_conditional = '#FFD700'  # Gold
    color_gap = '#FFB6C6'          # Light red

    # Level 1: Foundation (Established)
    y_foundation = 7.5
    boxes_foundation = [
        (1, y_foundation, 'Spectral Gap\nΔ = 0.0540', color_established),
        (4, y_foundation, 'Critical α Values\n√2, φ+1/4', color_established),
        (7, y_foundation, 'Numerical\nVerification\n143 cases', color_established),
    ]

    for x, y, text, color in boxes_foundation:
        box = FancyBboxPatch((x-0.4, y-0.3), 0.8, 0.6,
                             boxstyle="round,pad=0.05",
                             edgecolor='black', facecolor=color, linewidth=2)
        ax.add_patch(box)
        ax.text(x, y, text, ha='center', va='center', fontsize=9, fontweight='bold')

    # Level 2: Three Main Theorems
    y_theorems = 5.5

    # Theorem 1: Self-Adjointness
    thm1_color = color_conditional
    box1 = FancyBboxPatch((0.2, y_theorems-0.4), 1.6, 0.8,
                          boxstyle="round,pad=0.05",
                          edgecolor='black', facecolor=thm1_color, linewidth=2)
    ax.add_patch(box1)
    ax.text(1, y_theorems, 'Theorem 1\nSelf-Adjointness\nPartially Proven',
            ha='center', va='center', fontsize=9, fontweight='bold')

    # Theorem 2: Correspondence
    thm2_color = color_gap
    box2 = FancyBboxPatch((3.2, y_theorems-0.4), 1.6, 0.8,
                          boxstyle="round,pad=0.05",
                          edgecolor='black', facecolor=thm2_color, linewidth=3)
    ax.add_patch(box2)
    ax.text(4, y_theorems, 'Theorem 2\nTuring ↔ Operator\n⚠ MAIN GAP',
            ha='center', va='center', fontsize=9, fontweight='bold')

    # Theorem 3: Eigenvalues
    thm3_color = color_conditional
    box3 = FancyBboxPatch((6.2, y_theorems-0.4), 1.6, 0.8,
                          boxstyle="round,pad=0.05",
                          edgecolor='black', facecolor=thm3_color, linewidth=2)
    ax.add_patch(box3)
    ax.text(7, y_theorems, 'Theorem 3\nEigenvalue Formulas\nNumerically Verified',
            ha='center', va='center', fontsize=9, fontweight='bold')

    # Level 3: Required Components
    y_components = 3.5

    components = [
        (1, y_components, 'Deficiency\nIndices', color_gap, 'Missing'),
        (2.5, y_components, 'Language\nEncoding Φ', color_gap, 'Missing'),
        (4, y_components, 'Reduction\nPreservation', color_gap, 'Missing'),
        (5.5, y_components, 'WKB\nExactness', color_conditional, 'Partial'),
        (7, y_components, 'Modular\nForms', color_established, 'Done'),
    ]

    for x, y, text, color, status in components:
        box = FancyBboxPatch((x-0.35, y-0.25), 0.7, 0.5,
                            boxstyle="round,pad=0.03",
                            edgecolor='black', facecolor=color, linewidth=1.5)
        ax.add_patch(box)
        ax.text(x, y+0.05, text, ha='center', va='center', fontsize=7)
        ax.text(x, y-0.35, f'({status})', ha='center', va='top', fontsize=6, style='italic')

    # Level 4: Final Conclusion
    y_conclusion = 1.5
    conclusion_color = color_conditional
    box_conclusion = FancyBboxPatch((3, y_conclusion-0.35), 4, 0.7,
                                   boxstyle="round,pad=0.05",
                                   edgecolor='black', facecolor=conclusion_color, linewidth=3)
    ax.add_patch(box_conclusion)
    ax.text(5, y_conclusion, 'CONDITIONAL PROOF: IF Φ exists, THEN P ≠ NP',
            ha='center', va='center', fontsize=11, fontweight='bold')

    # Arrows connecting levels
    arrow_props = dict(arrowstyle='->', lw=2, color='black')

    # Foundation to Theorems
    ax.annotate('', xy=(1, y_theorems+0.4), xytext=(1, y_foundation-0.3),
                arrowprops=arrow_props)
    ax.annotate('', xy=(4, y_theorems+0.4), xytext=(4, y_foundation-0.3),
                arrowprops=arrow_props)
    ax.annotate('', xy=(7, y_theorems+0.4), xytext=(7, y_foundation-0.3),
                arrowprops=arrow_props)

    # Theorems to Components
    for comp_x in [1, 2.5]:
        ax.annotate('', xy=(comp_x, y_components+0.25), xytext=(1, y_theorems-0.4),
                    arrowprops=dict(arrowstyle='->', lw=1.5, color='red', linestyle='--'))

    for comp_x in [2.5, 4]:
        ax.annotate('', xy=(comp_x, y_components+0.25), xytext=(4, y_theorems-0.4),
                    arrowprops=dict(arrowstyle='->', lw=2, color='red'))

    for comp_x in [5.5, 7]:
        ax.annotate('', xy=(comp_x, y_components+0.25), xytext=(7, y_theorems-0.4),
                    arrowprops=dict(arrowstyle='->', lw=1.5, color='blue', linestyle='--'))

    # Components to Conclusion
    for comp_x in [1, 2.5, 4, 5.5, 7]:
        ax.annotate('', xy=(5, y_conclusion+0.35), xytext=(comp_x, y_components-0.25),
                    arrowprops=dict(arrowstyle='->', lw=1, color='gray'))

    # Legend
    legend_y = 0.3
    ax.add_patch(mpatches.Rectangle((0.2, legend_y), 0.3, 0.2,
                                    facecolor=color_established, edgecolor='black'))
    ax.text(0.6, legend_y+0.1, 'Rigorously Established', va='center', fontsize=8)

    ax.add_patch(mpatches.Rectangle((2.5, legend_y), 0.3, 0.2,
                                    facecolor=color_conditional, edgecolor='black'))
    ax.text(2.9, legend_y+0.1, 'Conditional/Partial', va='center', fontsize=8)

    ax.add_patch(mpatches.Rectangle((4.8, legend_y), 0.3, 0.2,
                                    facecolor=color_gap, edgecolor='black'))
    ax.text(5.2, legend_y+0.1, 'Research Gap', va='center', fontsize=8)

    plt.tight_layout()
    return fig

def create_gap_analysis_chart():
    """Create bar chart showing mathematical rigor by component"""

    components = [
        'Spectral Gap\nComputation',
        'Operator\nWell-Defined',
        'Self-Adjoint\nat Critical α',
        'Complete\nCharacterization',
        'Turing\nCorrespondence',
        'Eigenvalue\nFormulas',
        'Overall\nP≠NP Proof'
    ]

    rigor_scores = [9, 8, 7, 4, 3, 5, 4]
    colors = ['#90EE90' if s >= 7 else '#FFD700' if s >= 5 else '#FFB6C6'
              for s in rigor_scores]

    fig, ax = plt.subplots(figsize=(12, 6))
    bars = ax.barh(components, rigor_scores, color=colors, edgecolor='black', linewidth=1.5)

    # Add value labels
    for i, (bar, score) in enumerate(zip(bars, rigor_scores)):
        ax.text(score + 0.2, i, f'{score}/10', va='center', fontweight='bold')

    ax.set_xlabel('Mathematical Rigor Score', fontsize=12, fontweight='bold')
    ax.set_title('Proof Component Rigor Assessment', fontsize=14, fontweight='bold')
    ax.set_xlim(0, 10)
    ax.axvline(x=7, color='green', linestyle='--', linewidth=2, alpha=0.5, label='Strong')
    ax.axvline(x=5, color='orange', linestyle='--', linewidth=2, alpha=0.5, label='Moderate')
    ax.grid(axis='x', alpha=0.3)
    ax.legend()

    plt.tight_layout()
    return fig

def create_research_priority_chart():
    """Create chart showing research priorities"""

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))

    # Priority vs Impact
    priorities = {
        'Turing\nCorrespondence': (10, 10),  # (priority, impact)
        'Deficiency\nIndices': (9, 7),
        'WKB\nExactness': (6, 5),
        'Polylogarithm\nStructure': (5, 6),
        'GCT\nConnection': (3, 8),
        'Other\nComplexity Classes': (4, 7),
    }

    colors_priority = ['#FF6B6B', '#FFA07A', '#FFD700', '#90EE90', '#87CEEB', '#DDA0DD']

    for i, (task, (priority, impact)) in enumerate(priorities.items()):
        ax1.scatter(priority, impact, s=500, color=colors_priority[i],
                   edgecolor='black', linewidth=2, alpha=0.7, zorder=10)
        ax1.text(priority, impact, task, ha='center', va='center',
                fontsize=8, fontweight='bold')

    ax1.set_xlabel('Priority (1-10)', fontsize=12, fontweight='bold')
    ax1.set_ylabel('Impact on Proof (1-10)', fontsize=12, fontweight='bold')
    ax1.set_title('Research Priority Matrix', fontsize=14, fontweight='bold')
    ax1.set_xlim(0, 11)
    ax1.set_ylim(0, 11)
    ax1.grid(True, alpha=0.3)

    # Add quadrant labels
    ax1.text(7.5, 7.5, 'High Priority\nHigh Impact', ha='center', va='center',
            fontsize=10, style='italic', alpha=0.3, fontweight='bold')
    ax1.axhline(y=5.5, color='gray', linestyle='--', alpha=0.5)
    ax1.axvline(x=5.5, color='gray', linestyle='--', alpha=0.5)

    # Timeline estimate
    tasks_timeline = [
        'Spectral Gap\nVerified',
        'Numerical\nFramework',
        'Conditional\nProof',
        'Deficiency\nAnalysis',
        'Turing\nMapping',
        'Complete\nProof'
    ]
    completion = [100, 90, 70, 20, 10, 0]
    colors_timeline = ['#90EE90' if c == 100 else '#FFD700' if c >= 50 else '#FFB6C6'
                      for c in completion]

    bars = ax2.barh(tasks_timeline, completion, color=colors_timeline,
                    edgecolor='black', linewidth=1.5)

    for i, (bar, pct) in enumerate(zip(bars, completion)):
        if pct > 0:
            ax2.text(pct - 5, i, f'{pct}%', va='center', ha='right',
                    fontweight='bold', color='black')

    ax2.set_xlabel('Completion (%)', fontsize=12, fontweight='bold')
    ax2.set_title('Proof Completion Status', fontsize=14, fontweight='bold')
    ax2.set_xlim(0, 110)
    ax2.grid(axis='x', alpha=0.3)

    plt.tight_layout()
    return fig

def main():
    """Generate all diagrams"""

    print("Generating proof structure diagrams...")

    # Create output directory if needed
    import os
    os.makedirs('figures', exist_ok=True)

    # Generate diagrams
    fig1 = create_proof_structure_diagram()
    fig1.savefig('figures/proof_structure.png', dpi=300, bbox_inches='tight')
    print("✓ Saved: figures/proof_structure.png")

    fig2 = create_gap_analysis_chart()
    fig2.savefig('figures/rigor_analysis.png', dpi=300, bbox_inches='tight')
    print("✓ Saved: figures/rigor_analysis.png")

    fig3 = create_research_priority_chart()
    fig3.savefig('figures/research_priorities.png', dpi=300, bbox_inches='tight')
    print("✓ Saved: figures/research_priorities.png")

    print("\nAll diagrams generated successfully!")
    print("These can be included in the LaTeX document or presentations.")

if __name__ == "__main__":
    main()