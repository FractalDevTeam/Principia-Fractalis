/**
 * Principia Fractalis - Interactive Educational Website
 * JavaScript for animations, demos, and interactivity
 */

document.addEventListener('DOMContentLoaded', () => {
    // Initialize all components
    initNavigation();
    initFractalBackground();
    initConsciousnessMeters();
    initCountingDemo();
    initSudokuGame();
    initTopicTabs();
    initScrollAnimations();
});

// ===== Navigation =====
function initNavigation() {
    const mobileMenuBtn = document.querySelector('.mobile-menu-btn');
    const navLinks = document.querySelector('.nav-links');
    
    if (mobileMenuBtn && navLinks) {
        mobileMenuBtn.addEventListener('click', () => {
            navLinks.classList.toggle('active');
            mobileMenuBtn.classList.toggle('active');
        });
    }
    
    // Smooth scrolling for anchor links
    document.querySelectorAll('a[href^="#"]').forEach(anchor => {
        anchor.addEventListener('click', (e) => {
            e.preventDefault();
            const target = document.querySelector(anchor.getAttribute('href'));
            if (target) {
                const navHeight = document.querySelector('.navbar').offsetHeight;
                const targetPosition = target.offsetTop - navHeight - 20;
                window.scrollTo({
                    top: targetPosition,
                    behavior: 'smooth'
                });
                // Close mobile menu if open
                if (navLinks) navLinks.classList.remove('active');
            }
        });
    });
}

// ===== Fractal Background Animation =====
function initFractalBackground() {
    const canvas = document.getElementById('fractal-bg');
    if (!canvas) return;
    
    const ctx = canvas.getContext('2d');
    let animationId;
    let time = 0;
    
    function resize() {
        canvas.width = window.innerWidth;
        canvas.height = window.innerHeight;
    }
    
    function drawFractal() {
        ctx.fillStyle = 'rgba(10, 10, 26, 0.1)';
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        const centerX = canvas.width / 2;
        const centerY = canvas.height / 2;
        const maxRadius = Math.min(canvas.width, canvas.height) * 0.4;
        
        // Draw fractal spirals
        for (let i = 0; i < 3; i++) {
            const offset = (i * Math.PI * 2) / 3;
            drawSpiral(centerX, centerY, maxRadius, time + offset, i);
        }
        
        // Draw connecting lines
        drawConnections(centerX, centerY, maxRadius, time);
        
        time += 0.005;
        animationId = requestAnimationFrame(drawFractal);
    }
    
    function drawSpiral(cx, cy, maxR, t, colorIndex) {
        const colors = [
            'rgba(167, 139, 250, 0.3)',  // Purple
            'rgba(100, 255, 218, 0.3)',  // Cyan
            'rgba(255, 215, 0, 0.2)'     // Gold
        ];
        
        ctx.strokeStyle = colors[colorIndex];
        ctx.lineWidth = 1.5;
        ctx.beginPath();
        
        for (let angle = 0; angle < Math.PI * 6; angle += 0.1) {
            const r = (angle / (Math.PI * 6)) * maxR;
            const spiralAngle = angle + t;
            const x = cx + Math.cos(spiralAngle) * r;
            const y = cy + Math.sin(spiralAngle) * r;
            
            if (angle === 0) {
                ctx.moveTo(x, y);
            } else {
                ctx.lineTo(x, y);
            }
        }
        
        ctx.stroke();
    }
    
    function drawConnections(cx, cy, maxR, t) {
        const numPoints = 12;
        const points = [];
        
        for (let i = 0; i < numPoints; i++) {
            const angle = (i / numPoints) * Math.PI * 2 + t * 0.5;
            const r = maxR * (0.5 + 0.3 * Math.sin(t * 2 + i));
            points.push({
                x: cx + Math.cos(angle) * r,
                y: cy + Math.sin(angle) * r
            });
        }
        
        ctx.strokeStyle = 'rgba(167, 139, 250, 0.1)';
        ctx.lineWidth = 0.5;
        
        for (let i = 0; i < points.length; i++) {
            for (let j = i + 1; j < points.length; j++) {
                if ((i + j) % 3 === 0) {
                    ctx.beginPath();
                    ctx.moveTo(points[i].x, points[i].y);
                    ctx.lineTo(points[j].x, points[j].y);
                    ctx.stroke();
                }
            }
        }
        
        // Draw points
        points.forEach((p, i) => {
            const size = 2 + Math.sin(t * 3 + i) * 1;
            ctx.fillStyle = 'rgba(100, 255, 218, 0.5)';
            ctx.beginPath();
            ctx.arc(p.x, p.y, size, 0, Math.PI * 2);
            ctx.fill();
        });
    }
    
    resize();
    window.addEventListener('resize', resize);
    drawFractal();
    
    // Cleanup on page leave
    window.addEventListener('beforeunload', () => {
        cancelAnimationFrame(animationId);
    });
}

// ===== Consciousness Meters =====
function initConsciousnessMeters() {
    const meters = document.querySelectorAll('.meter-fill-animated');
    
    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                entry.target.style.width = '95%';
            }
        });
    }, { threshold: 0.5 });
    
    meters.forEach(meter => observer.observe(meter));
}

// ===== Counting Demo (For Kids) =====
function initCountingDemo() {
    const numberInput = document.getElementById('number-input');
    const base10Display = document.getElementById('base10-display');
    const base3Display = document.getElementById('base3-display');
    const digitSumDisplay = document.getElementById('digit-sum');
    
    if (!numberInput) return;
    
    function updateConversions() {
        const num = parseInt(numberInput.value) || 0;
        const clampedNum = Math.max(0, Math.min(100, num));
        
        // Update base-10 display
        base10Display.textContent = clampedNum;
        
        // Convert to base-3
        const base3 = clampedNum.toString(3);
        base3Display.textContent = base3 || '0';
        
        // Calculate digit sum
        const digits = base3.split('').map(Number);
        const sum = digits.reduce((a, b) => a + b, 0);
        const digitString = digits.join(' + ');
        digitSumDisplay.textContent = digits.length > 1 
            ? `${digitString} = ${sum}`
            : `${sum}`;
    }
    
    numberInput.addEventListener('input', updateConversions);
    updateConversions(); // Initial update
}

// ===== Mini Sudoku Game (For Kids) =====
function initSudokuGame() {
    const grid = document.getElementById('sudoku-grid');
    const checkBtn = document.getElementById('check-sudoku');
    const resetBtn = document.getElementById('reset-sudoku');
    const message = document.getElementById('sudoku-message');
    
    if (!grid) return;
    
    // 4x4 Sudoku puzzle (simplified for kids)
    // 0 means empty cell to fill
    const puzzle = [
        [1, 0, 3, 4],
        [3, 4, 0, 2],
        [4, 3, 2, 0],
        [0, 1, 4, 3]
    ];
    
    const solution = [
        [1, 2, 3, 4],
        [3, 4, 1, 2],
        [4, 3, 2, 1],
        [2, 1, 4, 3]
    ];
    
    let userAnswers = puzzle.map(row => [...row]);
    
    function renderGrid() {
        grid.innerHTML = '';
        
        for (let row = 0; row < 4; row++) {
            for (let col = 0; col < 4; col++) {
                const cell = document.createElement('div');
                cell.className = 'sudoku-cell';
                
                if (puzzle[row][col] !== 0) {
                    cell.classList.add('fixed');
                    cell.textContent = puzzle[row][col];
                } else {
                    const input = document.createElement('input');
                    input.type = 'text';
                    input.maxLength = 1;
                    input.value = userAnswers[row][col] || '';
                    input.dataset.row = row;
                    input.dataset.col = col;
                    
                    input.addEventListener('input', (e) => {
                        const val = e.target.value.replace(/[^1-4]/g, '');
                        e.target.value = val;
                        userAnswers[row][col] = parseInt(val) || 0;
                        message.textContent = '';
                        message.className = 'sudoku-message';
                    });
                    
                    cell.appendChild(input);
                }
                
                grid.appendChild(cell);
            }
        }
    }
    
    function checkSolution() {
        let correct = true;
        
        for (let row = 0; row < 4; row++) {
            for (let col = 0; col < 4; col++) {
                if (userAnswers[row][col] !== solution[row][col]) {
                    correct = false;
                    break;
                }
            }
        }
        
        if (correct) {
            message.textContent = 'Correct! Great job!';
            message.className = 'sudoku-message success';
        } else {
            // Check if all cells are filled
            const allFilled = userAnswers.every(row => row.every(cell => cell !== 0));
            if (allFilled) {
                message.textContent = 'Not quite right. Try again!';
            } else {
                message.textContent = 'Fill in all the empty squares first!';
            }
            message.className = 'sudoku-message error';
        }
    }
    
    function resetGame() {
        userAnswers = puzzle.map(row => [...row]);
        message.textContent = '';
        message.className = 'sudoku-message';
        renderGrid();
    }
    
    if (checkBtn) checkBtn.addEventListener('click', checkSolution);
    if (resetBtn) resetBtn.addEventListener('click', resetGame);
    
    renderGrid();
}

// ===== Topic Tabs (For Students) =====
function initTopicTabs() {
    const tabs = document.querySelectorAll('.topic-tab');
    const contents = document.querySelectorAll('.topic-content');
    
    if (tabs.length === 0) return;
    
    tabs.forEach(tab => {
        tab.addEventListener('click', () => {
            const topic = tab.dataset.topic;
            
            // Update active tab
            tabs.forEach(t => t.classList.remove('active'));
            tab.classList.add('active');
            
            // Show corresponding content
            contents.forEach(content => {
                if (content.id === `topic-${topic}`) {
                    content.classList.remove('hidden');
                } else {
                    content.classList.add('hidden');
                }
            });
        });
    });
}

// ===== Scroll Animations =====
function initScrollAnimations() {
    const animatedElements = document.querySelectorAll(
        '.idea-card, .activity-card, .problem-card, .resource-card, .support-card'
    );
    
    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                entry.target.style.opacity = '1';
                entry.target.style.transform = 'translateY(0)';
            }
        });
    }, { threshold: 0.1 });
    
    animatedElements.forEach(el => {
        el.style.opacity = '0';
        el.style.transform = 'translateY(30px)';
        el.style.transition = 'opacity 0.6s ease, transform 0.6s ease';
        observer.observe(el);
    });
}

// ===== Base-3 Canvas Demo =====
function initBase3Canvas() {
    const canvas = document.getElementById('base3-demo');
    if (!canvas) return;
    
    const ctx = canvas.getContext('2d');
    canvas.width = canvas.clientWidth;
    canvas.height = 100;
    
    function drawBase3Pattern() {
        ctx.fillStyle = '#0a0a1a';
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        const colors = ['#ff6b6b', '#51cf66', '#339af0'];
        const cellWidth = 20;
        const cellHeight = 30;
        const startX = (canvas.width - cellWidth * 15) / 2;
        const startY = (canvas.height - cellHeight * 2) / 2;
        
        // Draw numbers 1-15 in base 3
        for (let num = 1; num <= 15; num++) {
            const base3 = num.toString(3).padStart(3, '0');
            const x = startX + (num - 1) * cellWidth;
            
            for (let digit = 0; digit < 3; digit++) {
                const d = parseInt(base3[digit]);
                ctx.fillStyle = colors[d];
                ctx.fillRect(x + 2, startY + digit * 10, cellWidth - 4, 8);
            }
            
            // Label
            ctx.fillStyle = '#ffffff';
            ctx.font = '10px sans-serif';
            ctx.textAlign = 'center';
            ctx.fillText(num, x + cellWidth / 2, startY + 45);
        }
    }
    
    drawBase3Pattern();
}

// ===== Learn More Button Handlers =====
document.querySelectorAll('.learn-more-btn').forEach(btn => {
    btn.addEventListener('click', () => {
        const target = btn.dataset.target;
        
        switch(target) {
            case 'base3':
                scrollToSection('for-kids');
                break;
            case 'timeless':
                scrollToSection('for-students');
                break;
            case 'consciousness':
                // Switch to consciousness tab
                scrollToSection('for-students');
                setTimeout(() => {
                    const tab = document.querySelector('[data-topic="consciousness"]');
                    if (tab) tab.click();
                }, 500);
                break;
        }
    });
});

function scrollToSection(sectionId) {
    const section = document.getElementById(sectionId);
    if (section) {
        const navHeight = document.querySelector('.navbar').offsetHeight;
        const targetPosition = section.offsetTop - navHeight - 20;
        window.scrollTo({
            top: targetPosition,
            behavior: 'smooth'
        });
    }
}

// ===== Navbar scroll effect =====
window.addEventListener('scroll', () => {
    const navbar = document.querySelector('.navbar');
    if (window.scrollY > 100) {
        navbar.style.background = 'rgba(10, 10, 26, 0.95)';
    } else {
        navbar.style.background = 'rgba(10, 10, 26, 0.9)';
    }
});

// ===== Console Easter Egg =====
console.log(`
%c Principia Fractalis
%c Mathematics IS Reality

Discover more at: https://github.com/FractalDevTeam/Principia-Fractalis

"The unreasonable effectiveness of mathematics is not unreasonable at all — it is inevitable."
- Pablo Cohen
`, 
'font-size: 24px; font-weight: bold; color: #a78bfa;',
'font-size: 14px; color: #64ffda;'
);
