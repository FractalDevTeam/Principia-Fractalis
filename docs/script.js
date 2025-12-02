/**
 * Principia Fractalis - Complete Interactive Experience
 * All games, visualizations, and educational tools
 */

// ===== Global State =====
const AppState = {
    progress: 0,
    badges: {},
    audioContext: null
};

// Badge definitions
const BADGES = {
    'fractal-explorer': { icon: '🔍', name: 'Fractal Explorer', desc: 'Explored the Mandelbrot set' },
    'prime-hunter': { icon: '🔢', name: 'Prime Hunter', desc: 'Watched the prime sieve' },
    'sound-scientist': { icon: '🔊', name: 'Sound Scientist', desc: 'Heard the spectral gap' },
    'consciousness-explorer': { icon: '🧠', name: 'Consciousness Explorer', desc: 'Crossed the threshold' },
    'base3-master': { icon: '3️⃣', name: 'Base-3 Master', desc: 'Scored 5 in the quiz' },
    'fractal-artist': { icon: '🎨', name: 'Fractal Artist', desc: 'Created fractal art' },
    'pattern-hunter': { icon: '🎯', name: 'Pattern Hunter', desc: 'Found 3 patterns' },
    'story-complete': { icon: '📖', name: 'Story Complete', desc: 'Finished the story' }
};

// ===== Initialize Everything =====
document.addEventListener('DOMContentLoaded', () => {
    loadProgress();
    initParticles();
    initNavigation();
    initHeroFractal();
    initStoryMode();
    initFractalExplorer();
    initPrimeSieve();
    initSpectralAudio();
    initConsciousnessSimulator();
    initBase3Quiz();
    initFractalDrawing();
    initPatternHunter();
    initBadgesPanel();
    initScrollAnimations();
});

// ===== Progress & Badges =====
function loadProgress() {
    const saved = localStorage.getItem('principia-progress');
    if (saved) {
        const data = JSON.parse(saved);
        AppState.progress = data.progress || 0;
        AppState.badges = data.badges || {};
    }
    updateProgressDisplay();
}

function saveProgress() {
    localStorage.setItem('principia-progress', JSON.stringify({
        progress: AppState.progress,
        badges: AppState.badges
    }));
    updateProgressDisplay();
}

function updateProgressDisplay() {
    const fill = document.getElementById('progress-ring-fill');
    const text = document.getElementById('progress-text');
    if (fill && text) {
        const percent = Math.min(100, AppState.progress);
        fill.setAttribute('stroke-dasharray', `${percent}, 100`);
        text.textContent = `${percent}%`;
    }
}

function earnBadge(badgeId) {
    if (AppState.badges[badgeId]) return;
    
    AppState.badges[badgeId] = true;
    AppState.progress = Math.min(100, AppState.progress + 12);
    saveProgress();
    
    // Show notification
    showBadgeNotification(badgeId);
    updateBadgesPanel();
}

function showBadgeNotification(badgeId) {
    const badge = BADGES[badgeId];
    if (!badge) return;
    
    const notif = document.createElement('div');
    notif.className = 'badge-notification';
    notif.innerHTML = `
        <span class="badge-notif-icon">${badge.icon}</span>
        <div class="badge-notif-text">
            <strong>Badge Earned!</strong>
            <span>${badge.name}</span>
        </div>
    `;
    notif.style.cssText = `
        position: fixed;
        bottom: 100px;
        right: 20px;
        background: linear-gradient(135deg, #7c3aed, #a78bfa);
        color: white;
        padding: 1rem 1.5rem;
        border-radius: 12px;
        display: flex;
        align-items: center;
        gap: 1rem;
        z-index: 2000;
        animation: slideIn 0.5s ease, fadeOut 0.5s ease 2.5s forwards;
        box-shadow: 0 10px 30px rgba(167, 139, 250, 0.5);
    `;
    
    document.body.appendChild(notif);
    setTimeout(() => notif.remove(), 3000);
}

function initBadgesPanel() {
    const grid = document.getElementById('badges-grid');
    if (!grid) return;
    
    grid.innerHTML = Object.entries(BADGES).map(([id, badge]) => `
        <div class="badge-item ${AppState.badges[id] ? 'earned' : ''}" title="${badge.name}">
            ${badge.icon}
        </div>
    `).join('');
}

function updateBadgesPanel() {
    initBadgesPanel();
}

// ===== Particle Background =====
function initParticles() {
    const canvas = document.getElementById('particles-bg');
    if (!canvas) return;
    
    const ctx = canvas.getContext('2d');
    let particles = [];
    let animationId;
    
    function resize() {
        canvas.width = window.innerWidth;
        canvas.height = window.innerHeight;
    }
    
    function createParticles() {
        particles = [];
        const count = Math.floor((canvas.width * canvas.height) / 15000);
        for (let i = 0; i < count; i++) {
            particles.push({
                x: Math.random() * canvas.width,
                y: Math.random() * canvas.height,
                vx: (Math.random() - 0.5) * 0.5,
                vy: (Math.random() - 0.5) * 0.5,
                size: Math.random() * 2 + 1,
                alpha: Math.random() * 0.5 + 0.2
            });
        }
    }
    
    function animate() {
        ctx.clearRect(0, 0, canvas.width, canvas.height);
        
        particles.forEach((p, i) => {
            p.x += p.vx;
            p.y += p.vy;
            
            if (p.x < 0) p.x = canvas.width;
            if (p.x > canvas.width) p.x = 0;
            if (p.y < 0) p.y = canvas.height;
            if (p.y > canvas.height) p.y = 0;
            
            ctx.beginPath();
            ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2);
            ctx.fillStyle = `rgba(167, 139, 250, ${p.alpha})`;
            ctx.fill();
            
            // Connect nearby particles
            particles.slice(i + 1).forEach(p2 => {
                const dx = p.x - p2.x;
                const dy = p.y - p2.y;
                const dist = Math.sqrt(dx * dx + dy * dy);
                if (dist < 100) {
                    ctx.beginPath();
                    ctx.moveTo(p.x, p.y);
                    ctx.lineTo(p2.x, p2.y);
                    ctx.strokeStyle = `rgba(100, 255, 218, ${0.1 * (1 - dist / 100)})`;
                    ctx.stroke();
                }
            });
        });
        
        animationId = requestAnimationFrame(animate);
    }
    
    resize();
    createParticles();
    animate();
    
    window.addEventListener('resize', () => {
        resize();
        createParticles();
    });
}

// ===== Navigation =====
function initNavigation() {
    const btn = document.querySelector('.mobile-menu-btn');
    const nav = document.querySelector('.nav-links');
    
    if (btn && nav) {
        btn.addEventListener('click', () => nav.classList.toggle('active'));
    }
    
    document.querySelectorAll('a[href^="#"]').forEach(a => {
        a.addEventListener('click', e => {
            e.preventDefault();
            const target = document.querySelector(a.getAttribute('href'));
            if (target) {
                const offset = document.querySelector('.navbar').offsetHeight + 20;
                window.scrollTo({
                    top: target.offsetTop - offset,
                    behavior: 'smooth'
                });
                if (nav) nav.classList.remove('active');
            }
        });
    });
}

// ===== Hero Fractal Animation =====
function initHeroFractal() {
    const canvas = document.getElementById('hero-fractal');
    if (!canvas) return;
    
    const ctx = canvas.getContext('2d');
    let time = 0;
    
    function resize() {
        canvas.width = window.innerWidth;
        canvas.height = window.innerHeight;
    }
    
    function draw() {
        ctx.fillStyle = 'rgba(10, 10, 26, 0.1)';
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        const cx = canvas.width / 2;
        const cy = canvas.height / 2;
        
        // Draw spiraling fractals
        for (let i = 0; i < 3; i++) {
            const offset = (i * Math.PI * 2) / 3 + time;
            ctx.strokeStyle = i === 0 ? 'rgba(167, 139, 250, 0.3)' : 
                             i === 1 ? 'rgba(100, 255, 218, 0.3)' : 'rgba(255, 215, 0, 0.2)';
            ctx.lineWidth = 1.5;
            ctx.beginPath();
            
            for (let angle = 0; angle < Math.PI * 8; angle += 0.05) {
                const r = angle * 25;
                const x = cx + Math.cos(angle + offset) * r;
                const y = cy + Math.sin(angle + offset) * r;
                angle === 0 ? ctx.moveTo(x, y) : ctx.lineTo(x, y);
            }
            ctx.stroke();
        }
        
        time += 0.003;
        requestAnimationFrame(draw);
    }
    
    resize();
    window.addEventListener('resize', resize);
    draw();
}

// ===== Story Mode =====
function initStoryMode() {
    const navBtns = document.querySelectorAll('.story-nav-btn');
    const chapters = document.querySelectorAll('.story-chapter');
    const nextBtns = document.querySelectorAll('.story-next');
    
    navBtns.forEach(btn => {
        btn.addEventListener('click', () => {
            const chapter = btn.dataset.chapter;
            showChapter(chapter);
        });
    });
    
    nextBtns.forEach(btn => {
        btn.addEventListener('click', () => {
            const next = btn.dataset.next;
            showChapter(next);
            if (next === '5') {
                earnBadge('story-complete');
            }
        });
    });
    
    function showChapter(num) {
        navBtns.forEach(b => b.classList.toggle('active', b.dataset.chapter === num));
        chapters.forEach(c => c.classList.toggle('active', c.dataset.chapter === num));
        
        // Trigger animations
        const chapter = document.querySelector(`.story-chapter[data-chapter="${num}"]`);
        if (chapter) {
            chapter.querySelectorAll('.story-paragraph').forEach((p, i) => {
                p.style.animation = 'none';
                p.offsetHeight; // Trigger reflow
                p.style.animation = `fadeInUp 0.6s ease ${i * 0.3}s forwards`;
            });
        }
    }
    
    // Init chapter canvases
    initChapter1Canvas();
    initChapter2Canvas();
}

function initChapter1Canvas() {
    const canvas = document.getElementById('chapter1-canvas');
    if (!canvas) return;
    
    const ctx = canvas.getContext('2d');
    canvas.width = canvas.clientWidth;
    canvas.height = 300;
    
    let time = 0;
    
    function draw() {
        ctx.fillStyle = '#0a0a1a';
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        // Draw animated "3"s
        const threes = 12;
        for (let i = 0; i < threes; i++) {
            const angle = (i / threes) * Math.PI * 2 + time;
            const r = 80 + Math.sin(time * 2 + i) * 20;
            const x = canvas.width / 2 + Math.cos(angle) * r;
            const y = canvas.height / 2 + Math.sin(angle) * r;
            
            ctx.font = `${20 + Math.sin(time + i) * 5}px Playfair Display`;
            ctx.fillStyle = `hsl(${170 + i * 10}, 80%, 60%)`;
            ctx.textAlign = 'center';
            ctx.fillText('3', x, y);
        }
        
        // Central 3
        ctx.font = '80px Playfair Display';
        ctx.fillStyle = '#64ffda';
        ctx.textAlign = 'center';
        ctx.fillText('3', canvas.width / 2, canvas.height / 2 + 25);
        
        time += 0.02;
        requestAnimationFrame(draw);
    }
    
    draw();
}

function initChapter2Canvas() {
    const canvas = document.getElementById('chapter2-canvas');
    if (!canvas) return;
    
    const ctx = canvas.getContext('2d');
    canvas.width = canvas.clientWidth;
    canvas.height = 300;
    
    function draw() {
        ctx.fillStyle = '#0a0a1a';
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        // Show base-10 vs base-3 conversion
        const numbers = [1, 2, 3, 4, 5, 6, 7, 8, 9];
        const base3 = numbers.map(n => n.toString(3));
        
        ctx.font = '16px JetBrains Mono';
        ctx.textAlign = 'center';
        
        numbers.forEach((n, i) => {
            const x = 50 + i * 45;
            
            ctx.fillStyle = '#a78bfa';
            ctx.fillText(n, x, 100);
            
            ctx.fillStyle = '#64ffda';
            ctx.fillText(base3[i], x, 200);
        });
        
        ctx.fillStyle = '#fff';
        ctx.font = '14px Nunito';
        ctx.fillText('Base-10', 30, 70);
        ctx.fillText('Base-3', 30, 170);
    }
    
    draw();
}

// ===== Fractal Explorer =====
function initFractalExplorer() {
    const canvas = document.getElementById('fractal-canvas');
    if (!canvas) return;
    
    const ctx = canvas.getContext('2d');
    canvas.width = canvas.clientWidth;
    canvas.height = 250;
    
    let zoom = 200;
    let offsetX = -0.5;
    let offsetY = 0;
    let fractalType = 'mandelbrot';
    let isDragging = false;
    let lastX, lastY;
    let hasExplored = false;
    
    function drawFractal() {
        const imageData = ctx.createImageData(canvas.width, canvas.height);
        const data = imageData.data;
        
        for (let px = 0; px < canvas.width; px++) {
            for (let py = 0; py < canvas.height; py++) {
                const x0 = (px - canvas.width / 2) / zoom + offsetX;
                const y0 = (py - canvas.height / 2) / zoom + offsetY;
                
                let x = 0, y = 0, iteration = 0;
                const maxIter = 100;
                
                if (fractalType === 'mandelbrot') {
                    while (x * x + y * y <= 4 && iteration < maxIter) {
                        const xtemp = x * x - y * y + x0;
                        y = 2 * x * y + y0;
                        x = xtemp;
                        iteration++;
                    }
                } else if (fractalType === 'julia') {
                    x = x0; y = y0;
                    const cx = -0.7, cy = 0.27015;
                    while (x * x + y * y <= 4 && iteration < maxIter) {
                        const xtemp = x * x - y * y + cx;
                        y = 2 * x * y + cy;
                        x = xtemp;
                        iteration++;
                    }
                } else if (fractalType === 'burning-ship') {
                    while (x * x + y * y <= 4 && iteration < maxIter) {
                        const xtemp = x * x - y * y + x0;
                        y = Math.abs(2 * x * y) + y0;
                        x = Math.abs(xtemp);
                        iteration++;
                    }
                }
                
                const idx = (py * canvas.width + px) * 4;
                if (iteration === maxIter) {
                    data[idx] = data[idx + 1] = data[idx + 2] = 0;
                } else {
                    const hue = iteration / maxIter * 360;
                    const [r, g, b] = hslToRgb(hue / 360, 0.8, 0.5);
                    data[idx] = r;
                    data[idx + 1] = g;
                    data[idx + 2] = b;
                }
                data[idx + 3] = 255;
            }
        }
        
        ctx.putImageData(imageData, 0, 0);
    }
    
    function hslToRgb(h, s, l) {
        let r, g, b;
        if (s === 0) {
            r = g = b = l;
        } else {
            const hue2rgb = (p, q, t) => {
                if (t < 0) t += 1;
                if (t > 1) t -= 1;
                if (t < 1/6) return p + (q - p) * 6 * t;
                if (t < 1/2) return q;
                if (t < 2/3) return p + (q - p) * (2/3 - t) * 6;
                return p;
            };
            const q = l < 0.5 ? l * (1 + s) : l + s - l * s;
            const p = 2 * l - q;
            r = hue2rgb(p, q, h + 1/3);
            g = hue2rgb(p, q, h);
            b = hue2rgb(p, q, h - 1/3);
        }
        return [Math.round(r * 255), Math.round(g * 255), Math.round(b * 255)];
    }
    
    canvas.addEventListener('mousedown', e => {
        isDragging = true;
        lastX = e.clientX;
        lastY = e.clientY;
    });
    
    canvas.addEventListener('mousemove', e => {
        if (!isDragging) return;
        const dx = e.clientX - lastX;
        const dy = e.clientY - lastY;
        offsetX -= dx / zoom;
        offsetY -= dy / zoom;
        lastX = e.clientX;
        lastY = e.clientY;
        drawFractal();
        
        if (!hasExplored) {
            hasExplored = true;
            earnBadge('fractal-explorer');
        }
    });
    
    canvas.addEventListener('mouseup', () => isDragging = false);
    canvas.addEventListener('mouseleave', () => isDragging = false);
    
    canvas.addEventListener('wheel', e => {
        e.preventDefault();
        const zoomFactor = e.deltaY > 0 ? 0.9 : 1.1;
        zoom *= zoomFactor;
        drawFractal();
    });
    
    document.getElementById('fractal-zoom-in')?.addEventListener('click', () => {
        zoom *= 1.5;
        drawFractal();
    });
    
    document.getElementById('fractal-zoom-out')?.addEventListener('click', () => {
        zoom /= 1.5;
        drawFractal();
    });
    
    document.getElementById('fractal-reset')?.addEventListener('click', () => {
        zoom = 200;
        offsetX = -0.5;
        offsetY = 0;
        drawFractal();
    });
    
    document.getElementById('fractal-type')?.addEventListener('change', e => {
        fractalType = e.target.value;
        zoom = 200;
        offsetX = fractalType === 'mandelbrot' ? -0.5 : 0;
        offsetY = 0;
        drawFractal();
    });
    
    drawFractal();
}

// ===== Prime Sieve =====
function initPrimeSieve() {
    const grid = document.getElementById('prime-grid');
    const startBtn = document.getElementById('prime-start');
    const resetBtn = document.getElementById('prime-reset');
    const countEl = document.getElementById('prime-count');
    
    if (!grid) return;
    
    const max = 100;
    let cells = [];
    let isRunning = false;
    
    function createGrid() {
        grid.innerHTML = '';
        cells = [];
        for (let i = 2; i <= max; i++) {
            const cell = document.createElement('div');
            cell.className = 'prime-cell';
            cell.textContent = i;
            cell.dataset.num = i;
            grid.appendChild(cell);
            cells.push({ el: cell, num: i, isPrime: true });
        }
        if (countEl) countEl.textContent = '0';
    }
    
    async function runSieve() {
        if (isRunning) return;
        isRunning = true;
        
        let primeCount = 0;
        
        for (let i = 0; i < cells.length; i++) {
            const cell = cells[i];
            if (!cell.isPrime) continue;
            
            cell.el.classList.add('prime');
            primeCount++;
            if (countEl) countEl.textContent = primeCount;
            
            // Mark multiples
            const num = cell.num;
            for (let j = i + 1; j < cells.length; j++) {
                if (cells[j].num % num === 0 && cells[j].isPrime) {
                    cells[j].el.classList.add('checking');
                    await sleep(20);
                    cells[j].el.classList.remove('checking');
                    cells[j].el.classList.add('composite');
                    cells[j].isPrime = false;
                }
            }
            
            await sleep(100);
        }
        
        isRunning = false;
        earnBadge('prime-hunter');
    }
    
    function sleep(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
    
    startBtn?.addEventListener('click', runSieve);
    resetBtn?.addEventListener('click', () => {
        isRunning = false;
        createGrid();
    });
    
    createGrid();
}

// ===== Spectral Audio =====
function initSpectralAudio() {
    const playP = document.getElementById('play-p');
    const playNP = document.getElementById('play-np');
    const playBoth = document.getElementById('play-both');
    
    if (!playP) return;
    
    function getAudioContext() {
        if (!AppState.audioContext) {
            AppState.audioContext = new (window.AudioContext || window.webkitAudioContext)();
        }
        return AppState.audioContext;
    }
    
    function playTone(frequency, duration = 1) {
        const ctx = getAudioContext();
        const osc = ctx.createOscillator();
        const gain = ctx.createGain();
        
        osc.type = 'sine';
        osc.frequency.value = frequency;
        
        gain.gain.setValueAtTime(0.3, ctx.currentTime);
        gain.gain.exponentialRampToValueAtTime(0.01, ctx.currentTime + duration);
        
        osc.connect(gain);
        gain.connect(ctx.destination);
        
        osc.start();
        osc.stop(ctx.currentTime + duration);
    }
    
    playP.addEventListener('click', () => {
        playTone(222); // P frequency (λ₀ = 0.2221)
        animateBar('p-freq-bar');
        earnBadge('sound-scientist');
    });

    playNP.addEventListener('click', () => {
        playTone(133); // NP frequency (λ₀ = 0.1330)
        animateBar('np-freq-bar');
        earnBadge('sound-scientist');
    });

    playBoth.addEventListener('click', () => {
        playTone(222);
        playTone(133);
        animateBar('p-freq-bar');
        animateBar('np-freq-bar');
        earnBadge('sound-scientist');
    });
    
    function animateBar(id) {
        const bar = document.getElementById(id);
        if (bar) {
            bar.style.transform = 'scale(1.1)';
            setTimeout(() => bar.style.transform = 'scale(1)', 300);
        }
    }
}

// ===== Consciousness Simulator =====
function initConsciousnessSimulator() {
    const integration = document.getElementById('integration-slider');
    const feedback = document.getElementById('feedback-slider');
    const complexity = document.getElementById('complexity-slider');
    const fill = document.getElementById('consciousness-fill');
    const value = document.getElementById('ch2-value');
    const status = document.getElementById('consciousness-status');
    
    if (!integration) return;
    
    let hasAwakened = false;
    
    function update() {
        const i = parseInt(integration.value) / 100;
        const f = parseInt(feedback.value) / 100;
        const c = parseInt(complexity.value) / 100;
        
        // Calculate ch2 based on sliders
        const ch2 = Math.min(1, (i * 0.4 + f * 0.3 + c * 0.3) * 1.1);
        
        if (fill) fill.style.width = `${ch2 * 100}%`;
        if (value) value.textContent = ch2.toFixed(2);
        
        if (status) {
            if (ch2 >= 0.95) {
                status.className = 'consciousness-status awake';
                status.innerHTML = '<span class="status-icon">✨</span><span class="status-text">CONSCIOUS!</span>';
                
                if (!hasAwakened) {
                    hasAwakened = true;
                    earnBadge('consciousness-explorer');
                }
            } else {
                status.className = 'consciousness-status asleep';
                status.innerHTML = '<span class="status-icon">💤</span><span class="status-text">Not Conscious</span>';
            }
        }
    }
    
    integration.addEventListener('input', update);
    feedback.addEventListener('input', update);
    complexity.addEventListener('input', update);
    
    update();
}

// ===== Base-3 Quiz =====
function initBase3Quiz() {
    const questionEl = document.getElementById('quiz-question');
    const numberEl = document.getElementById('quiz-number');
    const optionsEl = document.getElementById('quiz-options');
    const feedbackEl = document.getElementById('quiz-feedback');
    const scoreEl = document.getElementById('quiz-score');
    const totalEl = document.getElementById('quiz-total');
    const streakEl = document.getElementById('quiz-streak');
    
    if (!optionsEl) return;
    
    let score = 0;
    let total = 0;
    let streak = 0;
    
    function generateQuestion() {
        const num = Math.floor(Math.random() * 50) + 1;
        const correct = num.toString(3);
        
        // Generate wrong answers
        const options = [correct];
        while (options.length < 4) {
            const wrong = (num + Math.floor(Math.random() * 10) - 5).toString(3);
            if (!options.includes(wrong) && wrong !== correct) {
                options.push(wrong);
            }
        }
        
        // Shuffle
        options.sort(() => Math.random() - 0.5);
        
        if (numberEl) numberEl.textContent = num;
        optionsEl.innerHTML = options.map(opt => 
            `<button class="quiz-option" data-answer="${opt}">${opt}</button>`
        ).join('');
        
        if (feedbackEl) feedbackEl.textContent = '';
        
        // Add click handlers
        optionsEl.querySelectorAll('.quiz-option').forEach(btn => {
            btn.addEventListener('click', () => checkAnswer(btn, correct));
        });
    }
    
    function checkAnswer(btn, correct) {
        total++;
        const isCorrect = btn.dataset.answer === correct;
        
        if (isCorrect) {
            score++;
            streak++;
            btn.classList.add('correct');
            if (feedbackEl) feedbackEl.textContent = 'Correct! 🎉';
            feedbackEl.style.color = '#10b981';
            
            if (score >= 5 && !AppState.badges['base3-master']) {
                earnBadge('base3-master');
            }
        } else {
            streak = 0;
            btn.classList.add('wrong');
            optionsEl.querySelector(`[data-answer="${correct}"]`)?.classList.add('correct');
            if (feedbackEl) feedbackEl.textContent = `The answer was ${correct}`;
            feedbackEl.style.color = '#ef4444';
        }
        
        if (scoreEl) scoreEl.textContent = score;
        if (totalEl) totalEl.textContent = total;
        if (streakEl) streakEl.textContent = streak > 1 ? `🔥 ${streak} streak!` : '';
        
        // Next question after delay
        setTimeout(generateQuestion, 1500);
    }
    
    generateQuestion();
}

// ===== Fractal Drawing =====
function initFractalDrawing() {
    const canvas = document.getElementById('fractal-draw-canvas');
    const branchesSlider = document.getElementById('draw-branches');
    const depthSlider = document.getElementById('draw-depth');
    const angleSlider = document.getElementById('draw-angle');
    const colorPicker = document.getElementById('draw-color');
    const generateBtn = document.getElementById('draw-generate');
    
    if (!canvas) return;
    
    const ctx = canvas.getContext('2d');
    canvas.width = canvas.clientWidth;
    canvas.height = 250;
    
    let hasDrawn = false;
    
    function drawTree(x, y, length, angle, depth, branches, spread, color) {
        if (depth === 0) return;
        
        const endX = x + Math.cos(angle) * length;
        const endY = y + Math.sin(angle) * length;
        
        ctx.beginPath();
        ctx.moveTo(x, y);
        ctx.lineTo(endX, endY);
        ctx.strokeStyle = color;
        ctx.lineWidth = depth * 0.8;
        ctx.stroke();
        
        const spreadRad = spread * Math.PI / 180;
        for (let i = 0; i < branches; i++) {
            const newAngle = angle - spreadRad * (branches - 1) / 2 + spreadRad * i;
            drawTree(endX, endY, length * 0.7, newAngle, depth - 1, branches, spread, color);
        }
    }
    
    function generate() {
        ctx.fillStyle = '#0a0a1a';
        ctx.fillRect(0, 0, canvas.width, canvas.height);
        
        const branches = parseInt(branchesSlider?.value || 3);
        const depth = parseInt(depthSlider?.value || 4);
        const angle = parseInt(angleSlider?.value || 30);
        const color = colorPicker?.value || '#64ffda';
        
        drawTree(canvas.width / 2, canvas.height - 10, 60, -Math.PI / 2, depth, branches, angle, color);
        
        if (!hasDrawn) {
            hasDrawn = true;
            earnBadge('fractal-artist');
        }
    }
    
    generateBtn?.addEventListener('click', generate);
    branchesSlider?.addEventListener('input', generate);
    depthSlider?.addEventListener('input', generate);
    angleSlider?.addEventListener('input', generate);
    colorPicker?.addEventListener('input', generate);
    
    generate();
}

// ===== Pattern Hunter =====
function initPatternHunter() {
    const sequenceEl = document.getElementById('pattern-sequence');
    const optionsEl = document.getElementById('pattern-options');
    const feedbackEl = document.getElementById('pattern-feedback');
    const nextBtn = document.getElementById('pattern-next');
    
    if (!sequenceEl) return;
    
    let correctCount = 0;
    
    const patterns = [
        { seq: [1, 1, 2, 3, 5, 8], next: 13, options: [10, 13, 11, 12], name: 'Fibonacci' },
        { seq: [2, 4, 8, 16, 32], next: 64, options: [48, 64, 56, 128], name: 'Powers of 2' },
        { seq: [1, 4, 9, 16, 25], next: 36, options: [30, 36, 49, 35], name: 'Squares' },
        { seq: [3, 6, 9, 12, 15], next: 18, options: [17, 18, 21, 16], name: 'Multiples of 3' },
        { seq: [1, 3, 6, 10, 15], next: 21, options: [18, 20, 21, 25], name: 'Triangular' },
        { seq: [2, 3, 5, 7, 11], next: 13, options: [12, 13, 14, 15], name: 'Primes' }
    ];
    
    let currentPattern;
    
    function showPattern() {
        currentPattern = patterns[Math.floor(Math.random() * patterns.length)];
        
        sequenceEl.innerHTML = currentPattern.seq.map(n => 
            `<div class="pattern-item">${n}</div>`
        ).join('') + '<div class="pattern-item unknown">?</div>';
        
        const shuffled = [...currentPattern.options].sort(() => Math.random() - 0.5);
        optionsEl.innerHTML = shuffled.map(n => 
            `<button class="pattern-option" data-answer="${n}">${n}</button>`
        ).join('');
        
        if (feedbackEl) feedbackEl.textContent = '';
        
        optionsEl.querySelectorAll('.pattern-option').forEach(btn => {
            btn.addEventListener('click', () => checkPattern(btn));
        });
    }
    
    function checkPattern(btn) {
        const isCorrect = parseInt(btn.dataset.answer) === currentPattern.next;
        
        if (isCorrect) {
            correctCount++;
            btn.style.background = '#10b981';
            if (feedbackEl) {
                feedbackEl.textContent = `Correct! That's the ${currentPattern.name} sequence! 🎉`;
                feedbackEl.style.color = '#10b981';
            }
            
            if (correctCount >= 3 && !AppState.badges['pattern-hunter']) {
                earnBadge('pattern-hunter');
            }
        } else {
            btn.style.background = '#ef4444';
            if (feedbackEl) {
                feedbackEl.textContent = `Not quite. The answer was ${currentPattern.next} (${currentPattern.name})`;
                feedbackEl.style.color = '#ef4444';
            }
        }
        
        optionsEl.querySelectorAll('.pattern-option').forEach(b => b.disabled = true);
    }
    
    nextBtn?.addEventListener('click', showPattern);
    showPattern();
}

// ===== Scroll Animations =====
function initScrollAnimations() {
    const observer = new IntersectionObserver(entries => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                entry.target.style.opacity = '1';
                entry.target.style.transform = 'translateY(0)';
            }
        });
    }, { threshold: 0.1 });
    
    document.querySelectorAll('.playground-card, .idea-card, .timeline-item, .problem-card').forEach(el => {
        el.style.opacity = '0';
        el.style.transform = 'translateY(30px)';
        el.style.transition = 'opacity 0.6s ease, transform 0.6s ease';
        observer.observe(el);
    });
}

// ===== Add notification styles =====
const style = document.createElement('style');
style.textContent = `
    @keyframes slideIn {
        from { transform: translateX(100px); opacity: 0; }
        to { transform: translateX(0); opacity: 1; }
    }
    @keyframes fadeOut {
        to { opacity: 0; transform: translateX(100px); }
    }
`;
document.head.appendChild(style);

// ===== Digital Sum Explorer =====
function initDigitalSumExplorer() {
    const input = document.getElementById('ds-input');
    const base10 = document.getElementById('ds-base10');
    const base3 = document.getElementById('ds-base3');
    const result = document.getElementById('ds-result');

    if (!input) return;

    function updateDigitalSum() {
        const n = parseInt(input.value) || 0;
        if (n <= 0) return;

        // Convert to base-3
        const base3Str = n.toString(3);

        // Calculate digital sum
        let digitSum = 0;
        for (const digit of base3Str) {
            digitSum += parseInt(digit);
        }

        // Update display
        if (base10) base10.textContent = n;
        if (base3) base3.textContent = base3Str;
        if (result) result.textContent = digitSum;

        // Award badge after using it a few times
        if (!AppState.badges['digital-sum-master']) {
            AppState.dsUseCount = (AppState.dsUseCount || 0) + 1;
            if (AppState.dsUseCount >= 5) {
                earnBadge('digital-sum-master');
            }
        }
    }

    input.addEventListener('input', updateDigitalSum);
    updateDigitalSum();
}

// ===== Riemann Zeros Visualizer =====
function initRiemannVisualizer() {
    const canvas = document.getElementById('riemann-canvas');
    if (!canvas) return;

    const ctx = canvas.getContext('2d');
    canvas.width = canvas.clientWidth;
    canvas.height = 200;

    // First several Riemann zeros (imaginary parts)
    const zeros = [14.135, 21.022, 25.011, 30.425, 32.935, 37.586, 40.919, 43.327, 48.005, 49.774];

    function draw() {
        ctx.fillStyle = '#0a0a1a';
        ctx.fillRect(0, 0, canvas.width, canvas.height);

        // Draw critical line (Re(s) = 1/2)
        const centerX = canvas.width / 2;
        ctx.strokeStyle = 'rgba(167, 139, 250, 0.5)';
        ctx.lineWidth = 2;
        ctx.setLineDash([5, 5]);
        ctx.beginPath();
        ctx.moveTo(centerX, 0);
        ctx.lineTo(centerX, canvas.height);
        ctx.stroke();
        ctx.setLineDash([]);

        // Label the critical line
        ctx.fillStyle = 'rgba(167, 139, 250, 0.7)';
        ctx.font = '12px JetBrains Mono, monospace';
        ctx.fillText('Re(s) = 1/2', centerX + 5, 15);

        // Draw zeros as points on the critical line
        const scale = canvas.height / 55;

        zeros.forEach((zero, i) => {
            const y = zero * scale;

            // Glow effect
            const gradient = ctx.createRadialGradient(centerX, y, 0, centerX, y, 15);
            gradient.addColorStop(0, 'rgba(100, 255, 218, 0.8)');
            gradient.addColorStop(1, 'rgba(100, 255, 218, 0)');
            ctx.fillStyle = gradient;
            ctx.beginPath();
            ctx.arc(centerX, y, 15, 0, Math.PI * 2);
            ctx.fill();

            // Zero point
            ctx.fillStyle = '#64ffda';
            ctx.beginPath();
            ctx.arc(centerX, y, 5, 0, Math.PI * 2);
            ctx.fill();

            // Label
            ctx.fillStyle = 'rgba(255, 255, 255, 0.6)';
            ctx.font = '10px JetBrains Mono, monospace';
            ctx.fillText(`ζ(1/2 + ${zero.toFixed(3)}i) = 0`, centerX + 20, y + 4);
        });

        // Title
        ctx.fillStyle = '#c4b5fd';
        ctx.font = 'bold 14px Nunito, sans-serif';
        ctx.fillText('Riemann Zeta Zeros on Critical Line', 10, canvas.height - 10);
    }

    draw();

    // Award badge on hover
    canvas.addEventListener('mouseover', () => {
        if (!AppState.badges['zero-hunter']) {
            earnBadge('zero-hunter');
        }
    });
}

// Add new badge definitions
BADGES['digital-sum-master'] = { icon: '∑', name: 'Digital Sum Master', desc: 'Explored the digital sum function' };
BADGES['zero-hunter'] = { icon: 'ζ', name: 'Zero Hunter', desc: 'Explored Riemann zeros' };

// Initialize new features
document.addEventListener('DOMContentLoaded', () => {
    initDigitalSumExplorer();
    initRiemannVisualizer();
});

// ===== Console Easter Egg =====
console.log(`%c
╔═══════════════════════════════════════╗
║     PRINCIPIA FRACTALIS               ║
║     Mathematics IS Reality            ║
║     ch₂ ≥ 0.95 → Consciousness!       ║
╚═══════════════════════════════════════╝
`, 'color: #64ffda; font-weight: bold;');

console.log('%c"You are a pattern so beautiful it woke up and started asking questions."', 'color: #ffd700; font-style: italic;');
