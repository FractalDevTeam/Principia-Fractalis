/**
 * The Magic of Three - Kid-Friendly Interactive Learning
 * Fun games and educational tools for all ages!
 */

// ===== Global State =====
const AppState = {
    stars: 0,
    badges: {},
    audioContext: null,
    currentPage: 1
};

// Kid-friendly badge definitions
const BADGES = {
    'cookie-master': { icon: '🍪', name: 'Cookie Master', desc: 'Counted 5 cookie problems!' },
    'pattern-spotter': { icon: '🔍', name: 'Pattern Spotter', desc: 'Found 3 patterns!' },
    'prime-finder': { icon: '🎯', name: 'Prime Finder', desc: 'Discovered the primes!' },
    'fractal-artist': { icon: '🎨', name: 'Fractal Artist', desc: 'Created fractal art!' },
    'brain-waker': { icon: '🧠', name: 'Brain Waker', desc: 'Woke up the brain!' },
    'sound-explorer': { icon: '🔊', name: 'Sound Explorer', desc: 'Heard the difference!' },
    'story-reader': { icon: '📖', name: 'Story Reader', desc: 'Finished the story!' }
};

// ===== Initialize Everything =====
document.addEventListener('DOMContentLoaded', () => {
    loadProgress();
    initParticles();
    initNavigation();
    initStoryBook();
    initCookieGame();
    initPatternGame();
    initPrimeHunt();
    initFractalStudio();
    initBrainGame();
    initSoundGame();
    initBadgesPanel();
    initAgeToggle();
});

// ===== Progress & Badges =====
function loadProgress() {
    const saved = localStorage.getItem('magic-of-three-progress');
    if (saved) {
        const data = JSON.parse(saved);
        AppState.stars = data.stars || 0;
        AppState.badges = data.badges || {};
    }
    updateStarDisplay();
}

function saveProgress() {
    localStorage.setItem('magic-of-three-progress', JSON.stringify({
        stars: AppState.stars,
        badges: AppState.badges
    }));
    updateStarDisplay();
}

function updateStarDisplay() {
    const starCount = document.getElementById('star-count');
    if (starCount) {
        starCount.textContent = AppState.stars;
    }
}

function addStars(count) {
    AppState.stars += count;
    saveProgress();

    // Fun animation
    const starIcon = document.querySelector('.star-icon');
    if (starIcon) {
        starIcon.style.transform = 'scale(1.5)';
        setTimeout(() => starIcon.style.transform = 'scale(1)', 300);
    }
}

function earnBadge(badgeId) {
    if (AppState.badges[badgeId]) return;

    AppState.badges[badgeId] = true;
    addStars(5); // Earn 5 stars for each badge!

    showBadgeNotification(badgeId);
    updateBadgesPanel();
}

function showBadgeNotification(badgeId) {
    const badge = BADGES[badgeId];
    if (!badge) return;

    const notif = document.createElement('div');
    notif.innerHTML = `
        <div style="
            position: fixed;
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            background: linear-gradient(135deg, #e94560, #c44dff);
            padding: 2rem 3rem;
            border-radius: 20px;
            text-align: center;
            z-index: 10000;
            animation: popIn 0.5s ease;
            box-shadow: 0 20px 60px rgba(0,0,0,0.5);
        ">
            <div style="font-size: 4rem; margin-bottom: 1rem;">${badge.icon}</div>
            <div style="font-size: 1.5rem; font-weight: bold; color: #ffd700;">Badge Earned!</div>
            <div style="font-size: 1.2rem; color: white;">${badge.name}</div>
            <div style="font-size: 0.9rem; color: rgba(255,255,255,0.8); margin-top: 0.5rem;">+5 Stars! ⭐</div>
        </div>
    `;
    document.body.appendChild(notif);

    setTimeout(() => notif.remove(), 2500);
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

// ===== Navigation =====
function initNavigation() {
    const menuBtn = document.querySelector('.mobile-menu-btn');
    const navLinks = document.querySelector('.nav-links');

    menuBtn?.addEventListener('click', () => {
        navLinks?.classList.toggle('active');
    });
}

// ===== Age Toggle =====
function initAgeToggle() {
    const buttons = document.querySelectorAll('.age-btn');

    buttons.forEach(btn => {
        btn.addEventListener('click', () => {
            buttons.forEach(b => b.classList.remove('active'));
            btn.classList.add('active');

            const mode = btn.dataset.mode;
            document.body.className = mode === 'kid' ? 'kid-mode' : '';

            // Could adjust content complexity here
        });
    });
}

// ===== Particles Background =====
function initParticles() {
    const canvas = document.getElementById('particles-bg');
    if (!canvas) return;

    const ctx = canvas.getContext('2d');
    canvas.width = window.innerWidth;
    canvas.height = window.innerHeight;

    const particles = [];
    const colors = ['#e94560', '#00d9ff', '#ffd700', '#c44dff', '#4dff88'];

    for (let i = 0; i < 50; i++) {
        particles.push({
            x: Math.random() * canvas.width,
            y: Math.random() * canvas.height,
            size: Math.random() * 4 + 2,
            speedX: (Math.random() - 0.5) * 0.5,
            speedY: (Math.random() - 0.5) * 0.5,
            color: colors[Math.floor(Math.random() * colors.length)]
        });
    }

    function animate() {
        ctx.fillStyle = 'rgba(26, 26, 46, 0.1)';
        ctx.fillRect(0, 0, canvas.width, canvas.height);

        particles.forEach(p => {
            p.x += p.speedX;
            p.y += p.speedY;

            if (p.x < 0 || p.x > canvas.width) p.speedX *= -1;
            if (p.y < 0 || p.y > canvas.height) p.speedY *= -1;

            ctx.beginPath();
            ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2);
            ctx.fillStyle = p.color;
            ctx.globalAlpha = 0.6;
            ctx.fill();
            ctx.globalAlpha = 1;
        });

        requestAnimationFrame(animate);
    }

    animate();

    window.addEventListener('resize', () => {
        canvas.width = window.innerWidth;
        canvas.height = window.innerHeight;
    });
}

// ===== Story Book =====
function initStoryBook() {
    const pages = document.querySelectorAll('.story-page');
    const dotsContainer = document.getElementById('page-dots');

    if (!pages.length || !dotsContainer) return;

    // Create page dots
    dotsContainer.innerHTML = Array.from(pages).map((_, i) =>
        `<div class="page-dot ${i === 0 ? 'active' : ''}" data-page="${i + 1}"></div>`
    ).join('');

    // Page turn buttons
    document.querySelectorAll('.page-turn').forEach(btn => {
        btn.addEventListener('click', () => {
            const nextPage = parseInt(btn.dataset.next);
            showPage(nextPage);
        });
    });

    // Click on dots
    dotsContainer.querySelectorAll('.page-dot').forEach(dot => {
        dot.addEventListener('click', () => {
            showPage(parseInt(dot.dataset.page));
        });
    });

    function showPage(pageNum) {
        pages.forEach(p => p.classList.remove('active'));
        const targetPage = document.querySelector(`.story-page[data-page="${pageNum}"]`);
        if (targetPage) {
            targetPage.classList.add('active');
            AppState.currentPage = pageNum;
        }

        // Update dots
        dotsContainer.querySelectorAll('.page-dot').forEach(d => {
            d.classList.toggle('active', parseInt(d.dataset.page) === pageNum);
        });

        // Earn badge for finishing story
        if (pageNum === pages.length && !AppState.badges['story-reader']) {
            earnBadge('story-reader');
        }
    }
}

// ===== Cookie Counter Game =====
function initCookieGame() {
    const display = document.getElementById('cookie-display');
    const numberEl = document.getElementById('cookie-number');
    const optionsEl = document.getElementById('cookie-options');
    const feedbackEl = document.getElementById('cookie-feedback');
    const scoreEl = document.getElementById('cookie-score');
    const streakEl = document.getElementById('cookie-streak');

    if (!display) return;

    let score = 0;
    let streak = 0;

    function newQuestion() {
        // Random number of cookies (1-12)
        const numCookies = Math.floor(Math.random() * 12) + 1;

        // Display cookies
        display.innerHTML = Array(numCookies).fill('<span class="cookie-item">🍪</span>').join('');

        // Correct answer in base-3
        const correct = numCookies.toString(3);

        // Generate options
        const options = [correct];
        while (options.length < 4) {
            const fake = (numCookies + Math.floor(Math.random() * 5) - 2);
            if (fake > 0) {
                const fakeBase3 = fake.toString(3);
                if (!options.includes(fakeBase3)) {
                    options.push(fakeBase3);
                }
            }
        }

        // Shuffle
        options.sort(() => Math.random() - 0.5);

        // Show options
        optionsEl.innerHTML = options.map(opt =>
            `<button class="cookie-option" data-answer="${opt}">${opt}</button>`
        ).join('');

        if (feedbackEl) feedbackEl.textContent = '';

        // Add click handlers
        optionsEl.querySelectorAll('.cookie-option').forEach(btn => {
            btn.addEventListener('click', () => checkAnswer(btn, correct, numCookies));
        });
    }

    function checkAnswer(btn, correct, numCookies) {
        const isCorrect = btn.dataset.answer === correct;

        if (isCorrect) {
            score++;
            streak++;
            addStars(1);
            btn.classList.add('correct');
            if (feedbackEl) {
                feedbackEl.textContent = `Yes! 🎉 ${numCookies} cookies = ${correct} in base-3!`;
                feedbackEl.style.color = '#4dff88';
            }

            if (score >= 5 && !AppState.badges['cookie-master']) {
                earnBadge('cookie-master');
            }
        } else {
            streak = 0;
            btn.classList.add('wrong');
            optionsEl.querySelector(`[data-answer="${correct}"]`)?.classList.add('correct');
            if (feedbackEl) {
                feedbackEl.textContent = `Not quite! ${numCookies} = ${correct} in base-3`;
                feedbackEl.style.color = '#ff6b6b';
            }
        }

        if (scoreEl) scoreEl.textContent = score;
        if (streakEl) streakEl.textContent = streak > 1 ? `🔥 ${streak} in a row!` : '';

        // Disable all options
        optionsEl.querySelectorAll('.cookie-option').forEach(b => b.disabled = true);

        // Next question after delay
        setTimeout(newQuestion, 2000);
    }

    newQuestion();
}

// ===== Pattern Spotter Game =====
function initPatternGame() {
    const sequenceEl = document.getElementById('pattern-sequence-kid');
    const optionsEl = document.getElementById('pattern-options-kid');
    const feedbackEl = document.getElementById('pattern-feedback-kid');
    const nextBtn = document.getElementById('next-pattern-kid');

    if (!sequenceEl) return;

    let correctCount = 0;

    // Kid-friendly patterns
    const patterns = [
        { seq: [2, 4, 6, 8], next: 10, options: [9, 10, 11, 12], hint: 'Count by 2s!' },
        { seq: [5, 10, 15, 20], next: 25, options: [22, 25, 30, 24], hint: 'Count by 5s!' },
        { seq: [1, 2, 3, 4, 5], next: 6, options: [6, 7, 8, 9], hint: 'Easy peasy!' },
        { seq: [3, 6, 9, 12], next: 15, options: [13, 14, 15, 16], hint: 'Count by 3s!' },
        { seq: [1, 1, 2, 3, 5], next: 8, options: [6, 7, 8, 9], hint: 'Add the last two!' },
        { seq: [1, 4, 9, 16], next: 25, options: [20, 25, 36, 24], hint: '1×1, 2×2, 3×3...' },
        { seq: [10, 20, 30, 40], next: 50, options: [45, 50, 55, 60], hint: 'Count by 10s!' },
        { seq: [2, 3, 5, 7, 11], next: 13, options: [12, 13, 14, 15], hint: 'Prime numbers!' }
    ];

    let currentPattern;

    function showPattern() {
        currentPattern = patterns[Math.floor(Math.random() * patterns.length)];

        // Show sequence with unknown
        sequenceEl.innerHTML = currentPattern.seq.map(n =>
            `<div class="pattern-item-kid">${n}</div>`
        ).join('') + '<div class="pattern-item-kid unknown">?</div>';

        // Show options
        const shuffled = [...currentPattern.options].sort(() => Math.random() - 0.5);
        optionsEl.innerHTML = shuffled.map(n =>
            `<button class="pattern-option-kid" data-answer="${n}">${n}</button>`
        ).join('');

        if (feedbackEl) feedbackEl.textContent = '';

        // Add click handlers
        optionsEl.querySelectorAll('.pattern-option-kid').forEach(btn => {
            btn.addEventListener('click', () => checkPattern(btn));
        });
    }

    function checkPattern(btn) {
        const isCorrect = parseInt(btn.dataset.answer) === currentPattern.next;

        if (isCorrect) {
            correctCount++;
            addStars(1);
            btn.style.background = '#4dff88';
            btn.style.borderColor = '#4dff88';
            if (feedbackEl) {
                feedbackEl.textContent = `Yes! ${currentPattern.hint} 🎉`;
                feedbackEl.style.color = '#4dff88';
            }

            if (correctCount >= 3 && !AppState.badges['pattern-spotter']) {
                earnBadge('pattern-spotter');
            }
        } else {
            btn.style.background = '#ff6b6b';
            btn.style.borderColor = '#ff6b6b';
            if (feedbackEl) {
                feedbackEl.textContent = `The answer was ${currentPattern.next}. ${currentPattern.hint}`;
                feedbackEl.style.color = '#ff6b6b';
            }
        }

        optionsEl.querySelectorAll('.pattern-option-kid').forEach(b => b.disabled = true);
    }

    nextBtn?.addEventListener('click', showPattern);
    showPattern();
}

// ===== Prime Number Hunt =====
function initPrimeHunt() {
    const grid = document.getElementById('prime-grid-kid');
    const startBtn = document.getElementById('prime-hunt-start');
    const countEl = document.getElementById('primes-found-count');

    if (!grid) return;

    let isRunning = false;

    function createGrid() {
        grid.innerHTML = '';
        for (let i = 2; i <= 50; i++) {
            const cell = document.createElement('div');
            cell.className = 'prime-cell-kid';
            cell.textContent = i;
            cell.dataset.number = i;
            grid.appendChild(cell);
        }
        if (countEl) countEl.textContent = '0';
    }

    async function runHunt() {
        if (isRunning) return;
        isRunning = true;

        createGrid();
        await sleep(500);

        const cells = grid.querySelectorAll('.prime-cell-kid');
        let primeCount = 0;

        for (let p = 2; p <= 50; p++) {
            if (!isRunning) break;

            const pCell = grid.querySelector(`[data-number="${p}"]`);
            if (!pCell || pCell.classList.contains('composite')) continue;

            // Mark as prime
            pCell.classList.add('prime');
            primeCount++;
            if (countEl) countEl.textContent = primeCount;

            await sleep(200);

            // Mark multiples as composite
            for (let m = p * 2; m <= 50; m += p) {
                const mCell = grid.querySelector(`[data-number="${m}"]`);
                if (mCell && !mCell.classList.contains('composite')) {
                    mCell.classList.add('composite');
                    await sleep(50);
                }
            }
        }

        isRunning = false;

        if (!AppState.badges['prime-finder']) {
            earnBadge('prime-finder');
        }
    }

    function sleep(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }

    startBtn?.addEventListener('click', runHunt);
    createGrid();
}

// ===== Fractal Art Studio =====
function initFractalStudio() {
    const canvas = document.getElementById('fractal-kid-canvas');
    const branchesSlider = document.getElementById('kid-branches');
    const depthSlider = document.getElementById('kid-depth');
    const angleSlider = document.getElementById('kid-angle');
    const colorPicker = document.getElementById('kid-color');
    const generateBtn = document.getElementById('kid-generate');

    const branchesVal = document.getElementById('branches-val');
    const depthVal = document.getElementById('depth-val');
    const angleVal = document.getElementById('angle-val');

    if (!canvas) return;

    const ctx = canvas.getContext('2d');
    canvas.width = canvas.clientWidth;
    canvas.height = 300;

    let hasDrawn = false;

    function drawTree(x, y, length, angle, depth, branches, spread, color) {
        if (depth === 0) return;

        const endX = x + Math.cos(angle) * length;
        const endY = y + Math.sin(angle) * length;

        // Rainbow gradient based on depth
        const hue = (depth * 40) % 360;
        ctx.strokeStyle = `hsl(${hue}, 80%, 60%)`;

        ctx.beginPath();
        ctx.moveTo(x, y);
        ctx.lineTo(endX, endY);
        ctx.lineWidth = depth * 1.5;
        ctx.lineCap = 'round';
        ctx.stroke();

        const spreadRad = spread * Math.PI / 180;
        for (let i = 0; i < branches; i++) {
            const newAngle = angle - spreadRad * (branches - 1) / 2 + spreadRad * i;
            drawTree(endX, endY, length * 0.65, newAngle, depth - 1, branches, spread, color);
        }
    }

    function generate() {
        ctx.fillStyle = '#1a1a2e';
        ctx.fillRect(0, 0, canvas.width, canvas.height);

        const branches = parseInt(branchesSlider?.value || 3);
        const depth = parseInt(depthSlider?.value || 4);
        const angle = parseInt(angleSlider?.value || 30);
        const color = colorPicker?.value || '#64ffda';

        // Update display values
        if (branchesVal) branchesVal.textContent = branches;
        if (depthVal) depthVal.textContent = depth;
        if (angleVal) angleVal.textContent = angle + '°';

        drawTree(canvas.width / 2, canvas.height - 20, 70, -Math.PI / 2, depth, branches, angle, color);

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

// ===== Wake Up the Brain Game =====
function initBrainGame() {
    const connectionsSlider = document.getElementById('connections-slider');
    const loopsSlider = document.getElementById('loops-slider');
    const complexitySlider = document.getElementById('complexity-slider-kid');
    const fill = document.getElementById('brain-fill');
    const status = document.getElementById('brain-status');
    const brainIcon = document.getElementById('brain-icon');

    if (!connectionsSlider) return;

    let hasAwakened = false;

    function update() {
        const c = parseInt(connectionsSlider.value) / 100;
        const l = parseInt(loopsSlider.value) / 100;
        const x = parseInt(complexitySlider.value) / 100;

        // Calculate "consciousness" level
        const level = Math.min(1, (c * 0.35 + l * 0.35 + x * 0.3) * 1.1);

        if (fill) fill.style.width = `${level * 100}%`;

        if (status && brainIcon) {
            if (level >= 0.95) {
                status.className = 'brain-status awake';
                status.textContent = '✨ AWAKE! Thinking happening! ✨';
                brainIcon.classList.add('awake');

                if (!hasAwakened) {
                    hasAwakened = true;
                    earnBadge('brain-waker');
                }
            } else if (level >= 0.7) {
                status.className = 'brain-status';
                status.textContent = '😴 Getting drowsy...';
                brainIcon.classList.remove('awake');
            } else if (level >= 0.4) {
                status.className = 'brain-status';
                status.textContent = '💤 Sleeping...';
                brainIcon.classList.remove('awake');
            } else {
                status.className = 'brain-status';
                status.textContent = '😴 Deep sleep...';
                brainIcon.classList.remove('awake');
            }
        }
    }

    connectionsSlider.addEventListener('input', update);
    loopsSlider.addEventListener('input', update);
    complexitySlider.addEventListener('input', update);

    update();
}

// ===== Sound the Gap Game =====
function initSoundGame() {
    const playEasy = document.getElementById('play-easy');
    const playHard = document.getElementById('play-hard');
    const playBoth = document.getElementById('play-both-kid');

    if (!playEasy) return;

    let hasPlayed = false;

    function getAudioContext() {
        if (!AppState.audioContext) {
            AppState.audioContext = new (window.AudioContext || window.webkitAudioContext)();
        }
        return AppState.audioContext;
    }

    function playTone(frequency, duration = 1.5) {
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

        if (!hasPlayed) {
            hasPlayed = true;
            earnBadge('sound-explorer');
        }
    }

    playEasy.addEventListener('click', () => {
        playTone(440); // Higher pitch for "easy" (P class)
        playEasy.style.transform = 'scale(1.1)';
        setTimeout(() => playEasy.style.transform = 'scale(1)', 200);
    });

    playHard.addEventListener('click', () => {
        playTone(280); // Lower pitch for "hard" (NP class)
        playHard.style.transform = 'scale(1.1)';
        setTimeout(() => playHard.style.transform = 'scale(1)', 200);
    });

    playBoth?.addEventListener('click', () => {
        playTone(440);
        playTone(280);
    });
}

// ===== Console Easter Egg =====
console.log(`%c
🔮 THE MAGIC OF THREE 🔮
========================
You found the secret console!
You must be a real explorer!

Here's a fun fact:
3 × 3 × 3 = 27
2 + 7 = 9
9 = 3 × 3

Three is EVERYWHERE! ✨
`, 'color: #00d9ff; font-size: 14px; font-weight: bold;');
