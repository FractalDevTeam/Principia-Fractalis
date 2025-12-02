// ============================================
// THE MAGIC OF THREE - ACCESSIBLE INTERACTIVE SCRIPT
// For neurotypical AND neurodivergent minds
// ============================================

// User Profile & Persistence
const USER_DATA_KEY = 'magic-of-three-user';

let userData = {
    name: '',
    learningStyles: [],
    calmMode: false,
    fontMode: 'default',
    soundEnabled: true,
    stars: 0,
    badges: [],
    completedPages: [],
    visitedSections: ['start'],
    ageMode: 'kid',
    currentPathway: 'all',
    gameScores: {
        cookie: 0,
        pattern: 0,
        prime: 0,
        fractal: 0,
        brain: 0,
        sound: 0
    }
};

// Badge definitions
const BADGES = {
    'cookie-master': { icon: '🍪', name: 'Cookie Master', desc: 'Counted 5 cookie problems!' },
    'pattern-spotter': { icon: '🔍', name: 'Pattern Spotter', desc: 'Found 3 patterns!' },
    'prime-finder': { icon: '🎯', name: 'Prime Finder', desc: 'Discovered the primes!' },
    'fractal-artist': { icon: '🎨', name: 'Fractal Artist', desc: 'Created fractal art!' },
    'brain-waker': { icon: '🧠', name: 'Brain Waker', desc: 'Woke up the brain!' },
    'sound-explorer': { icon: '🔊', name: 'Sound Explorer', desc: 'Heard the difference!' },
    'story-reader': { icon: '📖', name: 'Story Reader', desc: 'Finished the story!' },
    'ocean-explorer': { icon: '🌊', name: 'Ocean Explorer', desc: 'Explored the ocean!' },
    'color-mixer': { icon: '🎨', name: 'Color Mixer', desc: 'Mixed colors with THREE primaries!' },
    'mind-celebrator': { icon: '🧩', name: 'Mind Celebrator', desc: 'Discovered your superpowers!' }
};

// ============================================
// INITIALIZATION
// ============================================

document.addEventListener('DOMContentLoaded', () => {
    loadUserData();
    initWelcome();
    initAccessibility();
    initNavigation();
    initAgeToggle();
    initPathwaySelect();
    initStoryBook();
    initGames();
    initOcean();
    initSectionTracking();
    updateUI();
});

function loadUserData() {
    const saved = localStorage.getItem(USER_DATA_KEY);
    if (saved) {
        try {
            userData = { ...userData, ...JSON.parse(saved) };
        } catch (e) {
            console.log('Starting fresh user data');
        }
    }
}

function saveUserData() {
    localStorage.setItem(USER_DATA_KEY, JSON.stringify(userData));
}

// ============================================
// WELCOME MODAL / LOGIN
// ============================================

function initWelcome() {
    const modal = document.getElementById('welcome-modal');
    const toast = document.getElementById('welcome-back-toast');
    const nameInput = document.getElementById('user-name-input');
    const startBtn = document.getElementById('start-journey');
    const skipBtn = document.getElementById('skip-welcome');
    const calmModeWelcome = document.getElementById('calm-mode-welcome');
    const notMeBtn = document.getElementById('not-me-btn');

    // Check if returning user
    if (userData.name) {
        modal.classList.add('hidden');
        document.getElementById('returning-name').textContent = userData.name;
        toast.classList.remove('hidden');

        // Auto-hide toast after 5 seconds
        setTimeout(() => {
            toast.classList.add('hidden');
        }, 5000);

        // Apply saved preferences
        applyUserPreferences();
    }

    // Start journey button
    startBtn?.addEventListener('click', () => {
        userData.name = nameInput.value.trim() || 'Explorer';

        // Get learning styles
        const styleCheckboxes = document.querySelectorAll('input[name="learn-style"]:checked');
        userData.learningStyles = Array.from(styleCheckboxes).map(cb => cb.value);

        // Get calm mode preference
        userData.calmMode = calmModeWelcome?.checked || false;

        saveUserData();
        applyUserPreferences();
        modal.classList.add('hidden');
        updateGreeting();
    });

    // Skip button
    skipBtn?.addEventListener('click', () => {
        modal.classList.add('hidden');
    });

    // Not me button
    notMeBtn?.addEventListener('click', () => {
        toast.classList.add('hidden');
        resetUserData();
        modal.classList.remove('hidden');
    });
}

function resetUserData() {
    userData = {
        name: '',
        learningStyles: [],
        calmMode: false,
        fontMode: 'default',
        soundEnabled: true,
        stars: 0,
        badges: [],
        completedPages: [],
        visitedSections: ['start'],
        ageMode: 'kid',
        currentPathway: 'all',
        gameScores: {
            cookie: 0,
            pattern: 0,
            prime: 0,
            fractal: 0,
            brain: 0,
            sound: 0
        }
    };
    saveUserData();
    updateUI();
}

function applyUserPreferences() {
    // Apply calm mode
    if (userData.calmMode) {
        document.body.classList.add('calm-mode');
        document.getElementById('calm-mode-toggle')?.classList.add('active');
    }

    // Apply font mode
    if (userData.fontMode === 'lexend') {
        document.body.classList.add('font-lexend');
    }

    // Apply age mode
    document.body.className = document.body.className.replace(/kid-mode|teen-mode|adult-mode/g, '');
    document.body.classList.add(`${userData.ageMode}-mode`);

    // Set active age button
    document.querySelectorAll('.age-btn').forEach(btn => {
        btn.classList.toggle('active', btn.dataset.mode === userData.ageMode);
    });

    // Apply pathway
    setPathway(userData.currentPathway);
}

function updateGreeting() {
    const greeting = document.getElementById('personalized-greeting');
    if (greeting && userData.name) {
        greeting.innerHTML = `Hey ${userData.name}! Did you know there's a secret pattern hiding in EVERYTHING?<br>In your fingers, in snowflakes, even in your brain! 🤯`;
    }
}

// ============================================
// ACCESSIBILITY CONTROLS
// ============================================

function initAccessibility() {
    const calmToggle = document.getElementById('calm-mode-toggle');
    const fontToggle = document.getElementById('font-toggle');
    const soundToggle = document.getElementById('sound-toggle');
    const userMenuBtn = document.getElementById('user-menu-btn');

    // Calm mode toggle
    calmToggle?.addEventListener('click', () => {
        userData.calmMode = !userData.calmMode;
        document.body.classList.toggle('calm-mode', userData.calmMode);
        calmToggle.classList.toggle('active', userData.calmMode);
        saveUserData();
    });

    // Font toggle
    fontToggle?.addEventListener('click', () => {
        userData.fontMode = userData.fontMode === 'default' ? 'lexend' : 'default';
        document.body.classList.toggle('font-lexend', userData.fontMode === 'lexend');
        fontToggle.classList.toggle('active', userData.fontMode === 'lexend');
        saveUserData();
    });

    // Sound toggle
    soundToggle?.addEventListener('click', () => {
        userData.soundEnabled = !userData.soundEnabled;
        soundToggle.classList.toggle('active', userData.soundEnabled);
        const icon = soundToggle.querySelector('.access-icon');
        if (icon) icon.textContent = userData.soundEnabled ? '🔊' : '🔇';
        saveUserData();
    });

    // User menu
    userMenuBtn?.addEventListener('click', () => {
        if (userData.name) {
            if (confirm(`Logged in as ${userData.name}. Want to switch users?`)) {
                resetUserData();
                document.getElementById('welcome-modal').classList.remove('hidden');
            }
        } else {
            document.getElementById('welcome-modal').classList.remove('hidden');
        }
    });
}

// ============================================
// NAVIGATION
// ============================================

function initNavigation() {
    const mobileMenuBtn = document.querySelector('.mobile-menu-btn');
    const navLinks = document.querySelector('.nav-links');

    mobileMenuBtn?.addEventListener('click', () => {
        navLinks?.classList.toggle('active');
    });

    // Close mobile menu when clicking a link
    document.querySelectorAll('.nav-link').forEach(link => {
        link.addEventListener('click', () => {
            navLinks?.classList.remove('active');
        });
    });

    // Progress tracker hover
    const progressIcon = document.querySelector('.progress-icon');
    const badgesPanel = document.getElementById('badges-panel');

    progressIcon?.addEventListener('click', () => {
        badgesPanel?.classList.toggle('show');
    });

    // Close badges panel when clicking outside
    document.addEventListener('click', (e) => {
        if (!e.target.closest('.progress-tracker')) {
            badgesPanel?.classList.remove('show');
        }
    });
}

// ============================================
// AGE TOGGLE
// ============================================

function initAgeToggle() {
    document.querySelectorAll('.age-btn').forEach(btn => {
        btn.addEventListener('click', () => {
            const mode = btn.dataset.mode;
            setAgeMode(mode);
        });
    });
}

function setAgeMode(mode) {
    userData.ageMode = mode;

    document.body.className = document.body.className.replace(/kid-mode|teen-mode|adult-mode/g, '');
    document.body.classList.add(`${mode}-mode`);

    document.querySelectorAll('.age-btn').forEach(btn => {
        btn.classList.toggle('active', btn.dataset.mode === mode);
    });

    saveUserData();
}

// ============================================
// PATHWAY SELECT
// ============================================

function initPathwaySelect() {
    document.querySelectorAll('.pathway-btn').forEach(btn => {
        btn.addEventListener('click', () => {
            const path = btn.dataset.path;
            setPathway(path);
        });
    });
}

function setPathway(path) {
    userData.currentPathway = path;

    document.querySelectorAll('.pathway-btn').forEach(btn => {
        btn.classList.toggle('active', btn.dataset.path === path);
    });

    // Filter game cards
    document.querySelectorAll('.game-card[data-pathway]').forEach(card => {
        const cardPaths = card.dataset.pathway.split(' ');
        const show = path === 'all' || cardPaths.includes(path);
        card.classList.toggle('filtered-out', !show);
    });

    // Filter discovery cards
    document.querySelectorAll('.discovery-card[data-pathway]').forEach(card => {
        const show = path === 'all' || card.dataset.pathway === path;
        card.classList.toggle('filtered-out', !show);
    });

    saveUserData();
}

// ============================================
// SECTION TRACKING
// ============================================

function initSectionTracking() {
    const sections = ['story', 'games', 'ocean', 'discover', 'pablo', 'grownups'];

    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                const sectionId = entry.target.id;
                updateCurrentSection(sectionId);

                // Add to visited if not already
                if (!userData.visitedSections.includes(sectionId)) {
                    userData.visitedSections.push(sectionId);
                    saveUserData();
                    updateJourneyMap();
                }
            }
        });
    }, { threshold: 0.3 });

    sections.forEach(id => {
        const el = document.getElementById(id);
        if (el) observer.observe(el);
    });
}

function updateCurrentSection(sectionId) {
    const sectionNames = {
        'story': 'The Story',
        'games': 'Math Games',
        'ocean': 'The Ocean',
        'discover': 'Discoveries',
        'pablo': "Pablo's Story",
        'grownups': 'For Grown-Ups'
    };

    const currentEl = document.getElementById('current-section');
    if (currentEl) {
        currentEl.textContent = sectionNames[sectionId] || 'Welcome';
    }

    // Update journey map
    updateJourneyMap();
}

function updateJourneyMap() {
    const sectionMap = {
        'start': 'start',
        'story': 'story',
        'games': 'games',
        'ocean': 'ocean',
        'discover': 'discover'
    };

    document.querySelectorAll('.journey-step').forEach(step => {
        const section = step.dataset.section;
        step.classList.toggle('completed', userData.visitedSections.includes(section));
    });
}

// ============================================
// STORY BOOK
// ============================================

function initStoryBook() {
    const totalPages = 8;

    // Create page dots
    const dotsContainer = document.getElementById('page-dots');
    if (dotsContainer) {
        for (let i = 1; i <= totalPages; i++) {
            const dot = document.createElement('div');
            dot.className = `page-dot${i === 1 ? ' active' : ''}`;
            dot.dataset.page = i;
            dot.addEventListener('click', () => goToPage(i));
            dotsContainer.appendChild(dot);
        }
    }

    // Page turn buttons
    document.querySelectorAll('.page-turn').forEach(btn => {
        btn.addEventListener('click', () => {
            const nextPage = parseInt(btn.dataset.next);
            goToPage(nextPage);
        });
    });
}

function goToPage(pageNum) {
    // Update pages
    document.querySelectorAll('.story-page').forEach(page => {
        page.classList.remove('active');
    });

    const targetPage = document.querySelector(`.story-page[data-page="${pageNum}"]`);
    if (targetPage) {
        targetPage.classList.add('active');
    }

    // Update dots
    document.querySelectorAll('.page-dot').forEach(dot => {
        dot.classList.toggle('active', parseInt(dot.dataset.page) === pageNum);
    });

    // Track completed pages
    if (!userData.completedPages.includes(pageNum)) {
        userData.completedPages.push(pageNum);

        // Award badge for completing story
        if (userData.completedPages.length >= 8) {
            awardBadge('story-reader');
        }

        saveUserData();
    }
}

// ============================================
// GAMES
// ============================================

function initGames() {
    initCookieGame();
    initPatternGame();
    initPrimeGame();
    initFractalGame();
    initBrainGame();
    initSoundGame();
    initColorMixer();
    initMindQuiz();
}

// Cookie Counter Game
function initCookieGame() {
    let cookieScore = userData.gameScores.cookie;
    let currentCookies = 0;

    function newCookieRound() {
        currentCookies = Math.floor(Math.random() * 12) + 1;

        // Display cookies
        const display = document.getElementById('cookie-display');
        if (display) {
            display.innerHTML = '🍪'.repeat(currentCookies);
        }

        // Generate options
        const correctAnswer = toBase3(currentCookies);
        const options = generateOptions(correctAnswer, 4, true);

        const optionsContainer = document.getElementById('cookie-options');
        if (optionsContainer) {
            optionsContainer.innerHTML = '';
            options.forEach(opt => {
                const btn = document.createElement('button');
                btn.className = 'cookie-option';
                btn.textContent = opt;
                btn.addEventListener('click', () => checkCookieAnswer(opt, correctAnswer));
                optionsContainer.appendChild(btn);
            });
        }

        document.getElementById('cookie-feedback').innerHTML = '';
    }

    function checkCookieAnswer(selected, correct) {
        const feedback = document.getElementById('cookie-feedback');
        const options = document.querySelectorAll('.cookie-option');

        options.forEach(opt => {
            opt.style.pointerEvents = 'none';
            if (opt.textContent === correct) opt.classList.add('correct');
            if (opt.textContent === selected && selected !== correct) opt.classList.add('wrong');
        });

        if (selected === correct) {
            feedback.innerHTML = '⭐ Correct! Great counting!';
            feedback.style.color = '#00ff88';
            addStars(1);
            cookieScore++;
            userData.gameScores.cookie = cookieScore;
            document.getElementById('cookie-score').textContent = cookieScore;

            if (cookieScore >= 5) awardBadge('cookie-master');
            saveUserData();
            setTimeout(newCookieRound, 2000);
        } else {
            // Educational explanation for wrong answer
            const explanation = explainBase3Conversion(currentCookies, correct);
            feedback.innerHTML = explanation;
            feedback.style.color = '#e94560';
            // Give more time to read the explanation
            setTimeout(newCookieRound, 6000);
        }
    }

    newCookieRound();
}

// Educational explanation for base-3 conversion
function explainBase3Conversion(num, base3Result) {
    const steps = [];
    let remaining = num;
    let placeValues = [];

    // Calculate place values
    while (remaining > 0) {
        placeValues.unshift(remaining % 3);
        remaining = Math.floor(remaining / 3);
    }

    // Build explanation
    let explanation = `<strong>Let's learn!</strong> ${num} cookies in base-3 = <strong>${base3Result}</strong><br><br>`;
    explanation += `<strong>How to convert:</strong><br>`;
    explanation += `In base-3, we only use digits 0, 1, 2.<br>`;
    explanation += `Each place is worth 3× more than the one to its right.<br><br>`;

    // Show the division process
    remaining = num;
    let step = 1;
    explanation += `<strong>Divide by 3 repeatedly:</strong><br>`;
    while (remaining > 0) {
        const quotient = Math.floor(remaining / 3);
        const remainder = remaining % 3;
        explanation += `${remaining} ÷ 3 = ${quotient} remainder <strong>${remainder}</strong><br>`;
        remaining = quotient;
    }

    explanation += `<br>Read the remainders bottom-to-top: <strong>${base3Result}</strong>`;

    return explanation;
}

// Educational explanation for pattern recognition
function explainPattern(pattern) {
    const seq = pattern.sequence;
    const next = pattern.next;
    const name = pattern.name;

    let explanation = `<strong>Let's learn!</strong> The answer is <strong>${next}</strong><br><br>`;
    explanation += `<strong>This pattern is: ${name}</strong><br><br>`;

    switch(name) {
        case 'odd numbers':
            explanation += `Odd numbers skip the even ones.<br>`;
            explanation += `Rule: Start at 1, add 2 each time.<br><br>`;
            explanation += `<strong>Step by step:</strong><br>`;
            explanation += `1 → 1+2=<strong>3</strong> → 3+2=<strong>5</strong> → 5+2=<strong>7</strong> → 7+2=<strong>9</strong>`;
            break;

        case 'even numbers':
            explanation += `Even numbers are divisible by 2.<br>`;
            explanation += `Rule: Start at 2, add 2 each time.<br><br>`;
            explanation += `<strong>Step by step:</strong><br>`;
            explanation += `2 → 2+2=<strong>4</strong> → 4+2=<strong>6</strong> → 6+2=<strong>8</strong> → 8+2=<strong>10</strong>`;
            break;

        case 'powers of 3':
            explanation += `Each number is 3 times the previous!<br>`;
            explanation += `Rule: Multiply by 3 each time.<br><br>`;
            explanation += `<strong>Step by step:</strong><br>`;
            explanation += `1 → 1×3=<strong>3</strong> → 3×3=<strong>9</strong> → 9×3=<strong>27</strong> → 27×3=<strong>81</strong><br><br>`;
            explanation += `This is 3⁰, 3¹, 3², 3³, 3⁴ (the magic of THREE!)`;
            break;

        case 'Fibonacci':
            explanation += `Each number is the sum of the two before it!<br>`;
            explanation += `Rule: Add the last two numbers.<br><br>`;
            explanation += `<strong>Step by step:</strong><br>`;
            explanation += `1, 1 → 1+1=<strong>2</strong> → 1+2=<strong>3</strong> → 2+3=<strong>5</strong> → 3+5=<strong>8</strong><br><br>`;
            explanation += `Nature uses this pattern in flowers, shells, and galaxies!`;
            break;

        case 'multiples of 3':
            explanation += `These are numbers you land on when counting by 3.<br>`;
            explanation += `Rule: Add 3 each time.<br><br>`;
            explanation += `<strong>Step by step:</strong><br>`;
            explanation += `3 → 3+3=<strong>6</strong> → 6+3=<strong>9</strong> → 9+3=<strong>12</strong> → 12+3=<strong>15</strong><br><br>`;
            explanation += `Every third number: 1, 2, <strong>3</strong>, 4, 5, <strong>6</strong>, 7, 8, <strong>9</strong>...`;
            break;

        case 'squares':
            explanation += `These are numbers multiplied by themselves!<br>`;
            explanation += `Rule: 1², 2², 3², 4², 5²...<br><br>`;
            explanation += `<strong>Step by step:</strong><br>`;
            explanation += `1×1=<strong>1</strong> → 2×2=<strong>4</strong> → 3×3=<strong>9</strong> → 4×4=<strong>16</strong> → 5×5=<strong>25</strong><br><br>`;
            explanation += `Imagine: 1 dot, then 2×2 dots, then 3×3 dots forming a square!`;
            break;

        case 'primes':
            explanation += `Prime numbers can only be divided by 1 and themselves!<br>`;
            explanation += `Rule: Find numbers with exactly 2 factors.<br><br>`;
            explanation += `<strong>Why these are prime:</strong><br>`;
            explanation += `2 ✓ (only 1×2) → 3 ✓ (only 1×3) → 5 ✓ (only 1×5) → 7 ✓ (only 1×7) → 11 ✓ (only 1×11)<br><br>`;
            explanation += `4 is NOT prime because 4 = 2×2`;
            break;

        case 'tens':
            explanation += `Counting by 10s is like counting our fingers!<br>`;
            explanation += `Rule: Add 10 each time.<br><br>`;
            explanation += `<strong>Step by step:</strong><br>`;
            explanation += `10 → 10+10=<strong>20</strong> → 20+10=<strong>30</strong> → 30+10=<strong>40</strong> → 40+10=<strong>50</strong>`;
            break;

        default:
            explanation += `Look at how each number changes to find the pattern!`;
    }

    return explanation;
}

// Pattern Spotter Game
function initPatternGame() {
    const patterns = [
        { sequence: [1, 3, 5, 7], next: 9, name: 'odd numbers' },
        { sequence: [2, 4, 6, 8], next: 10, name: 'even numbers' },
        { sequence: [1, 3, 9, 27], next: 81, name: 'powers of 3' },
        { sequence: [1, 1, 2, 3, 5], next: 8, name: 'Fibonacci' },
        { sequence: [3, 6, 9, 12], next: 15, name: 'multiples of 3' },
        { sequence: [1, 4, 9, 16], next: 25, name: 'squares' },
        { sequence: [2, 3, 5, 7], next: 11, name: 'primes' },
        { sequence: [10, 20, 30, 40], next: 50, name: 'tens' }
    ];

    let patternScore = 0;
    let currentPattern = null;

    function newPattern() {
        currentPattern = patterns[Math.floor(Math.random() * patterns.length)];

        const seqContainer = document.getElementById('pattern-sequence-kid');
        if (seqContainer) {
            seqContainer.innerHTML = '';
            currentPattern.sequence.forEach(num => {
                const span = document.createElement('span');
                span.className = 'pattern-num';
                span.textContent = num;
                seqContainer.appendChild(span);
            });

            const mystery = document.createElement('span');
            mystery.className = 'pattern-num mystery';
            mystery.textContent = '?';
            seqContainer.appendChild(mystery);
        }

        // Generate options
        const options = generateOptions(currentPattern.next, 4, false);
        const optionsContainer = document.getElementById('pattern-options-kid');
        if (optionsContainer) {
            optionsContainer.innerHTML = '';
            options.forEach(opt => {
                const btn = document.createElement('button');
                btn.className = 'pattern-option-kid';
                btn.textContent = opt;
                btn.addEventListener('click', () => checkPatternAnswer(opt));
                optionsContainer.appendChild(btn);
            });
        }

        document.getElementById('pattern-feedback-kid').textContent = '';
    }

    function checkPatternAnswer(selected) {
        const feedback = document.getElementById('pattern-feedback-kid');
        const correct = currentPattern.next;

        if (parseInt(selected) === correct) {
            feedback.innerHTML = `⭐ Yes! It's ${currentPattern.name}!`;
            feedback.style.color = '#00ff88';
            addStars(1);
            patternScore++;

            if (patternScore >= 3) awardBadge('pattern-spotter');
            saveUserData();
        } else {
            // Educational explanation for wrong answer
            const explanation = explainPattern(currentPattern);
            feedback.innerHTML = explanation;
            feedback.style.color = '#e94560';
        }
    }

    document.getElementById('next-pattern-kid')?.addEventListener('click', newPattern);
    newPattern();
}

// Prime Number Hunt Game
function initPrimeGame() {
    const gridContainer = document.getElementById('prime-grid-kid');
    if (!gridContainer) return;

    // Create grid
    for (let i = 2; i <= 50; i++) {
        const cell = document.createElement('div');
        cell.className = 'prime-cell';
        cell.textContent = i;
        cell.dataset.num = i;
        gridContainer.appendChild(cell);
    }

    document.getElementById('prime-hunt-start')?.addEventListener('click', runSieve);
}

async function runSieve() {
    const cells = document.querySelectorAll('.prime-cell');
    const countEl = document.getElementById('primes-found-count');
    let primesFound = 0;

    // Reset
    cells.forEach(cell => {
        cell.classList.remove('is-prime', 'crossed-out');
    });

    // Sieve of Eratosthenes animation
    for (let p = 2; p <= 50; p++) {
        const pCell = document.querySelector(`.prime-cell[data-num="${p}"]`);
        if (pCell && !pCell.classList.contains('crossed-out')) {
            pCell.classList.add('is-prime');
            primesFound++;
            countEl.textContent = primesFound;

            // Cross out multiples
            for (let m = p * 2; m <= 50; m += p) {
                await new Promise(r => setTimeout(r, 50));
                const mCell = document.querySelector(`.prime-cell[data-num="${m}"]`);
                if (mCell && !mCell.classList.contains('is-prime')) {
                    mCell.classList.add('crossed-out');
                }
            }
        }
    }

    addStars(2);
    awardBadge('prime-finder');
}

// Fractal Art Studio
function initFractalGame() {
    const canvas = document.getElementById('fractal-kid-canvas');
    if (!canvas) return;

    const ctx = canvas.getContext('2d');

    function resizeCanvas() {
        canvas.width = canvas.offsetWidth;
        canvas.height = canvas.offsetHeight;
    }
    resizeCanvas();
    window.addEventListener('resize', resizeCanvas);

    const branchesInput = document.getElementById('kid-branches');
    const depthInput = document.getElementById('kid-depth');
    const angleInput = document.getElementById('kid-angle');
    const colorInput = document.getElementById('kid-color');

    branchesInput?.addEventListener('input', () => {
        document.getElementById('branches-val').textContent = branchesInput.value;
    });

    depthInput?.addEventListener('input', () => {
        document.getElementById('depth-val').textContent = depthInput.value;
    });

    angleInput?.addEventListener('input', () => {
        document.getElementById('angle-val').textContent = angleInput.value + '°';
    });

    document.getElementById('kid-generate')?.addEventListener('click', () => {
        drawFractal();
        awardBadge('fractal-artist');
        addStars(1);
    });

    function drawFractal() {
        const branches = parseInt(branchesInput?.value || 3);
        const depth = parseInt(depthInput?.value || 4);
        const spreadAngle = parseInt(angleInput?.value || 30) * Math.PI / 180;
        const baseColor = colorInput?.value || '#64ffda';

        ctx.fillStyle = '#16213e';
        ctx.fillRect(0, 0, canvas.width, canvas.height);

        function drawBranch(x, y, len, angle, d) {
            if (d === 0 || len < 2) return;

            const endX = x + Math.cos(angle) * len;
            const endY = y + Math.sin(angle) * len;

            // Rainbow effect
            const hue = (d / depth) * 120 + parseInt(baseColor.slice(1), 16) % 360;
            ctx.strokeStyle = `hsl(${hue}, 80%, 60%)`;
            ctx.lineWidth = d * 1.5;

            ctx.beginPath();
            ctx.moveTo(x, y);
            ctx.lineTo(endX, endY);
            ctx.stroke();

            // Create branches
            const newLen = len * 0.7;
            const angleStep = spreadAngle * 2 / (branches - 1);
            const startAngle = angle - spreadAngle;

            for (let i = 0; i < branches; i++) {
                const branchAngle = startAngle + angleStep * i;
                drawBranch(endX, endY, newLen, branchAngle, d - 1);
            }
        }

        drawBranch(canvas.width / 2, canvas.height - 20, 80, -Math.PI / 2, depth);
    }

    drawFractal();
}

// Brain Wake-Up Game
function initBrainGame() {
    const connectionsSlider = document.getElementById('connections-slider');
    const loopsSlider = document.getElementById('loops-slider');
    const complexitySlider = document.getElementById('complexity-slider-kid');
    const brainIcon = document.getElementById('brain-icon');
    const brainFill = document.getElementById('brain-fill');
    const brainStatus = document.getElementById('brain-status');
    const ch2Display = document.getElementById('ch2-display');

    let hasWoken = false;

    function updateBrain() {
        const c = parseInt(connectionsSlider?.value || 30);
        const l = parseInt(loopsSlider?.value || 30);
        const x = parseInt(complexitySlider?.value || 30);

        // Calculate ch2 (simulated)
        const ch2 = (c * 0.4 + l * 0.35 + x * 0.25) / 100;
        const percentage = ch2 * 100;

        if (brainFill) brainFill.style.width = `${percentage}%`;
        if (ch2Display) ch2Display.textContent = ch2.toFixed(2);

        // Check if awake (ch2 >= 0.95)
        if (ch2 >= 0.95 && !hasWoken) {
            hasWoken = true;
            brainIcon?.classList.add('awake');
            if (brainStatus) {
                brainStatus.textContent = '🎉 AWAKE! Consciousness achieved!';
                brainStatus.classList.add('awake');
            }
            addStars(2);
            awardBadge('brain-waker');

            if (userData.soundEnabled) playTone(880, 0.3);
        } else if (ch2 < 0.95) {
            hasWoken = false;
            brainIcon?.classList.remove('awake');
            if (brainStatus) {
                if (ch2 < 0.5) {
                    brainStatus.textContent = '💤 Sleeping...';
                } else if (ch2 < 0.8) {
                    brainStatus.textContent = '😴 Stirring...';
                } else {
                    brainStatus.textContent = '😳 Almost there!';
                }
                brainStatus.classList.remove('awake');
            }
        }
    }

    connectionsSlider?.addEventListener('input', updateBrain);
    loopsSlider?.addEventListener('input', updateBrain);
    complexitySlider?.addEventListener('input', updateBrain);

    updateBrain();
}

// Sound Game (P vs NP)
function initSoundGame() {
    const playEasy = document.getElementById('play-easy');
    const playHard = document.getElementById('play-hard');
    const playBoth = document.getElementById('play-both-kid');

    // λ₀(P) = 0.2221 -> higher frequency
    const freqP = 440 * 0.2221 * 4; // ~390 Hz
    // λ₀(NP) = 0.1330 -> lower frequency
    const freqNP = 440 * 0.1330 * 4; // ~234 Hz

    playEasy?.addEventListener('click', () => {
        if (userData.soundEnabled) playTone(freqP, 0.5);
        addStars(1);
    });

    playHard?.addEventListener('click', () => {
        if (userData.soundEnabled) playTone(freqNP, 0.5);
        addStars(1);
    });

    playBoth?.addEventListener('click', () => {
        if (userData.soundEnabled) {
            playTone(freqP, 1);
            playTone(freqNP, 1);
        }
        awardBadge('sound-explorer');
    });
}

// Color Three Mixer Game - Teaching why THREE primary colors make ALL colors
function initColorMixer() {
    const redSlider = document.getElementById('red-slider');
    const greenSlider = document.getElementById('green-slider');
    const blueSlider = document.getElementById('blue-slider');
    const preview = document.getElementById('color-preview');
    const output = document.getElementById('color-output');
    const feedback = document.getElementById('color-feedback');

    if (!redSlider || !greenSlider || !blueSlider) return;

    let matchedColors = new Set();

    function updateColor() {
        const r = parseInt(redSlider.value);
        const g = parseInt(greenSlider.value);
        const b = parseInt(blueSlider.value);

        document.getElementById('red-val').textContent = r;
        document.getElementById('green-val').textContent = g;
        document.getElementById('blue-val').textContent = b;

        const color = `rgb(${r}, ${g}, ${b})`;
        if (preview) preview.style.backgroundColor = color;

        // Describe the color
        let colorName = describeColor(r, g, b);
        if (output) output.textContent = colorName;

        // Check challenges
        checkColorChallenges(r, g, b);
    }

    function describeColor(r, g, b) {
        // Simple color naming
        if (r > 200 && g > 200 && b > 200) return "White - All THREE at max!";
        if (r < 50 && g < 50 && b < 50) return "Black - All THREE at zero!";
        if (r > 200 && g < 100 && b < 100) return "Red!";
        if (r < 100 && g > 200 && b < 100) return "Green!";
        if (r < 100 && g < 100 && b > 200) return "Blue!";
        if (r > 200 && g > 200 && b < 100) return "Yellow! (Red + Green)";
        if (r > 200 && g < 100 && b > 200) return "Magenta! (Red + Blue)";
        if (r < 100 && g > 200 && b > 200) return "Cyan! (Green + Blue)";
        if (r > 200 && g > 100 && g < 200 && b < 100) return "Orange! (Red + some Green)";
        if (r > 100 && g < 100 && b > 100) return "Purple! (Red + Blue)";
        return `RGB(${r}, ${g}, ${b})`;
    }

    function checkColorChallenges(r, g, b) {
        const challenges = document.querySelectorAll('.challenge-btn');

        challenges.forEach(btn => {
            const target = btn.dataset.target.split(',').map(Number);
            const [tr, tg, tb] = target;

            // Allow some tolerance (±30)
            const tolerance = 40;
            const matched = Math.abs(r - tr) < tolerance &&
                           Math.abs(g - tg) < tolerance &&
                           Math.abs(b - tb) < tolerance;

            if (matched && !matchedColors.has(btn.dataset.target)) {
                matchedColors.add(btn.dataset.target);
                btn.classList.add('matched');
                if (feedback) {
                    feedback.textContent = `🎉 You made ${btn.textContent}! THREE colors create everything!`;
                    feedback.style.color = '#00ff88';
                }
                addStars(1);

                // Award badge after matching 3 colors
                if (matchedColors.size >= 3) {
                    awardBadge('color-mixer');
                }
            }
        });
    }

    redSlider.addEventListener('input', updateColor);
    greenSlider.addEventListener('input', updateColor);
    blueSlider.addEventListener('input', updateColor);

    // Initialize
    updateColor();
}

// Mind Type Celebration Quiz - Neurodivergent validation
function initMindQuiz() {
    const quizContent = document.getElementById('mind-quiz-content');
    const resultDiv = document.getElementById('mind-result');
    const superpowerList = document.getElementById('superpower-list');
    const retakeBtn = document.getElementById('retake-quiz');

    if (!quizContent) return;

    let answers = {
        type: null,
        trait: null,
        energy: null
    };

    const superpowers = {
        // Learning types
        visual: { icon: '👁️', name: 'Pattern Vision', desc: 'You see patterns others miss!' },
        'hands-on': { icon: '✋', name: 'Body Wisdom', desc: 'Your hands know things your mind hasn\'t figured out yet!' },
        story: { icon: '📖', name: 'Narrative Mind', desc: 'You connect everything into meaningful stories!' },
        numbers: { icon: '🔢', name: 'Logic Flow', desc: 'Numbers and patterns speak to you!' },
        // Traits
        creative: { icon: '🎨', name: 'Idea Generator', desc: 'Your brain makes NEW things!' },
        detail: { icon: '🔍', name: 'Detail Detective', desc: 'You notice what everyone else misses!' },
        connect: { icon: '🔗', name: 'Connection Finder', desc: 'You see how everything links together!' },
        question: { icon: '❓', name: 'Question Asker', desc: 'Your "why?" finds hidden truths!' },
        // Energy
        focus: { icon: '🎯', name: 'Deep Diver', desc: 'You can go DEEP into one thing!' },
        variety: { icon: '🦋', name: 'Idea Butterfly', desc: 'You gather wisdom from many places!' },
        quiet: { icon: '🌙', name: 'Inner World', desc: 'You have a rich inner universe!' },
        move: { icon: '🏃', name: 'Body Thinker', desc: 'Movement helps your brain work!' }
    };

    let currentQuestion = 1;

    function showQuestion(num) {
        document.querySelectorAll('.mind-question').forEach(q => {
            q.classList.add('hidden');
        });
        const q = document.getElementById(`mind-q${num}`);
        if (q) q.classList.remove('hidden');
    }

    function handleAnswer(btn, answerType) {
        // Mark selected
        btn.closest('.mind-options').querySelectorAll('.mind-option').forEach(o => {
            o.classList.remove('selected');
        });
        btn.classList.add('selected');

        // Store answer
        if (btn.dataset.type) answers.type = btn.dataset.type;
        if (btn.dataset.trait) answers.trait = btn.dataset.trait;
        if (btn.dataset.energy) answers.energy = btn.dataset.energy;

        // Move to next question or show results
        setTimeout(() => {
            currentQuestion++;
            if (currentQuestion <= 3) {
                showQuestion(currentQuestion);
            } else {
                showResults();
            }
        }, 400);
    }

    function showResults() {
        quizContent.classList.add('hidden');
        resultDiv.classList.remove('hidden');

        // Build superpower display
        superpowerList.innerHTML = '';

        Object.entries(answers).forEach(([key, value]) => {
            if (value && superpowers[value]) {
                const sp = superpowers[value];
                const div = document.createElement('div');
                div.className = 'superpower-item';
                div.innerHTML = `
                    <span class="superpower-icon">${sp.icon}</span>
                    <span class="superpower-name">${sp.name}</span>
                    <span class="superpower-desc">${sp.desc}</span>
                `;
                superpowerList.appendChild(div);
            }
        });

        addStars(3);
        awardBadge('mind-celebrator');
    }

    function resetQuiz() {
        answers = { type: null, trait: null, energy: null };
        currentQuestion = 1;
        resultDiv.classList.add('hidden');
        quizContent.classList.remove('hidden');
        showQuestion(1);
        document.querySelectorAll('.mind-option').forEach(o => {
            o.classList.remove('selected');
        });
    }

    // Attach event listeners
    document.querySelectorAll('.mind-option').forEach(btn => {
        btn.addEventListener('click', () => handleAnswer(btn));
    });

    retakeBtn?.addEventListener('click', resetQuiz);

    // Initialize
    showQuestion(1);
}

// ============================================
// OCEAN SECTION
// ============================================

function initOcean() {
    const canvas = document.getElementById('ocean-canvas');
    if (!canvas) return;

    const ctx = canvas.getContext('2d');

    function resize() {
        canvas.width = canvas.offsetWidth;
        canvas.height = canvas.offsetHeight;
    }
    resize();
    window.addEventListener('resize', resize);

    // Particles representing possibilities
    const particles = [];
    for (let i = 0; i < 50; i++) {
        particles.push({
            x: Math.random() * canvas.width,
            y: Math.random() * canvas.height,
            vx: (Math.random() - 0.5) * 0.5,
            vy: (Math.random() - 0.5) * 0.5,
            size: Math.random() * 3 + 1,
            alpha: Math.random() * 0.5 + 0.2
        });
    }

    function animate() {
        if (document.body.classList.contains('calm-mode')) {
            // Static version for calm mode
            ctx.fillStyle = 'rgba(10, 22, 40, 1)';
            ctx.fillRect(0, 0, canvas.width, canvas.height);

            particles.forEach(p => {
                ctx.beginPath();
                ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2);
                ctx.fillStyle = `rgba(0, 217, 255, ${p.alpha})`;
                ctx.fill();
            });
            return;
        }

        ctx.fillStyle = 'rgba(10, 22, 40, 0.1)';
        ctx.fillRect(0, 0, canvas.width, canvas.height);

        particles.forEach(p => {
            p.x += p.vx;
            p.y += p.vy;

            // Wrap around
            if (p.x < 0) p.x = canvas.width;
            if (p.x > canvas.width) p.x = 0;
            if (p.y < 0) p.y = canvas.height;
            if (p.y > canvas.height) p.y = 0;

            ctx.beginPath();
            ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2);
            ctx.fillStyle = `rgba(0, 217, 255, ${p.alpha})`;
            ctx.fill();
        });

        requestAnimationFrame(animate);
    }

    animate();

    // Universe pie chart
    drawUniversePie();

    // Award badge for visiting ocean
    setTimeout(() => {
        awardBadge('ocean-explorer');
    }, 5000);
}

function drawUniversePie() {
    const canvas = document.getElementById('universe-chart');
    if (!canvas) return;

    const ctx = canvas.getContext('2d');
    canvas.width = 250;
    canvas.height = 250;

    const centerX = canvas.width / 2;
    const centerY = canvas.height / 2;
    const radius = 100;

    // Data: ~5% visible, ~26% dark matter, ~69% dark energy
    const data = [
        { value: 5, color: '#00d9ff', label: 'Visible' },
        { value: 26, color: '#6b5b95', label: 'Dark Matter' },
        { value: 69, color: '#2c3e50', label: 'Dark Energy' }
    ];

    let startAngle = -Math.PI / 2;

    data.forEach(slice => {
        const sliceAngle = (slice.value / 100) * Math.PI * 2;

        ctx.beginPath();
        ctx.moveTo(centerX, centerY);
        ctx.arc(centerX, centerY, radius, startAngle, startAngle + sliceAngle);
        ctx.closePath();
        ctx.fillStyle = slice.color;
        ctx.fill();

        // Add border
        ctx.strokeStyle = '#1a1a2e';
        ctx.lineWidth = 2;
        ctx.stroke();

        startAngle += sliceAngle;
    });

    // Center circle
    ctx.beginPath();
    ctx.arc(centerX, centerY, 30, 0, Math.PI * 2);
    ctx.fillStyle = '#1a1a2e';
    ctx.fill();

    // YOU text
    ctx.fillStyle = '#00d9ff';
    ctx.font = 'bold 12px Nunito';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText('YOU', centerX, centerY);
}

// ============================================
// UTILITY FUNCTIONS
// ============================================

function toBase3(num) {
    if (num === 0) return '0';
    let result = '';
    while (num > 0) {
        result = (num % 3) + result;
        num = Math.floor(num / 3);
    }
    return result;
}

function generateOptions(correct, count, isBase3) {
    const options = new Set();
    options.add(isBase3 ? correct : correct.toString());

    while (options.size < count) {
        let wrong;
        if (isBase3) {
            const wrongNum = Math.max(1, parseInt(correct, 3) + Math.floor(Math.random() * 8) - 4);
            wrong = toBase3(wrongNum);
        } else {
            wrong = (correct + Math.floor(Math.random() * 10) - 5).toString();
        }
        if (wrong !== correct.toString() && wrong !== '0') {
            options.add(wrong);
        }
    }

    return shuffleArray([...options]);
}

function shuffleArray(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
}

function addStars(count) {
    userData.stars += count;
    saveUserData();
    updateUI();

    // Visual feedback
    const starCount = document.getElementById('star-count');
    if (starCount) {
        starCount.classList.add('pulse');
        setTimeout(() => starCount.classList.remove('pulse'), 300);
    }
}

function awardBadge(badgeId) {
    if (userData.badges.includes(badgeId)) return;

    userData.badges.push(badgeId);
    addStars(5);
    saveUserData();
    updateUI();

    // Show notification
    const badge = BADGES[badgeId];
    if (badge && userData.soundEnabled) {
        playTone(523.25, 0.1);
        playTone(659.25, 0.1);
        playTone(783.99, 0.2);
    }
}

function updateUI() {
    // Update star count
    const starCount = document.getElementById('star-count');
    if (starCount) starCount.textContent = userData.stars;

    // Update user display
    const userInitial = document.getElementById('user-initial');
    const userDisplayName = document.getElementById('user-display-name');
    if (userInitial && userData.name) {
        userInitial.textContent = userData.name.charAt(0).toUpperCase();
    }
    if (userDisplayName) {
        userDisplayName.textContent = userData.name || 'Guest';
    }

    // Update badges grid
    const badgesGrid = document.getElementById('badges-grid');
    if (badgesGrid) {
        badgesGrid.innerHTML = '';
        Object.entries(BADGES).forEach(([id, badge]) => {
            const div = document.createElement('div');
            div.className = `badge-item${userData.badges.includes(id) ? ' earned' : ''}`;
            div.innerHTML = `
                <span class="badge-icon">${badge.icon}</span>
                <span class="badge-name">${badge.name}</span>
            `;
            div.title = badge.desc;
            badgesGrid.appendChild(div);
        });
    }

    // Update game badges
    Object.keys(BADGES).forEach(id => {
        const badgeEl = document.querySelector(`.game-badge[data-badge="${id}"]`);
        if (badgeEl) {
            badgeEl.classList.toggle('earned', userData.badges.includes(id));
        }
    });

    // Update journey map
    updateJourneyMap();
}

// Audio functions
let audioCtx = null;

function playTone(freq, duration) {
    if (!userData.soundEnabled) return;

    try {
        if (!audioCtx) {
            audioCtx = new (window.AudioContext || window.webkitAudioContext)();
        }

        const oscillator = audioCtx.createOscillator();
        const gainNode = audioCtx.createGain();

        oscillator.connect(gainNode);
        gainNode.connect(audioCtx.destination);

        oscillator.frequency.value = freq;
        oscillator.type = 'sine';

        gainNode.gain.setValueAtTime(0.3, audioCtx.currentTime);
        gainNode.gain.exponentialRampToValueAtTime(0.01, audioCtx.currentTime + duration);

        oscillator.start(audioCtx.currentTime);
        oscillator.stop(audioCtx.currentTime + duration);
    } catch (e) {
        console.log('Audio not available');
    }
}

// Particle background
function initParticles() {
    const canvas = document.getElementById('particles-bg');
    if (!canvas) return;

    const ctx = canvas.getContext('2d');

    function resize() {
        canvas.width = window.innerWidth;
        canvas.height = window.innerHeight;
    }
    resize();
    window.addEventListener('resize', resize);

    const particles = [];
    for (let i = 0; i < 30; i++) {
        particles.push({
            x: Math.random() * canvas.width,
            y: Math.random() * canvas.height,
            vx: (Math.random() - 0.5) * 0.3,
            vy: (Math.random() - 0.5) * 0.3,
            size: Math.random() * 2 + 1
        });
    }

    function animate() {
        if (document.body.classList.contains('calm-mode')) {
            ctx.clearRect(0, 0, canvas.width, canvas.height);
            return;
        }

        ctx.fillStyle = 'rgba(26, 26, 46, 0.05)';
        ctx.fillRect(0, 0, canvas.width, canvas.height);

        ctx.fillStyle = 'rgba(233, 69, 96, 0.3)';
        particles.forEach(p => {
            p.x += p.vx;
            p.y += p.vy;

            if (p.x < 0 || p.x > canvas.width) p.vx *= -1;
            if (p.y < 0 || p.y > canvas.height) p.vy *= -1;

            ctx.beginPath();
            ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2);
            ctx.fill();
        });

        requestAnimationFrame(animate);
    }

    animate();
}

// Start particle animation
initParticles();
