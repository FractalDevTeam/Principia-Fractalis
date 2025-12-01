/**
 * Principia Fractalis Website
 * Minimal JavaScript for accessibility and subtle interactions
 */

document.addEventListener('DOMContentLoaded', function() {
    // Smooth scroll for anchor links
    document.querySelectorAll('a[href^="#"]').forEach(anchor => {
        anchor.addEventListener('click', function(e) {
            e.preventDefault();
            const target = document.querySelector(this.getAttribute('href'));
            if (target) {
                target.scrollIntoView({
                    behavior: 'smooth',
                    block: 'start'
                });
            }
        });
    });

    // Animate elements on scroll
    const observerOptions = {
        root: null,
        rootMargin: '0px',
        threshold: 0.1
    };

    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                entry.target.classList.add('visible');
            }
        });
    }, observerOptions);

    // Observe cards, stats, and problems
    document.querySelectorAll('.card, .stat, .problem, .prover').forEach(el => {
        el.classList.add('animate-on-scroll');
        observer.observe(el);
    });

    // Animate consciousness meter on scroll
    const meterFill = document.querySelector('.meter-fill');
    if (meterFill) {
        const meterObserver = new IntersectionObserver((entries) => {
            entries.forEach(entry => {
                if (entry.isIntersecting) {
                    meterFill.style.width = '99.54%'; // Human brain ch₂ value
                }
            });
        }, { threshold: 0.5 });

        meterObserver.observe(meterFill.parentElement);
    }
});

// Add CSS for scroll animations
const style = document.createElement('style');
style.textContent = `
    .animate-on-scroll {
        opacity: 0;
        transform: translateY(20px);
        transition: opacity 0.6s ease, transform 0.6s ease;
    }

    .animate-on-scroll.visible {
        opacity: 1;
        transform: translateY(0);
    }

    .card:nth-child(2).animate-on-scroll { transition-delay: 0.1s; }
    .card:nth-child(3).animate-on-scroll { transition-delay: 0.2s; }

    .problem:nth-child(2).animate-on-scroll { transition-delay: 0.05s; }
    .problem:nth-child(3).animate-on-scroll { transition-delay: 0.1s; }
    .problem:nth-child(4).animate-on-scroll { transition-delay: 0.15s; }
    .problem:nth-child(5).animate-on-scroll { transition-delay: 0.2s; }
    .problem:nth-child(6).animate-on-scroll { transition-delay: 0.25s; }
`;
document.head.appendChild(style);
