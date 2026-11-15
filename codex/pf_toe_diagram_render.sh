#!/usr/bin/env bash
# Regenerate pf_toe_diagram.pdf from pf_toe_diagram.html.
# Uses puppeteer so Mermaid renders properly (snap chromium is AppArmor-blocked for headless PDF).
#
# Prerequisites (one-time):
#   mkdir -p /tmp/pdfgen && cd /tmp/pdfgen && npm init -y && npm install puppeteer
#   (this downloads chromium to ~/.cache/puppeteer; ~400MB first time)
#
# Usage:
#   ./pf_toe_diagram_render.sh
#
# To print from Pablo's own browser instead: open pf_toe_diagram.html in Chrome/Firefox, Ctrl+P, "Save as PDF."

set -e

HERE="$(cd "$(dirname "$0")" && pwd)"
HTML="$HERE/pf_toe_diagram.html"
PDF="$HERE/pf_toe_diagram.pdf"

if [ ! -f /tmp/pdfgen/node_modules/puppeteer/package.json ]; then
  echo "ERROR: puppeteer not installed. Run:"
  echo "  mkdir -p /tmp/pdfgen && cd /tmp/pdfgen && npm init -y && npm install puppeteer"
  exit 1
fi

cat > /tmp/pdfgen/_render_pf_toe.js <<EOF
const puppeteer = require('puppeteer');
(async () => {
  const browser = await puppeteer.launch({ headless: 'new', args: ['--no-sandbox', '--disable-setuid-sandbox'] });
  const page = await browser.newPage();
  await page.goto('file://$HTML', { waitUntil: ['load', 'networkidle0'], timeout: 60000 });
  await page.waitForFunction(() => document.querySelectorAll('.mermaid:not([data-processed])').length === 0, { timeout: 60000 });
  await new Promise(r => setTimeout(r, 1200));
  await page.pdf({
    path: '$PDF',
    format: 'Letter',
    printBackground: true,
    margin: { top: '0.6in', bottom: '0.6in', left: '0.5in', right: '0.5in' },
    preferCSSPageSize: true
  });
  await browser.close();
  console.log('Wrote $PDF');
})().catch(e => { console.error(e); process.exit(1); });
EOF

node /tmp/pdfgen/_render_pf_toe.js
echo "Done. Open $PDF to print."
