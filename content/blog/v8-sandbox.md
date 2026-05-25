---
date: 2026-05-24
tags: [sandbox]
---

# How V8 Sandbox Works

V8's sandbox is a well-known feature designed to address a core security problem: because vulnerabilities in the V8 engine are hard to fully eliminate, how can the browser be protected from being compromised by exploits targeting V8?

## Why V8 Sandbox is Needed?

Briefly, V8 is a JavaScript engine, which is a interpreter / compiler that is inherently more complex than many other browser components (such as parsers). Unlike most of those components, it also executes arbitrary user-supplied code. Together, that makes V8 both harder to secure and a much larger attack surface than typical projects.

If we look at other programming language interpreters/compilers, such as Python, PHP or Clang, they always have many open vulnerabilities awaiting repair. For example, a quick GitHub snapshot on 2026-05-25 looked like this:

- **CPython:** [81 open `type-security` issues](https://github.com/python/cpython/issues?q=is%3Aissue%20state%3Aopen%20label%3Atype-security).
- **PHP:** [256 open issues marked `Status: Verified`](https://github.com/php/php-src/issues?q=is%3Aissue%20state%3Aopen%20label%3A%22Status%3A%20Verified%22).
- **Clang/LLVM:** [239 open `crash-on-valid clang` issues](https://github.com/llvm/llvm-project/issues?q=is%3Aissue%20state%3Aopen%20label%3Acrash-on-valid%20clang).

In practice, V8 is even more complex than these engines because of its aggressive JIT optimizations, which we will discuss later. 

## V8 Sandbox Threat Model

The original text from V8 sandbox README is:

> The sandbox assumes that an attacker can arbitrarily and concurrently modify any memory inside the sandbox address space as this primitive can be constructed from typical V8 vulnerabilities. Further, it is assumed that an attacker will be able to read memory outside of the sandbox, for example through hardware side channels. The sandbox then aims to protect the rest of the process from such an attacker. As such, any write access leading to a corruption of memory outside of the sandbox address space that is not otherwise safeguarded is considered a sandbox violation. Note that some write accesses outside of the sandbox are not generally considered corruptions. Examples:
>
> - writes that are always trapped in safe regions (e.g., segmented tables);
> - counters that are re-validated when they are actually used;
> - tricking the garbage collector to free objects, as long as the metadata itself is consistent and the corruption stays within the sandbox;

One point worth noting is that, when reading the concrete mechanisms of the V8 sandbox directly, it can feel very secure because it seems to block every possible way to escape the sandbox. However, many harmful outcomes cannot be prevented by the sandbox itself; they still largely depend on the actual implementation of other parts of the browser.

To find these harmful results, we should understand the boundary of the V8 sandbox. Based on my understanding, the sandbox mainly prevents direct attacks from V8 code against memory outside the sandbox. For example, if V8 code reads attacker-controlled sandbox memory and uses it as a pointer for an out-of-sandbox write, or as a code pointer for execution, that behavior should be validated or controlled by the sandbox. However, if V8 code copies ordinary data from the sandbox into outside memory, and other browser code later reads, writes, or interprets that data in a harmful way, this is a different problem. The sandbox may have allowed the data flow correctly, while the real bug is that the other code trusted attacker-controlled data.

<figure>
  <svg viewBox="0 0 980 560" role="img" aria-label="Two V8 sandbox attack paths" xmlns="http://www.w3.org/2000/svg">
    <defs>
      <filter id="card-shadow" x="-20%" y="-20%" width="140%" height="140%">
        <feDropShadow dx="0" dy="2" stdDeviation="4" flood-color="#0f172a" flood-opacity="0.1"></feDropShadow>
      </filter>

      <marker id="arrow-green" viewBox="0 0 12 12" refX="10" refY="6" markerWidth="8" markerHeight="8" orient="auto-start-reverse">
        <path d="M 0 0 L 12 6 L 0 12 z" fill="#10b981"></path>
      </marker>
      <marker id="arrow-red" viewBox="0 0 12 12" refX="10" refY="6" markerWidth="8" markerHeight="8" orient="auto-start-reverse">
        <path d="M 0 0 L 12 6 L 0 12 z" fill="#ef4444"></path>
      </marker>
      <marker id="arrow-gray" viewBox="0 0 12 12" refX="10" refY="6" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
        <path d="M 0 0 L 12 6 L 0 12 z" fill="#64748b"></path>
      </marker>

      <linearGradient id="grad-sandbox" x1="0" y1="0" x2="0" y2="1">
        <stop offset="0%" stop-color="#ecfdf5"></stop>
        <stop offset="100%" stop-color="#d1fae5"></stop>
      </linearGradient>
      <linearGradient id="grad-code" x1="0" y1="0" x2="0" y2="1">
        <stop offset="0%" stop-color="#eff6ff"></stop>
        <stop offset="100%" stop-color="#dbeafe"></stop>
      </linearGradient>
      <linearGradient id="grad-outside" x1="0" y1="0" x2="0" y2="1">
        <stop offset="0%" stop-color="#fff7ed"></stop>
        <stop offset="100%" stop-color="#fed7aa"></stop>
      </linearGradient>
      <linearGradient id="grad-attacker" x1="0" y1="0" x2="0" y2="1">
        <stop offset="0%" stop-color="#f8fafc"></stop>
        <stop offset="100%" stop-color="#e2e8f0"></stop>
      </linearGradient>
    </defs>

    <style>
      .h { font-family: ui-sans-serif, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; font-weight: 700; }
      .b { font-family: ui-sans-serif, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; }
      .l { font-family: ui-sans-serif, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; font-weight: 600; }
    </style>

    <rect x="40" y="225" width="140" height="80" rx="12" fill="url(#grad-attacker)" stroke="#94a3b8" stroke-width="1.5" filter="url(#card-shadow)"></rect>
    <text x="110" y="261" text-anchor="middle" class="h" font-size="18" fill="#334155">Attacker</text>
    <text x="110" y="283" text-anchor="middle" class="b" font-size="11" fill="#64748b">via JS / V8 bug</text>

    <rect x="240" y="115" width="240" height="130" rx="12" fill="url(#grad-sandbox)" stroke="#10b981" stroke-width="1.5" filter="url(#card-shadow)"></rect>
    <text x="360" y="151" text-anchor="middle" class="h" font-size="17" fill="#065f46">Sandbox Memory</text>
    <text x="360" y="179" text-anchor="middle" class="b" font-size="12" fill="#047857">objects · metadata · data</text>
    <text x="360" y="199" text-anchor="middle" class="b" font-size="12" fill="#047857">attacker can read / write</text>
    <text x="360" y="223" text-anchor="middle" class="b" font-size="11" font-style="italic" fill="#059669">(threat model assumption)</text>

    <rect x="255" y="320" width="210" height="110" rx="12" fill="url(#grad-code)" stroke="#3b82f6" stroke-width="1.5" filter="url(#card-shadow)"></rect>
    <text x="360" y="356" text-anchor="middle" class="h" font-size="17" fill="#1e40af">V8 Code</text>
    <text x="360" y="383" text-anchor="middle" class="b" font-size="12" fill="#1d4ed8">reads sandbox memory</text>
    <text x="360" y="403" text-anchor="middle" class="b" font-size="12" fill="#1d4ed8">and calls helpers / APIs</text>

    <rect x="700" y="88" width="220" height="126" rx="12" fill="url(#grad-outside)" stroke="#fb923c" stroke-width="1.5" filter="url(#card-shadow)"></rect>
    <text x="810" y="124" text-anchor="middle" class="h" font-size="17" fill="#9a3412">Outside Memory</text>
    <text x="810" y="154" text-anchor="middle" class="b" font-size="12" fill="#c2410c">memory / registers</text>
    <text x="810" y="174" text-anchor="middle" class="b" font-size="12" fill="#c2410c">outside the sandbox</text>
    <text x="810" y="194" text-anchor="middle" class="b" font-size="12" fill="#c2410c">destination of writes / copies</text>

    <rect x="700" y="330" width="220" height="126" rx="12" fill="url(#grad-code)" stroke="#3b82f6" stroke-width="1.5" filter="url(#card-shadow)"></rect>
    <text x="810" y="366" text-anchor="middle" class="h" font-size="17" fill="#1e40af">Other Code</text>
    <text x="810" y="396" text-anchor="middle" class="b" font-size="12" fill="#1d4ed8">browser / renderer code</text>
    <text x="810" y="416" text-anchor="middle" class="b" font-size="12" fill="#1d4ed8">reads, writes, or</text>
    <text x="810" y="436" text-anchor="middle" class="b" font-size="12" fill="#1d4ed8">interprets copied data</text>

    <path d="M 180 252 C 205 235, 215 195, 240 178" fill="none" stroke="#10b981" stroke-width="2.5" marker-end="url(#arrow-green)"></path>
    <rect x="175" y="200" width="58" height="20" rx="10" fill="#10b981"></rect>
    <text x="204" y="214" text-anchor="middle" class="l" font-size="11" fill="white">change</text>

    <line x1="360" y1="245" x2="360" y2="320" stroke="#64748b" stroke-width="2" marker-end="url(#arrow-gray)"></line>
    <text x="370" y="277" class="b" font-size="11" fill="#475569">code reads</text>
    <text x="370" y="291" class="b" font-size="11" fill="#475569">sandbox memory</text>

    <path d="M 465 370 C 565 345, 650 248, 700 165" fill="none" stroke="#ef4444" stroke-width="2.5" marker-end="url(#arrow-red)"></path>
    <g transform="translate(250, 465)">
      <rect x="0" y="0" width="78" height="22" rx="11" fill="#ef4444"></rect>
      <text x="39" y="15" text-anchor="middle" class="l" font-size="12" fill="white">ATTACK 1</text>
      <text x="88" y="15" class="l" font-size="12" fill="#991b1b">V8 uses sandbox data as pointer / argument for write / execute</text>
      <text x="88" y="33" class="b" font-size="11" fill="#7f1d1d">validated by sandbox — this is the core sandbox check</text>
    </g>

    <path d="M 480 178 C 600 214, 632 348, 700 392" fill="none" stroke="#ef4444" stroke-width="2.5" stroke-dasharray="7 5" marker-end="url(#arrow-red)"></path>
    <line x1="700" y1="392" x2="700" y2="392" stroke="#ef4444" stroke-width="2.5"></line>
    <g transform="translate(250, 35)">
      <rect x="0" y="0" width="78" height="22" rx="11" fill="#ef4444"></rect>
      <text x="39" y="15" text-anchor="middle" class="l" font-size="12" fill="white">ATTACK 2</text>
      <text x="88" y="15" class="l" font-size="12" fill="#991b1b">V8 copies sandbox data out → other code later interprets it</text>
      <text x="88" y="33" class="b" font-size="11" fill="#7f1d1d">allowed by sandbox — safety depends on the other code</text>
    </g>
  </svg>
  <figcaption>Two attack paths from sandbox memory. Green: the threat model assumes the attacker can change sandbox memory at will. Attack 1 (solid red): V8 code uses attacker-controlled sandbox data as a pointer or argument for an outside write or execute — this is what the sandbox actually validates. Attack 2 (dashed red): V8 code copies attacker-controlled data into outside memory, and other browser code later reads, writes, or interprets it — the sandbox allows this, so safety depends on the other code.</figcaption>
</figure>


## How V8 Sandbox Validate Execute from Sandbox Memory to Outside?
