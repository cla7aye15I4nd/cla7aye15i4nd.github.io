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

To find these harmful results, we should understand the boundary of the V8 sandbox. Based on my understanding, there are two kinds of attacks worth distinguishing, and the second one has two sub-paths:

- **Attack 1** : V8 code reads attacker-controlled sandbox memory and uses it as a pointer for an out-of-sandbox write, or as a code pointer for execution. This is exactly the behavior the sandbox is designed to validate, so the sandbox should block it.
- **Attack 2** : attacker-controlled sandbox data ends up being read, written, or interpreted by some other browser code, which then does something harmful with it. The sandbox allows the data flow; the real bug is that the other code trusted attacker-controlled data. There are two sub-paths:
  - **A** : the other code reads sandbox memory directly. The sandbox does not restrict outside-in reads.
  - **B** : V8 copies the sandbox data into outside memory as ordinary data, and the other code later consumes it from there.

<figure>
  <svg viewBox="0 0 1020 560" role="img" aria-label="V8 sandbox attack paths" xmlns="http://www.w3.org/2000/svg">
    <defs>
      <marker id="arrow-green" viewBox="0 0 12 12" refX="10" refY="6" markerWidth="8" markerHeight="8" orient="auto-start-reverse">
        <path d="M 0 0 L 12 6 L 0 12 z" fill="#10b981"></path>
      </marker>
      <marker id="arrow-red" viewBox="0 0 12 12" refX="10" refY="6" markerWidth="8" markerHeight="8" orient="auto-start-reverse">
        <path d="M 0 0 L 12 6 L 0 12 z" fill="#ef4444"></path>
      </marker>
      <marker id="arrow-gray" viewBox="0 0 12 12" refX="10" refY="6" markerWidth="7" markerHeight="7" orient="auto-start-reverse">
        <path d="M 0 0 L 12 6 L 0 12 z" fill="#64748b"></path>
      </marker>
    </defs>

    <style>
      .h { font-family: ui-sans-serif, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; font-weight: 700; }
      .b { font-family: ui-sans-serif, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; }
      .l { font-family: ui-sans-serif, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; font-weight: 600; }
    </style>

    <rect x="40" y="255" width="140" height="80" rx="4" fill="#f1f5f9" stroke="#94a3b8" stroke-width="1.5"></rect>
    <text x="110" y="291" text-anchor="middle" class="h" font-size="18" fill="#334155">Attacker</text>
    <text x="110" y="313" text-anchor="middle" class="b" font-size="11" fill="#64748b">via JS / V8 bug</text>

    <rect x="230" y="120" width="240" height="120" rx="4" fill="#d1fae5" stroke="#10b981" stroke-width="1.5"></rect>
    <text x="350" y="156" text-anchor="middle" class="h" font-size="17" fill="#065f46">Sandbox Memory</text>
    <text x="350" y="183" text-anchor="middle" class="b" font-size="12" fill="#047857">objects · metadata · data</text>
    <text x="350" y="203" text-anchor="middle" class="b" font-size="12" fill="#047857">attacker can read / write</text>
    <text x="350" y="225" text-anchor="middle" class="b" font-size="11" font-style="italic" fill="#059669">(threat model assumption)</text>

    <rect x="230" y="330" width="240" height="110" rx="4" fill="#dbeafe" stroke="#3b82f6" stroke-width="1.5"></rect>
    <text x="350" y="366" text-anchor="middle" class="h" font-size="17" fill="#1e40af">V8 Code</text>
    <text x="350" y="393" text-anchor="middle" class="b" font-size="12" fill="#1d4ed8">reads sandbox memory,</text>
    <text x="350" y="413" text-anchor="middle" class="b" font-size="12" fill="#1d4ed8">writes outside, calls APIs</text>

    <rect x="555" y="195" width="220" height="140" rx="4" fill="#fed7aa" stroke="#f97316" stroke-width="1.5"></rect>
    <text x="665" y="231" text-anchor="middle" class="h" font-size="17" fill="#9a3412">Outside Memory</text>
    <text x="665" y="258" text-anchor="middle" class="b" font-size="12" fill="#c2410c">memory / registers</text>
    <text x="665" y="278" text-anchor="middle" class="b" font-size="12" fill="#c2410c">outside the sandbox</text>
    <line x1="580" y1="295" x2="750" y2="295" stroke="#fb923c" stroke-width="1" opacity="0.6"></line>
    <text x="665" y="316" text-anchor="middle" class="b" font-size="12" fill="#c2410c">destination of V8</text>
    <text x="665" y="328" text-anchor="middle" class="b" font-size="12" fill="#c2410c">writes / copies</text>

    <rect x="830" y="260" width="170" height="140" rx="4" fill="#e0e7ff" stroke="#6366f1" stroke-width="1.5"></rect>
    <text x="915" y="296" text-anchor="middle" class="h" font-size="17" fill="#3730a3">Other Code</text>
    <text x="915" y="324" text-anchor="middle" class="b" font-size="12" fill="#4338ca">browser / renderer</text>
    <text x="915" y="344" text-anchor="middle" class="b" font-size="12" fill="#4338ca">code reads, writes,</text>
    <text x="915" y="364" text-anchor="middle" class="b" font-size="12" fill="#4338ca">or interprets data</text>

    <path d="M 180 280 C 200 260, 215 215, 230 195" fill="none" stroke="#10b981" stroke-width="2.5" marker-end="url(#arrow-green)"></path>
    <rect x="175" y="220" width="58" height="20" rx="4" fill="#10b981"></rect>
    <text x="204" y="234" text-anchor="middle" class="l" font-size="11" fill="white">change</text>

    <line x1="350" y1="240" x2="350" y2="330" stroke="#64748b" stroke-width="2" marker-end="url(#arrow-gray)"></line>
    <text x="340" y="287" text-anchor="end" class="b" font-size="11" fill="#475569">V8 reads sandbox memory</text>

    <path d="M 470 360 C 510 330, 540 270, 555 245" fill="none" stroke="#ef4444" stroke-width="2.5" marker-end="url(#arrow-red)"></path>
    <text x="510" y="290" text-anchor="middle" class="b" font-size="10" font-weight="600" fill="#b91c1c">ptr / arg</text>

    <path d="M 470 410 C 510 390, 540 340, 555 320" fill="none" stroke="#ef4444" stroke-width="2.5" stroke-dasharray="7 5" marker-end="url(#arrow-red)"></path>
    <text x="510" y="412" text-anchor="middle" class="b" font-size="10" font-weight="600" fill="#b91c1c">data copy</text>

    <path d="M 775 285 C 795 295, 815 315, 830 325" fill="none" stroke="#ef4444" stroke-width="2.5" stroke-dasharray="7 5" marker-end="url(#arrow-red)"></path>

    <path d="M 470 145 C 660 65, 850 130, 880 260" fill="none" stroke="#ef4444" stroke-width="2.5" stroke-dasharray="7 5" marker-end="url(#arrow-red)"></path>

    <g transform="translate(320, 25)">
      <rect x="0" y="0" width="92" height="22" rx="4" fill="#ef4444"></rect>
      <text x="46" y="15" text-anchor="middle" class="l" font-size="12" fill="white">ATTACK 2A</text>
      <text x="102" y="15" class="l" font-size="12" fill="#991b1b">other code directly reads sandbox memory</text>
      <text x="102" y="33" class="b" font-size="11" fill="#7f1d1d">allowed by sandbox — it doesn't restrict outside-in reads</text>
    </g>

    <g transform="translate(40, 480)">
      <rect x="0" y="0" width="78" height="22" rx="4" fill="#ef4444"></rect>
      <text x="39" y="15" text-anchor="middle" class="l" font-size="12" fill="white">ATTACK 1</text>
      <text x="88" y="15" class="l" font-size="12" fill="#991b1b">V8 uses sandbox data as pointer / arg for write / execute</text>
      <text x="88" y="33" class="b" font-size="11" fill="#7f1d1d">validated by sandbox — this is the core sandbox check</text>
    </g>

    <g transform="translate(490, 480)">
      <rect x="0" y="0" width="92" height="22" rx="4" fill="#ef4444"></rect>
      <text x="46" y="15" text-anchor="middle" class="l" font-size="12" fill="white">ATTACK 2B</text>
      <text x="102" y="15" class="l" font-size="12" fill="#991b1b">V8 copies sandbox data out → other code interprets it</text>
      <text x="102" y="33" class="b" font-size="11" fill="#7f1d1d">allowed by sandbox — safety depends on the other code</text>
    </g>
  </svg>
</figure>


## How V8 Sandbox Validate Execute from Sandbox Memory to Outside?

Due to some historical reasons, V8 sandbox have mutiply mechanism related to prevent execute from sandbox memory to outside. The main mechanism is called **JDT** (JS Dispatch Table). V8 also have other mechanisms to prevent it, such as:
- **CPT** (Code Pointer Table): The mechanism is originally designed to prevent code execution from sandbox memory to outside. However, due to performance and campatibility reasons, it is gradually deprecated.
  > Comments from [v8/src/sandbox/code-pointer-table.h](https://chromium.googlesource.com/v8/v8/+/e88e94638bf0e99430828b1b27251b7e2db15147/src/sandbox/code-pointer-table.h):
  > A table containing pointers to Code.
  >
  > TODO(498510170): Removing this table and replacing the usages with the TPT is work in progress.
  >
  > Essentially a specialized version of the trusted pointer table (TPT). A code pointer table entry contains both a pointer to a Code object as well as a pointer to the entrypoint. This way, the performance sensitive code paths that for example call a JSFunction can directly load the entrypoint from the table without having to load it from the Code object.
  >
  > When the sandbox is enabled, a code pointer table (CPT) is used to ensure basic control-flow integrity in the absence of special hardware support (such as landing pad instructions): by referencing code through an index into a CPT, and ensuring that only valid code entrypoints are stored inside the table, it is then guaranteed that any indirect control-flow transfer ends up on a valid entrypoint as long as an attacker is still confined to the sandbox.
- **TPT** (Trusted Pointer Table): The mechanism is originally designed for storing pointers to trusted objects, these objects are also included code pointers.

