---
date: 2026-05-24
tags: [sandbox]
title: "Inside the V8 Sandbox"
description: "A practical map of V8's sandbox threat model, attack boundary, and the places browser code still has to be careful."
---

# Inside the V8 Sandbox

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

For historical reasons, V8 sandbox has multiple mechanisms related to preventing execution from sandbox memory to the outside. The main mechanism is the **JDT** (JS Dispatch Table). V8 also has supporting mechanisms:

- **CPT** (Code Pointer Table): The original mechanism designed to prevent code execution from sandbox memory to outside. It is gradually being deprecated in favor of TPT.

  > Comments from [`v8/src/sandbox/code-pointer-table.h`](https://source.chromium.org/chromium/_/chromium/v8/v8/+/e88e94638bf0e99430828b1b27251b7e2db15147:src/sandbox/code-pointer-table.h;l=94-113):
  >
  > A table containing pointers to Code.
  >
  > TODO(498510170): Removing this table and replacing the usages with the TPT is work in progress.
  >
  > Essentially a specialized version of the trusted pointer table (TPT). A code pointer table entry contains both a pointer to a Code object as well as a pointer to the entrypoint. This way, the performance sensitive code paths that for example call a JSFunction can directly load the entrypoint from the table without having to load it from the Code object.
  >
  > When the sandbox is enabled, a code pointer table (CPT) is used to ensure basic control-flow integrity in the absence of special hardware support (such as landing pad instructions): by referencing code through an index into a CPT, and ensuring that only valid code entrypoints are stored inside the table, it is then guaranteed that any indirect control-flow transfer ends up on a valid entrypoint as long as an attacker is still confined to the sandbox.

- **TPT** (Trusted Pointer Table): Originally designed for storing pointers to trusted objects in general. These objects can include Code, which is why the long-term plan is to absorb CPT into TPT.

### JS Dispatch Table

#### Quick View of JSFunction and Its Function Handle

A JavaScript function as the user sees it (`function f() { ... }` or `(x) => x + 1`), V8 will use a `JSFunction` object to represent it. A `JSFunction` object contains a field called [`dispatch_handle_`](https://source.chromium.org/chromium/_/chromium/v8/v8/+/e88e94638bf0e99430828b1b27251b7e2db15147:src/objects/js-function.h;l=505) to store the index of the `JSDispatchTable` entry, which is used to repace the direct call to the function.

`dispatch_handle_` is a 32-bit integer, it's lower 8 bits is always 0, and the other 24 bits is the index of the `JSDispatchTable` entry.

```text
+---------------------------------+------------+
| JSDispatchTable index (24 bits) | 0 (8 bits) |
+---------------------------------+------------+
```

Since the index have only 24 bits, the number of JDT entries will not exceed `2^24 = 16M`. Each entry's is 16 bytes, so the total size of JDT table is 256M. The 16 bytes include: 

```
Offset 0  ┌─────────────────────────────────────────────────┐
   |      │   entrypoint_   (atomic<Address>)               │  ← Word 0：raw machine code pointer
Offset 8  ├─────────────────────────────────────────────────┤
   |      │   encoded_word_ (atomic<Address>)               │  ← Word 1：pack 3 info
Offset 16 └─────────────────────────────────────────────────┘
```

for the second field, it includes:

```
bit  63               17 16                15            0
  +-------------------+----+-------------------------------+
  |  HeapObject ptr   |mark|     parameter_count           |
  |    (47 bits)      |    |       (16 bits)               |
  +-------------------+----+-------------------------------+
```

After finding the entry, V8 will use the `entrypoint_` to call the function. For freeed entry, the high 16 bits of `entrypoint_` are set to 1, which ensure dereference of free entry's `entrypoint_` will always cause segment faults. Such design ensure attacker can only replace one JS function to another JS function, considering directly call any JS function is allowed, JDT will not grant attacker any new primities. 

#### Some Pitfall Examples

Although JDT looks perfect, if we consider the attack path that I mentioned in the beginning, we will find some historical CVE that bypass the JDT check. Before JDT jumped to `entrypoint_`, the caller will put arguments into the stack (such mechanism is usually complex because different JIT optimizations may have different argument passing mechanisms), but the caller do not pass parameter size to the callee, the callee will recalculate the parameter size based on data stored in the sandbox again, which is called SFI. However, the attacker can swap the SFI to make the parameter size is longer than the actual parameter size, which will cause the stack overlow read. Hence, the harden for these issues is read JDT again to ensure the parameter size is consistent.

The essential of bug is the attacker indirectly affact the data in the register which is represent the offset of the stack, which will cause the stack overlow read. Commit [crrev.com/c/5906113 ](https://chromium-review.googlesource.com/c/v8/v8/+/5906113) record how the bug is fixed.

### Code Pointer Table

> TODO 

## How V8 Sandbox Validate Write from Sandbox Memory to Outside?

V8 use another two table to prevent write from sandbox memory to outside, based on the difference of allocator, these objects put outside sandbox memory but still need to be accessed are split into two tables:

- **EPT** (External Pointer Table): The mechanism is used to access objects allocated by other components / C++.
- **TPT** (Trusted Pointer Table): The mechanism is used to access objects allocated by V8 engine.

### External Pointer Table

Like the JDT, the sandbox never store the original pointer of the external objects but store the EPT handle, which is used to index the EPT table. EPT handle have 32 bits, the low 8 bits is always 0, and the other 24 bits is the index of the EPT table, which is exactly same as the JDT index. The difference is the EPT entry have only 8 bytes which is half of the JDT entry.

```text
bit 63                      56             49  48                               0
+---------------------------+--------------+---+--------------------------------+
| pointer high 8 bits       |   tag 7 bits |mrk| pointer low 48 bits            |
| (for hardware features)   |              |   |                                |
| (56 bits)                 | (7 bits)     |   | (48 bits)                      |
+---------------------------+--------------+---+--------------------------------+
```

the `mrk` is used for GC mechanism, which will be discussed later. If V8 code want to dereference a EPT handle, the V8 code will always provide a tag which is hardcodeed though template mechanism, the tag will used to compare with the tag in the EPT entry, if they are not the same, the V8 code will abort the execution. Specifically, the tag is a 7 bits integer, which will be XORed with the tag in the EPT entry, if the result is not 0, the V8 code abort the execution automatically.

```c++
template <ExternalPointerTag tag> // <= hardcoded tag
Address ReadExternalPointerField(Address field_address, IsolateForSandbox isolate) {
  // ① read handle from sandbox (4 bytes)
  ExternalPointerHandle handle = *reinterpret_cast<ExternalPointerHandle*>(field_address);
  
  // ② handle → index
  uint32_t index = handle >> kExternalPointerIndexShift;   // >> 6
  
  // ③ read entry
  Address payload = isolate.external_pointer_table().at(index).load();
  
  // ④ validate tag and extract pointer
  Address expected_tag_bits = static_cast<Address>(tag) << kExternalPointerTagShift;
  return (payload ^ expected_tag_bits) & kExternalPointerPayloadMask;
}
```

### Trusted Pointer Table

TPT is almost same as EPT, the main difference is the tag is wider than 7 bits, which is 15 bits.

```text
+----------------------+--------+--------------------+
| tag (15 bits)        | mark   | pointer (48 bits)  |
| bits 63..49          | bit 48 | bits 0..47         |
+----------------------+--------+--------------------+
```

Additionally, TPT have publish/unpublish mechanism, which is used to mark if an object is fully initialized or not. The mechanism is need is because the V8 engine may allocate a lot of objects which are depend on each other, if any one of them is not fully initialized, the other objects may be corrupted. So TPT allocated a special bit to mark if an object is fully initialized or not. The bit will never be used by other tag, which ensure the tag is always valid.

## Objects Partition

Now, let's refine the threat model again, we will figure out what objects are stored in sandbox memory, what objects are managed by JDT, EPT, TPT, etc.

> TODO
