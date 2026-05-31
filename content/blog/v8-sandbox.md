---
date: 2026-05-24
tags: [sandbox]
title: "Inside the V8 Sandbox"
description: "Notes on V8's sandbox threat model, attack boundary, and the browser code that still has to treat sandbox data carefully."
---

# Inside the V8 Sandbox

The V8 sandbox is one of Chrome's answers to an uncomfortable fact: V8 will continue to have bugs. The goal is not to make every engine bug harmless, but to keep a typical V8 memory-corruption bug from turning into arbitrary writes or control-flow hijacking in the rest of the renderer process.

## Why Does V8 Need a Sandbox?

V8 is a JavaScript engine, so it is both an interpreter and a compiler. It is also much more complex than many other browser components, especially compared with ordinary parsers. More importantly, it runs attacker-supplied JavaScript by design. Those two properties make V8 hard to audit and attractive to exploit.

Other language runtimes and compilers show the same pattern. Python, PHP, Clang, and similar projects usually have a non-trivial backlog of security or crash bugs. A quick GitHub snapshot on 2026-05-25 looked like this:

- **CPython:** [81 open `type-security` issues](https://github.com/python/cpython/issues?q=is%3Aissue%20state%3Aopen%20label%3Atype-security).
- **PHP:** [256 open issues marked `Status: Verified`](https://github.com/php/php-src/issues?q=is%3Aissue%20state%3Aopen%20label%3A%22Status%3A%20Verified%22).
- **Clang/LLVM:** [239 open `crash-on-valid clang` issues](https://github.com/llvm/llvm-project/issues?q=is%3Aissue%20state%3Aopen%20label%3Acrash-on-valid%20clang).

V8 is in the same family of difficult targets, with the extra burden of aggressive JIT optimization.

## V8 Sandbox Threat Model

The V8 sandbox README defines the threat model this way:

> The sandbox assumes that an attacker can arbitrarily and concurrently modify any memory inside the sandbox address space as this primitive can be constructed from typical V8 vulnerabilities. Further, it is assumed that an attacker will be able to read memory outside of the sandbox, for example through hardware side channels. The sandbox then aims to protect the rest of the process from such an attacker. As such, any write access leading to a corruption of memory outside of the sandbox address space that is not otherwise safeguarded is considered a sandbox violation. Note that some write accesses outside of the sandbox are not generally considered corruptions. Examples:
>
> - writes that are always trapped in safe regions (e.g., segmented tables);
> - counters that are re-validated when they are actually used;
> - tricking the garbage collector to free objects, as long as the metadata itself is consistent and the corruption stays within the sandbox;

At first glance, the concrete sandbox mechanisms can look nearly complete: every interesting pointer seems to go through a table, every indirect edge seems to be checked somewhere. The important caveat is that the sandbox only protects a particular boundary. Harmful behavior can still happen when code outside that boundary trusts data that came from inside it.

I find it useful to split the possible attacks into two groups. The second group has two common paths:

- **Attack 1:** V8 code reads attacker-controlled sandbox memory and uses it as a pointer for an out-of-sandbox write, or as a code pointer for execution. This is the kind of edge the sandbox is meant to validate, so a correctly implemented sandbox should block it.
- **Attack 2:** attacker-controlled sandbox data is read, copied, or interpreted by other browser code, and that code does something unsafe with it. The sandbox permits the data flow; the bug is that the consumer treated sandbox data as trusted. There are two sub-paths:
  - **A:** other code reads sandbox memory directly. The sandbox does not restrict outside-in reads.
  - **B:** V8 copies sandbox data into outside memory as ordinary data, and other code later consumes it from there.

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
    <text x="110" y="313" text-anchor="middle" class="b" font-size="11" fill="#64748b">through JS / V8 bug</text>

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
      <text x="102" y="33" class="b" font-size="11" fill="#7f1d1d">allowed by sandbox; outside-in reads are unrestricted</text>
    </g>

    <g transform="translate(40, 480)">
      <rect x="0" y="0" width="78" height="22" rx="4" fill="#ef4444"></rect>
      <text x="39" y="15" text-anchor="middle" class="l" font-size="12" fill="white">ATTACK 1</text>
      <text x="88" y="15" class="l" font-size="12" fill="#991b1b">V8 uses sandbox data as pointer / argument for write / execute</text>
      <text x="88" y="33" class="b" font-size="11" fill="#7f1d1d">validated by sandbox as the core check</text>
    </g>

    <g transform="translate(490, 480)">
      <rect x="0" y="0" width="92" height="22" rx="4" fill="#ef4444"></rect>
      <text x="46" y="15" text-anchor="middle" class="l" font-size="12" fill="white">ATTACK 2B</text>
      <text x="102" y="15" class="l" font-size="12" fill="#991b1b">V8 copies sandbox data out → other code interprets it</text>
      <text x="102" y="33" class="b" font-size="11" fill="#7f1d1d">allowed by sandbox; safety depends on the other code</text>
    </g>
  </svg>
</figure>


## How Does the Sandbox Validate Execution Edges?

V8 has several mechanisms that prevent sandbox-controlled data from becoming an unchecked control-flow target. The main one is the **JDT** (JS Dispatch Table), with a few related tables around it:

- **CPT** (Code Pointer Table): the older mechanism for preventing sandbox-controlled code pointers from jumping outside the sandbox. It is being phased out in favor of TPT.

  > Comments from [`v8/src/sandbox/code-pointer-table.h`](https://source.chromium.org/chromium/_/chromium/v8/v8/+/e88e94638bf0e99430828b1b27251b7e2db15147:src/sandbox/code-pointer-table.h;l=94-113):
  >
  > A table containing pointers to Code.
  >
  > TODO(498510170): Removing this table and replacing the usages with the TPT is work in progress.
  >
  > Essentially a specialized version of the trusted pointer table (TPT). A code pointer table entry contains both a pointer to a Code object as well as a pointer to the entrypoint. This way, the performance sensitive code paths that for example call a JSFunction can directly load the entrypoint from the table without having to load it from the Code object.
  >
  > When the sandbox is enabled, a code pointer table (CPT) is used to ensure basic control-flow integrity in the absence of special hardware support (such as landing pad instructions): by referencing code through an index into a CPT, and ensuring that only valid code entrypoints are stored inside the table, it is then guaranteed that any indirect control-flow transfer ends up on a valid entrypoint as long as an attacker is still confined to the sandbox.

- **TPT** (Trusted Pointer Table): the general table for trusted objects. Since those objects can include `Code`, the long-term direction is to absorb CPT into TPT.

> All four tables (JDT, EPT, TPT, CPT) are built on the same `SegmentedTable` infrastructure (via `ExternalEntityTable`, with EPT using the compactible variant `CompactibleExternalEntityTable`). They share the common shape *handle → shifted index → table load*, but they do **not** all share the same tag-validation logic: the type-tag check lives in [`src/sandbox/tagged-payload.h`](https://source.chromium.org/chromium/chromium/src/+/main:v8/src/sandbox/tagged-payload.h) (`TaggedPayload`) and is used only by EPT and TPT. The JDT has no type tag at all; its entry is `entrypoint_` + `encoded_word_`, and its safety comes from the entry always holding a valid entrypoint rather than from a tag check.

### JS Dispatch Table

#### JSFunction and Its Dispatch Handle

V8 represents a JavaScript function such as `function f() { ... }` or `(x) => x + 1` with a `JSFunction` object. That object has a [`dispatch_handle_`](https://source.chromium.org/chromium/_/chromium/v8/v8/+/e88e94638bf0e99430828b1b27251b7e2db15147:src/objects/js-function.h;l=505) field, which indexes the corresponding `JSDispatchTable` entry. Calls go through that table instead of storing a raw target directly in the sandbox.

`dispatch_handle_` is a 32-bit integer. In the default (desktop) configuration its lower 8 bits are always 0, and the other 24 bits are the index of the `JSDispatchTable` entry (`kJSDispatchHandleShift = 8`). The shift is configuration-dependent: under `V8_LOWER_LIMITS_MODE` it is 12 (smaller table), and on 32-bit targets it is 0.

```text
+---------------------------------+------------+
| JSDispatchTable index (24 bits) | 0 (8 bits) |
+---------------------------------+------------+
```

Since the index has only 24 bits, the table can hold at most `2^24 = 16M` JDT entries. Each entry is 16 bytes, so the default desktop reservation is 256MB (`kJSDispatchTableReservationSize`). Each entry contains:

```
Offset 0  ┌─────────────────────────────────────────────────┐
   |      │   entrypoint_   (atomic<Address>)               │  ← Word 0：raw machine code pointer
Offset 8  ├─────────────────────────────────────────────────┤
   |      │   encoded_word_ (atomic<Address>)               │  ← Word 1：packs 3 pieces of info
Offset 16 └─────────────────────────────────────────────────┘
```

The second word packs:

```
bit  63               17 16                15            0
  +-------------------+----+-------------------------------+
  |  HeapObject ptr   |mark|     parameter_count           |
  |    (47 bits)      |    |       (16 bits)               |
  +-------------------+----+-------------------------------+
```

After finding the entry, V8 calls the function through `entrypoint_`. For a freed entry, the high 16 bits of `entrypoint_` are set to 1 (`kFreeEntryTag = 0xffff000000000000`, ORed with the next free-list index), so dereferencing a freed entry lands on a non-canonical address and faults. In the normal attack model, this means an attacker can at most redirect one JS function to another JS function. Since direct calls to JS functions are already allowed, that does not create a new native-code primitive by itself.

#### Pitfalls

The JDT blocks the direct "sandbox value becomes code pointer" path, but historical bugs show that the surrounding call protocol still matters. Before jumping to `entrypoint_`, the caller places arguments on the stack. That logic is complicated because different JIT tiers and call stubs use different conventions. The caller does not pass the parameter count as a separate trusted value; the callee may recover it from sandbox-resident metadata such as the SFI. If an attacker can swap the SFI, the callee can believe the function has more parameters than were actually pushed and then read past the end of the argument area.

The bug is not "JDT accepted a bad entrypoint." The bug is that attacker-controlled sandbox data influenced the stack offset used by later code. Commit [crrev.com/c/5906113](https://chromium-review.googlesource.com/c/v8/v8/+/5906113) hardened this class of issue by reading the JDT again and checking that the parameter count is still consistent.

### Code Pointer Table

> TODO 

## How Does the Sandbox Validate Writes?

For references from sandbox objects to out-of-sandbox objects, V8 uses two more tables. The split mostly follows where the target object comes from:

- **EPT** (External Pointer Table): objects allocated by other components or by C++ code outside the sandbox.
- **TPT** (Trusted Pointer Table): trusted objects allocated and managed by V8 itself.

### External Pointer Table

Like the JDT, sandbox memory does not store the raw external pointer. It stores a 32-bit EPT handle, and V8 uses that handle to index the EPT. Unlike the JDT, the index shift is not fixed at 8; it depends on the platform (`kExternalPointerIndexShift`):

| Platform | shift | low zero bits | index width | reservation | max entries |
|----------|-------|---------------|-------------|-------------|-------------|
| Desktop (default) | 6 | 6 | 26 bits | 512MB | 64M |
| Android | 7 | 7 | 25 bits | 256MB | 32M |
| iOS | 8 | 8 | 24 bits | 128MB | 16M |

So on the default desktop build the low 6 bits of the handle are always 0 and the index is 26 bits, different from the JDT's 8-bit shift. Each EPT entry is 8 bytes, which is half of a JDT entry.

```text
bit 63                      56             49  48                               0
+---------------------------+--------------+---+--------------------------------+
| pointer high 8 bits       |   tag 7 bits |mrk| pointer low 48 bits            |
| (for hardware features)   |              |   |                                |
| (8 bits)                  | (7 bits)     |   | (48 bits)                      |
+---------------------------+--------------+---+--------------------------------+
```

This matches the constants in [`v8-internal.h`](https://source.chromium.org/chromium/chromium/src/+/main:v8/include/v8-internal.h): `kExternalPointerMarkBit = 1 << 48`, `kExternalPointerTagShift = 49`, `kExternalPointerTagMask = 0x00fe000000000000` (bits 49 to 55, i.e. 7 bits), and `kExternalPointerPayloadMask = 0xff00ffffffffffff` (the high 8 bits plus the low 48 bits).

The `mrk` bit is used by GC. When V8 dereferences an EPT handle, the access site provides an expected tag, or tag *range*, through the template mechanism. V8 extracts the actual tag from the entry and checks it against that range. This is a **range containment check** (`tag_range.Contains(actual_tag)`), not a single-tag XOR comparison, which lets one field accept a sub-range of related tags. On a mismatch the behavior depends on the access path:

- for pointers that may legitimately be null, the load returns `kNullAddress` (the inlined fast path in `v8-internal.h` also returns 0);
- for pointers that must not be null, the check is an `SBXCHECK`, so a mismatch aborts the process.

Either way the tag mismatch never yields an attacker-chosen out-of-sandbox pointer.

```c++
// hardcoded expected tag range, via template
template <ExternalPointerTagRange tag_range>
Address ReadExternalPointerField(Address field_address, IsolateForSandbox isolate) {
  // ① read handle from sandbox (4 bytes)
  ExternalPointerHandle handle = *reinterpret_cast<ExternalPointerHandle*>(field_address);

  // ② handle → index  (the low kExternalPointerIndexShift bits are always 0)
  uint32_t index = handle >> kExternalPointerIndexShift;   // >> 6 on desktop

  // ③ read entry
  Address entry = isolate.external_pointer_table().at(index).load();

  // ④ extract tag, range-check it, then extract the pointer payload
  ExternalPointerTag tag =
      (entry & kExternalPointerTagMask) >> kExternalPointerTagShift;
  if (V8_LIKELY(tag_range.Contains(tag))) {
    return entry & kExternalPointerPayloadMask;
  } else {
    return kNullAddress;   // disallow-null path uses SBXCHECK and aborts instead
  }
}
```

### Trusted Pointer Table

TPT is almost the same as EPT; the main difference is that the tag field is wider, up to 15 bits instead of 7 (`kTrustedPointerTableTagMask = 0xfffe000000000000`, `kTrustedPointerTableTagShift = 49`, mark bit at bit 48, payload in bits 0 to 47). The comment in [`indirect-pointer-tag.h`](https://source.chromium.org/chromium/chromium/src/+/main:v8/src/sandbox/indirect-pointer-tag.h) notes the tag is "currently in practice limited to maximum 15 bits since it needs to fit together with a marking bit into the unused parts of a pointer," and that today only ~8 bits are actually used.

```text
+----------------------+--------+--------------------+
| tag (15 bits)        | mark   | pointer (48 bits)  |
| bits 63..49          | bit 48 | bits 0..47         |
+----------------------+--------+--------------------+
```

The TPT also has a publish/unpublish mechanism for initialization. V8 often allocates groups of objects that refer to each other, and exposing a half-initialized object to sandbox code can corrupt internal state. To avoid that, TPT reserves a special **tag value**, `kUnpublishedIndirectPointerTag = 0xfc` (not a dedicated bit), for entries that are "not yet exposed to the sandbox." An entry can be created unpublished and `Publish()`-ed only after validation succeeds. Conversely, a group of related entries can be `Unpublish()`-ed together, through `TrustedPointerPublishingScope`, if initialization fails. Because the unpublished tag is outside the normal tag set, ordinary tag-checked loads of unpublished entries fail.

## Object Placement

With the table mechanics in place, the next useful question is where different object kinds live: which fields stay in sandbox memory, which ones go through JDT, EPT, or TPT, and which code is allowed to consume them.

> TODO
