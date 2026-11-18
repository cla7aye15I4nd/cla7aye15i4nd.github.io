---
date: 2026-11-18
tags: [compression, verification, security, lean]
title: "Zero Bits to Spare: A Pointer Chase Inside zlib"
description: "In deflate.c, a nearly forty-line comment argues why a write cursor can never overtake a read cursor inside the same buffer. The comment's proof is wrong—and the real proof comes down to zero bits of slack."
---

# Zero Bits to Spare: A Pointer Chase Inside zlib

At [`zlib/trees.c:945`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L941-L946), inside the inner loop of `compress_block`, sits a single assertion:

```c
/* Check for no overlay of pending_buf on needed symbols */
#ifdef LIT_MEM
    Assert(s->pending < 2 * (s->lit_bufsize + sx), "pendingBuf overflow");
#else
    Assert(s->pending < s->lit_bufsize + sx, "pendingBuf overflow");
#endif
```

In every release build of `zlib` (`#ifndef ZLIB_DEBUG`), `Assert` preprocesses to nothing. Neither `compress_block`, nor `send_bits`, nor `put_byte` checks whether `s->pending` has room before writing to `s->pending_buf`.

When we set out to build a machine-checked Lean 4 safety proof of upstream `zlib 1.4` ([zlib × Lean](/blog/zlib-lean.html); repository [`cla7aye15I4nd/zlib-f`](https://github.com/cla7aye15I4nd/zlib-f)), most of the library reduced to familiar systems invariants: ring-buffer wraparound in `inflate_fast`, hash-chain bounds over uninitialized memory in `longest_match`, and state-machine discipline across streaming calls. Line 945 of `trees.c` was different. Proving that this stripped assertion never fires turned into the single hardest lemma of the entire `deflate` verification—and along the way, it exposed a textbook fallacy in `deflate.c`'s own forty-line safety proof.

Even better: the terrifying pointer race in `trees.c` turned out to close with **zero bits of proof slack** at `memLevel = 1` (raising a sharp follow-up question of whether a zero-bit collision can actually be constructed in real C), while the same verification effort uncovered **eight real bugs** in parts of `zlib` that looked completely routine.

## Two Cursors in One Buffer

To keep its memory footprint small, `deflate` does not allocate separate buffers for recorded LZ77 symbols and emitted [DEFLATE](https://datatracker.ietf.org/doc/html/rfc1951) bitstream output. Instead, `deflateInit2_` ([`deflate.c:463–520`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L463-L520)) allocates one `4B`-byte block called `pending_buf`, where $B = \mathrm{lit}\_\mathrm{bufsize} = 2^{\mathrm{memLevel} + 6}$ ranges from $128$ bytes (`memLevel = 1`) to $32{,}768$ bytes (`memLevel = 9`, default $16{,}384$ at `memLevel = 8`), and points `sym_buf` one quarter of the way in:

```c
s->lit_bufsize = 1 << (memLevel + 6); /* 16K elements by default */
...
s->pending_buf = (uchf *) ZALLOC(strm, s->lit_bufsize, LIT_BUFS); /* 4 * B bytes */
s->pending_buf_size = (ulg)s->lit_bufsize * 4;
...
s->sym_buf = s->pending_buf + s->lit_bufsize;
s->sym_end = (s->lit_bufsize - 1) * 3;
```

While `deflate_fast` or `deflate_slow` scans input, `_tr_tally` ([`trees.c:1095–1119`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1095-L1119)) appends up to $n \le B - 1$ symbols into `sym_buf` starting at byte offset $B$. Each symbol occupies **3 bytes (24 bits)**: two bytes of `dist` ($0$ for a literal, $1 \dots 32{,}506$ for a match) and one byte of `lc` (the literal byte, or `match_length - 3`).

When the block closes, `_tr_flush_block` ([`trees.c:997–1089`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L997-L1089)) builds the Huffman trees and calls `compress_block`. At block-flush entry, the pending byte buffer has just been drained (`pending = 0`) and at most `bi_valid <= 7` leftover bits sit in the 16-bit holding register `bi_buf`. Now two cursors start moving left-to-right across the same `4B`-byte array:

- **The Runner (`B + 3k`)**: starts at byte $B$ ($8B$ bits). On iteration $k$, `compress_block` reads the 3-byte symbol at `[B + 3k, B + 3k + 3)`, advancing the boundary of unread data by **+24 bits**.
- **The Chaser (`8 * pending + bi_valid`)**: starts near bit $0$, immediately jumps forward by the block header, and then advances by `cost(sym_k)` bits as `send_bits` flushes 16-bit words into `pending_buf[pending++]`.

Try scrubbing `k` or pressing **Play** below, especially on tab **02 · Dynamic Surge** and **03 · Unconstrained 48b**:

<div class="zc-widget" data-zc="race" data-lang="en"></div>

Because `send_bits` ([`trees.c:274–285`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L274-L285)) flushes two bytes to `pending_buf` whenever `bi_valid + length > 16`, keeping every write strictly below the next unread symbol at `B + 3k` is guaranteed if the stream maintains **prefix room**:

$$
8 \cdot \mathrm{pending} + \mathrm{bi}\_\mathrm{valid} + 15 \le 8(B + 3k) \qquad \forall k \in \{0, \dots, n\}.
$$

## Wait—Isn't an Overlay Collision Just Corrupt Output?

Before trying to break or prove this overlay invariant, a security researcher should ask a basic triage question: *if `s->pending` did overtake `s->lit_bufsize + sx`, what is the actual primitive?*

If `compress_block` merely read corrupt literals and emitted corrupt Huffman codes into `pending_buf`, an overlay collision would only break decompression round-tripping, not memory safety. Look twenty lines above the `Assert` in [`trees.c:913–939`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L913-L939):

```c
dist = s->sym_buf[sx++] & 0xff;
dist += (unsigned)(s->sym_buf[sx++] & 0xff) << 8;
lc = s->sym_buf[sx++];
if (dist == 0) {
    send_code(s, lc, ltree); /* send a literal byte */
} else {
    code = _length_code[lc];
    send_code(s, code + LITERALS + 1, ltree);
    ...
    dist--; /* dist is now the match distance - 1 */
    code = d_code(dist);
    Assert(code < D_CODES, "bad d_code");
    send_code(s, code, dtree);
```

where `d_code` in [`deflate.h:320–321`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.h#L320-L321) is an unchecked macro indexing a **512-byte** static lookup table `const uch _dist_code[512]`:

```c
#define d_code(dist) \
   ((dist) < 256 ? _dist_code[dist] : _dist_code[256+((dist)>>7)])
```

When `_tr_tally` records a real match, `1 <= dist <= MAX_DIST <= 32506`, so `dist - 1 <= 32505 <= 32767`, and `256 + ((dist - 1) >> 7)` lands cleanly inside `256 .. 511`.

If emitted compressed bits overwrite an unread symbol in `sym_buf`, `dist` becomes an arbitrary 16-bit integer controlled by the bitstream. Any value in `32769 .. 65535` (`0x8001 .. 0xffff`) enters the `else` branch and drives `256 + ((dist - 1) >> 7)` to indices **`512 .. 767`**—reading up to **256 bytes past the end of `_dist_code`** in `.rodata`. Worse, if that out-of-bounds byte exceeds `60`, `send_code(s, code, dtree)` and `extra_dbits[code]` immediately read out of bounds on `dyn_dtree[61]` and `extra_dbits[30]`, feeding garbage `Len` values into bit-shifts in `send_bits`.

Drag the 16-bit `dist` slider below past `32,768` to trace the exact failure chain:

<div class="zc-widget" data-zc="oob" data-lang="en"></div>

In short, the overlay bound is load-bearing for **memory safety**. You cannot prove `deflate` free of undefined behavior without proving that the Chaser never catches the Runner.

## The Broken Proof in `deflate.c`

The authors of `zlib` knew this overlay looked dangerous, so they wrote a detailed 38-line proof in [`deflate.c:465–502`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L465-L502) right above the allocation of `pending_buf`. The first half analyzes **fixed** Huffman blocks:

> *The longest fixed codes are a length code of 8 bits plus 5 extra bits [...] The longest fixed distance codes are 5 bits plus 13 extra bits [...] The longest possible fixed-codes length/distance pair is then 31 bits total. [...] As each symbol is consumed, the pointer to the next `sym_buf` value to read moves forward three bytes. From that symbol, up to 31 bits are written to `pending_buf`. The closest the written `pending_buf` bits gets to the next `sym_buf` symbol to read is just before the last code is written.*

For **fixed** blocks, every word of this is right. Because *every individual symbol* costs at most $31$ bits while freeing $24$ bits, the Chaser gains at most $+7$ bits per step. Even at `memLevel = 1` ($B = 128$, $n = 127$) with 7 held entry bits and the 3-bit block header, `pending` reaches at most $494$ bytes while the last symbol starts at $128 + 3 \times 127 = 509$ bytes.

Then comes [`deflate.c:496–502`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L496-L502), extending the argument to **dynamic** Huffman blocks:

```c
/* That latter condition then assures that the above analysis also covers all
 * dynamic blocks. A dynamic-code block will only be chosen to be emitted if it
 * has fewer bits than a fixed-code block would for the same set of symbols.
 * Therefore its average symbol length is assured to be less than 31. So the
 * compressed data for a dynamic block also cannot overwrite the symbols from
 * which it is being constructed.
 */
```

Read those four sentences like a vulnerability researcher. **The deduction is completely invalid.**

An upper bound on the *average* cost across $n$ symbols says nothing about a *prefix* of $k < n$ symbols:

1. **Dynamic blocks pay a massive upfront header before $k = 0$.** Fixed blocks emit a 3-bit tag and start consuming `sym_buf` immediately. Dynamic blocks first call `send_all_trees` ([`trees.c:830–853`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L830-L853)), serializing `hlit`, `hdist`, `hclen`, up to 19 three-bit code lengths, and the bit-length-encoded `dyn_ltree` and `dyn_dtree`. In the worst case, that header is $14 + 19 \times 3 + (286 + 30) \times 7 = \mathbf{2{,}283\text{ bits}}$—emitted before a single byte of `sym_buf` is freed.
2. **Dynamic matches can cost up to 48 bits, not 31.** Dynamic Huffman codes go up to 15 bits in both trees, so one `(length, distance)` match can cost $15 + 5 + 15 + 13 = \mathbf{48\text{ bits}}$—gaining $+24$ bits on the Runner in a single step, more than $3\times$ the fixed-code catch-up rate.
3. **Expensive symbols can be front-loaded.** Suppose the first $k$ symbols of `sym_buf` are rare, max-extra-bit matches costing 42–48 bits each, and the remaining $n - k$ symbols are copies of a single literal `'A'` costing **1 bit** each. Over the full block, the dynamic encoding crushes the fixed encoding (`opt_lenb < static_lenb`), so `_tr_flush_block` happily selects the dynamic branch. Yet during the first $k$ symbols, the Chaser is sprinting toward `sym_buf` at nearly double speed—exactly the mid-block pinch shown in **02 · Dynamic Surge** above.

When we hit this comment during the Lean proof, we stopped trying to prove `deflate` safe and tried to **exploit** it instead. Set `memLevel = 1` ($B = 128$), where the entire head start is only $8 \times 128 = \mathbf{1{,}024\text{ bits}}$—less than half of the 2,283-bit theoretical header bound! Front-load rare matches at `sx = 0`, pack repeated literals at the end so `opt_lenb < static_lenb`, and watch `pending` smash through `sym_buf`.

Except every constructed input missed. Finding out *why* required proving three progressively tighter theorems.

## Three Walls Between `deflate` and an Exploit

To handle arbitrary adversarial symbol ordering, we cannot rely on where expensive symbols sit in `sym_buf`. Define the **excess** of a block as the total bits by which individual symbols exceed the 24-bit slot they free:

$$
\mathrm{excess} = \sum_{i=0}^{n-1} \max\big(0,\, \mathrm{cost}(s_i) - 24\big).
$$

Symbols costing $\le 24$ bits only push the Runner further ahead. Even if an adversary places *every* symbol with $\mathrm{cost} > 24$ at the very beginning of the block right after the header, any prefix of $k$ symbols costs at most $24k + \mathrm{excess}$ bits. Accounting for `bi_valid <= 7` at entry, the 3-bit block header, and the 15-bit `send_bits` slack ($7 + 3 + 15 = 25$ bits), prefix room holds for *every* $k$ whenever the block satisfies the order-free budget:

$$
\mathrm{header} + \mathrm{excess} + 25 \le 8B.
$$

Why can't an attacker blow past $8B$? Because **in a Huffman tree, long codewords cost frequency mass**. You cannot assign a symbol a 15-bit code unless enough *other* symbols exist in the same block to outvote it at 15 consecutive binary merges.

### Wall 1: `memLevel 5..9` ($B \ge 2048$) and the `6.257` Slope

Walk up the path from a leaf of frequency $f \ge 1$ at depth $l$ to the root of a Huffman tree. Because Huffman's greedy merge always pairs the two lightest available nodes, each sibling subtree along the path forces total tree weight $W$ to grow like the Fibonacci sequence: roughly $W \gtrsim f \cdot F_{l+1}$. A handful of rare matches can reach depth 15 (costing up to 48 bits with extra bits), and `gen_bitlen` ([`trees.c:583–593`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L583-L593)) may clamp trees deeper than 15 levels and lengthen a few shallower codes to restore Kraft's equality $\sum 2^{-l_i} = 1$. Even after paying for worst-case length clamping across all 286 literal/length symbols and 30 distance symbols ([`trees.c.heap.gbfibpush.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.heap.gbfibpush.lean)), our Lean proof establishes:

$$
\mathrm{excess} \le 6.257 \cdot (n + 3),
$$

where the $+3$ accounts for `END_BLOCK` and up to two dummy leaves added when a tree has fewer than two active codes. Since $n \le B - 1$, each unit of $B$ supplies **8 bits** of head start while consuming at most **6.257 bits** of excess. Combined with the 2,283-bit header bound, the budget holds for every $B \ge 1{,}332$, covering `memLevel` 5 through 9: at $B = 2{,}048$ ($8B = 16{,}384$), $2{,}283 + \lceil 6.257 \times 2{,}050 \rceil + 25 = 15{,}135 \le 16{,}384$.

Now try `memLevel = 4` ($B = 1{,}024$, $8B = 8{,}192$):

$$
2{,}283 + 6.257 \times 1{,}026 + 25 = 8{,}728 > 8{,}192.
$$

The general bound **overflows by 536 bits**.

### Wall 2: `memLevel 3..4` ($B = 512, 1024$) and $F_{17} = 1{,}597$

Why was $6.257$ too loose at $B = 1{,}024$? Because it budgeted for `gen_bitlen`'s 15-bit clamping distortion.

Look at the total weight $W$ of either tree when $B \le 1{,}024$: there are at most $B - 1 \le 1{,}023$ recorded symbols, plus `END_BLOCK`, plus at most two forced leaves, so $W \le B + 2 \le 1{,}026$. How light can a Huffman tree be if it has *any* node deeper than 15? Its parent sits at depth 15 or deeper, forcing total tree weight to be at least:

$$
F_{16} + F_{15} = F_{17} = \mathbf{1{,}597}.
$$

Because $1{,}026 < 1{,}597$, **at `memLevel <= 4`, `gen_bitlen` never clamps a single code in either data tree**: `overflow` is identically zero! Every code length $l$ is the exact depth of an unmodified Huffman tree and satisfies the sharp identity $f \cdot F_{l+1} + F_l \le W$. Summing the exact per-symbol maxima over `zlib`'s extra-bit tables cuts `excess` to $3{,}678$ bits at $B = 1{,}024$ ($5{,}986 \le 8{,}192$) and $1{,}777$ bits at $B = 512$:

$$
2{,}283 + 1{,}777 + 25 = 4{,}085 \le 4{,}096.
$$

At `memLevel = 3`, the worst-case header plus worst-case unclamped excess clears the $4{,}096$-bit wall with **11 bits**—less than two bytes—to spare.

Explore the minimal Fibonacci spine and the $1{,}597$ threshold across `memLevel` 1–9 below:

<div class="zc-widget" data-zc="fib" data-lang="en"></div>

### Wall 3: `memLevel 1..2` ($B = 128, 256$) and Zero Bits of Proof Slack

At `memLevel = 2` ($B = 256$, $8B = 2{,}048$) and `memLevel = 1` ($B = 128$, $8B = 1{,}024$), even zero excess cannot save the 2,283-bit header bound: $2{,}283 > 2{,}048 > 1{,}024$. Why doesn't the tree header *alone* smash straight into `sym_buf` before `compress_block` reads symbol 0?

Two constraints lock together, and dropping either one breaks the bound:

1. **Tiny blocks force shallow trees, starving the header alphabet.** From $f \cdot F_{l+1} + F_l \le W$, any used leaf of length $l$ requires $F_{l+2} \le B + 2$. At $B = 256$ ($W \le 258 < 377 = F_{14}$), no data code exceeds **11 bits**, so bit-length symbols `12..15` never occur when `scan_tree` encodes the trees. At $B = 128$ ($W \le 130 < 144 = F_{12}$), no data code exceeds **9 bits**, deleting symbols `10..15` from `bl_tree` altogether! Bounding `bl_tree` against an explicit complete reference prefix code on the remaining 13 bit-length symbols ([`deflate.c.engine.overlay-header-ref.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean)) expresses the header cost directly in terms of which tree entries are nonzero.
2. **`opt_lenb < static_lenb` comes back from the dead.** Remember `deflate.c`'s fallacious comment? Saying "dynamic beats fixed, therefore average symbol length $< 31$" could not bound prefixes directly—but `_tr_flush_block` *does* check `if (static_lenb <= opt_lenb) opt_lenb = static_lenb;` ([`trees.c:1035–1037`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1035-L1037)) before taking the dynamic branch! That check enforces a global inequality between the rounded byte costs:

$$
\left\lfloor \frac{\mathrm{header} + \mathrm{opt}\_\mathrm{payload} + 10}{8} \right\rfloor + 1 \le \left\lfloor \frac{\mathrm{static}\_\mathrm{payload} + 10}{8} \right\rfloor.
$$

Here is the catch-22 that traps the would-be exploit author: to bloat `header`, you must light up dozens of distinct symbols across `dyn_ltree` and `dyn_dtree` so `scan_tree` ([`trees.c:722–766`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L722-L766)) cannot compress long runs of zeros with repeat codes `17` and `18`. But lighting up dozens of distinct, low-frequency symbols makes `opt_payload` *expensive* relative to `static_payload`—and the moment `opt_lenb` catches up to `static_lenb`, `_tr_flush_block` refuses to emit the dynamic block and switches to fixed trees instead!

In Lean 4, one linear-combination certificate combines the Fibonacci caps, Kraft's equality, the reference header bounds, and the `opt_lenb < static_lenb` selection inequality:

- At $B = 256$ ($8B = 2{,}048$): $\mathrm{header} + \mathrm{excess} \le 2{,}023 \implies 2{,}023 + 25 = \mathbf{2{,}048 \le 2{,}048}$.
- At $B = 128$ ($8B = 1{,}024$): $\mathrm{header} + \mathrm{excess} \le 999 \implies 999 + 25 = \mathbf{1{,}024 \le 1{,}024}$.

Both proved certificates meet the $8B$ wall with **zero bits of proof slack**:

<div class="zc-widget" data-zc="regimes" data-lang="en"></div>

Together the three regimes cover all nine `memLevel` values: in every block, the write cursor stays behind the next unread symbol.

## Can Zero-Bit Slack Actually Be Constructed?

Seeing $999 + 25 = 1{,}024 \le 1{,}024$ begs an immediate question: **is there really an input at `memLevel = 1` where the write cursor grazes the very next unread byte with zero bits left, or is "zero slack" an artifact of the proof?**

The short answer: **we could not construct one, and the closest we got was still more than 300 bits away.** The $0$-bit margin belongs to the *proved upper bound*: the bound meets the budget exactly, but it is an upper bound, looser than the true worst case. Note that what follows is a search result, not a proof: not finding an input does not show that none exists.

Let's actually try to maximize $\mathrm{header} + \mathrm{excess}$ against the real `zlib/trees.c`. Unpacking `opt_lenb < static_lenb` gives:

$$
\mathrm{header} \le P_{\mathrm{static}} - P_{\mathrm{opt}} + 6,
$$

where $P_{\mathrm{static}}$ and $P_{\mathrm{opt}}$ are the static and dynamic payload bit totals. Notice a subtle algebraic gift to the attacker: match extra bits (`extra_lbits` and `extra_dbits`, up to $5 + 13 = 18$ bits) appear identically in *both* $P_{\mathrm{static}}$ and $P_{\mathrm{opt}}$ ([`trees.c:574–575`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L574-L575)), so they cancel completely in $P_{\mathrm{static}} - P_{\mathrm{opt}}$! To subsidize the largest possible header on $n \le 127$ symbols, the optimal "banker" symbol is not a 9-bit static literal ($9 - 1 = +8$ bits of credit per copy), but a repeated long match with length code `284` (8-bit static code) and distance code `29` (5-bit static code): when dominant, its Huffman codes shrink to $1 + 1 = 2$ bits, banking **$13 - 2 = +11$ bits of header credit per copy**.

Yet the moment you replace copies of that banker with distinct singleton symbols—either to break up zero-runs in `scan_tree` (inflating `header`) or to push rare matches down to depth 8–9 (inflating `excess`, which at $B = 128$ tops out at $9 + 5 + 9 + 13 = 36$ bits, i.e., $+12$ excess bits per match)—two things happen at once: you lose $+11$-credit banker slots, *and* the banker's own dynamic code lengths jump from $1+1 = 2$ bits to $3$ or $4$ bits, wiping out over a hundred bits of credit in one step.

We linked upstream `trees.c` directly into a simulated-annealing search harness: each symbol sequence is recorded with `_tr_tally` and then goes through the real `build_tree`, `send_all_trees` and `compress_block` output path. At `memLevel = 1` ($B = 128$, worst-case `bi_valid = 7` at entry, all high-excess matches placed first), we searched millions of candidate blocks that pass `opt_lenb < static_lenb`:

- **`header + excess` topped out around `686` bits** (`header = 644`, `excess = 42`, `opt_lenb = 327 < 328 = static_lenb`), putting `header + excess + 25` at **`711 / 1,024` bits**—still **313 bits** below the 1,024-bit budget.
- At [`trees.c:945`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L945)'s `Assert(s->pending < s->lit_bufsize + sx)`, the smallest runtime byte gap `(lit_bufsize + sx) - pending` never dropped below **`+44` bytes** (`+336` bits in the prefix-room metric, reached at $k = 8$).

The gap of about 313 bits between the worst case found (`711`) and the proved bound (`1,024`) comes from relaxations that keep the proof machine-checkable. The plainest one is in the C itself: [`trees.c:913–915`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L913-L915) **copies the 3 bytes of symbol $k$ into the locals `dist` and `lc` before calling `send_bits`**, so while symbol $k$ is being written, the next unread symbol is already at `B + 3(k + 1)`, 24 bits further than the `B + 3k` the proof uses. The rest comes from how the header is charged: the proof bounds the code-length tree against one fixed reference prefix code, while the real `bl_tree` adapts to the block's length histogram, and it does not take full advantage of `scan_tree`'s run-length coding of zeros. The proof only needs the inequality to hold, not to be tight.

## Plot Twist: The Eight Places Where `zlib` *Did* Break

There is a familiar irony in security research: you spend weeks staring at a hair-raising in-place buffer race defended by a broken comment, prove that Fibonacci numbers and block-selection arithmetic keep it safe—and then find real memory-safety bugs in code that nobody thought twice about.

Because our Lean 4 translation turns every reachable C undefined behavior into an explicit fault `Fault.ub` (and forbids `sorry`, `axiom`, `native_decide`, and `bv_decide` on `main`), closing the safety theorems for every documented function in `zlib.h` on `zlib 1.4` (commit [`99623ef7`](https://github.com/madler/zlib/tree/99623ef7097352da7993ba614161fd6a311e046e)) forced every edge case to be confronted. Across the library, that process uncovered **eight real bugs** in upstream `zlib` ([patches](https://github.com/cla7aye15I4nd/zlib-f/tree/main/patches))—six memory errors or undefined behaviors reproduced under AddressSanitizer / UndefinedBehaviorSanitizer, and two broken size-bound promises in `deflateBound`.

### 1. `deflateBound` Breaks Its Own Promise Under `Z_FIXED` ([`deflate.c:936`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L932-L940), [PR #1394](https://github.com/madler/zlib/pull/1394))

The funniest bug connects straight back to `_tr_flush_block`. According to `zlib.h`, if you allocate `deflateBound(strm, sourceLen)` output bytes after `deflateInit2`, a single call to `deflate(strm, Z_FINISH)` is guaranteed to compress the entire input and return `Z_STREAM_END`.

For the default `windowBits = 15` and `memLevel = 8`, `deflateBound_z` returns a razor-tight bound (~0.03% expansion: 5 header bytes per 16,383-byte block), counting on `_tr_flush_block` to fall back to an uncompressed **stored block** whenever Huffman coding expands the data. Look back at the stored-block guard in [`trees.c:1047–1056`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1047-L1056):

```c
if (stored_len + 4 <= opt_lenb && buf != (char*)0) {
    _tr_stored_block(s, buf, stored_len, last);
```

Notice `buf != (char*)0`! `buf` is a pointer to `window + block_start`—or `NULL` if `fill_window` slid the 64 KiB window in the middle of the current block (`block_start < 0`), discarding the raw input bytes before the block finished! Under `Z_FIXED` at levels 1–3 (`deflate_fast`), `deflate` greedily takes 3-byte matches at large distances, each costing **25 bits** ($7 + 5 + 13$)—that is **8.33 bits per input byte**. Once a block crosses a window slide, `buf` becomes `NULL`, the stored-block parachute vanishes, and the fixed-code block expands past the raw input size!

On $1{,}000{,}000$ bytes of concrete input with `windowBits = 15, memLevel = 8, Z_FIXED`, `deflateBound` promises **`1,000,318` bytes**. Running the real C library needs up to **`1,008,570` bytes**, so `deflate(Z_FINISH)` runs out of output space and returns `Z_OK` instead of `Z_STREAM_END` ([Patch 0007](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0007-deflatebound-fixed-conservative.patch)).

### 2. `gzread` Copies From a Stale `x.next` Pointer ([`gzread.c:271`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L271-L276), [PR #1363](https://github.com/madler/zlib/pull/1363))

In `gzread.c`, when reading non-gzip data in transparent `COPY` mode, `gz_fetch` refills `state->out` via `gz_load`:

```c
case COPY:      /* -> COPY */
    if (gz_load(state, state->out, state->size << 1, &(state->x.have)) == -1)
        return -1;
    state->x.next = state->out;
    return 0;
```

`gz_load` loops over `read()`. If the first `read()` call delivers some bytes (setting `state->x.have > 0`) and the next `read()` call fails with `-1`, `gz_load` leaves the partial byte count in `state->x.have` and returns `-1`. `gz_fetch` then returns `-1` **before** updating `state->x.next = state->out`! Back in `gz_read`, the error check happens only when `state->x.have == 0`; seeing `x.have > 0`, `gz_read` happily `memcpy`s `x.have` bytes from the **stale** `state->x.next` pointer—reading past the end of the output buffer on the heap (confirmed under AddressSanitizer at [`gzread.c:369`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L369); [Patch 0003](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0003-gzread-partial-copy-read-error.patch)). Hoisting `state->x.next = state->out;` two lines up fixes it.

### 3. Unrelated-Pointer Comparison in `inflateCopy` & 64-Bit Offset Overflows

In `inflateCopy` ([`inflate.c:1383–1387`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/inflate.c#L1383-L1387), [PR #1369](https://github.com/madler/zlib/pull/1369), [Patch 0001](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0001-inflate-copy-pointer-equality.patch)), `zlib` checked whether `state->lencode` pointed inside the heap-allocated `state->codes` table using relational operators:

```diff
-    if (state->lencode >= state->codes &&
-        state->lencode <= state->codes + ENOUGH - 1) {
-        copy->lencode = copy->codes + (state->lencode - state->codes);
+    if (state->lencode == state->codes) {
+        copy->lencode = copy->codes;
```

Right after decoding a fixed Huffman block, `state->lencode` points to `lenfix` in static `.rodata`, while `state->codes` lives on the heap. Comparing pointers into distinct objects with `>=` and `<=` is immediate undefined behavior in C (flagged by ASan's `pointer-compare` check), and `state->lencode` can only ever start at `state->codes` anyway.

The remaining bugs clustered around signed 64-bit file offsets (`z_off64_t`) in the `gz*` layer and 32-bit header arithmetic:

| Issue | Location & What goes wrong | Fix & Upstream |
| --- | --- | --- |
| `inflateCopy` pointer comparison | [`inflate.c:1383`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/inflate.c#L1383): `>=` / `<=` between `.rodata` `lenfix` and heap `state->codes` (UB) | [Patch 0001](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0001-inflate-copy-pointer-equality.patch) · [PR #1369](https://github.com/madler/zlib/pull/1369) |
| `gzseek` after initial `gzungetc` | [`gzlib.c:395, 403`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzlib.c#L395-L403): `gzopen` $\to$ `gzungetc` sets `x.pos = -1`; `GZ_OFF_MAX - pos` and `pos - state->x.pos` overflow signed 64-bit | [Patch 0002](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0002-gzseek-negative-position-overflow.patch) · [PR #1361](https://github.com/madler/zlib/pull/1361) |
| `gzread` stale `x.next` on read error | [`gzread.c:271, 369`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L271-L276): partial `read()` followed by error leaves `x.have > 0` with stale `x.next` $\to$ heap OOB read | [Patch 0003](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0003-gzread-partial-copy-read-error.patch) · [PR #1363](https://github.com/madler/zlib/pull/1363) |
| `gzread` / `gzgetc` `x.pos` overflow | [`gzread.c`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c): unbounded addition to signed `x.pos` after seeking near $2^{63}$ on `/dev/zero` | [Patch 0004](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0004-gzread-position-overflow.patch) · [PR #1405](https://github.com/madler/zlib/pull/1405) |
| `gzwrite` / `gzputc` `x.pos` overflow | [`gzwrite.c:230, 352`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzwrite.c#L230): unbounded addition to signed `x.pos` after seeking near $2^{63}$ on `/dev/null` | [Patch 0005](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0005-gzwrite-position-overflow.patch) · [PR #1406](https://github.com/madler/zlib/pull/1406) |
| `gzoffset64` negative `lseek` | [`gzlib.c:486–489`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzlib.c#L486-L489): checks `offset == -1` instead of `< 0`; negative offset on `/proc/<pid>/mem` overflows `offset - avail_in` | [Patch 0006](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0006-gzoffset-negative-lseek.patch) · [PR #1404](https://github.com/madler/zlib/pull/1404) |
| `deflateBound` under `Z_FIXED` | [`deflate.c:936`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L936): window slide disables stored-block fallback; 1 MB input needs `1,008,570` B vs promised `1,000,318` B | [Patch 0007](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0007-deflatebound-fixed-conservative.patch) · [PR #1394](https://github.com/madler/zlib/pull/1394) |
| `deflateBound` gzip `extra_len` wrap | [`deflate.c:901`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L901): `extra_len` of $2^{32}-2$ or $2^{32}-1$ wraps `2 + extra_len` in 32 bits (~64 KiB too small) | [PR #1360](https://github.com/madler/zlib/pull/1360) |

## Closing Notes & References

If there is one lesson from verifying thirty-year-old C, it is that human intuition is calibrated for the wrong places. Everyone who reads `trees.c` notices the overlaid symbol buffer, feels uneasy, writes a plausible-sounding comment about averages, and moves on. Fuzzers hammer `inflate` and `deflate` for billions of executions without ever setting `memLevel = 1` on a crafted match-banker histogram, or triggering `EIO` mid-refill in `COPY` mode, or calling `gzungetc` at byte 0 before `gzseek`.

A theorem prover has no intuition and no sense of boredom. When a comment in `deflate.c` claims an average bound prevents a mid-block collision, the kernel refuses the step until you supply Fibonacci trees, $F_{17} = 1{,}597$, and a zero-proof-slack certificate at $B = 128$. And when a three-line error path in `gzread.c` returns one line before assigning `state->x.next`, the invariant breaks on the spot.

- **Verified artifact & documentation**: [`cla7aye15I4nd/zlib-f`](https://github.com/cla7aye15I4nd/zlib-f) · [Project Overview](https://www.dataisland.org/zlib-f/en/overview.html) · [Trees & Overlay Proof Notes](https://www.dataisland.org/zlib-f/en/proof/trees.html) · [All Findings](https://www.dataisland.org/zlib-f/en/findings.html)
- **Key Lean 4 modules**: [`trees.c.universal-dynamic.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-dynamic.lean) (`memLevel >= 5`) · [`trees.c.universal-overlay-mid.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-overlay-mid.lean) (`memLevel 3..4`) · [`deflate.c.engine.overlay-header-ref.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean) & [`DeflateOverlayCertificate128W.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Math/DeflateOverlayCertificate128W.lean) (`memLevel 1..2`)
- **Upstream C & specification**: [`madler/zlib` @ `99623ef7`](https://github.com/madler/zlib/tree/99623ef7097352da7993ba614161fd6a311e046e) ([`trees.c`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c), [`deflate.c`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c)) · [RFC 1951 (DEFLATE)](https://datatracker.ietf.org/doc/html/rfc1951)

<script src="/static/zlib-chase.js?v=20261118-zlib-chase-v2"></script>
