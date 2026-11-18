---
date: 2026-11-18
tags: [compression, verification, security, lean]
title: "Right Code, Wrong Comment: The Pointer Chase Inside zlib"
description: "A 38-line comment in deflate.c argues that zlib's shared buffer can never overwrite unread symbols. That comment is wrong—yet when we tried to build an exploit, three hidden Huffman invariants stood in the way."
---

# Right Code, Wrong Comment: The Pointer Chase Inside zlib

At [`zlib/trees.c:945`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L941-L946), inside the inner loop of `compress_block`, sits a single assertion:

```c
/* Check for no overlay of pending_buf on needed symbols */
#ifdef LIT_MEM
    Assert(s->pending < 2 * (s->lit_bufsize + sx), "pendingBuf overflow");
#else
    Assert(s->pending < s->lit_bufsize + sx, "pendingBuf overflow");
#endif
```

In every release build of `zlib` (`#ifndef ZLIB_DEBUG`), `Assert` preprocesses to whitespace. Neither `compress_block`, nor `send_bits`, nor `put_byte` checks whether `s->pending` has room before writing to `s->pending_buf`.

When we set out to build a machine-checked Lean 4 safety proof of upstream `zlib 1.4` ([zlib × Lean](/blog/zlib-lean.html); repository [`cla7aye15I4nd/zlib-f`](https://github.com/cla7aye15I4nd/zlib-f)), most of the library came down to familiar systems invariants: ring-buffer wraparound in `inflate_fast`, hash-chain bounds over uninitialized slots in `longest_match`, and state-machine discipline across streaming calls. Line 945 of `trees.c` was different. Right above the buffer allocation in `deflate.c`, `zlib`'s authors wrote a 38-line mathematical proof that this stripped assertion can never fire—and **that proof is wrong**. Yet when we put down the theorem prover and tried to construct an exploit input that actually crashes `compress_block`, every single attempt hit an invisible wall.

This post walks through the whole investigation from the ground up:

1. **What `deflate` actually does**: why `zlib` needs two passes per block, and why two cursors end up racing through the same `pending_buf` array.
2. **Why `deflate.c`'s proof fails (and why an exploit still won't fit)**: why an *average* bit-length bound cannot prevent a mid-block collision—and why a collision would trigger an out-of-bounds `.rodata` read, not just corrupt output.
3. **How the C code connects to our Lean 4 proof**: step by step, how pointer mutations and `bi_buf` bit-shifts reduce to pure Huffman-tree inequalities—culminating in an algebraic cancellation that closes `memLevel 1..2` without brute-force search.
4. **Proof geometry vs. physical reality**: the exact byte-and-bit closest approaches we synthesized on unmodified `deflate()`, why slot-by-slot proofs hit a mathematical ceiling near `980` while physical C stops at `720`, how one could close that gap, and the eight places where `zlib 1.4` *did* break.

---

## 1. How `deflate` Actually Works (and Why Two Pointers Share One Buffer)

If you have never read `zlib`'s source code, variable names like `pending_buf`, `sym_buf`, `bi_valid`, and `_dist_code` look opaque. The underlying idea, however, is straightforward once you trace a concrete string like `"abcde_abcde_!"` through one [DEFLATE](https://datatracker.ietf.org/doc/html/rfc1951) block.

### Pass 1: Why `deflate` Cannot Emit Bits Immediately

Suppose `deflate` is scanning `"abcde_abcde_!"`. Its LZ77 matcher (`deflate_fast` or `deflate_slow`) spots that the second `"abcde"` repeats the bytes 6 positions earlier, turning the 13-byte string into **9 symbols**:

```text
'a', 'b', 'c', 'd', 'e', '_',  Match(dist = 6, len = 5),  '_', '!'
```

Why doesn't `deflate` immediately write the Huffman bitcodes for `'a'`, `'b'`, `'c'` to the output stream as soon as it sees them?

**Because it does not know the Huffman tree yet!** Optimal Huffman coding assigns short bitstrings (down to 1 bit) to frequent symbols and long bitstrings (up to 15 bits) to rare ones. Until `deflate` has scanned the *entire* block and counted how many times each byte and match length occurs, it cannot build the block's custom Huffman trees.

So `deflate` processes every block in **two passes**:

- **Pass 1 — Record & Tally (`_tr_tally`, [`trees.c:1095–1119`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1095-L1119)):** As the matcher scans input, it parks each symbol in an intermediate array `sym_buf` using a fixed **3-byte (24-bit)** encoding—two bytes for `dist` (`0` for a literal, `1..32506` for a match) and one byte for `lc` (the literal byte, or `len - 3`)—while incrementing frequency counters `Freq[]`.
- **Pass 2 — Build Trees & Emit Bits (`_tr_flush_block`, [`trees.c:997–1089`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L997-L1089)):** Once `sym_buf` fills up, `deflate` builds Huffman trees from `Freq[]`, reads back the recorded 3-byte symbols from `sym_buf` one by one, and packs their variable-length bitcodes into the output byte queue `pending_buf`.

### Buckets and Extra Bits: How a 3-Byte Symbol Can Become 48 Bits (or 1 Bit)

There is one more piece of the format we need before everything clicks: **how matches are Huffman-coded**.

A match distance `dist` can be anywhere from `1` to `32,768`. If DEFLATE built a Huffman tree with 32,768 leaves, transmitting the tree description at the start of every block would cost kilobytes—far larger than small files! Instead, [RFC 1951 §3.2.5](https://datatracker.ietf.org/doc/html/rfc1951#section-3.2.5) splits every length and distance into a **coarse bucket** (which is Huffman-coded) plus **raw binary "extra bits"** (which pinpoint the exact offset inside that bucket):

- **Literals & Lengths share one 286-symbol tree (`dyn_ltree`)**: codes `0..255` are literal bytes; `256` is `END_BLOCK`; `257..285` are **29 length buckets**, carrying `0` to `5` extra bits (for example, bucket `284` covers lengths `227..257` using 1 Huffman code + **5 extra bits**; bucket `285` is length `258` alone with **0 extra bits**).
- **Distances use a 30-symbol tree (`dyn_dtree`)**: codes `0..29` are **30 distance buckets**, carrying `0` to `13` extra bits (bucket `29` covers distances `16,385..32,768` using 1 Huffman code + **13 extra bits**). To map `dist - 1` (`0..32,767`) to its bucket `0..29` in $O(1)$ time, `zlib` uses a 512-byte lookup table `_dist_code[512]` ([`deflate.h:320–321`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.h#L320-L321)).

Because DEFLATE caps Huffman code lengths at 15 bits, one 3-byte symbol in `sym_buf` can turn into:

- **As little as 1 bit** (a very frequent literal byte), or
- **As much as $15 + 5 + 15 + 13 = 48$ bits** (a rare match landing in a 5-extra-bit length bucket and a 13-extra-bit distance bucket)—**twice** the 24 bits it occupied in `sym_buf`!

### Three Competing Block Formats—and the Shared Buffer Overlay

When Pass 1 finishes recording up to $n \le B - 1$ symbols—where $B = \mathrm{lit}\_\mathrm{bufsize} = 2^{\mathrm{memLevel}+6}$ ranges from **$128$** (`memLevel = 1`) to **$32{,}768$** (`memLevel = 9`, default $16{,}384$ at `memLevel = 8`)—`_tr_flush_block` evaluates **three legal DEFLATE encodings** for the block and picks whichever produces the fewest bytes:

1. **Stored (`00`)**: Abandon compression and copy the raw uncompressed input bytes straight out of the sliding window (`stored_len + 4` bytes).
2. **Fixed Huffman (`01`)**: Use RFC 1951's hardcoded Huffman tables (literals take 8 or 9 bits, lengths 7 or 8 bits, distances 5 bits). No tree header is needed—just a 3-bit tag—and **every symbol costs at most $8 + 5 + 5 + 13 = 31$ bits**.
3. **Dynamic Huffman (`10`)**: Build custom trees `dyn_ltree` and `dyn_dtree` from `Freq[]`. Because the decoder does not know these custom trees yet, `send_all_trees` must **serialize the tree code-lengths at the very start of the block** (compressed with a tiny 19-symbol run-length Huffman tree called `bl_tree`) *before* `compress_block` encodes symbol 0.

Now look at memory layout. Pass 2 only begins when `pending_buf` (the output queue) has been completely flushed to the caller (`pending = 0`), leaving at most `bi_valid <= 7` leftover bits from the previous block sitting in the 16-bit shift register `bi_buf`. Rather than allocating $4B$ bytes for `pending_buf` plus another $3B$ bytes for `sym_buf`, `deflateInit2_` ([`deflate.c:463–520`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L463-L520)) allocates **one `4B`-byte array**, leaves the first $B$ bytes (`8B` bits) empty as a head start, and places `sym_buf` directly at `pending_buf + B`:

```c
s->lit_bufsize = 1 << (memLevel + 6); /* B: 128 .. 32768 (16384 by default) */
...
s->pending_buf = (uchf *) ZALLOC(strm, s->lit_bufsize, LIT_BUFS); /* 4 * B bytes */
s->pending_buf_size = (ulg)s->lit_bufsize * 4;
...
s->sym_buf = s->pending_buf + s->lit_bufsize;   /* starts 1/4 of the way in */
s->sym_end = (s->lit_bufsize - 1) * 3;          /* max n = B - 1 triples */
```

Step through all four stages of a block below to watch how Pass 1 and Pass 2 share `pending_buf[0 .. 4B)`:

<div class="zc-widget" data-zc="pipeline" data-lang="en"></div>

Once `compress_block` starts Pass 2b, two cursors race left-to-right across the same array:

- **The Runner (`B + 3k`)**: starts at byte $B$ ($8B$ bits). On step $k$, reading symbol $k$ frees 3 bytes, advancing the boundary of unread symbols by **+24 bits**.
- **The Chaser (`pending` + `bi_valid`)**: starts near byte $0$ (with at most 7 leftover bits), leaps forward by the 3-bit tag + dynamic tree header *before* symbol 0 is read, and then advances by **1 to 48 bits** per symbol.

Overwriting `[B .. B + 3k)` is completely harmless—those symbols have already been read! Disaster strikes only if the Chaser ever catches `B + 3k` and overwrites a symbol that `compress_block` hasn't read yet.

---

## 2. Why Overwriting `sym_buf` Breaks Memory Safety—and Why `deflate.c`'s Proof Is Wrong

### Not Just Corrupt Output: The `_dist_code[512]` Cliff

Before trying to break or prove this invariant, ask a triage question: *if `s->pending` did overtake `B + 3k` and overwrite unread symbols, wouldn't `deflate` merely emit a corrupt compressed stream?*

Look twenty lines above the `Assert` in [`trees.c:913–939`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L913-L939):

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

Remember `_dist_code[512]` from Pass 1? Its macro in [`deflate.h:320–321`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.h#L320-L321) has no bounds check:

```c
#define d_code(dist) \
   ((dist) < 256 ? _dist_code[dist] : _dist_code[256+((dist)>>7)])
```

When `_tr_tally` records a legitimate match, `1 <= dist <= MAX_DIST <= 32506`, so `dist - 1 <= 32505 <= 32767`, and `256 + ((dist - 1) >> 7)` stays safely inside `256 .. 511`.

If compressed bits overwrite an unread symbol in `sym_buf`, the two bytes of `dist` become an arbitrary `uint16_t` up to `65535`. Any value in `32769 .. 65535` (`0x8001 .. 0xffff`) enters the `else` branch and drives `256 + ((dist - 1) >> 7)` to indices **`512 .. 767`**—an out-of-bounds read up to **256 bytes past `_dist_code`** in `.rodata`! If that adjacent `.rodata` byte exceeds `60`, `send_code(s, code, dtree)` and `extra_dbits[code]` read out of bounds again on `dyn_dtree[61]` and `extra_dbits[30]`. Drag the 16-bit `dist` slider below past `32,768` to see the exact cascade:

<div class="zc-widget" data-zc="oob" data-lang="en"></div>

So even if your goal is *pure memory safety*—proving `deflate` free of undefined behavior—you cannot dodge proving that the Chaser never catches the Runner.

### The Fallacy in `deflate.c:465–502`

`zlib`'s authors knew this overlay needed a justification, so they wrote a 38-line mathematical proof in [`deflate.c:465–502`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L465-L502). First, they analyze **Fixed** blocks:

> *The longest possible fixed-codes length/distance pair is then 31 bits total. [...] As each symbol is consumed, the pointer to the next `sym_buf` value to read moves forward three bytes. From that symbol, up to 31 bits are written to `pending_buf`. The closest the written `pending_buf` bits gets to the next `sym_buf` symbol to read is just before the last code is written.*

For **Fixed** blocks, the logic is sound: every single symbol frees 24 bits and writes at most 31 bits, so the Chaser gains at most $+7$ bits per step. Even at `memLevel = 1` ($B = 128, n = 127$), $127 \times 7 = 889$ bits of net catch-up cannot close a $1{,}024$-bit head start. *(Minor detail: the comment concludes on line 490 that 139 bits remain because it forgets `bi_valid <= 7` leftover bits from the prior block—as we will verify shortly, the true minimum is 7 bits tighter: **132 bits / 18 bytes**!)*

Then comes [`deflate.c:496–502`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L496-L502), extending the proof to **Dynamic** blocks:

```c
/* That latter condition then assures that the above analysis also covers all
 * dynamic blocks. A dynamic-code block will only be chosen to be emitted if it
 * has fewer bits than a fixed-code block would for the same set of symbols.
 * Therefore its average symbol length is assured to be less than 31. So the
 * compressed data for a dynamic block also cannot overwrite the symbols from
 * which it is being constructed.
 */
```

**This deduction is broken.** Bounding the *average* cost across all $n$ symbols says nothing about a *prefix* of $k < n$ symbols:

1. **Upfront header tax before $k = 0$.** `send_all_trees` ([`trees.c:830–853`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L830-L853)) writes `5 + 5 + 4 = 14` count bits, up to $19 \times 3 = 57$ bits for `bl_tree`, and up to $(286 + 30) \times 7 = 2{,}212$ bits of tree lengths—up to **$2{,}283$ bits** in general—before symbol 0 is even read!
2. **Up to 48 bits per match (+24 bits/step catch-up).** Dynamic codes reach 15 bits, not 8 and 5.
3. **Front-loading.** If a block puts its rare, expensive matches at the *front* of `sym_buf` ($k = 0..28$) and cheap 1-to-8-bit frequent symbols at the *back* ($k = 29..126$), the total block easily beats Fixed codes (`opt_lenb < static_lenb`), yet the Chaser surges toward `B + 3k` in the first quarter of the block!

Seeing a broken safety argument guarding an unchecked write, our immediate reaction was to switch from proving to attacking: dial down to `memLevel = 1` ($B = 128$, only $1{,}024$ bits of head start against a $2{,}283$-bit max header), front-load rare matches, pad the tail with cheap anchors so Dynamic beats Fixed, and watch `pending` smash into `sym_buf`. Yet every candidate input stalled short of collision. Play with all three trajectories below—including our closest real-`deflate()` Dynamic block (**Tab 02**), which pinches right at mid-block `k = 29` (`37 B / +294 bits`) before pulling away:

<div class="zc-widget" data-zc="race" data-lang="en"></div>

---

## 3. Bridging Imperative C Code to a Lean 4 Proof

How do you turn messy C code—pointer increments, a 16-bit shift register `bi_buf`, heap-based Huffman construction, and in-place length clamping—into a clean mathematical proof? Let's trace the exact four-step bridge used in [`cla7aye15I4nd/zlib-f`](https://github.com/cla7aye15I4nd/zlib-f).

### Step A: What "Safe" Means in the Lean Translation

In `zlib-f`, every C file (`zlib/trees.c`, `zlib/deflate.c`, ...) is translated statement-by-statement into Lean 4 over an explicit heap-and-fault monad. Every array indexing (`_dist_code[...]`, `pending_buf[...]`), pointer offset, signed arithmetic op, and bit-shift checks exact C bounds; any violation raises `Fault.ub`. Proving `deflate` safe means proving that starting from any valid initialized stream, no sequence of public API calls ever reaches `Fault.ub`.

### Step B: Turning `pending` and `bi_buf` Into One Bit Odometer

In C, `send_bits(s, val, len)` ([`trees.c:274–285`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L274-L285)) packs bits into the 16-bit register `s->bi_buf` (`s->bi_valid` tracks how many bits are held) and flushes **two bytes** (`put_short`) to `pending_buf[pending++]` strictly when `bi_valid + len > 16`.

Tracking `pending` and `bi_valid` separately through dozens of `send_bits` calls is painful because `pending` jumps in 2-byte steps. Instead, define the **total emitted bit count**:

$$
S = 8 \cdot \mathrm{pending} + \mathrm{bi}\_\mathrm{valid}.
$$

Every `send_bits(s, val, len)` call—whether it flushes two bytes or not!—increases $S$ by **literally `len`**. Because `put_short` flushes 16 bits only when $S$ crosses a multiple of 16 (`bi_valid` stays in `1..16` after any write), `pending` is completely determined by $S$:

$$
\mathrm{pending} = 2 \left\lfloor \frac{S - 1}{16} \right\rfloor \le \frac{S}{8}.
$$

At block-flush entry, `pending = 0` and `bi_valid` $= v_0 \le 7$. After the 3-bit block tag, $H$ bits of dynamic header, and the first $k$ symbols $s_0, \dots, s_{k-1}$, we have $S_k = v_0 + 3 + H + \sum_{i=0}^{k-1} \mathrm{cost}(s_i)$. Meanwhile, at the end of the block ($k = n$), `compress_block` still has to emit the $\le 15$-bit `END_BLOCK` code and byte-align within `4B` bytes (`block_room`). Unifying both prefix safety ($S_k \le 8(B + 3k)$) and end-of-block room into one condition (`DynamicRoom` in [`trees.c.universal-dynamic.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-dynamic.lean#L35-L41)) asks for:

$$
\underbrace{(v_0 + 3 + 15)}_{\le\, 25} + H + \sum_{i=0}^{k-1} \big(\mathrm{cost}(s_i) - 24\big) \le 8B \qquad \forall k \in \{0, \dots, n\}.
$$

### Step C: Erasing `sym_buf` Order (`sym_buf` $\to$ `Freq[]`)

Notice a crucial structural fact about `trees.c`: **`build_tree` and `build_bl_tree` never read `sym_buf`!** They read *only* the total frequency arrays `dyn_ltree[c].Freq` and `dyn_dtree[d].Freq` tallied during Pass 1.

If an adversary permutes the $n$ symbols inside `sym_buf`—moving every expensive match (> 24 bits) to the front and every cheap literal (< 24 bits) to the back—the Huffman trees, header size $H$, `opt_lenb`, and `static_lenb` **do not change by a single bit**. Under that worst-case permutation, the prefix sum $\sum_{i=0}^{k-1}(\mathrm{cost}(s_i) - 24)$ peaks right after the last symbol with $\mathrm{cost} > 24$, where its value is the **block excess**:

$$
E = \sum_{i=0}^{n-1} \max\big(0,\, \mathrm{cost}(s_i) - 24\big).
$$

In one stroke, the heap array `sym_buf` and the loop index $k$ disappear! Proving `compress_block` safe for *every* input order reduces to proving one order-free budget inequality on the trees produced by `build_tree`:

$$
H + E + 25 \le 8B.
$$

### Step D: Connecting C's Tree Functions to Three `memLevel` Regimes

Why can't $H + E + 25$ exceed $8B$? Because **in `build_tree`, deep codewords require exponentially large block weight**.

Trace `build_tree` ([`trees.c:627–716`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L627-L716)) on a tiny example. Suppose you want to push a leaf $x$ (with `Freq = 1`) down to depth $4$. At each step, `pqremove` pops the two lightest nodes from the min-heap and merges them:

- Depth $4 \to 3$: $x$ (weight $1$) merges with a sibling of weight $\ge 1 \implies$ parent has weight $\ge 2$.
- Depth $3 \to 2$: to avoid merging earlier, the next sibling must weigh $\ge 1 \implies$ grandparent weighs $\ge 3$.
- Depth $2 \to 1$: the next sibling must weigh $\ge 2$ (since two $1$s were available when $1+1$ merged!) $\implies$ weight $\ge 5$.
- Depth $1 \to 0$: the root's other child must weigh $\ge 3 \implies$ total tree weight $W \ge \mathbf{8 = F_6}$!

By induction on the min-heap pops in `build_tree`, our Lean proof establishes that in any unclamped Huffman tree of total weight $W$, every used leaf of frequency $f \ge 1$ at depth $l$ satisfies:

$$
f \cdot F_{l+1} + F_l \le W \qquad (\text{so in particular } F_{l+2} \le W).
$$

From here, as $B = 2^{\mathrm{memLevel}+6}$ shrinks from $32{,}768$ down to $128$, the proof connects to three distinct parts of `trees.c`:

#### Regime 1: `memLevel 5..9` ($B \ge 2{,}048$) — Bounding `gen_bitlen` Clamping

When $B \ge 2{,}048$, a skewed block can have $W > 1{,}597$ and grow a Huffman tree deeper than DEFLATE's 15-bit format cap. In C, `gen_bitlen` ([`trees.c:583–593`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L583-L593)) clamps any depth $> 15$ down to $15$. Clamping breaks the prefix-code Kraft equality ($\sum 2^{-l_i} > 1$), so `gen_bitlen` runs a repair loop that demotes shallower leaves (`bits -> bits + 1`) until $\sum 2^{-l_i} = 1$ again.

Even accounting for worst-case demotions across all 286 literal/length buckets and 30 distance buckets ([`trees.c.heap.gbfibpush.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.heap.gbfibpush.lean)), our Lean proof bounds $E \le 6.257 \cdot (n + 3)$. Because $n \le B - 1$ gives 8 bits of head start per symbol against $6.257$ bits of excess, $2{,}283 + \lceil 6.257(B+2) \rceil + 25 \le 8B$ holds for all $B \ge 1{,}332$ (`dynamic_room_large` in [`trees.c.universal-dynamic.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-dynamic.lean#L52-L67)).

At `memLevel = 4` ($B = 1{,}024, 8B = 8{,}192$), however, $2{,}283 + 6.257 \times 1{,}026 + 25 = 8{,}728 > 8{,}192$—**overflowing by 536 bits**.

#### Regime 2: `memLevel 3..4` ($B = 512, 1{,}024$) — Proving `trees.c:577` Always Returns Early

Look at line 577 of [`trees.c`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L577), right before `gen_bitlen`'s clamping repair loop:

```c
if (overflow == 0) return;
```

When $B \le 1{,}024$, a block has $n \le 1{,}023$ symbols, plus `END_BLOCK` and at most two dummy leaves, so total tree weight is $W \le B + 2 \le \mathbf{1{,}026}$. By our Fibonacci law, a tree can only contain a node at depth $\ge 16$ (`overflow > 0`) if its parent at depth $15$ forces total weight at least:

$$
F_{16} + F_{15} = F_{17} = \mathbf{1{,}597}.
$$

Since $1{,}026 < 1{,}597$, **at `memLevel <= 4`, `trees.c:577` takes the early `return` on every possible input!** With zero clamping distortion, every symbol satisfies $f \cdot F_{l+1} + F_l \le W$, cutting $E$ to $3{,}678$ bits at $B = 1{,}024$ ($5{,}986 \le 8{,}192$) and $1{,}777$ bits at $B = 512$ ($2{,}283 + 1{,}777 + 25 = \mathbf{4{,}085 \le 4{,}096}$—just **11 bits** of proof slack, [`trees.c.universal-overlay-mid.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-overlay-mid.lean)).

Test how $B + 2 < 1{,}597$ locks out depth 16 and forces the early return at `trees.c:577` below:

<div class="zc-widget" data-zc="fib" data-lang="en"></div>

#### Regime 3: `memLevel 1..2` ($B = 128, 256$) — Algebraic Cancellation via `_tr_flush_block`

At $B = 256$ ($8B = 2{,}048$) and $B = 128$ ($8B = 1{,}024$), the 2,283-bit general header bound *alone* exceeds $8B$. Why doesn't the tree header by itself smash past $B$ before symbol 0 is even read? Because **three C functions lock together**:

1. **In `build_tree` (`prepared_lengths_fib`, [`deflate.c.engine.overlay-lengths.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/deflate.c.engine.overlay-lengths.lean)):** At $B = 128$ ($W \le 130 < 144 = F_{12}$), $F_{l+2} \le 130$ forces **every code length $l \le 9$** (and $l \le 11$ at $B = 256$). Moreover, any zero-frequency dummy leaf added when a tree has $< 2$ real symbols sits in a 2-leaf tree and therefore has $l = 1$.
2. **In `scan_tree` & `build_bl_tree` ([`deflate.c.engine.overlay-header-ref.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean)):** Because lengths `10..15` never occur at $B = 128$, `bl_tree` uses at most 13 of its 19 symbols. Bounding `bl_tree` against a fixed complete reference code bounds twice the header by per-slot region charges across the $286 + 30$ tree entries.
3. **In `_tr_flush_block` ([`trees.c:1035`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1035-L1037)):** Remember `deflate.c`'s broken comment? While `opt_lenb < static_lenb` cannot bound prefixes via an average, `_tr_flush_block` *does* check `if (static_lenb <= opt_lenb)` before emitting a dynamic block! Canceling the identical extra-bit sums on both sides bounds the dynamic code lengths ($l_c, l_d$) against the fixed RFC 1951 code lengths ($l_c^{\mathrm{static}} \in \{7,8,9\}$ and $5$).

Putting those two inequalities side by side reveals the clean algebraic cancellation:

$$
2H \le H_{\mathrm{const}} + \sum_{c=0}^{285} \mathrm{charge}_L(l_c) + \sum_{d=0}^{29} \mathrm{charge}_D(l_d),
$$

$$
H + \sum_{c=0}^{285} f_c\, l_c + \sum_{d=0}^{29} f_d\, l_d + 1 \le \sum_{c=0}^{285} f_c\, l_c^{\mathrm{static}} + 5 \sum_{d=0}^{29} f_d.
$$

Adding **$a$ copies of the first** and **$b$ copies of the second** ($a = 2, b = 4$ at $B = 128$; $a = 1, b = 1$ at $B = 256$) puts $(2a + b)(H + E) + b$ on the left while **canceling the dynamic code-length sums against the static ones**! All 256 literals, `END_BLOCK`, and low-extra-bit match buckets immediately have nonpositive frequency slope; bounding the remaining high-extra-bit buckets via Kraft ($\sum 2^{15-l} \le 2^{15}$) and $f \cdot F_{l+1} + F_l \le W$ closes the entire `memLevel 1..2` proof in one ~485-line parametric module with **zero brute-force search** ([`DeflateOverlayTiny.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Math/DeflateOverlayTiny.lean)):

- At $B = 256$ ($8B = 2{,}048$): $H + E \le \mathbf{1{,}899} \implies 1{,}899 + 25 = \mathbf{1{,}924 \le 2{,}048}$ (**124 bits** of budget slack).
- At $B = 128$ ($8B = 1{,}024$): $H + E \le \mathbf{983} \implies 983 + 25 = \mathbf{1{,}008 \le 1{,}024}$ (**16 bits** of budget slack).

Compare the naive general formula, the Lean 4 theorem bound, and the actual real-C physical peak across all nine `memLevel`s:

<div class="zc-widget" data-zc="regimes" data-lang="en"></div>

---

## 4. Proof Geometry vs. Physical Reality: How Close Can `zlib` *Actually* Get?

Our formal bound at `memLevel = 1` clears `1,024` with just 16 bits to spare (`1,008 <= 1,024`), and `memLevel = 3` clears `4,096` with 11 bits to spare (`4,085 <= 4,096`). That begs two questions:

1. **In real, unmodified `zlib 1.4`, how close can a valid uncompressed input physically push `s->pending` to the next unread symbol?**
2. **Why does our proof land near `983` (`1,008` total), and what would it take to push a formal proof all the way down to the physical C limit?**

To answer the first question with certainty, we analyzed all three block types across every `memLevel = 1..9` and every symbol count $n \in [1, B-1]$, synthesized concrete uncompressed byte streams, and ran them end-to-end through unmodified `deflateInit2` + `deflate` + `inflate` with an instrumentation hook on every `put_byte`.

### 1. The Global Closest Approach in `zlib`: Fixed Blocks (`18 Bytes / 132 Bits`)

Ironically, the closest physical approach in all of `zlib` is **not** a Dynamic block—it is a **Fixed** block (`Z_FIXED`) at `memLevel = 1` ($B = 128, n = 127$)!

Under `Z_FIXED`, `_tr_flush_block` skips the `opt_lenb < static_lenb` test and emits 0 header bits (just the 3-bit block tag), allowing all 127 symbols to be worst-case **31-bit matches** (lengths `131..257` using 8 + 5 = 13 bits, at distances `16,385..32,506` using 5 + 13 = 18 bits; $E = 127 \times 7 = \mathbf{889\text{ bits}}$). For any entry remainder $v_0 \in \{0..7\}$ and step $k_{\mathrm{unread}} \in \{1..127\}$, the exact gap is closed-form:

$$
\mathrm{BitGap} = 8B - v_0 - 3 - 7\,k_{\mathrm{unread}}, \qquad \mathrm{ByteGap} = (B + 3\,k_{\mathrm{unread}}) - 2\left\lfloor \frac{v_0 + 2 + 31\,k_{\mathrm{unread}}}{16} \right\rfloor.
$$

Look back at `deflate.c:490`, which claimed *"That space is actually 139 bits, due to the three-bit fixed-code block header."* Setting $v_0 = 0$ and $k_{\mathrm{unread}} = 126$ (just before reading the final symbol at byte `506`) gives $1{,}024 - 0 - 3 - 882 = \mathbf{139\text{ bits}}$—matching the comment to the bit!

**Except $v_0$ does not have to be $0$.** Preceding that block with tiny `Z_BLOCK` flushes leaves $v_0 = \mathbf{7}$ bits in `bi_buf` at entry. We synthesized a **33,404-byte uncompressed input** (placing 1 dummy byte at window index `0` so `hash_head != NIL`, 127 unique 131-byte match templates across the 32 KiB window, 1-byte `Z_BLOCK` flushes to align `bi_valid = 7`, and the 127 concatenated templates) that hits the exact global floor in unmodified `deflate(Z_FIXED)`:

- **At the last unread symbol ($k = 126$, byte `506`):** `pending = 488`, `bi_valid = 12` $\implies$ **`18 bytes` (`132 bits`)** of true unread margin (7 bits tighter than `deflate.c:490`!).
- **At [`trees.c:945`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L945)'s `Assert` ($k = 127$, `B + sx = 509`):** `pending = 492`, `bi_valid = 11` $\implies$ **`17 bytes` (`125 bits`)**.

*(Under `Z_DEFAULT_STRATEGY` without `Z_FIXED`, packing 31-bit matches causes Dynamic trees to crush Fixed trees by $> 1{,}000$ bits; naturally-selected Fixed blocks never get closer than **`65 bytes` / `515 bits`**.)*

### 2. The Closest Dynamic Block (`Z_DEFAULT_COMPRESSION`): `37 Bytes / 294 Bits` at `k = 29`

Why can't a Dynamic block reach 18 bytes? Because `opt_lenb < static_lenb` ($H + P_{\mathrm{opt}} \le P_{\mathrm{static}} + 6$) acts as a self-throttling brake!

Notice that match extra bits (`extra_lbits`, `extra_dbits`) appear identically in both $P_{\mathrm{opt}}$ and $P_{\mathrm{static}}$ ([`trees.c:574–575`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L574-L575)), so they cancel out of $P_{\mathrm{static}} - P_{\mathrm{opt}}$. Every bit of header $H$ and every rare, deep match ($ll + dl \ge 7$) must be subsidized by high-frequency "anchor" symbols whose Dynamic codes beat Fixed codes—and repeating a match often enough to subsidize $H$ shrinks its Huffman lengths ($ll + dl \le 5 \implies \mathrm{cost} \le 5 + 18 = 23 < 24$), collapsing its own excess to **zero**!

Crucially, because `_tr_tally` records only marginal symbol frequencies, sorting a block's matches assortatively (longest length codes paired with longest distance codes) and placing all $\mathrm{cost} > 24$ symbols first **provably minimizes both bit gap and byte gap over all $M! \cdot n!$ pairings and orderings simultaneously**. Across all $n \in [1..127]$ at `memLevel = 1`, the extremum occurs at full capacity $n = 127$ using a subtle three-part construction:

- **49 `MAX_MATCH = 258` anchor matches** (bucket `285`, which has **0 extra bits** and costs 8 static bits vs. 2 dynamic bits—banking high header subsidy *without* touching buckets `281..284`, keeping all four 5-extra-bit length buckets rare and deep!),
- **38 literals across 37 spaced byte values** (strategically breaking zero-runs so `scan_tree` cannot use `REPZ_3_10` / `REPZ_11_138`), and
- **29 front-loaded max-extra-bit matches** (`dcode = 24..29`, costing 26–29 bits each).

We synthesized a **50,184-byte uncompressed buffer** whose exact LZ77 parse in unmodified `deflateInit2(&strm, Z_DEFAULT_COMPRESSION, Z_DEFLATED, 15, 1, Z_DEFAULT_STRATEGY)` produces these exact 127 symbols with entry `bi_valid = 7` (and round-trips byte-for-byte through `inflate()`):

- `opt_len = 2,211` bits (`277` B) `< static_len = 2,214` bits (`278` B — winning Dynamic selection by **1 byte**!),
- **$H = 623$ bits**, **$E = 97$ bits** $\implies$ **$H + E = \mathbf{720\text{ bits}}$**,
- **Minimum physical gap (at $k = 29$, with 98 symbols still unread at `[215..509)`):** `pending = 178`, `bi_valid = 2` vs. unread byte `215` $\implies$ **`37 bytes` (`294 bits`)**!

### 3. Why Slot-by-Slot Proofs Bottom Out at `980`—and How You Would Reach `720`

Compare the three milestones at `memLevel = 1` ($8B = 1{,}024$):

- **Physical Dynamic extremum in C:** $H + E = \mathbf{720}$ bits (`294` bits of unread margin: $1{,}024 - 10 - 720 = 294$).
- **Mathematical ceiling of *any* per-slot decoupled linear proof:** $H + E = \mathbf{979.12 \approx 980}$ bits.
- **Our small-integer cancellation proof (`2 × header + 4 × choice`):** $H + E \le \mathbf{983}$ bits (`1,008 / 1,024` with `+25`).

That middle number (`979.12`) is the punchline. Even if you use an exact continuous LP solver with arbitrary real weights, **decomposing the $286 + 30 = 316$ tree slots into independent per-entry bounds cannot prove anything tighter than `980`**—our hand-written 2-digit integer proof (`983`) is already within **4 bits** of that theoretical floor! Evaluating each relaxation on our $H + E = 720$ extremal block shows exactly where the gap between `980` and `720` lives, and what a proof would have to model to close it:

| Relaxation Layer | Bits | What It Would Take to Close in Lean |
| --- | ---: | --- |
| Per-slot tree decoupling (`316` independent entries) | `169.5` | **Joint single-tree spine coupling:** prove that multiple rare leaves in *one* tree share a single weight budget $W \le 130$ instead of each leaf independently claiming its own Fibonacci spine, and bound the ~230 empty ($f = 0$) slots jointly |
| Fixed reference code + local RLE charges | `87.7` | **Global `scan_tree` automaton & adaptive `bl_tree`:** reason across *adjacent* zero slots (`REPZ_3_10 = 17`, `REPZ_11_138 = 18`) and dynamic `bl_tree` code lengths rather than charging one fixed reference code per slot |
| Unified `END_BLOCK` margin (`+25` vs `+10`) | `15.0` | **Separate mid-block vs. block-end theorems:** `END_BLOCK` ($\le 15$ bits) is emitted *after* all $n$ symbols are read, where the ceiling is `4B = 4,096` bits rather than `8B = 1,024` bits |
| Integer weights (`983` vs LP `979.1`) & rounding | `5.8` | Scale `8` small integers vs. continuous reals (`3.9`b) + split match excess (`1.0`b) + byte rounding (`0.9`b) |

Why stop at `H + E <= 983` instead of formalizing joint multi-leaf spines and global zero-run automata to push the theorem down toward `720`? Because for **memory safety**, proving `1,008 <= 1,024` and proving `730 <= 1,024` yield the **exact same `Fault.ub`-freedom theorem**—whereas stopping right at the per-slot decoupling boundary keeps the proof 485 lines long, transparent, and completely free of brute-force search.

---

## 5. Plot Twist: The Eight Places Where `zlib` *Did* Break

There is a recurring comedy in vulnerability research: you spend weeks trying to break a terrifying in-place pointer chase defended by a wrong comment, discover it stays safe by 18 bytes in Fixed mode and 37 bytes in Dynamic mode—and then find real memory-safety bugs in routine code ten files away.

Closing the Lean 4 safety proofs for every documented function in `zlib.h` on `zlib 1.4` ([`99623ef7`](https://github.com/madler/zlib/tree/99623ef7097352da7993ba614161fd6a311e046e)) uncovered **eight real defects** in upstream `zlib` ([patches](https://github.com/cla7aye15I4nd/zlib-f/tree/main/patches))—six undefined behaviors or memory errors confirmed under AddressSanitizer / UndefinedBehaviorSanitizer, and two broken upper-bound promises in `deflateBound`.

### 1. `deflateBound` Breaks Its Promise Under `Z_FIXED` ([`deflate.c:936`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L932-L940), [PR #1394](https://github.com/madler/zlib/pull/1394))

The sharpest bug connects right back to `_tr_flush_block`. `zlib.h` promises that allocating `deflateBound(strm, sourceLen)` output bytes guarantees a single `deflate(strm, Z_FINISH)` call will finish the stream (`Z_STREAM_END`). For `windowBits = 15, memLevel = 8`, `deflateBound_z` returns a tight ~0.03% expansion bound, assuming any expanding block can fall back to an uncompressed **stored block**. Look at [`trees.c:1047–1056`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1047-L1056):

```c
if (stored_len + 4 <= opt_lenb && buf != (char*)0) {
    _tr_stored_block(s, buf, stored_len, last);
```

`buf` is `NULL` whenever `fill_window` slid the 64 KiB window mid-block (`block_start < 0`), discarding the raw input bytes! Under `Z_FIXED` at levels 1–3, `deflate_fast` emits 3-byte matches at far distances costing **25 bits** (**8.33 bits per input byte**). Once a block crosses a window slide, `buf == NULL` disables the stored-block fallback: on $1{,}000{,}000$ input bytes, `deflateBound` promises `1,000,318` bytes while real C needs up to **`1,008,570` bytes**, failing with `Z_OK`.

### 2. `gzread` Copies From a Stale `x.next` Pointer ([`gzread.c:271`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L271-L276), [PR #1363](https://github.com/madler/zlib/pull/1363))

In transparent `COPY` mode, `gz_fetch` refills `state->out` via `gz_load`:

```c
case COPY:      /* -> COPY */
    if (gz_load(state, state->out, state->size << 1, &(state->x.have)) == -1)
        return -1;
    state->x.next = state->out;
    return 0;
```

If `gz_load` reads some bytes (`state->x.have > 0`) and the next `read()` syscall fails with `-1`, `gz_fetch` returns `-1` **before** updating `state->x.next = state->out`! Outer `gz_read` sees `x.have > 0` and `memcpy`s from the **stale** `state->x.next` pointer—a heap buffer over-read outside `state->out` (caught by ASan at [`gzread.c:369`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L369)).

### 3. `inflateCopy` Pointer UB & `gz*` 64-Bit Offset Overflows

In `inflateCopy` ([`inflate.c:1383`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/inflate.c#L1383-L1387), [PR #1369](https://github.com/madler/zlib/pull/1369)), `state->lencode >= state->codes && state->lencode <= state->codes + ENOUGH - 1` compares a pointer to `.rodata` (`lenfix`) against a heap array using `>=` / `<=` (C undefined behavior, caught by ASan `pointer-compare`). Replacing the range test with `state->lencode == state->codes` fixes it. Here are all eight upstream issues:

| Issue | Location | Upstream |
| --- | --- | --- |
| `inflateCopy` compares unrelated pointers (UB) | [`inflate.c:1383`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/inflate.c#L1383) | [PR #1369](https://github.com/madler/zlib/pull/1369) |
| `gzseek` signed overflow after initial `gzungetc` | [`gzlib.c:395`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzlib.c#L395-L403) | [PR #1361](https://github.com/madler/zlib/pull/1361) |
| `gzread` heap over-read from stale `x.next` | [`gzread.c:271`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L271-L276) | [PR #1363](https://github.com/madler/zlib/pull/1363) |
| `gzread` / `gzgetc` signed `x.pos` overflow | [`gzread.c:413`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L413) | [PR #1405](https://github.com/madler/zlib/pull/1405) |
| `gzwrite` / `gzputc` signed `x.pos` overflow | [`gzwrite.c:230`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzwrite.c#L230) | [PR #1406](https://github.com/madler/zlib/pull/1406) |
| `gzoffset64` overflow on negative `lseek` | [`gzlib.c:486`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzlib.c#L486-L489) | [PR #1404](https://github.com/madler/zlib/pull/1404) |
| `deflateBound` too small under `Z_FIXED` | [`deflate.c:936`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L936) | [PR #1394](https://github.com/madler/zlib/pull/1394) |
| `deflateBound` 32-bit wrap on gzip `extra_len` | [`deflate.c:901`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L901) | [PR #1360](https://github.com/madler/zlib/pull/1360) |

## References

- **Lean 4 proof & documentation**: [`cla7aye15I4nd/zlib-f`](https://github.com/cla7aye15I4nd/zlib-f) · [Overview](https://www.dataisland.org/zlib-f/en/overview.html) · [Trees & Overlay Proof](https://www.dataisland.org/zlib-f/en/proof/trees.html) · [All Findings](https://www.dataisland.org/zlib-f/en/findings.html)
- **Overlay theorems by regime**: [`trees.c.universal-dynamic.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-dynamic.lean) (`memLevel 5..9`) · [`trees.c.universal-overlay-mid.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-overlay-mid.lean) (`memLevel 3..4`) · [`DeflateOverlayTiny.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Math/DeflateOverlayTiny.lean) & [`deflate.c.engine.overlay-header-ref.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean) (`memLevel 1..2`)
- **Upstream C & spec**: [`madler/zlib` @ `99623ef7`](https://github.com/madler/zlib/tree/99623ef7097352da7993ba614161fd6a311e046e) · [RFC 1951 (DEFLATE)](https://datatracker.ietf.org/doc/html/rfc1951)

<script src="/static/zlib-chase.js?v=20261118-zlib-chase-v6"></script>
