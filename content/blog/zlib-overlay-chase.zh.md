---
date: 2026-11-18
tags: [compression, verification, security, lean]
title: "写对的代码，写错的注释：zlib 里的双指针追逐战"
description: "deflate.c 用 38 行注释论证共用缓冲区绝不会覆写未读符号——这段注释其实是错的。当我们顺着破绽试图构造 Exploit 时，却撞上了藏在 Huffman 树里的三道数学防线。"
---

# 写对的代码，写错的注释：zlib 里的双指针追逐战

打开 [`zlib/trees.c:945`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L941-L946)，在 `compress_block` 的主循环末尾，有一条孤零零的断言：

```c
/* Check for no overlay of pending_buf on needed symbols */
#ifdef LIT_MEM
    Assert(s->pending < 2 * (s->lit_bufsize + sx), "pendingBuf overflow");
#else
    Assert(s->pending < s->lit_bufsize + sx, "pendingBuf overflow");
#endif
```

在所有生产环境的发布版编译（`#ifndef ZLIB_DEBUG`）下，`Assert` 都会被预处理器直接抹成空白。无论是 `compress_block`、`send_bits` 还是 `put_byte`，在向 `s->pending_buf` 写入字节时，都**没有任何运行时边界检查**。

当我们用 Lean 4 对上游 `zlib 1.4` 做完整的内存安全形式化证明（见前文 [zlib × Lean](/blog/zlib-lean.zh.html)，代码库 [`cla7aye15I4nd/zlib-f`](https://github.com/cla7aye15I4nd/zlib-f)）时，绝大多数模块的证明都属于经典的系统验证问题：`inflate_fast` 环形窗口的回绕、`longest_match` 在未初始化数组上的哈希链有界性、流式状态机的跨调用不变量。唯独 `trees.c` 的第 945 行是个例外：在 `deflate.c` 分配这块缓冲区的正上方，`zlib` 作者专门写了一段 38 行的数学证明来论证这条被删掉的 `Assert` 绝不会触发——**但那段证明在逻辑上是错的**。更奇妙的是，当我们放下证明器、顺着注释的漏洞试图构造 Exploit 去打穿它时，所有攻击样本却全都撞上了一堵无形的墙。

这篇文章不省篇幅、不跳步骤，从头把整场调查拆清楚：

1. **`deflate` 原来的算法到底长什么样**：为什么压缩一个块非要分两遍（Two Passes），为什么两个指针会被迫挤进同一个 `pending_buf` 数组里你追我赶。
2. **为什么官方注释证错了，而 Exploit 却塞不进去**：为什么“平均码长小于 31”防不住块中途追尾，以及一旦追尾为什么会直接触发 `.rodata` 越界读。
3. **怎么把 C 代码和 Lean 4 证明一步步联系起来**：指针自增与位寄存器移位是如何化归为 Huffman 树不等式，最后靠一步干净的代数对消（无需任何暴力搜索）封死 `memLevel 1..2` 的。
4. **证明的几何 vs. 物理的几何**：真实 `deflate()` 物理上最极限能贴到多少字节、为什么逐槽位独立求和的证明天花板卡在 `980` 而真实 C 停在 `720`、怎样才能继续逼近物理极限——以及最后反转：同一次证明在 `zlib 1.4` 其他地方真正抓出来的 **8 个真实 Bug**。

---

## 1. `deflate` 原来的算法长什么样（为什么两个指针会共用一块内存）

如果你以前没读过 `zlib` 源码，`pending_buf`、`sym_buf`、`bi_valid`、`_dist_code` 这些变量名很容易让人一头雾水。其实只要跟着一个具体的字符串——比如 `"abcde_abcde_!"`——走完一个 [DEFLATE](https://datatracker.ietf.org/doc/html/rfc1951) 块的生命周期，整个设计就一目了然了。

### 第一遍（Pass 1）：为什么 `deflate` 不能边扫描边输出比特？

假设 `deflate` 正在扫描 `"abcde_abcde_!"`。它的 LZ77 匹配器（`deflate_fast` 或 `deflate_slow`）发现第二个 `"abcde"` 重复了 6 个字节之前的内容，于是把这 13 个输入字节切成了 **9 个符号**：

```text
'a', 'b', 'c', 'd', 'e', '_',  Match(dist = 6, len = 5),  '_', '!'
```

问题来了：当匹配器看到 `'a'`、`'b'`、`'c'` 的时候，为什么不干脆当场把它们的 Huffman 比特码写进输出流呢？

**因为这时候它还不知道 Huffman 树长什么样！** 最优 Huffman 编码的核心是“高频符号用短码（最短 1 bit），罕见符号用长码（最长 15 bits）”。在把**整个块**扫描完、统计出每个字节和匹配长度各自出现了多少次之前，`deflate` 根本造不出当前块的定制 Huffman 树。

所以，`deflate` 处理每一个块都必须分成**两遍（Two Passes）**：

- **第一遍 —— 记录符号并统计词频（`_tr_tally`，[`trees.c:1095–1119`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1095-L1119)）：** 匹配器一边扫描输入，一边把每个符号以固定的 **3 字节（24 bits）** 格式暂存进中间数组 `sym_buf`——2 字节存距离 `dist`（字面量填 `0`，匹配填 `1..32506`），1 字节存 `lc`（字面量本身，或匹配长度减 3 即 `len - 3`）——同时给对应的词频计数器 `Freq[]` 加一。
- **第二遍 —— 建树并编码输出（`_tr_flush_block`，[`trees.c:997–1089`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L997-L1089)）：** 等 `sym_buf` 攒满一个块，`deflate` 根据 `Freq[]` 造出最优 Huffman 树，然后回过头从 `sym_buf` 里把刚才暂存的 3 字节符号一个个读出来，翻译成变长比特流，打包塞进输出字节队列 `pending_buf`。

### 分桶（Buckets）与附加位：一个 3 字节符号怎么变成 48 bits（或 1 bit）？

在看内存布局之前，还需要拼上编码格式的最后一块拼图：**匹配（Match）是怎么做 Huffman 编码的？**

回溯距离 `dist` 的取值范围是 `1` 到 `32,768`。如果直接给 32,768 种距离建一棵巨大的 Huffman 树，光在每个块开头把这棵树的形状告诉解压器就要花掉好几 KB，压缩小文件反而血亏！为此，[RFC 1951 §3.2.5](https://datatracker.ietf.org/doc/html/rfc1951#section-3.2.5) 采用了一个非常精巧的**“粗分桶 + 附加位（Extra Bits）”**设计——只对“落入哪个区间桶”做 Huffman 编码，桶内的精确偏移直接附带原始二进制位：

- **字面量与长度共用一棵 286 项的树（`dyn_ltree`）**：编号 `0..255` 是 256 种字面量字节；`256` 是块结束符 `END_BLOCK`；`257..285` 是 **29 个长度桶**，附带 `0` 到 `5` 个附加位（例如桶 `284` 覆盖长度 `227..257`，需要 1 个 Huffman 码加 **5 个附加位**；而桶 `285` 单独代表最大长度 `258`，**0 个附加位**）。
- **距离单独使用一棵 30 项的树（`dyn_dtree`）**：编号 `0..29` 是 **30 个距离桶**，附带 `0` 到 `13` 个附加位（例如桶 `29` 覆盖最远距离 `16,385..32,768`，需要 1 个 Huffman 码加 **13 个附加位**）。为了在 $O(1)$ 时间内把 `dist - 1`（`0..32,767`）映射到桶号 `0..29`，`zlib` 用了一张 512 字节的静态查找表 `_dist_code[512]`（[`deflate.h:320–321`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.h#L320-L321)）。

由于 DEFLATE 规定单棵树的码长上限是 15 bits，原本在 `sym_buf` 里占固定 **24 bits（3 字节）** 的一个符号，在第二遍写出时：

- **最短只需 1 bit**（高频重复的字面量字节）；
- **最长可达 $15 + 5 + 15 + 13 = 48$ bits**（一个罕见匹配，同时落入 5 附加位的长度桶与 13 附加位的距离桶）——整整是它在 `sym_buf` 中所占空间的 **两倍**！

### 三种块格式竞争，与叠在一起的共用缓冲区

当第一遍收集了至多 $n \le B - 1$ 个符号时——其中 $B = \mathrm{lit}\_\mathrm{bufsize} = 2^{\mathrm{memLevel}+6}$，取值从 `memLevel = 1` 的 **$128$** 到 `memLevel = 9` 的 **$32{,}768$**（默认 `memLevel = 8` 为 $16{,}384$）——`_tr_flush_block` 会给当前块评估 **三种合法的 DEFLATE 编码方案**，谁算出来的总字节数最小就选谁：

1. **存储块 Stored（标记 `00`）**：放弃压缩，直接从滑动窗口把未压缩的原始输入字节原样拷出（占 `stored_len + 4` 字节）。
2. **固定 Huffman 块 Fixed（标记 `01`）**：使用标准写死的静态码表（字面量 8 或 9 bits，长度码 7 或 8 bits，距离码固定 5 bits）。无需传树头，只写 3 bits 块标记即可开始编码，且**任何单个符号封顶只有 $8 + 5 + 5 + 13 = 31$ bits**。
3. **动态 Huffman 块 Dynamic（标记 `10`）**：根据当前块词频定制 `dyn_ltree` 和 `dyn_dtree`。由于解压器事先不知道这两棵树长什么样，在编码第 0 个数据符号之前，`send_all_trees` **必须先把两棵树的码长表完整写进块头**（还会再用一棵 19 项的游程码长树 `bl_tree` 压缩一遍）。

现在看最关键的内存布局。第二遍刷块只在上一块的输出队列已完全排空（`pending = 0`）时才会启动，此时只有 16 位移位寄存器 `bi_buf` 里至多残留 `bi_valid <= 7` 个还没凑够整字节的比特。为了省掉单独分配 `sym_buf` 的 $3B$ 字节内存，`deflateInit2_`（[`deflate.c:463–520`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L463-L520)）只申请了**一块 `4B` 字节的 `pending_buf`**，把前 $B$ 字节（`8B` bits）空出来当起跑缓冲，直接把 `sym_buf` 架在 `pending_buf + B` 上：

```c
s->lit_bufsize = 1 << (memLevel + 6); /* B：128 .. 32768（默认 16384） */
...
s->pending_buf = (uchf *) ZALLOC(strm, s->lit_bufsize, LIT_BUFS); /* 4 * B 字节 */
s->pending_buf_size = (ulg)s->lit_bufsize * 4;
...
s->sym_buf = s->pending_buf + s->lit_bufsize;   /* 从 1/4 处开始叠放 */
s->sym_end = (s->lit_bufsize - 1) * 3;          /* 最多存 n = B - 1 个三元组 */
```

点击下方交互示意图的四个阶段，一步步看清第一遍和第二遍是如何共用 `pending_buf[0 .. 4B)` 的：

<div class="zc-widget" data-zc="pipeline" data-lang="zh"></div>

一旦进入 **阶段 4（Pass 2b 原地追逐）**，两个游标就在同一个数组里同时从左向右狂奔：

- **逃跑者（读边界 `B + 3k`）**：从字节 $B$（$8B$ bits）出发。每读走第 $k$ 个符号就腾出 3 字节，使“未读符号”的左边界向右推进 **+24 bits**。
- **追逐者（写游标 `pending` + `bi_valid`）**：从字节 $0$ 附近出发（带至多 7 个残留比特），在读第 0 个符号前先猛跨一步写出块头，随后每编码一个符号推进 **1 到 48 bits**。

写游标覆盖 `[B .. B + 3k)` 完全没问题——那些符号已经读过了！真正致命的是：写游标一旦追上 `B + 3k`，把 `compress_block` **还没读到的符号**给改写了。

---

## 2. 为什么追尾会破坏内存安全，以及 `deflate.c` 注释错在哪

### 不只是输出乱码：`_dist_code[512]` 的越界悬崖

在动手证明或构造攻击之前，先问一个安全审计最关心的问题：**就算写游标真的追上了 `B + 3k`、覆盖了未读符号，难道不就是吐出一串解压失败的损坏压缩流吗？为什么会威胁内存安全？**

往 `Assert` 上方看二十行（[`trees.c:913–939`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L913-L939)）：

```c
dist = s->sym_buf[sx++] & 0xff;
dist += (unsigned)(s->sym_buf[sx++] & 0xff) << 8;
lc = s->sym_buf[sx++];
if (dist == 0) {
    send_code(s, lc, ltree); /* 发送字面量 */
} else {
    code = _length_code[lc];
    send_code(s, code + LITERALS + 1, ltree);
    ...
    dist--; /* 此时 dist 为匹配距离 - 1 */
    code = d_code(dist);
    Assert(code < D_CODES, "bad d_code");
    send_code(s, code, dtree);
```

还记得第一遍提过的 512 字节查找表 `_dist_code[512]` 吗？它在 [`deflate.h:320–321`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.h#L320-L321) 里的宏没有任何边界检查：

```c
#define d_code(dist) \
   ((dist) < 256 ? _dist_code[dist] : _dist_code[256+((dist)>>7)])
```

正常情况下，`_tr_tally` 写入的合法匹配满足 `1 <= dist <= MAX_DIST <= 32506`，减一后不超过 `32505 <= 32767`，因此 `256 + ((dist - 1) >> 7)` 最大只到下标 `511`，刚好停在 `_dist_code[512]` 内部。

但如果未读符号被压缩比特流覆盖，`dist` 的两个字节就变成了最高可达 `65535` 的任意 `uint16_t`！只要落进 `32769 .. 65535`（`0x8001 .. 0xffff`），就会走入 `else` 分支，把 `256 + ((dist - 1) >> 7)` 推到 **`512 .. 767`**——直接在 `.rodata` 只读数据段上越界读取 `_dist_code` 之后的 **256 个字节**！如果读出的相邻常量字节超过 `60`，紧接着的 `send_code(s, code, dtree)` 与 `extra_dbits[code]` 又会对 `dyn_dtree[61]` 和 `extra_dbits[30]` 触发二次越界读。拖动下方滑块越过 `32,768`，就能看到整条越界链：

<div class="zc-widget" data-zc="oob" data-lang="zh"></div>

所以，哪怕我们的目标纯粹是**内存安全**（证明 `deflate` 绝无未定义行为），也绕不开证明写游标永远追不上读游标。

### `deflate.c:465–502` 注释里的平均值谬误

`zlib` 的作者很清楚这种内存叠放需要数学担保，所以在 [`deflate.c:465–502`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L465-L502) 里写了一段 38 行的证明。前半段分析 **Fixed（固定编码）块**：

> *固定编码下一对长度/距离至多占 31 位。每消费一个符号，读 `sym_buf` 的指针前进 3 字节（24 位），同时向 `pending_buf` 写出至多 31 位。因此写出的比特离下一个待读符号最近的时刻，就在最后一个编码写出之前。*

对于 **固定块**，逻辑是对的：每个符号释放 24 bits、至多写 31 bits，每步最多净追近 $+7$ bits。哪怕在最小的 `memLevel = 1`（$B = 128, n = 127$），$127 \times 7 = 889$ bits 的净追近量也追不平 $1{,}024$ bits 的起跑优势。*（顺带一提：注释第 490 行算出还剩 139 bits，是因为漏算了上一块遗留的 `bi_valid <= 7` bits——我们马上会验证，真实物理极限比注释紧了整整 7 bits，是 **132 bits / 18 字节**！）*

紧接着在 [`deflate.c:496–502`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L496-L502)，作者试图把证明推广到 **Dynamic（动态编码）块**：

```c
/* That latter condition then assures that the above analysis also covers all
 * dynamic blocks. A dynamic-code block will only be chosen to be emitted if it
 * has fewer bits than a fixed-code block would for the same set of symbols.
 * Therefore its average symbol length is assured to be less than 31. So the
 * compressed data for a dynamic block also cannot overwrite the symbols from
 * which it is being constructed.
 */
```

**这段推理在逻辑上是坏的。** 整块 $n$ 个符号的**平均**代价受控，根本管不住前 $k < n$ 个符号组成的**前缀**：

1. **读第 0 个符号前先交大额块头税。** `send_all_trees`（[`trees.c:830–853`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L830-L853)）要先写 `5 + 5 + 4 = 14` bits 计数、至多 $19 \times 3 = 57$ bits 的 `bl_tree`、以及至多 $(286 + 30) \times 7 = 2{,}212$ bits 的树码长——在通用上限下高达 **$2{,}283$ bits**，此时第 0 个符号还没读！
2. **单步最高 48 bits（每步净追近 +24 bits）。** 动态码长可达 15 bits，而不是固定块的 8 和 5。
3. **昂贵符号前置（Front-loading）。** 如果把罕见高代价匹配全排在 `sym_buf` 开头（$k = 0..28$），把廉价高频符号全排在末尾（$k = 29..126$），整块总长依然轻松赢过固定块（`opt_lenb < static_lenb`），但写游标会在前四分之一路程里向 `B + 3k` 猛扑！

看到一段没有边界检查的写循环正上方摆着一份写错的证明，我们的第一反应立刻是从“证明者”切换成“攻击者”：把配置调到最小的 `memLevel = 1`（$B = 128$，起跑缓冲只有 $1{,}024$ bits，连理论最大树头 $2{,}283$ bits 的一半都不到！），在块首塞满罕见匹配，块尾垫满廉价锚点压低总体积，试图一举撞穿 `sym_buf`。然而我们构造的所有样本全都在半路刹住了车。在下方交互面板里切换三种轨迹——其中 **02 · 动态块真实极限** 就是我们在未修改 `deflate()` 中实测构造出的极限动态块，它在中途 **$k = 29$** 处逼近到 `37 B / +294 bits` 的谷底，随后被硬生生拉回安全区：

<div class="zc-widget" data-zc="race" data-lang="zh"></div>

---

## 3. 怎么把 C 语言算法和 Lean 4 证明一步步联系起来

一边是充斥着指针自增、16 位移位寄存器 `bi_buf`、最小堆建树与码长截断的 C 代码；另一边是 Lean 4 里的纯数学定理。两者是怎么严丝合缝接上的？下面沿着 [`cla7aye15I4nd/zlib-f`](https://github.com/cla7aye15I4nd/zlib-f) 的真实证明结构，走完这座四步桥梁。

### 第一步：Lean 翻译模型里“安全”到底指什么？

在 `zlib-f` 中，`zlib/trees.c`、`zlib/deflate.c` 等每个 C 文件都被逐语句翻译到带显式堆与故障状态的 Lean 4 单子（Monad）中。每一次数组下标访问（`_dist_code[...]`、`pending_buf[...]`）、指针偏移、有符号整数运算和位移都会做精确的 C 标准边界检查；一旦违规就触发 `Fault.ub`。证明 `deflate` 安全，就是证明从任何合法初始化流出发，任意公开 API 调用序列都永远不会到达 `Fault.ub`。

### 第二步：把 `pending` 和 `bi_buf` 合成为一个“比特里程表”

在 C 代码里，`send_bits(s, val, len)`（[`trees.c:274–285`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L274-L285)）先把比特塞进 16 位寄存器 `s->bi_buf`（`s->bi_valid` 记录当前攒了几位），只有当 `bi_valid + len > 16` 时，才调用 `put_short` 一次性向 `pending_buf[pending++]` 刷入 **2 个字节**。

如果在几十次 `send_bits` 调用中分别追踪 `pending` 和 `bi_valid`，证明会被每两字节一次的跳变折磨得苦不堪言。反之，定义**总已发射比特数（比特里程表）**：

$$
S = 8 \cdot \mathrm{pending} + \mathrm{bi}\_\mathrm{valid}.
$$

无论某次 `send_bits(s, val, len)` 有没有触发双字节刷出，它对 $S$ 的效果永远只有一句话：**$S$ 精确增加 `len`**！而且由于 `put_short` 只在 $S$ 跨过 16 的倍数时才刷出 16 bits（每次写入后 `bi_valid` 恒落在 `1..16`），字节下标 `pending` 完全由 $S$ 唯一决定：

$$
\mathrm{pending} = 2 \left\lfloor \frac{S - 1}{16} \right\rfloor \le \frac{S}{8}.
$$

在刷块入口处，`pending = 0`，`bi_valid` $= v_0 \le 7$。写完 3 bits 块标记、$H$ bits 动态树头以及前 $k$ 个符号 $s_0, \dots, s_{k-1}$ 后，$S_k = v_0 + 3 + H + \sum_{i=0}^{k-1} \mathrm{cost}(s_i)$。与此同时，在块末尾（$k = n$），`compress_block` 还要写出 $\le 15$ bits 的 `END_BLOCK` 并对齐字节，且不能越过 `4B` 缓冲区末端（`block_room`）。把块中不追尾（$S_k \le 8(B + 3k)$）和块尾不越界合并成一条统一充分条件（[`trees.c.universal-dynamic.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-dynamic.lean#L35-L41) 中的 `DynamicRoom`），只需对所有 $k \in \{0, \dots, n\}$ 证明：

$$
\underbrace{(v_0 + 3 + 15)}_{\le\, 25} + H + \sum_{i=0}^{k-1} \big(\mathrm{cost}(s_i) - 24\big) \le 8B.
$$

### 第三步：擦除 `sym_buf` 的顺序（从指针数组 `sym_buf` 化归到词频表 `Freq[]`）

观察 `trees.c` 里一个极其关键的结构性质：**`build_tree` 和 `build_bl_tree` 自始至终根本不读 `sym_buf`！** 它们只读第一遍统计出来的总词频数组 `dyn_ltree[c].Freq` 和 `dyn_dtree[d].Freq`。

这意味着：假如对手把 `sym_buf` 里的 $n$ 个符号任意重排——把所有 $\mathrm{cost} > 24$ 的昂贵匹配全搬到最前面，把所有 $\mathrm{cost} \le 24$ 的廉价符号全丢到最后面——建出来的两棵 Huffman 树、树头位数 $H$、`opt_lenb` 和 `static_lenb` **连 1 个比特都不会变**！在这种最坏排列下，前缀和 $\sum_{i=0}^{k-1}(\mathrm{cost}(s_i) - 24)$ 恰好在最后一个昂贵符号处达到峰值，也就是整块的**超额位数（Block Excess）**：

$$
E = \sum_{i=0}^{n-1} \max\big(0,\, \mathrm{cost}(s_i) - 24\big).
$$

只用这一步，堆上的字节数组 `sym_buf` 和循环下标 $k$ 就彻底从证明目标里消失了！证明任意符号顺序下 `compress_block` 永不追尾，完全归结为证明 `build_tree` 产出的树满足一条与顺序无关的预算不等式：

$$
H + E + 25 \le 8B.
$$

### 第四步：把 C 的三个树函数连接到三个 `memLevel` 区间

为什么 $H + E + 25$ 不可能突破 $8B$？核心原因只有一句话：**在 C 函数 `build_tree` 里，深层长码必须用指数级膨胀的块总频数去换。**

不妨在脑海里跟着 `build_tree`（[`trees.c:627–716`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L627-L716)）跑一个微型例子：假设你想把一片频数 `Freq = 1` 的叶子 $x$ 挤到深度 $4$。每一步 `pqremove` 都会从最小堆里弹出当前最轻的两个节点合并：

- 深度 $4 \to 3$：$x$（权重 $1$）与权重 $\ge 1$ 的兄弟合并 $\implies$ 父节点权重 $\ge 2$。
- 深度 $3 \to 2$：要想不让上一步被提前拆散，这一层的旁系兄弟权重至少 $\ge 1 \implies$ 祖父权重 $\ge 3$。
- 深度 $2 \to 1$：刚才合并 $1+1$ 时堆里既然没挑中这一层的兄弟，它的权重就必须 $\ge 2 \implies$ 曾祖父权重 $\ge 5$。
- 深度 $1 \to 0$：同理，根节点的另一半子树权重必须 $\ge 3 \implies$ 整棵树总权重 $W \ge \mathbf{8 = F_6}$！

通过对 `build_tree` 的最小堆弹出过程做归纳，我们的 Lean 证明严格建立了未截断 Huffman 树的斐波那契定律：在总权重为 $W$ 的树中，任何频数 $f \ge 1$、深度为 $l$ 的叶子必然满足

$$
f \cdot F_{l+1} + F_l \le W \qquad (\text{特别地，} F_{l+2} \le W).
$$

从这里出发，随着 $B = 2^{\mathrm{memLevel}+6}$ 从 $32{,}768$ 一路缩小到 $128$，证明分别与 `trees.c` 中的三处具体代码机制咬合：

#### 区间 1：`memLevel 5..9`（$B \ge 2{,}048$）—— 约束 `gen_bitlen` 的 15 位截断修复

当 $B \ge 2{,}048$ 时，极端偏斜的块总权重 $W > 1{,}597$，可能长出深度超过 DEFLATE 15 位上限的树。在 C 代码里，`gen_bitlen`（[`trees.c:583–593`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L583-L593)）会把所有 $> 15$ 的深度强行截断为 $15$。截断破坏了前缀码的 Kraft 等式（使 $\sum 2^{-l_i} > 1$），于是 `gen_bitlen` 紧接着跑一个修复循环，把若干较浅叶子的码长加一（`bits -> bits + 1`）直到恢复 $\sum 2^{-l_i} = 1$。

即便把 286 个字面量/长度桶与 30 个距离桶上的最坏降级损耗全部算进来（[`trees.c.heap.gbfibpush.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.heap.gbfibpush.lean)），Lean 依然证出 $E \le 6.257 \cdot (n + 3)$。由于每增加一个符号容量提供 8 bits 起步空间、最多消耗 6.257 bits 超额位，$2{,}283 + \lceil 6.257(B+2) \rceil + 25 \le 8B$ 对所有 $B \ge 1{,}332$ 恒成立（[`trees.c.universal-dynamic.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-dynamic.lean#L52-L67) 中的 `dynamic_room_large`）。

但在 `memLevel = 4`（$B = 1{,}024, 8B = 8{,}192$）处，$2{,}283 + 6.257 \times 1{,}026 + 25 = 8{,}728 > 8{,}192$——**超支了 536 bits**。

#### 区间 2：`memLevel 3..4`（$B = 512, 1{,}024$）—— 证明 `trees.c:577` 永远提前返回

打开 [`trees.c:577`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L577)，就在 `gen_bitlen` 进入截断修复循环的正上方，有一行早退判断：

```c
if (overflow == 0) return;
```

当 $B \le 1{,}024$ 时，块内至多有 $n \le 1{,}023$ 个符号，加上 `END_BLOCK` 和至多两个补位叶子，整棵树的总权重 $W \le B + 2 \le \mathbf{1{,}026}$。而根据上面的斐波那契定律，要想长出哪怕一个深度 $\ge 16$ 的节点（使 `overflow > 0`），它深度为 $15$ 的父节点会迫使总权重至少达到：

$$
F_{16} + F_{15} = F_{17} = \mathbf{1{,}597}.
$$

因为 $1{,}026 < 1{,}597$，**在 `memLevel <= 4` 时，`trees.c:577` 对一切输入都 100% 走早退 `return` 分支！** 既然没有任何截断扭曲，每个符号都严格满足 $f \cdot F_{l+1} + F_l \le W$，使 $E$ 在 $B = 1{,}024$ 时骤降到 $3{,}678$ bits（$5{,}986 \le 8{,}192$），在 $B = 512$ 时降到 $1{,}777$ bits（$2{,}283 + 1{,}777 + 25 = \mathbf{4{,}085 \le 4{,}096}$——只剩 **11 bits** 证明余量，见 [`trees.c.universal-overlay-mid.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-overlay-mid.lean)）。

在下方切换 `memLevel` 并拖动深度 $l$，直观查看 $B + 2 < 1{,}597$ 是如何锁死第 16 层、强制触发 `trees.c:577` 提前返回的：

<div class="zc-widget" data-zc="fib" data-lang="zh"></div>

#### 区间 3：`memLevel 1..2`（$B = 128, 256$）—— `_tr_flush_block` 的块选择与代数对消

来到 $B = 256$（$8B = 2{,}048$）和 $B = 128$（$8B = 1{,}024$），光一个 2,283 bits 的通用块头上限本身就已经比整个 $8B$ 预算还大了。为什么光写树头没有当场击穿 $B$？因为 **三个 C 函数的行为像齿轮一样咬合在了一起**：

1. **在 `build_tree` 中（[`deflate.c.engine.overlay-lengths.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/deflate.c.engine.overlay-lengths.lean)）：** 当 $B = 128$（$W \le 130 < 144 = F_{12}$）时，$F_{l+2} \le 130$ 迫使**所有数据码长 $l \le 9$**（在 $B = 256$ 时 $l \le 11$）；并且任何因有效符号不足 2 个而补入的 `f = 0` 占位叶子必然处在 2 叶树中，码长恒为 $l = 1$。
2. **在 `scan_tree` 与 `build_bl_tree` 中（[`deflate.c.engine.overlay-header-ref.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean)）：** 因为 $B = 128$ 时码长 `10..15` 绝不出现，`bl_tree` 至多只用到 19 个符号中的 13 个。用一组显式完全参考前缀码给 `bl_tree` 计费，可把两倍树头严格控制在 $286 + 30$ 个树槽位的逐项费用之和以内。
3. **在 `_tr_flush_block` 中（[`trees.c:1035`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1035-L1037)）：** 还记得 `deflate.c` 里那段坏掉的注释吗？虽然 `opt_lenb < static_lenb` 不能靠平均值直接保住前缀，但 `_tr_flush_block` 在发动态块前确实执行了 `if (static_lenb <= opt_lenb)`！消去两边完全相同的附加位总和后，它直接给出了动态码长（$l_c, l_d$）与固定码长（$l_c^{\mathrm{static}} \in \{7,8,9\}$ 及 $5$）之间的全局不等式。

把这两条不等式并排放在一起，就能看到一步极其干净的代数对消：

$$
2H \le H_{\mathrm{const}} + \sum_{c=0}^{285} \mathrm{charge}_L(l_c) + \sum_{d=0}^{29} \mathrm{charge}_D(l_d),
$$

$$
H + \sum_{c=0}^{285} f_c\, l_c + \sum_{d=0}^{29} f_d\, l_d + 1 \le \sum_{c=0}^{285} f_c\, l_c^{\mathrm{static}} + 5 \sum_{d=0}^{29} f_d.
$$

只需将 **$a$ 倍的第一式** 与 **$b$ 倍的第二式** 直接相加（在 $B = 128$ 取 $a = 2, b = 4$；在 $B = 256$ 取 $a = 1, b = 1$），左边凑出 $(2a + b)(H + E) + b$，而**两边未知的动态码长加权和与静态码长直接精确抵消**！全部 256 个字面量、`END_BLOCK` 与低附加位匹配桶的频率斜率瞬间变为非正数；只剩寥寥几个高附加位匹配桶，结合 Kraft 不等式（$\sum 2^{15-l} \le 2^{15}$）与 $f \cdot F_{l+1} + F_l \le W$，无需任何暴力搜索，一个约 485 行的参数化模块（[`DeflateOverlayTiny.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Math/DeflateOverlayTiny.lean)）就直接合拢了全部极小块证明：

- 当 $B = 256$（$8B = 2{,}048$）时：$H + E \le \mathbf{1{,}899} \implies 1{,}899 + 25 = \mathbf{1{,}924 \le 2{,}048}$（留出 **124 bits** 预算余量）。
- 当 $B = 128$（$8B = 1{,}024$）时：$H + E \le \mathbf{983} \implies 983 + 25 = \mathbf{1{,}008 \le 1{,}024}$（留出 **16 bits** 预算余量）。

在下方切换全部 9 个 `memLevel`，对比朴素通用公式、Lean 4 定理上界与真实 C 代码物理极限：

<div class="zc-widget" data-zc="regimes" data-lang="zh"></div>

---

## 4. 证明的几何 vs. 物理的几何：真实 `zlib` 到底能贴到多近？

我们的形式化证明在 `memLevel = 1` 下以 16 bits 余量过线（`1,008 <= 1,024`），在 `memLevel = 3` 下以 11 bits 余量过线（`4,085 <= 4,096`）。这自然引出两个核心追问：

1. **在原封不动的真实 `zlib 1.4` 里，合法的未压缩输入物理上最极限能把 `s->pending` 推到离下一个未读符号多近？**
2. **为什么我们的证明停在 `983`（总计 `1,008`）附近？如果要把形式化证明的上界继续压向真实 C 的物理极限，究竟需要做什么？**

为了不留死角地回答第一个问题，我们对全部三种块格式、`memLevel = 1..9` 以及每个块符号数 $n \in [1, B-1]$ 做了完整分析，反向合成出真实的未压缩输入字节流，并在未修改的 `deflateInit2` + `deflate` + `inflate` 中挂上 `put_byte` 探针完成了端到端实测验证。

### 1. 全局物理最接近记录：固定块（`18 字节 / 132 bits`）

出人意料的是，整个 `zlib` 里写指针离未读符号物理距离最近的，**并不是动态块**，而是 `memLevel = 1`（$B = 128, n = 127$）下的 **固定块（`Z_FIXED`）**！

在 `Z_FIXED` 策略下，`_tr_flush_block` 跳过了 `opt_lenb < static_lenb` 比较，块头又是 0 bits（只有 3 bits 块标记），允许全部 127 个符号清一色取最重的 **31-bit 匹配**（长度 `131..257` 占 $8 + 5 = 13$ bits，距离 `16,385..32,506` 占 $5 + 13 = 18$ bits，整块超额位高达 $E = 127 \times 7 = \mathbf{889\text{ bits}}$）。对任意入口残留位 $v_0 \in \{0..7\}$ 与未读符号下标 $k_{\mathrm{unread}} \in \{1..127\}$，间距有精确闭式解：

$$
\mathrm{BitGap} = 8B - v_0 - 3 - 7\,k_{\mathrm{unread}}, \qquad \mathrm{ByteGap} = (B + 3\,k_{\mathrm{unread}}) - 2\left\lfloor \frac{v_0 + 2 + 31\,k_{\mathrm{unread}}}{16} \right\rfloor.
$$

回头看一眼 `deflate.c:490` 的原话：*“由于 3 比特固定块头，剩余空间实际上是 139 比特。”* 把 $v_0 = 0$ 和 $k_{\mathrm{unread}} = 126$（刚要读取字节 `506` 处的最后一个符号前）代入上式：$1{,}024 - 0 - 3 - 882 = \mathbf{139\text{ bits}}$——与注释一比特不差！

**但入口处的 $v_0$ 未必等于 $0$。** 只要在目标块之前用微小的 `Z_BLOCK` 刷块垫出 $v_0 = \mathbf{7}$ 个残留比特，就能再压掉 7 bits！我们据此合成了一段 **33,404 字节的未压缩输入**（在窗口下标 `0` 放 1 个垫片字节避开 `hash_head == NIL`，在 32 KiB 窗口内铺设 127 组互异的 131 字节模板，用单字节 `Z_BLOCK` 对齐出 `bi_valid = 7`，最后拼上这 127 组模板），在未修改的 `deflate(Z_FIXED)` 中一举命中全局物理下限：

- **在最后一个未读符号处（$k = 126$，未读字节 `506`）：** `pending = 488`，`bi_valid = 12` $\implies$ 真实未读余量仅剩 **`18 字节`（`132 bits`）**（比 `deflate.c:490` 注释声称的极限还要紧 7 bits！）。
- **在 [`trees.c:945`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L945) 的 `Assert` 检查点（$k = 127$，`B + sx = 509`）：** `pending = 492`，`bi_valid = 11` $\implies$ **`17 字节`（`125 bits`）**。

*（注：如果不强制指定 `Z_FIXED`，在默认的 `Z_DEFAULT_STRATEGY` 下塞满 31-bit 匹配会让动态树比固定树短一千多比特；自然获选的固定块余量从不会低于 **`65 字节` / `515 bits`**。）*

### 2. 动态块物理最接近记录（默认 `Z_DEFAULT_COMPRESSION`）：`k = 29` 处的 `37 字节 / 294 bits`

为什么动态块反而追不到 18 字节那么近？因为 `opt_lenb < static_lenb`（$H + P_{\mathrm{opt}} \le P_{\mathrm{static}} + 6$）是一道天然的自限刹车！

注意匹配的附加位（`extra_lbits`、`extra_dbits`）在 $P_{\mathrm{opt}}$ 和 $P_{\mathrm{static}}$ 两边完全一样（[`trees.c:574–575`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L574-L575)），相减时直接抵消。因此，树头 $H$ 的每一比特、以及每一个罕见深层匹配（$ll + dl \ge 7$），都必须靠高频“锚点（Anchor）”符号在动态树下省出的比特来补贴——而一旦把某个匹配重复足够多次去赚取补贴，它自己的动态码长就会缩水到 $ll + dl \le 5$（总代价 $\le 5 + 18 = 23 < 24$），它自身的超额位瞬间归零！

更重要的是，由于 `_tr_tally` 只统计长度与距离各自的边缘词频，把块内所有匹配按“最长长度码配最长距离码”同序配对，再把所有 $\mathrm{cost} > 24$ 的符号排在最前，**可以严格证明在全部 $M! \cdot n!$ 种配对与排列中同时极小化比特间距与字节间距**。在 `memLevel = 1` 的全部 $n \in [1..127]$ 上，极限出现在满载 $n = 127$，由三部分精密咬合而成：

- **49 个 `MAX_MATCH = 258` 锚点匹配**（桶 `285` 恰好有 **0 个附加位**，静态占 8 bits、动态仅占 2 bits——既能高效攒出树头补贴，又**完全不碰桶 `281..284`**，让全部四个 5 附加位长度桶都保持生僻深层状态！），
- **分布在 37 种间隔字节上的 38 个字面量**（精准切断零游程，阻止 `scan_tree` 使用 `REPZ_3_10` / `REPZ_11_138` 压缩），
- **前置在块首的 29 个满附加位罕见匹配**（`dcode = 24..29`，单符号 26–29 bits）。

我们反向构造出一段 **50,184 字节的真实未压缩数据**，在完全默认策略 `deflateInit2(&strm, Z_DEFAULT_COMPRESSION, Z_DEFLATED, 15, 1, Z_DEFAULT_STRATEGY)` 下，其真实 LZ77 分词一字不差地生成上述 127 个符号（入口 `bi_valid = 7`，且经 `inflate()` 逐字节无损还原）：

- `opt_len = 2,211` bits（`277` 字节）`< static_len = 2,214` bits（`278` 字节 —— 仅凭 **1 字节优势**惊险保住动态块！），
- **$H = 623$ bits**，**$E = 97$ bits** $\implies$ **$H + E = \mathbf{720\text{ bits}}$**，
- **最小物理未读间距（出现在块中途 $k = 29$，此时 `[215..509)` 仍有 98 个符号未读）：** `pending = 178`，`bi_valid = 2`，距离未读字节 `215` 仅剩 **`37 字节`（`294 bits`）**！

### 3. 为什么“逐槽位独立求和”的天花板卡在 `980`——怎样才能逼近物理极限 `720`？

把 `memLevel = 1`（$8B = 1{,}024$）下的三个关键刻度放在一起对比：

- **真实 C 代码的动态块物理极值：** $H + E = \mathbf{720}$ bits（未读符号物理余量 $1{,}024 - 10 - 720 = 294$ bits）。
- **任意“逐槽位独立求和”线性证明的数学极限：** $H + E = \mathbf{979.12 \approx 980}$ bits。
- **我们手写的小整数代数对消证明（`2 × 头部界 + 4 × 选择不等式`）：** $H + E \le \mathbf{983}$ bits（加上 `+25` 后为 `1,008 / 1,024`）。

中间那个数字（`979.12`）道破了天机：哪怕动用连续实数线性规划求解器取任意最优权重，**只要证明结构把 $286 + 30 = 316$ 个树槽位拆成独立项分别定界再相加，数学上就不可能证出比 `980` 更紧的上界**——我们仅靠两位数整数手写消元证出的 `983`，其实已经贴到了这个解耦架构理论极限的 **4 bits** 以内！把每一层松弛代回 $H + E = 720$ 的真实极值块，不仅能把差距逐比特算平，也能看清**如果真想在 Lean 里把证明从 `980` 一路压向 `720`，必须打破哪三层独立性**：

| 松弛来源 | 比特数 | 要在 Lean 中收紧它需要做什么 |
| --- | ---: | --- |
| 316 个树槽位逐项独立解耦 | `169.5` | **单树多叶联合脊柱约束：** 证明同一棵树里的多片深层叶子共享同一个总权重预算 $W \le 130$（而非每个槽位各自假装独占一条斐波那契脊柱），并对约 230 个未出现的空槽位（$f = 0$）做联合计数 |
| 固定参考码 + 局部零费用计费 | `87.7` | **`scan_tree` 全局跨槽位零游程自动机：** 对相邻空槽位的连续零游程（`REPZ_3_10 = 17`、`REPZ_11_138 = 18`）与自适应 `bl_tree` 码长做全局归纳，替代逐槽位固定参考码 |
| 统一并入块尾 `END_BLOCK` 裕量（`+25` 对比 `+10`） | `15.0` | **拆分块中追逐与块尾收尾定理：** `END_BLOCK`（$\le 15$ bits）在全部 $n$ 个符号读完之后才写出，面对的是缓冲区末端 `4B = 4,096` bits 而非 `8B = 1,024` bits |
| 小整数权重（`983` 对比 LP `979.1`）与取整 | `5.8` | 缩放因子 `8` 的整数近似（`3.9`b）+ 匹配超额位拆树（`1.0`b）+ 字节取整（`0.9`b） |

为什么我们在 `H + E <= 983` 就停手，而不继续形式化多叶联合脊柱与全局游程自动机去逼近 `720`？因为对于**内存安全定理**而言，证出 `1,008 <= 1,024` 和证出 `730 <= 1,024` 得到的 `Fault.ub`-free 结论**一模一样**——停在逐槽位解耦这一层，恰好能用 485 行完全透明、零暴力搜索的代数证明跨过 `1,024` 生死线，而不必让证明体积膨胀十倍。

---

## 5. 反转：`zlib 1.4` 真正出 Bug 的 8 个地方

做安全验证经常会遇到这种冷幽默：你花了好几周死磕一段连注释都写错了的原地双指针追逐，发现它在固定块下靠 18 字节、在动态块下靠 37 字节涉险过关；结果转头去证十个文件之外看似平平无奇的常规代码时，却接连抓出真正的内存安全漏洞。

在完成 `zlib.h` 全部公开函数对 `zlib 1.4`（[`99623ef7`](https://github.com/madler/zlib/tree/99623ef7097352da7993ba614161fd6a311e046e)）的 Lean 4 安全性证明过程中，我们在上游 `zlib` 中共发现了 **8 个真实缺陷**（[补丁目录](https://github.com/cla7aye15I4nd/zlib-f/tree/main/patches)）——6 个通过 AddressSanitizer / UndefinedBehaviorSanitizer 实测复现的未定义行为或内存错误，以及 2 个违背 API 承诺的 `deflateBound` 上界错误。

### 1. `Z_FIXED` 下 `deflateBound` 算小了输出上界（[`deflate.c:936`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L932-L940)，[PR #1394](https://github.com/madler/zlib/pull/1394)）

最戏剧性的一个 Bug 恰好又回到了 `_tr_flush_block`。`zlib.h` 承诺：只要按 `deflateBound(strm, sourceLen)` 分配输出空间，单次调用 `deflate(strm, Z_FINISH)` 就保证返回 `Z_STREAM_END`。在默认 `windowBits = 15, memLevel = 8` 下，`deflateBound_z` 给出了仅膨胀约 0.03% 的极紧上界，理由是“万一压缩变大了，总能退回不压缩的存储块（Stored Block）”。但看一眼 [`trees.c:1047–1056`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1047-L1056)：

```c
if (stored_len + 4 <= opt_lenb && buf != (char*)0) {
    _tr_stored_block(s, buf, stored_len, last);
```

只要 `fill_window` 在块中途滑动过 64 KiB 窗口（`block_start < 0`），原始输入字节已被挤出窗口，`buf` 就会变成 `NULL`——**存储块退路当场关闭**！而在 `Z_FIXED` 配合级别 1–3 时，`deflate_fast` 发出的远距离 3 字节匹配占 **25 bits**（每输入字节 **8.33 bits**）。面对 $1{,}000{,}000$ 字节输入，`deflateBound` 只给 `1,000,318` 字节，真实 C 代码却需要 **`1,008,570` 字节**，导致单次压缩半途返回 `Z_OK`。

### 2. `gzread` 在部分读取报错后从悬空的旧 `x.next` 拷贝（[`gzread.c:271`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L271-L276)，[PR #1363](https://github.com/madler/zlib/pull/1363)）

在透明直通 `COPY` 模式下，`gz_fetch` 调用 `gz_load` 填充 `state->out`：

```c
case COPY:      /* -> COPY */
    if (gz_load(state, state->out, state->size << 1, &(state->x.have)) == -1)
        return -1;
    state->x.next = state->out;
    return 0;
```

如果 `gz_load` 第一次 `read()` 读出了一部分字节（`state->x.have > 0`），下一次 `read()` 返回 `-1` 失败，`gz_fetch` 会在更新 `state->x.next = state->out` **之前**直接 `return -1`！外层 `gz_read` 看到 `x.have > 0`，照常从**过期的旧指针 `state->x.next`** 处 `memcpy` 数据——当场触发堆缓冲区越界读（ASan 于 [`gzread.c:369`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L369) 捕获）。

### 3. `inflateCopy` 跨对象指针比较 UB 与 `gz*` 64 位偏移量溢出

在 `inflateCopy`（[`inflate.c:1383`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/inflate.c#L1383-L1387)，[PR #1369](https://github.com/madler/zlib/pull/1369)）中，`state->lencode >= state->codes && state->lencode <= state->codes + ENOUGH - 1` 用 `>=` / `<=` 比较指向 `.rodata` 段静态表 `lenfix` 的指针与堆数组 `state->codes`（C 标准未定义行为，ASan `pointer-compare` 直接报错），改成 `state->lencode == state->codes` 即可修复。全部 8 个上游问题汇总如下：

| 问题 | 位置 | 上游 |
| --- | --- | --- |
| `inflateCopy` 跨对象比较指针（UB） | [`inflate.c:1383`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/inflate.c#L1383) | [PR #1369](https://github.com/madler/zlib/pull/1369) |
| `gzungetc` 后 `gzseek` 有符号溢出 | [`gzlib.c:395`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzlib.c#L395-L403) | [PR #1361](https://github.com/madler/zlib/pull/1361) |
| `gzread` 出错后读悬空 `x.next` | [`gzread.c:271`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L271-L276) | [PR #1363](https://github.com/madler/zlib/pull/1363) |
| `gzread` / `gzgetc` 位置 `x.pos` 溢出 | [`gzread.c:413`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L413) | [PR #1405](https://github.com/madler/zlib/pull/1405) |
| `gzwrite` / `gzputc` 位置 `x.pos` 溢出 | [`gzwrite.c:230`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzwrite.c#L230) | [PR #1406](https://github.com/madler/zlib/pull/1406) |
| `gzoffset64` 未拒绝负的 `lseek` 结果 | [`gzlib.c:486`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzlib.c#L486-L489) | [PR #1404](https://github.com/madler/zlib/pull/1404) |
| `Z_FIXED` 下 `deflateBound` 偏小 | [`deflate.c:936`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L936) | [PR #1394](https://github.com/madler/zlib/pull/1394) |
| gzip `extra_len` 使 `deflateBound` 回绕 | [`deflate.c:901`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L901) | [PR #1360](https://github.com/madler/zlib/pull/1360) |

## 参考链接

- **Lean 4 证明与文档**：[`cla7aye15I4nd/zlib-f`](https://github.com/cla7aye15I4nd/zlib-f) · [项目总览](https://www.dataisland.org/zlib-f/zh/overview.html) · [树与共用缓冲区证明详解](https://www.dataisland.org/zlib-f/zh/proof/trees.html) · [完整问题清单](https://www.dataisland.org/zlib-f/zh/findings.html)
- **分区间核心证明源码**：[`trees.c.universal-dynamic.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-dynamic.lean)（`memLevel 5..9`）· [`trees.c.universal-overlay-mid.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-overlay-mid.lean)（`memLevel 3..4`）· [`DeflateOverlayTiny.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Math/DeflateOverlayTiny.lean) 与 [`deflate.c.engine.overlay-header-ref.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean)（`memLevel 1..2`）
- **上游 C 源码与规范**：[`madler/zlib` @ `99623ef7`](https://github.com/madler/zlib/tree/99623ef7097352da7993ba614161fd6a311e046e) · [RFC 1951 (DEFLATE 规范)](https://datatracker.ietf.org/doc/html/rfc1951)

<script src="/static/zlib-chase.js?v=20261118-zlib-chase-v6"></script>
