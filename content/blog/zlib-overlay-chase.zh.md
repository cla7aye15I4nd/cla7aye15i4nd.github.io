---
date: 2026-11-18
tags: [compression, verification, security, lean]
title: "零比特余量：zlib 缓冲区里的双指针追逐战"
description: "deflate.c 的一段注释论证 zlib 共用的缓冲区不会被覆盖，但这个论证是错的；真正的证明在最小配置下只剩零比特余量。"
---

# 零比特余量：zlib 缓冲区里的双指针追逐战

打开 [`zlib/trees.c:945`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L941-L946)，在 `compress_block` 的主循环末尾，有一条孤零零的断言：

```c
/* Check for no overlay of pending_buf on needed symbols */
#ifdef LIT_MEM
    Assert(s->pending < 2 * (s->lit_bufsize + sx), "pendingBuf overflow");
#else
    Assert(s->pending < s->lit_bufsize + sx, "pendingBuf overflow");
#endif
```

在所有生产环境的编译配置（`#ifndef ZLIB_DEBUG`）下，`Assert` 都会被预处理器直接抹成空白。无论是 `compress_block`、`send_bits` 还是 `put_byte`，在向 `s->pending_buf` 写入字节时，都**没有任何运行时边界检查**。

当我们用 Lean 4 对上游 `zlib 1.4` 做完整的内存安全形式化证明（见前文 [zlib × Lean](/blog/zlib-lean.zh.html)，代码库 [`cla7aye15I4nd/zlib-f`](https://github.com/cla7aye15I4nd/zlib-f)）时，绝大多数模块的证明都属于经典的系统验证问题：`inflate_fast` 环形窗口的回绕、`longest_match` 在未初始化数组上的哈希链有界性、流式状态机的跨调用不变量。唯独 `trees.c` 的第 945 行是个例外。证明这条在发布版里被删掉的 `Assert` 永远不会被触发，成了整个 `deflate` 证明里最硬的一块骨头——而在拆解它的过程中，我们发现 `deflate.c` 作者自己写下的那段四十行“安全性证明”，在逻辑上其实是错的。

更有意思的是故事的结局：`trees.c` 里这场看似随时会撞车的裸奔指针追逐，在 `memLevel = 1` 下以**零比特证明余量**惊险收官（这也引出了一个值得深挖的问题：物理执行中真的能构造出零比特擦肩而过的输入吗？）；反倒是 `zlib` 里其他看起来平平无奇的代码，在同一套形式化证明的穷追猛打下爆出了 **8 个真实的 Bug**。

## 同一个缓冲区里的追逐战

为了省内存，`deflate` 没有给 LZ77 中间符号流和最终 [DEFLATE](https://datatracker.ietf.org/doc/html/rfc1951) 压缩比特流分别申请缓冲区。相反，`deflateInit2_`（[`deflate.c:463–520`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L463-L520)）只分配了一块大小为 `4B` 字节的 `pending_buf`——其中 $B = \mathrm{lit}\_\mathrm{bufsize} = 2^{\mathrm{memLevel} + 6}$，取值从 `memLevel = 1` 时的 $128$ 字节一直到 `memLevel = 9` 时的 $32{,}768$ 字节（默认 `memLevel = 8` 为 $16{,}384$）——然后把符号缓冲指针 `sym_buf` 直接指到了这块内存四分之一的位置上：

```c
s->lit_bufsize = 1 << (memLevel + 6); /* 默认 16K 个元素 */
...
s->pending_buf = (uchf *) ZALLOC(strm, s->lit_bufsize, LIT_BUFS); /* 4 * B 字节 */
s->pending_buf_size = (ulg)s->lit_bufsize * 4;
...
s->sym_buf = s->pending_buf + s->lit_bufsize;
s->sym_end = (s->lit_bufsize - 1) * 3;
```

在扫描输入期间，匹配器通过 `_tr_tally`（[`trees.c:1095–1119`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1095-L1119)）从偏移 $B$ 开始往 `sym_buf` 里记录至多 $n \le B - 1$ 个符号。每个符号固定占 **3 个字节（24 bits）**：2 字节的距离 `dist`（字面量为 $0$，匹配为 $1 \dots 32{,}506$）加上 1 字节的 `lc`（字面量字符或 `匹配长度 - 3`）。

当一个块收集满、调用 `_tr_flush_block`（[`trees.c:997–1089`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L997-L1089)）刷出时，待输出字节队列已被排空（`pending = 0`），16 位寄存器 `bi_buf` 里至多残留 `bi_valid <= 7` 个上一块未凑够整字节的比特。随后，两个游标开始在同一个 `4B` 数组里同时从左向右狂奔：

- **逃跑者（读指针 `B + 3k`）**：起跑线在偏移 $B$（即 $8B$ bits）处。`compress_block` 每消费第 $k$ 个符号，就从 `[B + 3k, B + 3k + 3)` 读走 3 个字节，使“未读符号”的左边界向右推进 **+24 bits**。
- **追逐者（写指针 `8 * pending + bi_valid`）**：从偏移 $0$ 附近出发，先一口气写出整个块的头部（Block Header），随后每编码一个符号 $k$，就向前推进 `cost(sym_k)` 个比特。

你可以点击下方的 **▶ 播放** 或直接拖拽图表，对比 **01 · 固定编码**、**02 · 动态块前置突进** 与 **03 · 假想无约束 48b** 三种情形下双指针的距离变化：

<div class="zc-widget" data-zc="race" data-lang="zh"></div>

由于 `send_bits`（[`trees.c:274–285`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L274-L285)）在 `bi_valid + length > 16` 时会一次性向 `pending_buf` 刷入两个字节（16 bits），要想保证任何一次写入都碰不到 `B + 3k` 处的下一个未读符号，只需始终维持如下**前缀余量不变量**：

$$
8 \cdot \mathrm{pending} + \mathrm{bi}\_\mathrm{valid} + 15 \le 8(B + 3k) \qquad \forall k \in \{0, \dots, n\}.
$$

## 等等——追尾难道不只是把压缩结果写坏吗？

以漏洞挖掘的视角看，在花大力气研究这条不追尾性质之前，必须先问一个定性问题：**就算 `s->pending` 真的追上了 `s->lit_bufsize + sx`，最坏后果是什么？**

如果后果仅仅是读到了被覆盖的符号、吐出一串解压失败的乱码，那它只是一个功能正确性问题，根本威胁不到内存安全。但往 `Assert` 上方看二十行（[`trees.c:913–939`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L913-L939)）：

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

其中 `d_code` 定义在 [`deflate.h:320–321`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.h#L320-L321)，是一个没有任何边界检查的查表宏，直接索引 `.rodata` 段里长度为 **512 字节** 的静态常量表 `const uch _dist_code[512]`：

```c
#define d_code(dist) \
   ((dist) < 256 ? _dist_code[dist] : _dist_code[256+((dist)>>7)])
```

对于 `_tr_tally` 正常记录的合法匹配，`1 <= dist <= MAX_DIST <= 32506`，减一后至多为 `32505 <= 32767`，因此 `256 + ((dist - 1) >> 7)` 最大只到下标 `511`——严丝合缝停在 `_dist_code[512]` 的最后一个字节内。

但一旦写出的压缩比特流追尾覆盖了尚未读取的符号，`dist` 就变成了由压缩流内容决定的任意 16 位无符号整数！只要它的值落在 `32769 .. 65535`（`0x8001 .. 0xffff`）之间，就会进入 `else` 分支，把 `256 + ((dist - 1) >> 7)` 推高到 **`512 .. 767`**——直接在只读数据段上越界读取 `_dist_code` 之后的 **256 个字节**！更糟的是，如果越界读出的脏字节大于 `60`，紧接着的 `send_code(s, code, dtree)` 和 `extra_dbits[code]` 又会对 `dyn_dtree[61]` 和 `extra_dbits[30]` 触发二次越界读，甚至把乱码码长送进 `send_bits` 触发移位未定义行为。

拖动下方的 16 位 `dist` 滑块越过 `32,768`，可以直观看到整条越界链是如何被点燃的：

<div class="zc-widget" data-zc="oob" data-lang="zh"></div>

换句话说，**在 `deflate` 里，信息论与编码长度直接替内存安全站岗**。不证明写指针追不上读指针，就不可能证明 `deflate` 没有内存越界。

## `deflate.c` 注释里的错误证明

`zlib` 的作者当然知道把两个缓冲区叠在一起有多刺激。于是在 [`deflate.c:465–502`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L465-L502) 分配 `pending_buf` 的代码正上方，作者专门写了一段长达 38 行的数学证明。前半段分析的是 **固定（Fixed）Huffman 块**：

> *最长的固定长度码是 8 位加 5 位附加位……最长的固定距离码是 5 位加 13 位附加位……因此固定编码下一对长度/距离至多占 31 位。每消费一个符号，读指针前进 3 字节（24 位），而写指针至多写出 31 位。写指针离未读符号最近的时刻，就出现在最后一个符号写出之前。*

对于 **固定块**，这段推理无懈可击：因为**每一个单独的符号**封顶就是 $31$ bits，每步最多净追近 $+7$ bits，安全余量单调递减，最危险的点必然在块末尾。哪怕取最小的 `memLevel = 1`（$B = 128, n = 127$），算上入口残留的 7 bits 和 3 bits 块头，`pending` 最大也只到 $494$ 字节，而最后一个符号位于 $128 + 3 \times 127 = 509$ 字节。

真正精彩的部分在接下来的 [`deflate.c:496–502`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L496-L502)——作者试图把结论推广到 **动态（Dynamic）Huffman 块**：

```c
/* That latter condition then assures that the above analysis also covers all
 * dynamic blocks. A dynamic-code block will only be chosen to be emitted if it
 * has fewer bits than a fixed-code block would for the same set of symbols.
 * Therefore its average symbol length is assured to be less than 31. So the
 * compressed data for a dynamic block also cannot overwrite the symbols from
 * which it is being constructed.
 */
```

用安全审计的眼光读一遍这四句话：**这个推论是完全错误的。**

“整块的**平均**符号长度小于 31”，根本推不出“块内每一个**前缀**都不会追尾”：

1. **动态块在读第 0 个符号前，要先交一笔巨额“过路费”。** 固定块只写 3 bits 头部就开始读符号；动态块则要先调用 `send_all_trees`（[`trees.c:830–853`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L830-L853)）把两棵 Huffman 树和码长树完整序列化进 `pending_buf`。最坏情况下，光这个头部就高达 $14 + 19 \times 3 + (286 + 30) \times 7 = \mathbf{2{,}283\text{ bits}}$——此时 `sym_buf` 连一个字节都还没腾出来！
2. **动态块单个符号最高可达 48 bits，而不是 31 bits。** 两棵动态树的最大码长都是 15 bits，因此一个匹配最多耗费 $15 + 5 + 15 + 13 = \mathbf{48\text{ bits}}$——单步就能净追近 $+24$ bits，追击速度是固定块的 3 倍以上。
3. **长编码可以被全部前置（Front-loading）。** 设想一个块的前 $k$ 个符号全是罕见超长距离匹配（每个 42–48 bits），而后 $n - k$ 个符号全是高频重复字面量 `'A'`（每个仅 **1 bit**！）。算总账时，动态块总体积远小于固定块（`opt_lenb < static_lenb`），`_tr_flush_block` 毫不犹豫地选择输出动态块；但在前 $k$ 个符号期间，写指针正以两倍速向读指针猛扑——也就是前面交互演示 **02 · 动态块前置突进** 里在中途出现的那个深谷！

当时推进到这里，我们立刻停下了手里的 Lean 证明，切换成漏洞利用模式：把参数调到最小的 `memLevel = 1`（$B = 128$），此时整个起跑优势只有 $8 \times 128 = \mathbf{1{,}024\text{ bits}}$——连头部理论上限 $2{,}283$ bits 的一半都不到！只要在块首塞满罕见匹配，块尾垫满 1-bit 字面量压低 `opt_lenb`，岂不是当场就能打穿 `sym_buf`？

然而我们构造的所有输入全都撞上了一堵无形的墙。为了搞清楚到底是谁在暗中保护 `zlib`，我们被迫在 Lean 4 里证明了三道越来越锋利的数学防线。

## 挡在漏洞利用面前的三道数学防线

为了防御攻击者把所有昂贵符号全部排在块最前面的极端排布，我们不能依赖符号的顺序。定义整块的 **符号超额位（excess）**：

$$
\mathrm{excess} = \sum_{i=0}^{n-1} \max\big(0,\, \mathrm{cost}(s_i) - 24\big).
$$

任何不超过 $24$ bits 的符号只会帮读指针拉开距离；哪怕攻击者把所有 $\mathrm{cost} > 24$ 的符号全都集中堆在块开头，任意前 $k$ 个符号的总代价也绝不会超过 $24k + \mathrm{excess}$。算上入口残留的 `bi_valid <= 7`、3 bits 块类型标记和 15 bits 寄存器缓冲余量（合计 $7 + 3 + 15 = 25$ bits），只要满足下面这条与顺序无关的预算不等式，任意前缀 $k$ 都绝不会追尾：

$$
\mathrm{header} + \mathrm{excess} + 25 \le 8B.
$$

为什么攻击者凑不出突破 $8B$ 的输入？因为 **在 Huffman 树里，长编码是用总频数买来的**：想让某个符号被挤到第 15 层，同一个块里就必须有足够多的其他符号在连续 15 轮二叉树合并中在权重上压过它。

### 第一道墙：`memLevel 5..9`（$B \ge 2048$）与 `6.257` 斜率

从深度为 $l$、频数为 $f \ge 1$ 的叶子一路向根节点回溯：由于 Huffman 算法每一步都挑当前最轻的两个节点合并，路径上每一层挂着的兄弟子树都会迫使整棵树的总权重按斐波那契数列增长，大约满足 $W \gtrsim f \cdot F_{l+1}$。即便考虑树深超过 15 层后 `gen_bitlen`（[`trees.c:583–593`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L583-L593)）强制截断码长、为恢复 Kraft 等式 $\sum 2^{-l_i} = 1$ 而拉长部分浅层节点的最坏损耗（[`trees.c.heap.gbfibpush.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.heap.gbfibpush.lean)），我们在 Lean 中对全部 286 个字面量/长度符号与 30 个距离符号求和，证明了：

$$
\mathrm{excess} \le 6.257 \cdot (n + 3),
$$

其中 $+3$ 来自块结束符 `END_BLOCK` 以及树不足两片叶子时补入的至多两个占位符。因为 $n \le B - 1$，$B$ 每增加 1 就提供 **8 bits** 的起步空间，而至多消耗 **6.257 bits** 的超额位。加上 2,283 bits 的头部上界，从 $B = 1{,}332$ 往上预算恒成立，覆盖 `memLevel` 5 到 9：在 $B = 2{,}048$（$8B = 16{,}384$）处，$2{,}283 + \lceil 6.257 \times 2{,}050 \rceil + 25 = 15{,}135 \le 16{,}384$。

但把 `memLevel = 4`（$B = 1{,}024, 8B = 8{,}192$）代进去试试：

$$
2{,}283 + 6.257 \times 1{,}026 + 25 = 8{,}728 > 8{,}192.
$$

通用上界**当场超支 536 bits**！

### 第二道墙：`memLevel 3..4`（$B = 512, 1024$）与 $F_{17} = 1{,}597$ 阈值

为什么 $6.257$ 的斜率在 $B = 1{,}024$ 处算炸了？因为它替 `gen_bitlen` 的 15 位截断修复交了“保护费”。

仔细算一下 $B \le 1{,}024$ 时两棵数据树的最大总频数 $W$：块内至多记录 $B - 1 \le 1{,}023$ 个符号，加上 `END_BLOCK` 和至多两个补位叶子，$W \le B + 2 \le 1{,}026$。而一棵 Huffman 树要想长出**哪怕一个**深度超过 15 的节点，它的父节点深度至少是 15，这迫使整棵树的总权重至少达到：

$$
F_{16} + F_{15} = F_{17} = \mathbf{1{,}597}.
$$

因为 $1{,}026 < 1{,}597$，**在 `memLevel <= 4` 时，`gen_bitlen` 的码长截断修复循环在两棵数据树上永远不会执行**（`overflow` 恒等于 0）！每一个码长都是未经扭曲的真实树深，严格满足更强的斐波那契不等式 $f \cdot F_{l+1} + F_l \le W$。在 `zlib` 真实的附加位表上重新求解整数上界，`excess` 在 $B = 1{,}024$ 时骤降到 $3{,}678$ bits（总计 $5{,}986 \le 8{,}192$），在 $B = 512$ 时降到 $1{,}777$ bits：

$$
2{,}283 + 1{,}777 + 25 = 4{,}085 \le 4{,}096.
$$

在 `memLevel = 3` 下，整个 2 KB 缓冲区的最坏预算距离撞墙只剩 **11 bits**——不到两个字节。

在下方切换 `memLevel` 并拖动目标深度 $l$，可以看到最轻斐波那契脊柱与 $1{,}597$ 阈值是如何锁死树深的：

<div class="zc-widget" data-zc="fib" data-lang="zh"></div>

### 第三道墙：`memLevel 1..2`（$B = 128, 256$）与证明层的零比特余量

来到 `memLevel = 2`（$B = 256, 8B = 2{,}048$）和 `memLevel = 1`（$B = 128, 8B = 1{,}024$），就算 `excess = 0`，光是一个 2,283 bits 的头部上界就已经把整个 $8B$ 起步空间彻底击穿（$2{,}283 > 2{,}048 > 1{,}024$）！为什么光写树头本身没有直接把 `sym_buf` 覆盖掉？

这里有两个约束像齿轮一样咬合在一起，少任何一个都不成立：

1. **极小块长不出深树，直接饿死了头部字母表。** 由 $f \cdot F_{l+1} + F_l \le W$，任何实际出现的码长 $l$ 都必须满足 $F_{l+2} \le B + 2$。当 $B = 256$（$W \le 258 < 377 = F_{14}$）时，数据码长绝不超过 **11 bits**，因此 `scan_tree` 扫描出的码长序列里根本不会出现符号 `12..15`；当 $B = 128$（$W \le 130 < 144 = F_{12}$）时，数据码长绝不超过 **9 bits**，符号 `10..15` 全部从 `bl_tree` 中消失！利用 `build_tree` 在剩余 13 个码长符号上相对于一组显式完全参考前缀码的最优性（[`deflate.c.engine.overlay-header-ref.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean)），就能把当前块的真实头部大小严格控制在非零树项个数的线性函数以内。
2. **`deflate.c` 注释里的 `opt_lenb < static_lenb`，以正确的方式复活了。** 还记得前面被我们判了死刑的那句注释吗？“因为动态块比固定块短，所以平均码长 $< 31$”虽然不能直接推导前缀安全，但 `_tr_flush_block` 在走入动态块分支前，确实执行了 `if (static_lenb <= opt_lenb) opt_lenb = static_lenb;`（[`trees.c:1035–1037`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1035-L1037)）！这为我们提供了一条货真价实的全局字节代价不等式：

$$
\left\lfloor \frac{\mathrm{header} + \mathrm{opt}\_\mathrm{payload} + 10}{8} \right\rfloor + 1 \le \left\lfloor \frac{\mathrm{static}\_\mathrm{payload} + 10}{8} \right\rfloor.
$$

这就是封死漏洞利用的“二律背反”：攻击者要想把 `header` 撑大，就必须在 `dyn_ltree` 和 `dyn_dtree` 里点亮大量零散的不同符号，打断 `scan_tree`（[`trees.c:722–766`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L722-L766)）用游程编码 `17`、`18` 压缩连续零的能力；但点亮大量低频符号的同时，`opt_payload` 相对于固定编码 `static_payload` 的优势就会迅速蒸发——一旦 `opt_lenb` 追平 `static_lenb`，`_tr_flush_block` 当场就会放弃动态块，改用绝对安全的固定块输出！

在 Lean 4 中，我们用一份线性组合证书把斐波那契码长上界、Kraft 等式、参考前缀码头部界与 `opt_lenb < static_lenb` 选择条件合成为最终不等式：

- 当 $B = 256$（$8B = 2{,}048$）时：$\mathrm{header} + \mathrm{excess} \le 2{,}023 \implies 2{,}023 + 25 = \mathbf{2{,}048 \le 2{,}048}$。
- 当 $B = 128$（$8B = 1{,}024$）时：$\mathrm{header} + \mathrm{excess} \le 999 \implies 999 + 25 = \mathbf{1{,}024 \le 1{,}024}$。

在最小的两个缓冲区配置上，证明给出的安全上界与 $8B$ 预算严丝合缝地贴在一起——**零比特证明余量**：

<div class="zc-widget" data-zc="regimes" data-lang="zh"></div>

三段合在一起，覆盖了全部 9 个 `memLevel`：在任何一个块里，写指针都追不上下一个未读符号。

## 追问：这个“零比特余量”，真的能在 C 里构造出来吗？

看到 $999 + 25 = 1{,}024 \le 1{,}024$，一个最自然的好奇是：**在真实的 `zlib` C 代码里，真的存在某个 `memLevel = 1` 的输入，能让写指针在运行中贴到距离下一个未读符号 0 比特的刀尖上吗？还是说，“零余量”只是证明方法本身的产物？**

简短的回答：**我们没能构造出来，最接近的一次也还差三百多比特。** 这里的 `0 bits` 是**证明上界的余量**：证明给出的上界恰好等于预算，但它是一个上界，比真实的最坏情况更松。注意，下面的结果来自搜索，不是证明：搜索没找到，不等于不存在。

不妨直接在真实的 `zlib/trees.c` 上动手做一次极限构造。把 `opt_lenb < static_lenb` 展开成比特不等式：

$$
\mathrm{header} \le P_{\mathrm{static}} - P_{\mathrm{opt}} + 6,
$$

其中 $P_{\mathrm{static}}$ 和 $P_{\mathrm{opt}}$ 分别是静态树与动态树编码全体符号的载荷位数。这里藏着一个对构造者非常有利的代数细节：匹配的附加位（`extra_lbits` 与 `extra_dbits`，最高 $5 + 13 = 18$ bits）在 $P_{\mathrm{static}}$ 和 $P_{\mathrm{opt}}$ 两边**完全相同**（[`trees.c:574–575`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L574-L575)），相减时直接抵消！因此，要想在 $n \le 127$ 个符号里攒出尽可能多的“头部预算补贴”，最高效的“攒钱符号（Banker）”并不是 9 位静态字面量（每个最多省 $9 - 1 = 8$ bits），而是大量重复长度码 `284`（静态 8 bits）配距离码 `29`（静态 5 bits）的超长匹配——当它占绝对多数时，两棵动态树都给它分配 1 bit 编码，**每重复一次就能净赚 $13 - 2 = +11$ bits 的头部预算**！

但一旦你往这 127 个槽位里塞入零散的单次符号——无论是为了打断 `scan_tree` 的连续零游程（撑大 `header`），还是为了把生僻匹配挤到第 8–9 层（撑大 `excess`；注意 $B = 128$ 下码长封顶为 9，单符号最高 $9 + 5 + 9 + 13 = 36$ bits，即每符号至多贡献 $+12$ bits 超额位）——两笔反噬会同时发生：你不仅少掉了几个 $+11$ bits 的攒钱槽位，还会把攒钱符号自身的动态码长从 $1+1 = 2$ bits 顶高到 $3$ 或 $4$ bits，瞬间蒸发掉上百比特的预算。

我们把上游 `trees.c` 直接编译进一个模拟退火（Simulated Annealing）搜索程序：符号序列直接交给 `_tr_tally` 记录，再走真实的 `build_tree`、`send_all_trees` 与 `compress_block` 输出路径。在 `memLevel = 1`（$B = 128$，入口预置最坏残留 `bi_valid = 7`，并把所有高代价匹配排在最前）下，对数百万组满足 `opt_lenb < static_lenb` 的符号块做了搜索：

- **`header + excess` 在约 `686` bits 处见顶**（例如 `header = 644`、`excess = 42`，此时 `opt_lenb = 327 < 328 = static_lenb` 已经卡到只差 1 字节翻车），算上 25 bits 固定开销后为 **`711 / 1,024` bits**——距离 1,024 bits 的红线依然留有 **313 bits** 的空间。
- 在 [`trees.c:945`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L945) 的 `Assert(s->pending < s->lit_bufsize + sx)` 处，运行时真实字节间距 `(lit_bufsize + sx) - pending` 最小也从未低于 **`+44` 字节**（对应前缀余量指标 `+336` bits，出现在 $k = 8$ 处）。

搜索到的最坏情况（`711`）和证明上界（`1,024`）之间这约 313 bits 的差距，来自证明为了能被机器检查而做的放松。最直观的一处在 C 代码本身：[`trees.c:913–915`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L913-L915) 是**先把第 $k$ 个符号的 3 个字节读进局部变量 `dist` 和 `lc`，再调用 `send_bits` 写出编码**，所以写第 $k$ 个符号时，下一个未读符号其实已经在 `B + 3(k + 1)`，比证明里用的 `B + 3k` 多出 24 bits。其余的差距来自头部的计费方式：证明用一组固定的参考前缀码给码长树计费，而真实的 `bl_tree` 会按当前块的码长分布自适应；`scan_tree` 对连续零的游程压缩也没有被完全利用。证明只需要不等式成立，不需要它是最紧的。

## 反转：那 `zlib` 真正出 Bug 的地方在哪？

做安全研究经常会遇到这种黑色幽默：你盯着一段连注释都写错了的高危内存复用循环死磕了好几个星期，结果发现斐波那契数列和块选择条件稳稳护住了它；转头去证旁边看似人畜无害的常规代码时，却接二连三踩中真正的内存错误。

在我们的 Lean 4 翻译模型中，任何可达的 C 未定义行为都会触发显式故障 `Fault.ub`（且主干严禁使用 `sorry`、`axiom`、`native_decide` 或 `bv_decide`）。为了把 `zlib.h` 中每一个公开函数在 `zlib 1.4`（提交 [`99623ef7`](https://github.com/madler/zlib/tree/99623ef7097352da7993ba614161fd6a311e046e)）上的安全定理全部证完，每一条冷门分支都必须向内核交账。整个过程中，我们在上游 `zlib` 中共发现了 **8 个真实缺陷**（[补丁目录](https://github.com/cla7aye15I4nd/zlib-f/tree/main/patches)）——其中 6 个是未定义行为或内存错误（均在真实 C 代码上通过 AddressSanitizer / UndefinedBehaviorSanitizer 复现），另外 2 个是 `deflateBound` 违背了 `zlib.h` 的输出长度上限承诺。

### 1. `Z_FIXED` 下 `deflateBound` 算小了输出上界（[`deflate.c:936`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c#L932-L940)，[PR #1394](https://github.com/madler/zlib/pull/1394)）

最戏剧性的一个 Bug 恰好又回到了 `_tr_flush_block`。`zlib.h` 承诺：只要调用者按 `deflateBound(strm, sourceLen)` 分配输出缓冲区，单次调用 `deflate(strm, Z_FINISH)` 就一定能一次性完成压缩并返回 `Z_STREAM_END`。

在默认的 `windowBits = 15, memLevel = 8` 下，`deflateBound_z` 返回的是一个极紧的上界（仅膨胀约 0.03%，即每 16,383 字节加 5 字节块头），它的底气是：万一 Huffman 编码把数据越压越大，`_tr_flush_block` 总能退回不压缩的 **存储块（Stored Block）** 兜底。但回头看一眼 [`trees.c:1047–1056`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c#L1047-L1056) 选择存储块的条件：

```c
if (stored_len + 4 <= opt_lenb && buf != (char*)0) {
    _tr_stored_block(s, buf, stored_len, last);
```

注意那个 `buf != (char*)0`！`buf` 指向窗口里的原始输入起点 `window + block_start`；如果在一个块还没填满 `16,383` 个符号之前，`fill_window` 就因为滑动窗口把旧数据挤出了 64 KiB 窗口（导致 `block_start < 0`），`FLUSH_BLOCK_ONLY` 传进来的 `buf` 就会变成 `NULL`——**存储块降级通道直接关闭**！而在 `Z_FIXED` 策略配合级别 1–3（`deflate_fast`）时，压缩器会贪婪地采纳远距离的 3 字节匹配，每个匹配耗费 **25 bits**（$7 + 5 + 13$），折合每输入字节 **8.33 bits**。一旦跨越窗口滑动，无法退回存储块的固定编码块就会实打实地比原始输入更长！

面对 $1{,}000{,}000$ 字节的真实输入（`windowBits = 15, memLevel = 8, Z_FIXED`），`deflateBound` 承诺只需 **`1,000,318` 字节**，而真实 C 代码实际需要多达 **`1,008,570` 字节**——单次 `deflate(Z_FINISH)` 因空间不足半途返回 `Z_OK`，直接打破了 API 契约（[Patch 0007](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0007-deflatebound-fixed-conservative.patch)）。

### 2. `gzread` 在部分读取失败后从悬空的旧 `x.next` 拷贝数据（[`gzread.c:271`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L271-L276)，[PR #1363](https://github.com/madler/zlib/pull/1363)）

当 `gzread` 以透明直通模式（`COPY`，处理非 gzip 原始文件）读取数据时，`gz_fetch` 调用 `gz_load` 填充 `state->out`：

```c
case COPY:      /* -> COPY */
    if (gz_load(state, state->out, state->size << 1, &(state->x.have)) == -1)
        return -1;
    state->x.next = state->out;
    return 0;
```

`gz_load` 内部循环调用系统调用 `read()`。如果第一次 `read()` 读出了一部分字节（使 `state->x.have > 0`），紧接着下一次 `read()` 返回 `-1` 报错，`gz_load` 会保留 `x.have` 里的已读字节数并返回 `-1`。于是 `gz_fetch` **在执行 `state->x.next = state->out` 之前就直接 `return -1` 退出了**！回到外层 `gz_read` 后，错误处理只在 `state->x.have == 0` 时中止；看到 `x.have > 0`，`gz_read` 照常从**过期的旧指针 `state->x.next`** 处 `memcpy` 走 `x.have` 个字节——当场在堆上触发输出缓冲区越界读（ASan 于 [`gzread.c:369`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/gzread.c#L369) 捕获；[Patch 0003](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0003-gzread-partial-copy-read-error.patch)）。修复只需把 `state->x.next = state->out;` 往上提两行。

### 3. `inflateCopy` 跨对象指针大小比较与 `gz*` 64 位有符号溢出

在 `inflateCopy`（[`inflate.c:1383–1387`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/inflate.c#L1383-L1387)，[PR #1369](https://github.com/madler/zlib/pull/1369)，[Patch 0001](https://github.com/cla7aye15I4nd/zlib-f/blob/main/patches/0001-inflate-copy-pointer-equality.patch)）中，代码用 `>=` 和 `<=` 判断 `state->lencode` 是否指向堆上的 `state->codes` 数组内部：

```diff
-    if (state->lencode >= state->codes &&
-        state->lencode <= state->codes + ENOUGH - 1) {
-        copy->lencode = copy->codes + (state->lencode - state->codes);
+    if (state->lencode == state->codes) {
+        copy->lencode = copy->codes;
```

当流刚刚解完一个固定 Huffman 块时，`state->lencode` 指向的是 `.rodata` 段里的静态表 `lenfix`，而 `state->codes` 在堆上。在 C 语言标准中，对指向不同对象的指针使用 `>=` / `<=` 属于直接的未定义行为（ASan `pointer-compare` 直接报错），而且逻辑上 `lencode` 在动态块下本来就只可能等于 `state->codes` 首地址。

其余几个 Bug 则集中在 `gz*` 文件接口的有符号 64 位偏移量 `z_off64_t` 算术溢出与 32 位头部长度回绕上：

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

## 小结与参考链接

给一段写了三十多年的 C 代码做形式化证明，最深刻的体会是：**人类的直觉总是盯错地方。** 每个读过 `trees.c` 的人都会被 `pending_buf` 与 `sym_buf` 的同缓冲追逐吓一跳，然后写一段看似合理的“平均值小于 31”来安慰自己；Fuzzer 可以跑上百亿次迭代，却几乎不可能同时凑齐 `memLevel = 1` 的攒钱匹配直方图，或者在透明模式读了一半字节时恰好注入一次 `EIO`，又或者在文件第 0 字节先调一次 `gzungetc` 再去 `gzseek`。

定理证明器没有直觉，也不会觉得错误处理分支枯燥。当 `deflate.c` 的注释试图用平均值蒙混过关时，Lean 内核会寸步不让，逼着你把斐波那契树、$F_{17} = 1{,}597$ 和 $B = 128$ 的零证明余量证书全部掏出来；而当 `gzread.c` 的错误处理路径少赋了一行 `state->x.next` 时，不变量当场就会在证明里断掉。

- **证明仓库与文档**：[`cla7aye15I4nd/zlib-f`](https://github.com/cla7aye15I4nd/zlib-f) · [项目总览](https://www.dataisland.org/zlib-f/zh/overview.html) · [树与共用缓冲区证明详解](https://www.dataisland.org/zlib-f/zh/proof/trees.html) · [完整问题清单](https://www.dataisland.org/zlib-f/zh/findings.html)
- **核心 Lean 4 证明源码**：[`trees.c.universal-dynamic.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-dynamic.lean)（`memLevel >= 5`）· [`trees.c.universal-overlay-mid.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/trees.c.universal-overlay-mid.lean)（`memLevel 3..4`）· [`deflate.c.engine.overlay-header-ref.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Proof/deflate.c.engine.overlay-header-ref.lean) 与 [`DeflateOverlayCertificate128W.lean`](https://github.com/cla7aye15I4nd/zlib-f/blob/main/ZlibF/Math/DeflateOverlayCertificate128W.lean)（`memLevel 1..2` 证书）
- **上游 C 源码与标准**：[`madler/zlib` @ `99623ef7`](https://github.com/madler/zlib/tree/99623ef7097352da7993ba614161fd6a311e046e)（[`trees.c`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/trees.c)、[`deflate.c`](https://github.com/madler/zlib/blob/99623ef7097352da7993ba614161fd6a311e046e/deflate.c)）· [RFC 1951 (DEFLATE 规范)](https://datatracker.ietf.org/doc/html/rfc1951)

<script src="/static/zlib-chase.js?v=20261118-zlib-chase-v2"></script>
