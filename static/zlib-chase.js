(() => {
  if (window.__zlibChaseLoadedV5) {
    window.__mountZlibChaseV5?.();
    return;
  }
  window.__zlibChaseLoadedV5 = true;

  const STYLE_ID = "zc-interactive-styles-v5";
  const CSS = `
.zc-widget {
  margin: 2.4rem 0;
  background: #f6f6f3;
  border: 1px solid #c8c8c6;
  color: #0a0a0a;
  font-family: var(--nan-sans, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif);
  font-size: 14px;
  line-height: 1.45;
  user-select: none;
  -webkit-user-select: none;
}
.zc-bar {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  justify-content: space-between;
  gap: 10px 16px;
  padding: 12px 16px;
  background: #eeeeec;
  border-bottom: 1px dashed #cfcfcc;
}
.zc-title-wrap {
  display: flex;
  flex-direction: column;
  gap: 2px;
}
.zc-kicker {
  font-family: Menlo, Monaco, Consolas, "Liberation Mono", monospace;
  font-size: 10.5px;
  letter-spacing: 0.06em;
  text-transform: uppercase;
  color: #6b6b68;
}
.zc-title {
  font-family: var(--nan-serif, Georgia, "Times New Roman", serif);
  font-size: 21px;
  line-height: 1.15;
  color: #0a0a0a;
}
.zc-controls {
  display: flex;
  flex-wrap: wrap;
  align-items: center;
  gap: 6px;
}
.zc-seg {
  display: inline-flex;
  flex-wrap: wrap;
  border: 1px solid #b8b8b4;
  background: #fbfbfa;
}
.zc-seg button,
.zc-btn {
  appearance: none;
  border: 0;
  background: transparent;
  color: #262626;
  font-family: Menlo, Monaco, Consolas, "Liberation Mono", monospace;
  font-size: 11.5px;
  line-height: 1.2;
  padding: 6px 10px;
  cursor: pointer;
  transition: background-color 120ms ease, color 120ms ease;
}
.zc-seg button + button {
  border-left: 1px solid #d0d0cc;
}
.zc-seg button:hover,
.zc-btn:hover {
  background: #e9e9e5;
}
.zc-seg button.is-active,
.zc-btn.is-active {
  background: #0a0a0a;
  color: #f6f6f3;
}
.zc-btn {
  border: 1px solid #b8b8b4;
  background: #fbfbfa;
}
.zc-btn:active,
.zc-seg button:active {
  transform: translateY(0.5px);
}
.zc-metrics {
  display: grid;
  grid-template-columns: repeat(4, minmax(0, 1fr));
  background: #fbfbfa;
  border-bottom: 1px dashed #cfcfcc;
}
.zc-metric {
  padding: 10px 14px;
  border-right: 1px dashed #d8d8d4;
  min-width: 0;
}
.zc-metric:last-child {
  border-right: 0;
}
.zc-metric-label {
  font-family: Menlo, Monaco, Consolas, "Liberation Mono", monospace;
  font-size: 10px;
  text-transform: uppercase;
  letter-spacing: 0.05em;
  color: #737370;
  margin-bottom: 3px;
}
.zc-metric-val {
  font-family: Menlo, Monaco, Consolas, "Liberation Mono", monospace;
  font-size: 13.5px;
  line-height: 1.3;
  font-weight: 600;
  font-variant-numeric: tabular-nums;
  color: #0a0a0a;
  white-space: normal;
  overflow-wrap: break-word;
}
.zc-metric-sub {
  font-family: Menlo, Monaco, Consolas, "Liberation Mono", monospace;
  font-size: 10.5px;
  color: #6e6e6a;
  margin-top: 2px;
  font-variant-numeric: tabular-nums;
}
.zc-val-danger { color: #b91c1c !important; }
.zc-val-warn   { color: #b45309 !important; }
.zc-val-safe   { color: #0f766e !important; }
.zc-stage {
  padding: 16px 18px 14px;
  background: #fbfbfa;
}
.zc-svg {
  display: block;
  width: 100%;
  height: auto;
  overflow: visible;
}
.zc-scrubber-row {
  display: flex;
  align-items: center;
  gap: 12px;
  padding: 10px 18px;
  background: #f2f2ee;
  border-top: 1px dashed #cfcfcc;
}
.zc-scrubber-row label {
  font-family: Menlo, Monaco, Consolas, "Liberation Mono", monospace;
  font-size: 11px;
  color: #52524e;
  white-space: nowrap;
  font-variant-numeric: tabular-nums;
}
.zc-range {
  flex: 1;
  accent-color: #0a0a0a;
  cursor: pointer;
  height: 4px;
}
.zc-note {
  padding: 12px 18px;
  background: #eeeeec;
  border-top: 1px dashed #cfcfcc;
  font-size: 13.5px;
  line-height: 1.6;
  color: #262624;
  user-select: text;
  -webkit-user-select: text;
}
.zc-note code {
  font-family: Menlo, Monaco, Consolas, "Liberation Mono", monospace;
  font-size: 12px;
  background: #e2e2de;
  padding: 1px 5px;
}
.zc-badge {
  display: inline-block;
  padding: 1px 6px;
  font-family: Menlo, Monaco, Consolas, "Liberation Mono", monospace;
  font-size: 10.5px;
  font-weight: 600;
  text-transform: uppercase;
  letter-spacing: 0.04em;
  margin-right: 6px;
}
.zc-badge-safe   { background: #d1fae5; color: #065f46; border: 1px solid #6ee7b7; }
.zc-badge-warn   { background: #fef3c7; color: #92400e; border: 1px solid #fcd34d; }
.zc-badge-danger { background: #fee2e2; color: #991b1b; border: 1px solid #fca5a5; }
.zc-badge-ink    { background: #0a0a0a; color: #f6f6f3; border: 1px solid #0a0a0a; }
.zc-anim-rect {
  transition: x 180ms cubic-bezier(0.22, 1, 0.36, 1), width 180ms cubic-bezier(0.22, 1, 0.36, 1), fill 180ms ease, opacity 180ms ease;
}
.zc-anim-x {
  transition: transform 180ms cubic-bezier(0.22, 1, 0.36, 1);
}
.zc-pipeline {
  display: grid;
  grid-template-columns: repeat(4, minmax(0, 1fr));
  gap: 10px;
  margin-bottom: 14px;
}
.zc-pipe-box {
  padding: 10px 12px;
  border: 1px solid #cfcfcc;
  background: #f6f6f3;
  font-family: Menlo, Monaco, Consolas, "Liberation Mono", monospace;
}
.zc-pipe-box.is-fault {
  border-color: #dc2626;
  background: #fef2f2;
}
.zc-pipe-step {
  font-size: 10px;
  color: #737370;
  text-transform: uppercase;
  margin-bottom: 4px;
}
.zc-pipe-expr {
  font-size: 13px;
  font-weight: 600;
  color: #0a0a0a;
  font-variant-numeric: tabular-nums;
}
.zc-pipe-detail {
  font-size: 11px;
  color: #575753;
  margin-top: 3px;
  font-variant-numeric: tabular-nums;
}
.zc-regime-bars {
  display: grid;
  gap: 14px;
}
.zc-bar-track {
  position: relative;
  height: 30px;
  background: repeating-linear-gradient(135deg, #f3f3ef 0, #f3f3ef 4px, #e9e9e4 4px, #e9e9e4 8px);
  border: 1px solid #c8c8c4;
  overflow: hidden;
}
.zc-bar-seg {
  position: absolute;
  top: 0;
  bottom: 0;
  transition: left 240ms cubic-bezier(0.22, 1, 0.36, 1), width 240ms cubic-bezier(0.22, 1, 0.36, 1), background-color 180ms ease;
}
.zc-wall-line {
  position: absolute;
  top: -4px;
  bottom: -4px;
  width: 2px;
  background: #0a0a0a;
  z-index: 4;
}
.zc-legend {
  display: flex;
  flex-wrap: wrap;
  gap: 10px 18px;
  margin-top: 10px;
  font-family: Menlo, Monaco, Consolas, "Liberation Mono", monospace;
  font-size: 11px;
  color: #4a4a46;
}
.zc-legend span {
  display: inline-flex;
  align-items: center;
  gap: 6px;
}
.zc-swatch {
  width: 10px;
  height: 10px;
  border: 1px solid rgba(0,0,0,0.25);
  display: inline-block;
}
@media (max-width: 760px) {
  .zc-metrics,
  .zc-pipeline {
    grid-template-columns: repeat(2, minmax(0, 1fr));
  }
  .zc-metric:nth-child(2) {
    border-right: 0;
  }
  .zc-metric:nth-child(1),
  .zc-metric:nth-child(2) {
    border-bottom: 1px dashed #d8d8d4;
  }
}
`;

  const injectStyles = () => {
    if (!document.getElementById(STYLE_ID)) {
      const style = document.createElement("style");
      style.id = STYLE_ID;
      style.textContent = CSS;
      document.head.appendChild(style);
    }
  };

  const FIB = [0, 1];
  for (let i = 2; i <= 22; i++) FIB.push(FIB[i - 1] + FIB[i - 2]);

  const getLang = (el) => {
    if (el.dataset.lang) return el.dataset.lang;
    return (document.documentElement.lang || "en").toLowerCase().startsWith("zh") ? "zh" : "en";
  };

  /* ==========================================================================
   * WIDGET 0: TWO-PASS BLOCK PIPELINE (How deflate Actually Works!)
   * ========================================================================== */
  const mountPipeline = (el) => {
    const zh = getLang(el) === "zh";
    let step = 0;

    const stages = [
      {
        tab: zh ? "阶段 1 · LZ77 扫描与记录" : "Pass 1 · Scan & Tally",
        fn: "_tr_tally()",
        fnSub: "trees.c:1095–1119",
        inLabel: zh ? "输入窗口字节流" : "INPUT WINDOW BYTES",
        freqLabel: zh ? "同步累加频率表" : "LIVE FREQ COUNTERS",
        modeLabel: zh ? "为什么还不能输出比特？" : "WHY NOT EMIT BITS NOW?",
        modeVal: zh ? "还不知道整块词频!" : "Need full-block Freq[]",
        bufState: "tally",
        note: zh
          ? `<span class="zc-badge zc-badge-ink">第 1 遍：只记符号，不写比特</span> <code>deflate</code> 扫描原始输入（如 <code>"abcde_abcde_!"</code>），每识别出一个<strong>字面量</strong>（如 <code>'a'</code> → <code>[0, 0, 'a']</code>）或一次<strong>回溯匹配</strong>（如“往回 6 字节复制 5 字节” → <code>[6, 0, 2]</code>），就调用 <code>_tr_tally</code> 把固定的 <strong>3 字节三元组（24 bits）</strong> 顺序写进共享缓冲区的后 3/4（从偏移 <code>B</code> 开始的 <code>sym_buf</code>），同时给 <code>dyn_ltree</code> / <code>dyn_dtree</code> 的词频计数器加一。此时前 1/4（<code>[0 .. B)</code>）完全空置！`
          : `<span class="zc-badge zc-badge-ink">PASS 1 · RECORD SYMBOLS ONLY</span> Why can't <code>deflate</code> emit Huffman bits as bytes arrive? Because optimal Huffman code lengths depend on symbol frequencies across the <em>entire</em> block! So Pass 1 (<code>_tr_tally</code>) parks each literal (<code>[0, 0, 'a']</code>) or LZ77 match (<code>[dist_lo, dist_hi, len-3]</code>) as a fixed <strong>3-byte triple (24 bits)</strong> starting at offset <code>B</code> (<code>sym_buf</code>), while incrementing <code>Freq[]</code> counters. Bytes <code>[0 .. B)</code> remain completely empty.`,
      },
      {
        tab: zh ? "阶段 2 · 建树与三选一" : "Interlude · Build & Choose",
        fn: "_tr_flush_block()",
        fnSub: "trees.c:997–1089",
        inLabel: zh ? "块已收集满 (n ≤ B−1)" : "BLOCK FULL (n ≤ B−1)",
        freqLabel: zh ? "生成两棵动态树 + 码长树" : "BUILD 3 HUFFMAN TREES",
        modeLabel: zh ? "三种格式比总字节数" : "CHEAPEST OF 3 FORMATS",
        modeVal: "opt_lenb < static_lenb",
        bufState: "choose",
        note: zh
          ? `<span class="zc-badge zc-badge-safe">决出最省格式</span> 当收集满 <code>B - 1</code> 个符号（或外部请求刷新）时，<code>_tr_flush_block</code> 根据刚刚统计好的词频建出当前块专属的<strong>动态字面量/长度树</strong>、<strong>动态距离树</strong>以及压缩树头用的<strong>码长树 <code>bl_tree</code></strong>，然后精确算出三种块格式的总字节数：① 原样拷贝的<strong>存储块</strong>；② 免树头、用 RFC 1951 死表的<strong>固定块</strong>（<code>static_lenb</code>）；③ 带树头、量身定制的<strong>动态块</strong>（<code>opt_lenb</code>）。只有当动态块严格最省时，才会进入动态块分支！`
          : `<span class="zc-badge zc-badge-safe">PICK CHEAPEST FORMAT</span> Once <code>sym_buf</code> fills (up to <code>B - 1</code> symbols), <code>_tr_flush_block</code> uses <code>Freq[]</code> to construct custom literal/length and distance Huffman trees plus a tiny 19-symbol tree (<code>bl_tree</code>) to compress their code lengths. It then compares exact byte sizes of <strong>Stored</strong> (raw copy), <strong>Fixed</strong> (<code>static_lenb</code>, hardcoded RFC 1951 codes), and <strong>Dynamic</strong> (<code>opt_lenb</code>, custom trees + header)—and picks Dynamic <em>only</em> if it strictly beats both.`,
      },
      {
        tab: zh ? "阶段 3 · 先写动态树头" : "Pass 2a · Emit Tree Header",
        fn: "send_all_trees()",
        fnSub: "trees.c:830–853",
        inLabel: zh ? "未读符号仍在 [B .. B+3n)" : "UNREAD SYMS AT [B .. B+3n)",
        freqLabel: zh ? "序列化树表到开头" : "SERIALIZE TREES TO [0..)",
        modeLabel: zh ? "起跑优势被吃掉一截" : "HEAD START CONSUMED",
        modeVal: zh ? "pending 向 B 推进!" : "pending moves toward B",
        bufState: "header",
        note: zh
          ? `<span class="zc-badge zc-badge-warn">先交过路费</span> 解压端事先不知道你定制的动态树长什么样，因此在编码第 0 个符号之前，<code>send_all_trees</code> 必须先把 3 bit 块标记和整套动态树描述从偏移 <code>0</code> 开始写进 <code>pending_buf</code>！注意此时 <code>sym_buf</code> 里的符号一个都还没读（读指针停在 <code>B</code>），写指针 <code>pending</code> 已经单方面吃掉了 <code>[0 .. B)</code> 起跑优势的一大截。`
          : `<span class="zc-badge zc-badge-warn">UPFRONT HEADER TAX</span> Because the decoder doesn't know our custom trees yet, <code>send_all_trees</code> must serialize the 3-bit block tag and the entire compressed tree description starting at byte <code>0</code> of <code>pending_buf</code> <em>before</em> reading symbol 0! The read cursor is still frozen at <code>B</code>, so this header comes straight out of our <code>B</code>-byte head start.`,
      },
      {
        tab: zh ? "阶段 4 · 原地双指针追逐!" : "Pass 2b · In-Place Chase!",
        fn: "compress_block()",
        fnSub: "trees.c:908–950",
        inLabel: zh ? "每步读 3B (释放 24 bits)" : "READS 3B (+24b FREED)",
        freqLabel: zh ? "每步写 1..48 bits" : "WRITES 1..48 BITS",
        modeLabel: zh ? "核心安全问题" : "THE SAFETY QUESTION",
        modeVal: "pending < B + 3k ?",
        bufState: "chase",
        note: zh
          ? `<span class="zc-badge zc-badge-danger">生死追逐</span> 现在 <code>compress_block</code> 循环 <code>k = 0 .. n-1</code>：每轮先从 <code>B + 3k</code> 读走 3 字节符号（读边界右移 <strong>+24 bits</strong>），查动态树与附加位表后，调用 <code>send_bits</code> 往 <code>pending</code> 写出 <strong>1 到 48 bits</strong>！只要遇到超过 24 bits 的罕见长匹配，写指针就在缩小差距；遇到短字面量，读指针就拉开差距。全过程没有任何边界检查——如果写指针在任意时刻追上 <code>B + 3k</code>，未读符号就会被当场覆写！`
          : `<span class="zc-badge zc-badge-danger">THE IN-PLACE RACE</span> Finally, <code>compress_block</code> loops <code>k = 0 .. n-1</code>: read 3 bytes from <code>B + 3k</code> (moving the unread boundary right by <strong>+24 bits</strong>), then emit that symbol's Huffman code + extra bits (<strong>1 to 48 bits</strong>) at <code>pending</code>. Whenever a symbol costs &gt; 24 bits, the writer gains ground; whenever it costs &lt; 24 bits, the reader pulls away. Nothing checks bounds at runtime.`,
      },
    ];

    el.innerHTML = `
      <div class="zc-bar">
        <div class="zc-title-wrap">
          <span class="zc-kicker">${zh ? "交互导览 01 · 原算法全貌：为什么两个指针会撞进同一个数组？" : "INTERACTIVE 01 · HOW A ZLIB BLOCK WORKS (TWO PASSES IN ONE ARRAY)"}</span>
          <span class="zc-title">${zh ? "从原始字节到共享缓冲区 pending_buf[0 .. 4B)" : "From Raw Input Bytes to the Shared pending_buf[0 .. 4B) Array"}</span>
        </div>
        <div class="zc-controls">
          <div class="zc-seg" data-role="p-tabs">
            ${stages.map((s, i) => `<button type="button" data-i="${i}" class="${i === 0 ? "is-active" : ""}">${s.tab}</button>`).join("")}
          </div>
          <button type="button" class="zc-btn" data-act="prev">◀</button>
          <button type="button" class="zc-btn" data-act="next">▶</button>
        </div>
      </div>
      <div class="zc-metrics">
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "当前执行 C 函数" : "ACTIVE C FUNCTION"}</div>
          <div class="zc-metric-val" data-pm="fn"></div>
          <div class="zc-metric-sub" data-pm="fnsub">zlib/trees.c</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label" data-pm="l1"></div>
          <div class="zc-metric-val">"abcde_abcde_!"</div>
          <div class="zc-metric-sub">${zh ? "字面量 + (dist=6, len=5)" : "literals + match(d=6, len=5)"}</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label" data-pm="l2"></div>
          <div class="zc-metric-val" data-pm="v2"></div>
          <div class="zc-metric-sub" data-pm="s2"></div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label" data-pm="l3"></div>
          <div class="zc-metric-val" data-pm="v3"></div>
          <div class="zc-metric-sub">pending_buf = 4B bytes</div>
        </div>
      </div>
      <div class="zc-stage">
        <svg class="zc-svg" viewBox="0 0 860 176" data-svg="pipe-canvas"></svg>
      </div>
      <div class="zc-note" data-role="p-note"></div>
    `;

    const q = (s) => el.querySelector(s);

    const render = () => {
      const st = stages[step];
      q('[data-pm="fn"]').textContent = st.fn;
      q('[data-pm="fnsub"]').textContent = st.fnSub;
      q('[data-pm="l1"]').textContent = st.inLabel;
      q('[data-pm="l2"]').textContent = st.freqLabel;
      q('[data-pm="l3"]').textContent = st.modeLabel;
      q('[data-pm="v3"]').textContent = st.modeVal;
      q('[data-pm="v3"]').className = "zc-metric-val " + (step === 3 ? "zc-val-danger" : step === 2 ? "zc-val-warn" : "zc-val-safe");

      if (step === 0) {
        q('[data-pm="v2"]').textContent = "Freq['a']=2, len5=1…";
        q('[data-pm="s2"]').textContent = zh ? "仅统计次数，暂不编码" : "counting occurrences";
      } else if (step === 1) {
        q('[data-pm="v2"]').textContent = zh ? "Stored / Fixed / Dynamic" : "Stored vs Fixed vs Dyn";
        q('[data-pm="s2"]').textContent = zh ? "挑字节数最小者输出" : "pick minimum byte size";
      } else if (step === 2) {
        q('[data-pm="v2"]').textContent = zh ? "hlit + hdist + bl_tree" : "hlit + hdist + bl_tree";
        q('[data-pm="s2"]').textContent = zh ? "写入 [0 .. pending)" : "written into [0 .. pending)";
      } else {
        q('[data-pm="v2"]').textContent = zh ? "读 [B+3k] → 写 [pending]" : "[B+3k] → [pending]";
        q('[data-pm="s2"]').textContent = zh ? "同数组一读一写同时右移" : "both cursors move right";
      }

      // Render crisp SVG diagram of the shared 4B buffer in each stage
      let svg = `
        <defs>
          <pattern id="zc-p-hatch" width="8" height="8" patternTransform="rotate(45 0 0)" patternUnits="userSpaceOnUse">
            <line x1="0" y1="0" x2="0" y2="8" stroke="#d8d8d2" stroke-width="2" />
          </pattern>
        </defs>
        <text x="20" y="20" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#6b6b66">
          ${zh ? "共享数组 pending_buf[0 .. 4B) —— 前 1/4 是起跑空地 [0..B)，后 3/4 存放 sym_buf[0..3(B-1))" : "SHARED ARRAY pending_buf[0 .. 4B) — FIRST 1/4 IS HEAD START [0..B), LAST 3/4 IS sym_buf"}
        </text>
        <!-- Full 4B box: x=20..840 (width 820); B is at x = 20 + 205 = 225 -->
        <rect x="20" y="42" width="820" height="58" fill="url(#zc-p-hatch)" stroke="#0a0a0a" stroke-width="1.3" />
        <line x1="225" y1="34" x2="225" y2="108" stroke="#0a0a0a" stroke-width="1.2" stroke-dasharray="4 3" />
        <text x="122" y="34" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10" fill="#52524e">
          ${zh ? "[0 .. B) 起跑缓冲 (8B bits)" : "[0 .. B) HEAD START (8B bits)"}
        </text>
        <text x="532" y="34" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10" fill="#52524e">
          ${zh ? "[B .. 4B) 符号区 sym_buf (每个符号 3 字节 = 24 bits)" : "[B .. 4B) SYMBOL REGION sym_buf (3 bytes = 24 bits per symbol)"}
        </text>
      `;

      if (step === 0) {
        // Show 3-byte symbol triples filling from B=225 rightward
        const cells = [
          { lbl: "[0,0,'a']", w: 72 },
          { lbl: "[0,0,'b']", w: 72 },
          { lbl: "[0,0,'c']", w: 72 },
          { lbl: "…", w: 46 },
          { lbl: "[6,0,len5]", w: 86, hi: true },
          { lbl: "[0,0,'!']", w: 72 },
        ];
        let cx = 225;
        cells.forEach((c) => {
          svg += `
            <rect x="${cx}" y="42" width="${c.w}" height="58" fill="${c.hi ? "#d1fae5" : "#dfe7ec"}" stroke="#334155" stroke-width="1" />
            <text x="${cx + c.w / 2}" y="75" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10" font-weight="600" fill="#0f172a">${c.lbl}</text>
          `;
          cx += c.w;
        });
        svg += `
          <text x="122" y="75" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#737370">
            ${zh ? "空 (pending = 0)" : "EMPTY (pending = 0)"}
          </text>
          <text x="${cx + 14}" y="75" font-family="Menlo, Consolas, monospace" font-size="11" font-weight="700" fill="#0f766e">
            → sym_next += 3
          </text>
          <text x="20" y="136" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#334155">
            ${zh
              ? "每个符号无论将来压成 1 bit 还是 48 bits，在 sym_buf 里一律占 3 字节（2 字节距离 dist + 1 字节字面量/长度 lc）。"
              : "Every symbol—whether it will later compress to 1 bit or 48 bits—occupies 3 bytes in sym_buf (2B dist + 1B literal/length)."}
          </text>
        `;
      } else if (step === 1) {
        svg += `
          <rect x="225" y="42" width="590" height="58" fill="#dfe7ec" stroke="#334155" stroke-width="1" />
          <text x="520" y="75" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="11" font-weight="600" fill="#0f172a">
            ${zh ? "n 个未读符号静候编码 (3n 字节)" : "n recorded 3-byte symbols waiting in sym_buf (3n bytes)"}
          </text>
          <text x="122" y="75" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#737370">pending = 0</text>
          <!-- Three mode comparison pills at bottom -->
          <rect x="20" y="120" width="250" height="40" fill="#f6f6f3" stroke="#94a3b8" />
          <text x="145" y="138" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#475569">${zh ? "① 存储块: stored_len + 4" : "① Stored: stored_len + 4"}</text>
          <text x="145" y="152" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#64748b">${zh ? "若选它，直接从窗口拷原字节，不再读 sym_buf" : "copies raw window; sym_buf no longer needed"}</text>

          <rect x="285" y="120" width="260" height="40" fill="#f6f6f3" stroke="#94a3b8" />
          <text x="415" y="138" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#475569">${zh ? "② 固定块: static_lenb (≤31b/符号)" : "② Fixed: static_lenb (≤31b/sym)"}</text>
          <text x="415" y="152" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#64748b">${zh ? "仅 3b 头部，每步至多追近 +7 bits" : "3-bit header; gains at most +7b/step"}</text>

          <rect x="560" y="120" width="280" height="40" fill="#d1fae5" stroke="#0f766e" stroke-width="1.4" />
          <text x="700" y="138" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10.5" font-weight="700" fill="#065f46">${zh ? "③ 动态块: opt_lenb < static_lenb ✓" : "③ Dynamic: opt_lenb < static_lenb ✓"}</text>
          <text x="700" y="152" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#047857">${zh ? "仅在严格比固定块更省字节时才被选中！" : "selected ONLY when strictly smaller than Fixed!"}</text>
        `;
      } else if (step === 2) {
        svg += `
          <rect x="20" y="42" width="135" height="58" fill="#d6d3c9" stroke="#b91c1c" stroke-width="1.2" />
          <text x="87" y="68" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10.5" font-weight="700" fill="#7f1d1d">${zh ? "3b + 动态树头" : "3b + Tree Header"}</text>
          <text x="87" y="84" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#991b1b">send_all_trees()</text>

          <rect x="225" y="42" width="590" height="58" fill="#dfe7ec" stroke="#334155" stroke-width="1" />
          <text x="520" y="75" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="11" font-weight="600" fill="#0f172a">
            ${zh ? "第 0 个符号尚未读取！(读边界仍在 B)" : "Symbol 0 still unread! (Read cursor waiting at B)"}
          </text>

          <line x1="155" y1="36" x2="155" y2="108" stroke="#b91c1c" stroke-width="2.2" />
          <text x="148" y="124" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="10.5" font-weight="700" fill="#b91c1c">${zh ? "写指针 pending →" : "CHASER pending →"}</text>
          <text x="232" y="124" text-anchor="start" font-family="Menlo, Consolas, monospace" font-size="10.5" font-weight="700" fill="#0a0a0a">${zh ? "→ 读起点 B" : "→ RUNNER @ B"}</text>
          <text x="20" y="152" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#334155">
            ${zh
              ? "注意：如果树头本身超过 8B bits（在 B=128 时 8B 只有 1024 bits，而理论最大树头达 2283 bits！），还没开始编码就会撞穿 B！"
              : "Notice: at memLevel=1 (B=128), 8B is only 1,024 bits—whereas a general dynamic tree header can reach 2,283 bits!"}
          </text>
        `;
      } else {
        svg += `
          <rect x="20" y="42" width="135" height="58" fill="#d6d3c9" />
          <rect x="155" y="42" width="175" height="58" fill="#e7cfc8" />
          <text x="242" y="75" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10" font-weight="600" fill="#7f1d1d">${zh ? "已编码比特流 (0..k-1)" : "Encoded bits (0..k-1)"}</text>

          <!-- Freed symbols [B .. B+3k): 225..390 -->
          <rect x="225" y="42" width="165" height="58" fill="none" stroke="#94a3b8" stroke-dasharray="3 3" />
          <!-- Unread symbols [B+3k .. B+3n): 390..815 -->
          <rect x="390" y="42" width="425" height="58" fill="#dfe7ec" stroke="#0a0a0a" stroke-width="1.2" />
          <text x="602" y="75" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10.5" font-weight="600" fill="#0f172a">${zh ? "尚未读取的符号 [B+3k .. B+3n)" : "Unread symbols [B+3k .. B+3n)"}</text>

          <!-- Chaser at 330, Runner at 390 -->
          <line x1="330" y1="36" x2="330" y2="108" stroke="#b91c1c" stroke-width="2.4" />
          <text x="305" y="124" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="10.5" font-weight="700" fill="#b91c1c">${zh ? "写指针 (+1..48b/步) →" : "CHASER (+1..48b/step) →"}</text>

          <line x1="390" y1="36" x2="390" y2="108" stroke="#0a0a0a" stroke-width="2.4" />
          <text x="402" y="124" text-anchor="start" font-family="Menlo, Consolas, monospace" font-size="10.5" font-weight="700" fill="#0a0a0a">${zh ? "→ 读指针 B+3k (+24b/步)" : "→ RUNNER B+3k (+24b/step)"}</text>

          <text x="20" y="154" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#b91c1c" font-weight="600">
            ${zh
              ? "只要已编码比特流始终停在 B + 3k 左侧，被覆盖的就只是已经读完作废的旧槽位 [B .. B+3k)！"
              : "Overwriting [B .. B+3k) is harmless—those symbols were already read! Safety means pending NEVER reaches B + 3k."}
          </text>
        `;
      }

      q('[data-svg="pipe-canvas"]').innerHTML = svg;
      q('[data-role="p-note"]').innerHTML = st.note;
      el.querySelectorAll('[data-role="p-tabs"] button').forEach((b, i) => b.classList.toggle("is-active", i === step));
    };

    q('[data-role="p-tabs"]').addEventListener("click", (e) => {
      const btn = e.target.closest("button[data-i]");
      if (!btn) return;
      step = Number(btn.dataset.i);
      render();
    });
    q('[data-act="prev"]').addEventListener("click", () => { step = (step + 3) % 4; render(); });
    q('[data-act="next"]').addEventListener("click", () => { step = (step + 1) % 4; render(); });
    render();
  };

  /* ==========================================================================
   * WIDGET 1: THE OVERLAY BUFFER RACE (Verified Real-C Extrema at B = 128!)
   * ========================================================================== */
  const buildRaceScenarios = (zh) => {
    const B = 128; // memLevel = 1 -> lit_bufsize = 128, 4B = 512 bytes = 4096 bits
    const N = 127; // max symbols = B - 1

    // Exacttrees.c bit-buffer physics:
    // After emitting S = v0 + 3 + header + sum_{i<k} cost_i >= 1 bits,
    // send_bits flushes 2 bytes strictly when bi_valid + len > 16:
    // pending(S) = 2 * floor((S - 1) / 16), bi_valid(S) = ((S - 1) % 16) + 1.
    const makeTrace = (headerBits, entryBits, costFn) => {
      const steps = [];
      let S = entryBits + 3 + headerBits;
      for (let k = 0; k <= N; k++) {
        const readByte = B + 3 * k;
        const readBit = 8 * readByte;
        const pendingBytes = S > 0 ? 2 * Math.floor((S - 1) / 16) : 0;
        const biValid = S > 0 ? ((S - 1) % 16) + 1 : 0;
        const bitGap = readBit - S; // Exact unread bit gap (or sx gap at k=N)
        const byteGap = readByte - pendingBytes;
        steps.push({
          k,
          S,
          readBit,
          readByte,
          bitGap,
          byteGap,
          pendingBytes,
          biValid,
          nextCost: k < N ? costFn(k) : 0,
        });
        if (k < N) S += costFn(k);
      }
      // Find minimum gap among true unread symbols (k = 0..N-1) and overall (0..N)
      let minUnreadIdx = 0;
      for (let i = 1; i < N; i++) {
        if (steps[i].bitGap < steps[minUnreadIdx].bitGap) minUnreadIdx = i;
      }
      let minAllIdx = 0;
      for (let i = 1; i <= N; i++) {
        if (steps[i].bitGap < steps[minAllIdx].bitGap) minAllIdx = i;
      }
      return { B, N, headerBits, entryBits, steps, minUnreadIdx, minAllIdx };
    };

    return [
      {
        id: "fixed",
        tab: zh ? "01 · 固定块极限 (18B / 132b)" : "01 · Z_FIXED (18B / 132b)",
        // v0 = 7 leftover bits + 3-bit tag + 127 x 31-bit matches:
        // At k = 126 (last unread symbol @ 506B): S = 3916, pending = 488 -> 18B / +132b!
        // At k = 127 (trees.c:945 Assert @ 509B): S = 3947, pending = 492 -> 17B / +125b!
        trace: makeTrace(0, 7, () => 31),
        defaultK: 126,
        pinIdx: (tr) => tr.minUnreadIdx, // k = 126 (+132b / 18B unread; +125b / 17B at k=127)
        describe: (s) => {
          if (zh) {
            return `<span class="zc-badge zc-badge-safe">全库物理最近点 · 固定块</span> 这是整个 <code>zlib</code> 真实运行能达到的最小间距（已通过 33,404 字节真实输入在 <code>deflate(Z_FIXED)</code> 验证）：入口携带上一块残留的 <code>bi_valid = 7</code> bits（<code>deflate.c</code> 注释漏算了这 7 bits，所以写了 139 bits），随后连发 127 个 31-bit 匹配。在读最后一个未读符号前（<code>k = 126</code>），间距缩至 <strong>18 字节 / +132 bits</strong>；在 <code>k = 127</code> 的 <code>trees.c:945 Assert</code> 处缩至 <strong>17 字节 / +125 bits</strong>。`;
          }
          return `<span class="zc-badge zc-badge-safe">CLOSEST APPROACH IN ZLIB · Z_FIXED</span> Verified on a real 33,404-byte input in <code>deflate(Z_FIXED)</code>: starting with <code>bi_valid = 7</code> leftover bits from the prior block (7 bits tighter than <code>deflate.c:490</code>'s 139-bit figure, which assumed <code>bi_valid = 0</code>) and 127 consecutive 31-bit matches, the gap reaches <strong>18 bytes / +132 bits</strong> at the last unread symbol (<code>k = 126</code>) and <strong>17 bytes / +125 bits</strong> at <code>trees.c:945</code>'s <code>Assert</code> (<code>k = 127</code>).`;
        },
      },
      {
        id: "surge",
        tab: zh ? "02 · 动态块真实极限 (37B / 294b)" : "02 · Dynamic (37B / 294b)",
        // Exact verified 50,184-byte real deflate(level=6) extremum!
        // v0 = 7, tag = 3, header = 623 bits (S_0 = 633).
        // First 29 symbols are heavy matches whose total excess over 24*29 is +97 bits
        // (11 matches of 28b + 18 matches of 27b -> 11*4 + 18*3 = 98, make 17 of 27b + 1 of 26b + 11 of 28b = +97 bits!
        // Wait: 11*28 + 17*27 + 1*26 = 308 + 459 + 26 = 793 = 29*24 + 97! At k=29: S = 633 + 793 = 1426,
        // pending = 2*floor(1425/16) = 178, bi_valid = 2, readByte = 128 + 87 = 215 -> byteGap = 37B, bitGap = 1720 - 1426 = +294b!!).
        // Remaining 98 symbols: 49 MAX_MATCH=258 anchors (~8b each) + 38 literals + 11 light matches -> opt_len = 2211 (total payload = 1588b, minus 793 = 795 across 98 syms + EOB -> ~8b/sym!).
        trace: makeTrace(623, 7, (k) => (k < 11 ? 28 : k < 28 ? 27 : k === 28 ? 26 : 8)),
        defaultK: 29,
        pinIdx: (tr) => tr.minUnreadIdx, // k = 29 (+294b / 37B!)
        describe: (s) => {
          if (zh) {
            if (s.k === 0) {
              return `<span class="zc-badge zc-badge-warn">树头先行</span> 这是我们在默认压缩策略下构造出的 50,184 字节真实输入极限块：还没读第 0 个符号，<code>send_all_trees</code> 就写出了 <code>623</code> bits 动态树头（连同入口残留共 <code>633</code> bits，<code>pending = 78</code> 字节），上来就吃掉了近 2/3 的起跑缓冲！`;
            }
            if (s.k <= 29) {
              return `<span class="zc-badge zc-badge-warn">中途谷底 @ k = 29</span> 前 29 个符号全是高附加位的稀有长匹配（共多耗 <code>+97</code> bits 超额位）！在 <code>k = 29</code> 处，<code>pending = 178</code> 字节逼近未读边界 <code>215</code> 字节——达到动态块的真实物理极限：<strong>37 字节 / +294 bits</strong>（而此时还有 98 个符号没读！）。`;
            }
            return `<span class="zc-badge zc-badge-safe">攒钱锚点拉开距离</span> 后 98 个符号是用来压低总体积的 <code>MAX_MATCH = 258</code> 高频锚点与字面量（平均仅 ~8 bits/符号，每步反拉 +16 bits！），使整块 <code>opt_len = 2211 &lt; 2214 = static_len</code>（以 1 字节优势击败固定块），同时把安全距离重新拉大到 180+ 字节。`;
          }
          if (s.k === 0) {
            return `<span class="zc-badge zc-badge-warn">623-BIT TREE HEADER</span> From our 50,184-byte real <code>deflate(level = 6)</code> extremum: before symbol 0 is read, <code>send_all_trees</code> emits <code>623</code> header bits (<code>633</code> bits with entry bits, <code>pending = 78</code> B)—consuming over 60% of the 128-byte head start upfront.`;
          }
          if (s.k <= 29) {
            return `<span class="zc-badge zc-badge-warn">MID-BLOCK MINIMUM @ k = 29</span> Front-loading 29 rare max-extra-bit matches adds <code>+97</code> excess bits, pinching the gap right at <code>k = 29</code> (<code>pending = 178</code> B vs. unread symbol 29 at <code>215</code> B): <strong>37 bytes / +294 bits</strong>—with 98 symbols still unread!`;
          }
          return `<span class="zc-badge zc-badge-safe">ANCHOR SYMBOLS PULL AWAY</span> The remaining 98 symbols are cheap ~8-bit <code>MAX_MATCH = 258</code> anchors and literals needed so Dynamic beats Fixed (<code>opt_len = 2,211 &lt; 2,214 = static_len</code>, winning by 1 byte!). They widen the gap by +16 bits/step all the way to the end.`;
        },
      },
      {
        id: "collision",
        tab: zh ? "03 · 假想无约束 48b (追尾!)" : "03 · Unbounded 48b (Crash!)",
        trace: makeTrace(420, 7, (k) => (k < 36 ? 48 : 1)),
        defaultK: 28,
        pinIdx: (tr) => tr.minAllIdx,
        describe: (s) => {
          if (zh) {
            if (s.bitGap >= 0) {
              return `<span class="zc-badge zc-badge-warn">逼近追尾</span> 如果没有 Huffman 树的斐波那契频数约束，假设攻击者能自由排布 36 个 48-bit 匹配（<code>15+5+15+13</code>，每步净追 +24 bits）加 91 个 1-bit 字面量（整块平均仅 17.7 bits/符号 &lt; 31！）：向右拖过 <code>k = 25</code> 即可看到追尾现场。`;
            }
            return `<span class="zc-badge zc-badge-danger">缓冲区追尾覆盖!</span> 在 <code>k = 25</code> 处写指针越过未读边界 <code>B + 3k</code>（<code>${s.bitGap}</code> bits）！尚未读取的符号三元组被压缩比特流直接覆写，伪造出越界的 16 位 <code>dist</code>，随即击穿 <code>_dist_code[512]</code>！`;
          }
          if (s.bitGap >= 0) {
            return `<span class="zc-badge zc-badge-warn">CLOSING IN</span> If Huffman depths didn't cost frequency weight, thirty-six 48-bit matches (+24b/step catch-up) followed by ninety-one 1-bit literals would average 17.7 bits/sym (&lt; 31!) yet sprint toward <code>B + 3k</code>. Step past <code>k = 25</code> to watch the collision.`;
          }
          return `<span class="zc-badge zc-badge-danger">OVERLAY COLLISION!</span> Past <code>k = 25</code>, emitted bits overtake <code>B + 3k</code> (<code>${s.bitGap}</code> bits), overwriting unread 3-byte triples in <code>sym_buf</code> and corrupting <code>dist</code> into an out-of-bounds read on <code>_dist_code[512]</code>!`;
        },
      },
    ];
  };

  const mountRace = (el) => {
    const zh = getLang(el) === "zh";
    const scenarios = buildRaceScenarios(zh);
    let scenIdx = 1; // Default to Real Dynamic Extremum
    let k = scenarios[1].defaultK;
    let timer = null;

    el.innerHTML = `
      <div class="zc-bar">
        <div class="zc-title-wrap">
          <span class="zc-kicker">${zh ? "交互演示 03 · 真实极限双指针追逐 (memLevel = 1, B = 128)" : "INTERACTIVE 03 · REAL EXTREMAL POINTER CHASE (memLevel = 1, B = 128)"}</span>
          <span class="zc-title">${zh ? "写指针 pending 到底能离未读符号 B + 3k 多近？" : "How Close Can pending Actually Get to Unread Symbols B + 3k?"}</span>
        </div>
        <div class="zc-controls">
          <div class="zc-seg" data-role="tabs">
            ${scenarios.map((s, i) => `<button type="button" data-idx="${i}" class="${i === scenIdx ? "is-active" : ""}">${s.tab}</button>`).join("")}
          </div>
          <button type="button" class="zc-btn" data-action="play">${zh ? "▶ 播放" : "▶ Play"}</button>
          <button type="button" class="zc-btn" data-action="prev" aria-label="Previous step">◀</button>
          <button type="button" class="zc-btn" data-action="next" aria-label="Next step">▶</button>
          <button type="button" class="zc-btn" data-action="reset" aria-label="Reset">↺</button>
        </div>
      </div>
      <div class="zc-metrics">
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "已处理符号数 k" : "SYMBOLS CONSUMED k"}</div>
          <div class="zc-metric-val" data-m="k">29 / 127</div>
          <div class="zc-metric-sub" data-m="sx">sx = 87 B</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "已发出比特流 (CHASER)" : "BITS EMITTED (CHASER)"}</div>
          <div class="zc-metric-val" data-m="write">1426 bits</div>
          <div class="zc-metric-sub" data-m="write-sub">pending = 178 B, bi_valid = 2</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "下一未读符号 (RUNNER)" : "NEXT UNREAD SYM (RUNNER)"}</div>
          <div class="zc-metric-val" data-m="read">1720 bits</div>
          <div class="zc-metric-sub" data-m="read-sub">offset B + 3k = 215 B</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "真实物理间距" : "PHYSICAL MARGIN"}</div>
          <div class="zc-metric-val" data-m="gap">37 B (+294b)</div>
          <div class="zc-metric-sub" data-m="gap-sub">(B + 3k) − pending</div>
        </div>
      </div>
      <div class="zc-stage">
        <svg class="zc-svg" viewBox="0 0 880 326" role="img" aria-label="Overlay buffer race">
          <defs>
            <pattern id="zc-hatch-free" width="8" height="8" patternTransform="rotate(45 0 0)" patternUnits="userSpaceOnUse">
              <line x1="0" y1="0" x2="0" y2="8" stroke="#d4d4ce" stroke-width="2" />
            </pattern>
            <pattern id="zc-hatch-danger" width="8" height="8" patternTransform="rotate(45 0 0)" patternUnits="userSpaceOnUse">
              <line x1="0" y1="0" x2="0" y2="8" stroke="#fca5a5" stroke-width="3" />
            </pattern>
          </defs>

          <text x="20" y="15" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#6b6b66">
            ${zh ? "pending_buf 内存视图 [0 .. 4B = 512 字节 / 4096 bits]" : "pending_buf MEMORY MAP [0 .. 4B = 512 BYTES / 4096 BITS]"}
          </text>
          <text x="860" y="15" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#6b6b66">4B = 4096b</text>

          <rect x="20" y="44" width="840" height="44" fill="url(#zc-hatch-free)" stroke="#111" stroke-width="1.2" />
          <rect data-svg="hdr-rect" class="zc-anim-rect" x="20" y="44" width="0" height="44" fill="#d6d3c9" />
          <rect data-svg="pay-rect" class="zc-anim-rect" x="20" y="44" width="0" height="44" fill="#e7cfc8" />
          <rect data-svg="probe-rect" class="zc-anim-rect" x="20" y="44" width="3" height="44" fill="#c23b22" />

          <rect data-svg="read-done" class="zc-anim-rect" x="230" y="44" width="0" height="44" fill="#e5e5e0" opacity="0.85" />
          <rect data-svg="unread-rect" class="zc-anim-rect" x="230" y="44" width="625" height="44" fill="#dfe7ec" stroke="#334155" stroke-width="0.8" />
          <rect data-svg="crash-rect" class="zc-anim-rect" x="230" y="44" width="0" height="44" fill="url(#zc-hatch-danger)" stroke="#b91c1c" stroke-width="1.4" />

          <line x1="230" y1="44" x2="230" y2="88" stroke="#52524e" stroke-width="1" stroke-dasharray="3 2" />
          <text x="225" y="69" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#52524e">B=128B</text>

          <!-- Write cursor pin (TOP RAIL) -->
          <g data-svg="write-pin" class="zc-anim-x" transform="translate(20, 0)">
            <line x1="0" y1="38" x2="0" y2="91" stroke="#b91c1c" stroke-width="2.2" />
            <polygon points="-5,38 5,38 0,44" fill="#b91c1c" />
            <text data-svg="write-lbl" x="0" y="33" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10.5" font-weight="700" fill="#b91c1c">
              ${zh ? "▼ 写指针" : "▼ CHASER"}
            </text>
          </g>

          <!-- Read cursor pin (BOTTOM RAIL) -->
          <g data-svg="read-pin" class="zc-anim-x" transform="translate(230, 0)">
            <line x1="0" y1="41" x2="0" y2="94" stroke="#0a0a0a" stroke-width="2.2" />
            <polygon points="-5,94 5,94 0,88" fill="#0a0a0a" />
            <text data-svg="read-lbl" x="0" y="108" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10.5" font-weight="700" fill="#0a0a0a">
              ${zh ? "▲ 读边界 B+3k" : "▲ RUNNER B+3k"}
            </text>
          </g>

          <text x="54" y="142" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#6b6b66">
            ${zh ? "全程轨迹图：点击或拖动图表任意位置跳转符号 k" : "TRAJECTORY ACROSS BLOCK (CLICK OR DRAG ON CHART TO SCRUB k)"}
          </text>
          <rect data-svg="chart-bg" x="54" y="150" width="796" height="148" fill="#f6f6f3" stroke="#c8c8c4" stroke-width="1" style="cursor: crosshair;" />

          <line x1="54" y1="261" x2="850" y2="261" stroke="#deded9" stroke-dasharray="3 3" />
          <text x="48" y="264" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#787874">1024</text>
          <line x1="54" y1="224" x2="850" y2="224" stroke="#deded9" stroke-dasharray="3 3" />
          <text x="48" y="227" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#787874">2048</text>
          <line x1="54" y1="187" x2="850" y2="187" stroke="#deded9" stroke-dasharray="3 3" />
          <text x="48" y="190" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#787874">3072</text>
          <text x="48" y="154" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#787874">4096</text>
          <text x="48" y="300" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#787874">0</text>

          <path data-svg="gap-area" d="" fill="rgba(15, 118, 110, 0.09)" />
          <path data-svg="crash-area" d="" fill="rgba(185, 28, 28, 0.18)" />
          <path data-svg="read-path" d="" fill="none" stroke="#0a0a0a" stroke-width="1.8" stroke-dasharray="5 4" />
          <path data-svg="write-path" d="" fill="none" stroke="#b91c1c" stroke-width="2.2" />

          <g data-svg="pinch-marker" style="pointer-events: none;">
            <line data-svg="pinch-line" x1="0" y1="0" x2="0" y2="0" stroke="#0f766e" stroke-width="1.4" stroke-dasharray="2 2" />
            <line data-svg="pinch-leader" x1="0" y1="0" x2="0" y2="0" stroke="#0f766e" stroke-width="1" />
            <rect data-svg="pinch-bg" x="0" y="0" width="150" height="20" rx="2" fill="#fbfbfa" stroke="#0f766e" stroke-width="1" />
            <text data-svg="pinch-label" x="0" y="0" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10" font-weight="600" fill="#0f766e"></text>
          </g>

          <line data-svg="playhead" x1="54" y1="150" x2="54" y2="298" stroke="#0a0a0a" stroke-width="1.2" />
          <circle data-svg="dot-read" cx="54" cy="261" r="4" fill="#0a0a0a" />
          <circle data-svg="dot-write" cx="54" cy="288" r="4.5" fill="#b91c1c" stroke="#fff" stroke-width="1" />

          <text x="54" y="316" font-family="Menlo, Consolas, monospace" font-size="10" fill="#6b6b66">k = 0</text>
          <text x="452" y="316" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10" fill="#6b6b66">
            ${zh ? "符号序号 k (每步消费 3 字节 = 24 bits)" : "symbol index k (each step consumes 3 bytes = 24 bits)"}
          </text>
          <text x="850" y="316" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="10" fill="#6b6b66">k = 127</text>
        </svg>
      </div>
      <div class="zc-scrubber-row">
        <label data-role="slider-label">k = 29</label>
        <input type="range" class="zc-range" min="0" max="127" value="29" data-role="slider" />
        <label>${zh ? "下一符号位长:" : "Next sym bits:"} <strong data-role="next-cost">8b</strong></label>
      </div>
      <div class="zc-note" data-role="note"></div>
    `;

    const q = (sel) => el.querySelector(sel);
    const slider = q('[data-role="slider"]');
    const playBtn = q('[data-action="play"]');

    const chartX = (idx) => 54 + (idx / 127) * 796;
    const chartY = (bits) => 298 - Math.min(4300, Math.max(0, bits)) * (148 / 4096);
    const tapeX = (bits) => 20 + Math.min(4096, Math.max(0, bits)) * (840 / 4096);

    const drawStaticPaths = () => {
      const sc = scenarios[scenIdx];
      const st = sc.trace.steps;
      const rPts = st.map((p) => `${chartX(p.k).toFixed(1)},${chartY(p.readBit).toFixed(1)}`);
      const wPts = st.map((p) => `${chartX(p.k).toFixed(1)},${chartY(p.S).toFixed(1)}`);
      q('[data-svg="read-path"]').setAttribute("d", `M ${rPts.join(" L ")}`);
      q('[data-svg="write-path"]').setAttribute("d", `M ${wPts.join(" L ")}`);

      const safeTop = st.map((p) => `${chartX(p.k).toFixed(1)},${chartY(p.readBit).toFixed(1)}`);
      const safeBot = [...st].reverse().map((p) => `${chartX(p.k).toFixed(1)},${chartY(Math.min(p.readBit, p.S)).toFixed(1)}`);
      q('[data-svg="gap-area"]').setAttribute("d", `M ${safeTop.join(" L ")} L ${safeBot.join(" L ")} Z`);

      const hasCrash = st.some((p) => p.S > p.readBit);
      if (hasCrash) {
        const cTop = st.map((p) => `${chartX(p.k).toFixed(1)},${chartY(Math.max(p.readBit, p.S)).toFixed(1)}`);
        const cBot = [...st].reverse().map((p) => `${chartX(p.k).toFixed(1)},${chartY(p.readBit).toFixed(1)}`);
        q('[data-svg="crash-area"]').setAttribute("d", `M ${cTop.join(" L ")} L ${cBot.join(" L ")} Z`);
      } else {
        q('[data-svg="crash-area"]').setAttribute("d", "");
      }

      const pIdx = sc.pinIdx(sc.trace);
      const minStep = st[pIdx];
      const px = chartX(minStep.k);
      const py1 = chartY(minStep.readBit);
      const py2 = chartY(minStep.S);
      const pLine = q('[data-svg="pinch-line"]');
      const pLeader = q('[data-svg="pinch-leader"]');
      const pBg = q('[data-svg="pinch-bg"]');
      const pLbl = q('[data-svg="pinch-label"]');
      pLine.setAttribute("x1", px.toFixed(1));
      pLine.setAttribute("x2", px.toFixed(1));
      pLine.setAttribute("y1", py1.toFixed(1));
      pLine.setAttribute("y2", py2.toFixed(1));
      const isNeg = minStep.bitGap < 0;
      const stroke = isNeg ? "#b91c1c" : "#0f766e";
      const txt = isNeg
        ? (zh ? `追尾! (${minStep.bitGap}b)` : `COLLISION (${minStep.bitGap}b)`)
        : (zh ? `最近 @ k=${minStep.k} (${minStep.byteGap}B / +${minStep.bitGap}b)` : `closest @ k=${minStep.k} (${minStep.byteGap}B / +${minStep.bitGap}b)`);

      let bx, by, ax, ay;
      if (scenIdx === 0) {
        bx = 685; by = 198; ax = px; ay = (py1 + py2) / 2;
      } else if (scenIdx === 1) {
        bx = 345; by = 272; ax = px; ay = py2;
      } else {
        bx = 215; by = 172; ax = px; ay = Math.min(py1, py2);
      }
      const bw = Math.max(142, txt.length * 7.1 + 18);
      pLine.setAttribute("stroke", stroke);
      pLeader.setAttribute("stroke", stroke);
      pLeader.setAttribute("x1", ax.toFixed(1));
      pLeader.setAttribute("y1", ay.toFixed(1));
      pLeader.setAttribute("x2", bx.toFixed(1));
      pLeader.setAttribute("y2", by.toFixed(1));
      pBg.setAttribute("x", (bx - bw / 2).toFixed(1));
      pBg.setAttribute("y", (by - 10).toFixed(1));
      pBg.setAttribute("width", bw.toFixed(1));
      pBg.setAttribute("stroke", stroke);
      pLbl.setAttribute("fill", stroke);
      pLbl.setAttribute("x", bx.toFixed(1));
      pLbl.setAttribute("y", (by + 3.5).toFixed(1));
      pLbl.textContent = txt;
    };

    const render = () => {
      const sc = scenarios[scenIdx];
      const s = sc.trace.steps[k];
      slider.value = String(k);
      q('[data-role="slider-label"]').textContent = `k = ${k}`;
      q('[data-role="next-cost"]').textContent = k < 127 ? `${s.nextCost} bits` : "EOB";

      q('[data-m="k"]').textContent = `${k} / 127`;
      q('[data-m="sx"]').textContent = `sx = ${3 * k} B (${24 * k} bits freed)`;
      q('[data-m="write"]').textContent = `${s.S} bits`;
      q('[data-m="write-sub"]').textContent = `pending = ${s.pendingBytes} B, bi_valid = ${s.biValid}`;
      q('[data-m="read"]').textContent = `${s.readBit} bits`;
      q('[data-m="read-sub"]').textContent = k < 127 ? `B + 3k = ${s.readByte} B (unread)` : `B + sx = ${s.readByte} B (Assert)`;

      const gapEl = q('[data-m="gap"]');
      gapEl.textContent = `${s.byteGap} B (${s.bitGap >= 0 ? "+" : ""}${s.bitGap}b)`;
      gapEl.className = "zc-metric-val " + (s.bitGap < 0 ? "zc-val-danger" : s.bitGap < 320 ? "zc-val-warn" : "zc-val-safe");

      const hdrEnd = tapeX(sc.trace.entryBits + 3 + sc.trace.headerBits);
      const flushedEnd = tapeX(s.pendingBytes * 8);
      const sEnd = tapeX(s.S);
      const bStart = tapeX(1024);
      const readPos = tapeX(s.readBit);
      const symEndPos = tapeX(8 * (128 + 3 * 127));

      q('[data-svg="hdr-rect"]').setAttribute("width", Math.max(0, hdrEnd - 20).toFixed(1));
      q('[data-svg="pay-rect"]').setAttribute("x", hdrEnd.toFixed(1));
      q('[data-svg="pay-rect"]').setAttribute("width", Math.max(0, Math.max(flushedEnd, sEnd) - hdrEnd).toFixed(1));
      q('[data-svg="probe-rect"]').setAttribute("x", flushedEnd.toFixed(1));
      q('[data-svg="probe-rect"]').setAttribute("width", Math.max(2, sEnd - flushedEnd).toFixed(1));

      q('[data-svg="read-done"]').setAttribute("x", bStart.toFixed(1));
      q('[data-svg="read-done"]').setAttribute("width", Math.max(0, readPos - bStart).toFixed(1));
      q('[data-svg="unread-rect"]').setAttribute("x", readPos.toFixed(1));
      q('[data-svg="unread-rect"]').setAttribute("width", Math.max(0, symEndPos - readPos).toFixed(1));

      if (s.S > s.readBit) {
        const crashW = Math.min(symEndPos, sEnd) - readPos;
        q('[data-svg="crash-rect"]').setAttribute("x", readPos.toFixed(1));
        q('[data-svg="crash-rect"]').setAttribute("width", Math.max(0, crashW).toFixed(1));
      } else {
        q('[data-svg="crash-rect"]').setAttribute("width", "0");
      }

      q('[data-svg="write-pin"]').setAttribute("transform", `translate(${sEnd.toFixed(1)}, 0)`);
      q('[data-svg="write-lbl"]').setAttribute("x", sEnd < 60 ? String(60 - sEnd) : sEnd > 820 ? String(820 - sEnd) : "0");
      q('[data-svg="read-pin"]').setAttribute("transform", `translate(${readPos.toFixed(1)}, 0)`);
      q('[data-svg="read-lbl"]').setAttribute("x", readPos > 805 ? String(805 - readPos) : "0");

      const cx = chartX(k);
      q('[data-svg="playhead"]').setAttribute("x1", cx.toFixed(1));
      q('[data-svg="playhead"]').setAttribute("x2", cx.toFixed(1));
      q('[data-svg="dot-read"]').setAttribute("cx", cx.toFixed(1));
      q('[data-svg="dot-read"]').setAttribute("cy", chartY(s.readBit).toFixed(1));
      q('[data-svg="dot-write"]').setAttribute("cx", cx.toFixed(1));
      q('[data-svg="dot-write"]').setAttribute("cy", chartY(s.S).toFixed(1));

      q('[data-role="note"]').innerHTML = sc.describe(s);
    };

    const stopPlay = () => {
      if (timer) { clearInterval(timer); timer = null; }
      playBtn.textContent = zh ? "▶ 播放" : "▶ Play";
      playBtn.classList.remove("is-active");
    };

    const startPlay = () => {
      if (k >= 127) k = 0;
      playBtn.textContent = zh ? "⏸ 暂停" : "⏸ Pause";
      playBtn.classList.add("is-active");
      timer = setInterval(() => {
        if (k < 127) { k++; render(); } else { stopPlay(); }
      }, 45);
    };

    q('[data-role="tabs"]').addEventListener("click", (e) => {
      const btn = e.target.closest("button[data-idx]");
      if (!btn) return;
      stopPlay();
      scenIdx = Number(btn.dataset.idx);
      el.querySelectorAll('[data-role="tabs"] button').forEach((b, i) => b.classList.toggle("is-active", i === scenIdx));
      k = scenarios[scenIdx].defaultK;
      drawStaticPaths();
      render();
    });

    playBtn.addEventListener("click", () => (timer ? stopPlay() : startPlay()));
    q('[data-action="prev"]').addEventListener("click", () => { stopPlay(); k = Math.max(0, k - 1); render(); });
    q('[data-action="next"]').addEventListener("click", () => { stopPlay(); k = Math.min(127, k + 1); render(); });
    q('[data-action="reset"]').addEventListener("click", () => { stopPlay(); k = 0; render(); });
    slider.addEventListener("input", () => { stopPlay(); k = Number(slider.value); render(); });

    const svg = q("svg");
    let dragging = false;
    const scrubFromEvent = (ev) => {
      const pt = svg.createSVGPoint();
      pt.x = ev.clientX; pt.y = ev.clientY;
      const ctm = svg.getScreenCTM();
      if (!ctm) return;
      const loc = pt.matrixTransform(ctm.inverse());
      const ratio = Math.max(0, Math.min(1, (loc.x - 54) / 796));
      k = Math.round(ratio * 127);
      render();
    };
    q('[data-svg="chart-bg"]').addEventListener("pointerdown", (ev) => {
      stopPlay(); dragging = true;
      ev.target.setPointerCapture?.(ev.pointerId);
      scrubFromEvent(ev);
    });
    svg.addEventListener("pointermove", (ev) => { if (dragging) scrubFromEvent(ev); });
    window.addEventListener("pointerup", () => { dragging = false; });

    drawStaticPaths();
    render();
  };

  /* ==========================================================================
   * WIDGET 2: THE OUT-OF-BOUNDS CASCADE (_dist_code[512])
   * ========================================================================== */
  const mountOob = (el) => {
    const zh = getLang(el) === "zh";
    let dist = 48879;

    const presets = [
      { label: zh ? "合法匹配 (18,400)" : "Valid (18,400)", val: 18400 },
      { label: zh ? "最大合法距离 (32,768)" : "Max Valid (32,768)", val: 32768 },
      { label: zh ? "被覆写脏值 (0xBEEF)" : "Overwritten (0xBEEF)", val: 0xbeef },
      { label: zh ? "16 位上限 (0xFFFF)" : "Max uint16 (0xFFFF)", val: 0xffff },
    ];

    el.innerHTML = `
      <div class="zc-bar">
        <div class="zc-title-wrap">
          <span class="zc-kicker">${zh ? "交互演示 02 · 为什么压缩率问题会变成内存安全漏洞" : "INTERACTIVE 02 · WHY OVERWRITING sym_buf BREAKS MEMORY SAFETY"}</span>
          <span class="zc-title">${zh ? "从被覆写的 16 位距离 dist 到 _dist_code[512] 越界读" : "From Overwritten 16-Bit dist to _dist_code[512] Out-of-Bounds Read"}</span>
        </div>
        <div class="zc-controls">
          <div class="zc-seg" data-role="presets">
            ${presets.map((p) => `<button type="button" data-val="${p.val}" class="${p.val === dist ? "is-active" : ""}">${p.label}</button>`).join("")}
          </div>
        </div>
      </div>
      <div class="zc-stage">
        <div class="zc-pipeline">
          <div class="zc-pipe-box" data-box="sym">
            <div class="zc-pipe-step">1 · sym_buf[sx..sx+2]</div>
            <div class="zc-pipe-expr" data-p="bytes">[ef] [be] [12]</div>
            <div class="zc-pipe-detail" data-p="bytes-sub">dist = 48879</div>
          </div>
          <div class="zc-pipe-box" data-box="dec">
            <div class="zc-pipe-step">2 · trees.c:929</div>
            <div class="zc-pipe-expr" data-p="dm1">dist - 1 = 48878</div>
            <div class="zc-pipe-detail" data-p="shift">(dist - 1) &gt;&gt; 7 = 381</div>
          </div>
          <div class="zc-pipe-box" data-box="idx">
            <div class="zc-pipe-step">3 · d_code(dist - 1)</div>
            <div class="zc-pipe-expr" data-p="index">_dist_code[637]</div>
            <div class="zc-pipe-detail" data-p="index-sub">array length = 512!</div>
          </div>
          <div class="zc-pipe-box" data-box="res">
            <div class="zc-pipe-step">4 · C / Lean Model</div>
            <div class="zc-pipe-expr" data-p="verdict">Fault.ub (OOB)</div>
            <div class="zc-pipe-detail" data-p="verdict-sub">+126 B past _dist_code</div>
          </div>
        </div>

        <svg class="zc-svg" viewBox="0 0 860 112" role="img" aria-label="_dist_code memory layout">
          <text x="16" y="18" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#6b6b66">
            ${zh ? ".rodata 只读段布局：const uch _dist_code[512] (分桶表) vs. 相邻越界内存 [512 .. 767]" : ".rodata LAYOUT: const uch _dist_code[512] BUCKET TABLE VS. ADJACENT MEMORY [512 .. 767]"}
          </text>
          <rect x="16" y="28" width="276" height="42" fill="#e4ebe8" stroke="#0f766e" stroke-width="1" />
          <text x="154" y="47" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="11" font-weight="600" fill="#065f46">_dist_code[0 .. 255]</text>
          <text x="154" y="61" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#0f766e">dist 1 .. 256 (direct)</text>

          <rect x="292" y="28" width="276" height="42" fill="#d7e6e1" stroke="#0f766e" stroke-width="1" />
          <text x="430" y="47" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="11" font-weight="600" fill="#065f46">_dist_code[256 .. 511]</text>
          <text x="430" y="61" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#0f766e">dist 257 .. 32768 (256 + (d&gt;&gt;7))</text>

          <rect x="568" y="28" width="276" height="42" fill="rgba(254,226,226,0.72)" stroke="#b91c1c" stroke-width="1.3" />
          <text x="706" y="47" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="11" font-weight="700" fill="#991b1b">
            ${zh ? "越界区 [512 .. 767] (OOB!)" : "OUT OF BOUNDS [512 .. 767]"}
          </text>
          <text x="706" y="61" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#b91c1c">dist 32769 .. 65535 → Fault.ub</text>

          <line x1="568" y1="20" x2="568" y2="82" stroke="#0a0a0a" stroke-width="2" />
          <text x="568" y="95" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10" font-weight="700" fill="#0a0a0a">sizeof = 512</text>

          <g data-svg="needle" class="zc-anim-x" transform="translate(600, 0)">
            <polygon points="-6,22 6,22 0,30" fill="#b91c1c" data-svg="needle-head" />
            <line x1="0" y1="26" x2="0" y2="74" stroke="#b91c1c" stroke-width="2.4" data-svg="needle-line" />
            <text x="0" y="108" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="11" font-weight="700" fill="#b91c1c" data-svg="needle-txt">idx = 637</text>
          </g>
        </svg>
      </div>
      <div class="zc-scrubber-row">
        <label>${zh ? "拖动 16 位距离 dist:" : "16-bit symbol dist:"}</label>
        <input type="range" class="zc-range" min="1" max="65535" value="${dist}" data-role="dist-slider" />
        <label><strong data-role="dist-hex">0xbeef (48879)</strong></label>
      </div>
      <div class="zc-note" data-role="oob-note"></div>
    `;

    const q = (s) => el.querySelector(s);
    const slider = q('[data-role="dist-slider"]');

    const render = () => {
      const lo = dist & 0xff;
      const hi = (dist >> 8) & 0xff;
      const dm1 = dist - 1;
      const idx = dm1 < 256 ? dm1 : 256 + (dm1 >> 7);
      const oob = idx >= 512;

      q('[data-role="dist-hex"]').textContent = `0x${dist.toString(16).padStart(4, "0")} (${dist})`;
      q('[data-p="bytes"]').textContent = `[0x${lo.toString(16).padStart(2, "0")}] [0x${hi.toString(16).padStart(2, "0")}] [0x12]`;
      q('[data-p="bytes-sub"]').textContent = `dist = ${dist} ${dist <= 32768 ? "(≤ 32768)" : "(> 32768!)"}`;
      q('[data-p="dm1"]').textContent = `dist - 1 = ${dm1}`;
      q('[data-p="shift"]').textContent = dm1 < 256 ? "< 256 (direct)" : `256 + (${dm1} >> 7) = ${idx}`;
      q('[data-p="index"]').textContent = `_dist_code[${idx}]`;
      q('[data-p="index-sub"]').textContent = oob ? (zh ? `越过 512 上界 +${idx - 511} 字节!` : `+${idx - 511} B past 512-byte table!`) : (zh ? "落在 [0..511] 合法表内" : "within [0..511] bounds");
      q('[data-p="verdict"]').textContent = oob ? "Fault.ub (OOB Read)" : "Safe (< 512)";
      q('[data-p="verdict"]').className = "zc-pipe-expr " + (oob ? "zc-val-danger" : "zc-val-safe");
      q('[data-p="verdict-sub"]').textContent = oob ? (zh ? "随后再触发 dtree[code] 越界" : "then indexes dtree[code] OOB") : "bucket code < 30";

      q('[data-box="idx"]').classList.toggle("is-fault", oob);
      q('[data-box="res"]').classList.toggle("is-fault", oob);

      const x = 16 + (idx / 767) * 828;
      const color = oob ? "#b91c1c" : "#0f766e";
      q('[data-svg="needle"]').setAttribute("transform", `translate(${x.toFixed(1)}, 0)`);
      q('[data-svg="needle-head"]').setAttribute("fill", color);
      q('[data-svg="needle-line"]').setAttribute("stroke", color);
      q('[data-svg="needle-txt"]').setAttribute("fill", color);
      q('[data-svg="needle-txt"]').textContent = `idx = ${idx}`;

      q('[data-role="oob-note"]').innerHTML = oob
        ? (zh
            ? `<span class="zc-badge zc-badge-danger">内存越界读</span> 一旦写指针追上并覆写了未读符号，<code>dist</code> 就变成了压缩流里的任意 16 位整数：只要落在 <code>32769..65535</code>，分桶查表宏 <code>d_code(dist - 1)</code> 就会冲出 512 字节的 <code>_dist_code</code>，再拿读出的脏字节去索引只有 61 项的 <code>dyn_dtree</code>。所以<strong>证明不追尾是内存安全证明的必经之路</strong>。`
            : `<span class="zc-badge zc-badge-danger">OUT-OF-BOUNDS READ</span> Once emitted bits overwrite an unread symbol, <code>dist</code> becomes an arbitrary 16-bit integer: any value in <code>32769..65535</code> drives the bucket-lookup macro <code>d_code(dist - 1)</code> up to index <code>767</code>—256 bytes past <code>_dist_code[512]</code>—and uses that garbage byte to index <code>dyn_dtree[61]</code>.`)
        : (zh
            ? `<span class="zc-badge zc-badge-safe">在合法界内</span> 只要写指针没有碰过未读符号，读出来的就是第 1 遍记录的真实匹配距离 <code>1 ≤ dist ≤ 32506 ≤ 32768</code>，查表下标最大为 <code>511</code>，绝不越界。`
            : `<span class="zc-badge zc-badge-safe">IN BOUNDS</span> As long as unread symbols remain untouched, <code>1 ≤ dist ≤ 32506 ≤ 32768</code>, keeping <code>d_code(dist - 1) ≤ 511</code> and the resulting bucket code strictly below <code>30</code>.`);
    };

    slider.addEventListener("input", () => {
      dist = Number(slider.value);
      el.querySelectorAll('[data-role="presets"] button').forEach((b) => b.classList.toggle("is-active", Number(b.dataset.val) === dist));
      render();
    });
    q('[data-role="presets"]').addEventListener("click", (e) => {
      const btn = e.target.closest("button[data-val]");
      if (!btn) return;
      dist = Number(btn.dataset.val);
      slider.value = String(dist);
      el.querySelectorAll('[data-role="presets"] button').forEach((b) => b.classList.toggle("is-active", b === btn));
      render();
    });

    render();
  };

  /* ==========================================================================
   * WIDGET 3: FIBONACCI HUFFMAN SPINE & THE F(17) = 1597 WALL
   * ========================================================================== */
  const mountFib = (el) => {
    const zh = getLang(el) === "zh";
    let memLevel = 4;
    let depth = 15;

    el.innerHTML = `
      <div class="zc-bar">
        <div class="zc-title-wrap">
          <span class="zc-kicker">${zh ? "交互演示 04 · 为什么长编码需要指数级的总频数" : "INTERACTIVE 04 · WHY DEEP HUFFMAN CODES COST FIBONACCI WEIGHT"}</span>
          <span class="zc-title">${zh ? "最小 Huffman 树脊柱与 F(17) = 1597 零截断阈值" : "Minimal Huffman Spine & the F(17) = 1597 Early-Return Wall"}</span>
        </div>
        <div class="zc-controls">
          <span style="font-family:monospace;font-size:11px;color:#666;">memLevel:</span>
          <div class="zc-seg" data-role="mem">
            ${[1,2,3,4,5,6,7,8,9].map((m) => `<button type="button" data-m="${m}" class="${m === memLevel ? "is-active" : ""}">${m}</button>`).join("")}
          </div>
        </div>
      </div>
      <div class="zc-metrics">
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "树总频数上限 (B + 2)" : "MAX TREE WEIGHT (B + 2)"}</div>
          <div class="zc-metric-val" data-f="wmax">1,026</div>
          <div class="zc-metric-sub" data-f="bsub">B = 1024 (memLevel 4)</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "探测叶子深度 l" : "TARGET LEAF DEPTH l"}</div>
          <div class="zc-metric-val" data-f="depth">15 bits</div>
          <div class="zc-metric-sub" data-f="fib-eq">1·F(l+1) + F(l) = F(l+2)</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "达到深度 l 所需最小总频数" : "MIN WEIGHT REQUIRED"}</div>
          <div class="zc-metric-val" data-f="wreq">1,597</div>
          <div class="zc-metric-sub" data-f="wreq-sub">F(17) = 1597</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "C 代码 trees.c:577 行为" : "C BRANCH AT trees.c:577"}</div>
          <div class="zc-metric-val" data-f="maxd">14 bits max</div>
          <div class="zc-metric-sub" data-f="clamp-sub">if (overflow == 0) return;</div>
        </div>
      </div>
      <div class="zc-stage">
        <svg class="zc-svg" viewBox="0 0 860 185" data-svg="spine"></svg>
      </div>
      <div class="zc-scrubber-row">
        <label>${zh ? "尝试构造深度 l:" : "Probe leaf depth l:"} <strong data-f="slider-l">15</strong></label>
        <input type="range" class="zc-range" min="1" max="16" value="${depth}" data-role="l-slider" />
        <label data-f="status-pill"></label>
      </div>
      <div class="zc-note" data-role="fib-note"></div>
    `;

    const q = (s) => el.querySelector(s);
    const slider = q('[data-role="l-slider"]');

    const render = () => {
      const B = 1 << (memLevel + 6);
      const Wmax = B + 2;
      const wReq = depth === 16 ? FIB[17] : FIB[depth + 2];
      const reachable = wReq <= Wmax;

      let maxTrueDepth = 1;
      for (let d = 1; d <= 15; d++) {
        if (FIB[d + 2] <= Wmax) maxTrueDepth = d;
      }
      const canOverflow15 = Wmax >= 1597;

      q('[data-f="wmax"]').textContent = Wmax.toLocaleString();
      q('[data-f="bsub"]').textContent = `B = ${B.toLocaleString()} (memLevel ${memLevel})`;
      q('[data-f="depth"]').textContent = `${depth} bits`;
      q('[data-f="fib-eq"]').textContent = depth === 16 ? "parent @ 15 ⇒ F(16)+F(15)" : `1·F(${depth + 1}) + F(${depth}) = F(${depth + 2})`;
      q('[data-f="wreq"]').textContent = wReq.toLocaleString();
      q('[data-f="wreq"]').className = "zc-metric-val " + (reachable ? "zc-val-safe" : "zc-val-danger");
      q('[data-f="wreq-sub"]').textContent = depth === 16 ? "F(17) = 1597 threshold" : `F(${depth + 2}) = ${wReq}`;
      q('[data-f="maxd"]').textContent = canOverflow15 ? (zh ? ">15 (触发截断)" : ">15 (clamped to 15)") : `≤ ${maxTrueDepth} bits`;
      q('[data-f="clamp-sub"]').textContent = canOverflow15
        ? (zh ? "进入修复循环 (overflow > 0)" : "repair loop can run")
        : (zh ? "trees.c:577 必然提前返回!" : "trees.c:577 ALWAYS returns early!");
      q('[data-f="slider-l"]').textContent = String(depth);
      q('[data-f="status-pill"]').innerHTML = reachable
        ? `<span class="zc-badge zc-badge-safe">${zh ? "可构造" : "POSSIBLE"} (${wReq} ≤ ${Wmax})</span>`
        : `<span class="zc-badge zc-badge-danger">${zh ? "频数不够!" : "IMPOSSIBLE!"} (${wReq} &gt; ${Wmax})</span>`;

      const steps = depth;
      const x0 = 48;
      const x1 = 812;
      const dx = steps > 1 ? (x1 - x0) / steps : 0;
      let svgHtml = `
        <text x="20" y="18" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#6b6b66">
          ${zh
            ? `深度 l = ${depth} 的最轻 Huffman 树脊柱（左：频数 1 的最深叶子 → 右：树根；虚线框为每轮合并必需的最小兄弟权重）`
            : `LIGHTEST HUFFMAN SPINE FOR DEPTH l = ${depth} (LEFT: FREQ-1 LEAF → RIGHT: ROOT; DASHED BOXES = MIN SIBLING WEIGHTS)`}
        </text>
      `;

      for (let i = 0; i <= steps; i++) {
        const cx = steps === 0 ? 430 : x0 + i * dx;
        const cy = 74;
        if (i < steps) {
          const nx = x0 + (i + 1) * dx;
          svgHtml += `<line x1="${cx.toFixed(1)}" y1="${cy}" x2="${nx.toFixed(1)}" y2="${cy}" stroke="${reachable ? "#0a0a0a" : "#b91c1c"}" stroke-width="2" />`;
          const sibWeight = depth === 16 ? (i === 0 ? 1 : FIB[i + 1]) : FIB[i + 1];
          svgHtml += `
            <line x1="${nx.toFixed(1)}" y1="${cy}" x2="${(nx - dx * 0.28).toFixed(1)}" y2="142" stroke="#8a8a84" stroke-width="1.3" stroke-dasharray="3 2" />
            <rect x="${(nx - dx * 0.28 - 17).toFixed(1)}" y="134" width="34" height="22" fill="#eeeeec" stroke="#8a8a84" stroke-width="1" />
            <text x="${(nx - dx * 0.28).toFixed(1)}" y="149" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#333">${sibWeight}</text>
          `;
        }
      }

      for (let i = 0; i <= steps; i++) {
        const cx = x0 + i * dx;
        const cy = 74;
        const nodeW = i === 0 ? 1 : FIB[i + 2];
        const isRoot = i === steps;
        const isLeaf = i === 0;
        const over = nodeW > Wmax;
        const fill = over ? "#fee2e2" : isRoot ? "#0a0a0a" : isLeaf ? "#d1fae5" : "#fbfbfa";
        const stroke = over ? "#b91c1c" : isLeaf ? "#0f766e" : "#0a0a0a";
        const txtFill = over ? "#991b1b" : isRoot ? "#f6f6f3" : "#0a0a0a";
        const r = isRoot ? 18 : steps > 12 ? 13.5 : 15.5;
        svgHtml += `
          <circle cx="${cx.toFixed(1)}" cy="${cy}" r="${r}" fill="${fill}" stroke="${stroke}" stroke-width="1.6" />
          <text x="${cx.toFixed(1)}" y="${cy + 3.5}" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="${nodeW >= 1000 ? "8.5" : "9.5"}" font-weight="700" fill="${txtFill}">${nodeW}</text>
          <text x="${cx.toFixed(1)}" y="${cy - r - 6}" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9" fill="#737370">d=${steps - i}</text>
        `;
      }
      svgHtml += `
        <text x="20" y="176" font-family="Menlo, Consolas, monospace" font-size="10" fill="#6b6b66">
          ${zh ? "圆圈数字 = 该子树最小累计频数 (1, 2, 3, 5, 8, 13, … 斐波那契数列)" : "Circle numbers = minimum subtree weight along spine (1, 2, 3, 5, 8, 13, … Fibonacci numbers)"}
        </text>
      `;
      q('[data-svg="spine"]').innerHTML = svgHtml;

      if (memLevel <= 2) {
        q('[data-role="fib-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-ink">memLevel ${memLevel} · 极浅树</span> 整棵树总频数至多 <code>${Wmax} &lt; F(${maxTrueDepth + 3}) = ${FIB[maxTrueDepth + 3]}</code>，连深度 <code>${maxTrueDepth + 1}</code> 都凑不够！因此所有动态码长 <code>≤ ${maxTrueDepth}</code>，不仅 <code>trees.c:577</code> 直接返回，而且树头里的码长符号 <code>${maxTrueDepth + 1}..15</code> 出现次数恒为 <strong>0</strong>。`
          : `<span class="zc-badge zc-badge-ink">memLevel ${memLevel} · SHALLOW TREE</span> Total weight is at most <code>${Wmax} &lt; F(${maxTrueDepth + 3}) = ${FIB[maxTrueDepth + 3]}</code>: no code can exceed <strong>${maxTrueDepth} bits</strong>. Not only does <code>trees.c:577</code> always return early, bit-length symbols <code>${maxTrueDepth + 1}..15</code> never appear in the header!`;
      } else if (memLevel <= 4) {
        q('[data-role="fib-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-safe">memLevel ${memLevel} · 对应 C 第 577 行提前返回</span> 因为 <code>B + 2 = ${Wmax} &lt; 1597 = F(17)</code>，任何节点都不可能长到深度 16！这直接对应 C 代码 <code>gen_bitlen</code> 第 577 行的 <code>if (overflow == 0) return;</code> <strong>100% 走提前返回分支</strong>，完全避开了截断修复带来的额外码长膨胀。`
          : `<span class="zc-badge zc-badge-safe">memLevel ${memLevel} · MAPS DIRECTLY TO trees.c:577</span> Because <code>B + 2 = ${Wmax} &lt; 1597 = F(17)</code>, no node can reach depth 16! That mathematical fact connects directly to C control flow: <code>if (overflow == 0) return;</code> at <code>trees.c:577</code> <strong>always</strong> takes the early exit.`;
      } else {
        q('[data-role="fib-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-warn">memLevel ${memLevel} · 可触发 15 位截断</span> 当 <code>B = ${B.toLocaleString()}</code> 时总频数可达 <code>${Wmax.toLocaleString()} ≥ 1597</code>，极端偏斜的词频能长出超过 15 层的树并进入 <code>trees.c:583</code> 的修复循环。好在此时 <code>8B = ${(8 * B).toLocaleString()}</code> bits 足够宽裕，通用斜率 <code>6.257</code> 轻松过关。`
          : `<span class="zc-badge zc-badge-warn">memLevel ${memLevel} · CLAMPING REACHABLE</span> With <code>W_max = ${Wmax.toLocaleString()} ≥ 1597</code>, skewed inputs can exceed depth 15 and enter <code>trees.c:583</code>'s repair loop—but here <code>8B = ${(8 * B).toLocaleString()}</code> bits is wide enough that the <code>6.257</code> bits/symbol bound holds easily.`;
      }
    };

    q('[data-role="mem"]').addEventListener("click", (e) => {
      const btn = e.target.closest("button[data-m]");
      if (!btn) return;
      memLevel = Number(btn.dataset.m);
      el.querySelectorAll('[data-role="mem"] button').forEach((b) => b.classList.toggle("is-active", b === btn));
      render();
    });
    slider.addEventListener("input", () => {
      depth = Number(slider.value);
      render();
    });

    render();
  };

  /* ==========================================================================
   * WIDGET 4: THE memLevel 1..9 BUDGET RAZOR (3-Bar Comparison!)
   * ========================================================================== */
  const REGIME_DATA = [
    { mem: 1, B: 128,   hdr: 0,    comb: 999,    proved: 1024,   realHE: 720,   realGapB: 37,    thm: "tinyOverlayAt_128",   regime: 3 },
    { mem: 2, B: 256,   hdr: 0,    comb: 2023,   proved: 2048,   realHE: 1038,  realGapB: 126,   thm: "tinyOverlayAt_256",   regime: 3 },
    { mem: 3, B: 512,   hdr: 2283, excess: 1777, proved: 4085,   realHE: 1296,  realGapB: 349,   thm: "dynamic_overlay_mid", regime: 2 },
    { mem: 4, B: 1024,  hdr: 2283, excess: 3678, proved: 5986,   realHE: 1764,  realGapB: 803,   thm: "dynamic_overlay_mid", regime: 2 },
    { mem: 5, B: 2048,  hdr: 2283, excess: 12827, proved: 15135, realHE: 2529,  realGapB: 1731,  thm: "dynamic_overlay_large", regime: 1 },
    { mem: 6, B: 4096,  hdr: 2283, excess: 25641, proved: 27949, realHE: 4110,  realGapB: 3582,  thm: "dynamic_overlay_large", regime: 1 },
    { mem: 7, B: 8192,  hdr: 2283, excess: 51270, proved: 53578, realHE: 6794,  realGapB: 7342,  thm: "dynamic_overlay_large", regime: 1 },
    { mem: 8, B: 16384, hdr: 2283, excess: 102528, proved: 104836, realHE: 10457, realGapB: 15076, thm: "dynamic_overlay_large", regime: 1 },
    { mem: 9, B: 32768, hdr: 2283, excess: 205042, proved: 207350, realHE: 16822, realGapB: 30665, thm: "dynamic_overlay_large", regime: 1 },
  ];

  const mountRegimes = (el) => {
    const zh = getLang(el) === "zh";
    let idx = 0;

    el.innerHTML = `
      <div class="zc-bar">
        <div class="zc-title-wrap">
          <span class="zc-kicker">${zh ? "交互演示 05 · 全部 9 个 memLevel：粗放上界 vs. Lean 证明上界 vs. 真实 C 极限" : "INTERACTIVE 05 · ALL NINE memLevels: NAIVE FORMULA VS. LEAN BOUND VS. REAL C"}</span>
          <span class="zc-title">${zh ? "三把尺子对比：为什么小缓冲区必须分段证明？" : "Three Rulers Compared Against the 8B Head-Start Wall"}</span>
        </div>
        <div class="zc-controls">
          <span style="font-family:monospace;font-size:11px;color:#666;">memLevel:</span>
          <div class="zc-seg" data-role="r-tabs">
            ${REGIME_DATA.map((d, i) => `<button type="button" data-i="${i}" class="${i === idx ? "is-active" : ""}">${d.mem}</button>`).join("")}
          </div>
        </div>
      </div>
      <div class="zc-metrics">
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "起跑空间 8B" : "HEAD START BUDGET (8B)"}</div>
          <div class="zc-metric-val" data-r="budget">1,024 bits</div>
          <div class="zc-metric-sub" data-r="b-bytes">B = 128 B (4B = 512 B)</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "Lean 4 证明上界" : "LEAN 4 PROVED BOUND"}</div>
          <div class="zc-metric-val" data-r="proved">1,024 bits</div>
          <div class="zc-metric-sub" data-r="proved-sub">proof slack: 0 bits</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "真实动态块物理峰值" : "REAL DYNAMIC EXTREMUM"}</div>
          <div class="zc-metric-val zc-val-safe" data-r="real">730 bits</div>
          <div class="zc-metric-sub" data-r="real-sub">min gap: 37 B (+294b)</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "Z_FIXED 固定块最近间距" : "Z_FIXED MIN MARGIN"}</div>
          <div class="zc-metric-val" data-r="fixed-gap">18 B (+132b)</div>
          <div class="zc-metric-sub">${zh ? "17 B (+125b) @ Assert" : "17 B (+125b) @ Assert"}</div>
        </div>
      </div>
      <div class="zc-stage">
        <div class="zc-regime-bars">
          <div>
            <div style="display:flex;justify-content:space-between;font-family:monospace;font-size:11px;margin-bottom:4px;">
              <span>${zh ? "① 粗放通用公式 (2283 + 6.257(B+2) + 25)" : "① Naive General Formula (2283 + 6.257(B+2) + 25)"}</span>
              <strong data-r="bar1-lbl"></strong>
            </div>
            <div class="zc-bar-track">
              <div class="zc-bar-seg" data-r="n-bar" style="left:0;width:50%;background:#94a3b8;"></div>
              <div class="zc-wall-line" style="left:62.5%;"></div>
            </div>
          </div>

          <div>
            <div style="display:flex;justify-content:space-between;font-family:monospace;font-size:11px;margin-bottom:4px;">
              <span>${zh ? "② Lean 4 分段定理证明上界" : "② Lean 4 Stratified Theorem"} (<code data-r="thm" style="font-size:11px;"></code>)</span>
              <strong data-r="bar2-lbl"></strong>
            </div>
            <div class="zc-bar-track">
              <div class="zc-bar-seg" data-r="p-fixed" style="left:0;background:#b45309;"></div>
              <div class="zc-bar-seg" data-r="p-hdr" style="background:#64748b;"></div>
              <div class="zc-bar-seg" data-r="p-exc" style="background:#0f766e;"></div>
              <div class="zc-wall-line" style="left:62.5%;"></div>
            </div>
          </div>

          <div>
            <div style="display:flex;justify-content:space-between;font-family:monospace;font-size:11px;margin-bottom:4px;">
              <span>${zh ? "③ 真实 C 动态块可构造峰值 (7 + 3 + H + E)" : "③ Constructible Real-C Dynamic Peak (7 + 3 + H + E)"}</span>
              <strong data-r="bar3-lbl" class="zc-val-safe"></strong>
            </div>
            <div class="zc-bar-track">
              <div class="zc-bar-seg" data-r="c-bar" style="left:0;background:#1d4ed8;"></div>
              <div class="zc-wall-line" style="left:62.5%;"></div>
            </div>
          </div>
        </div>

        <div style="position:relative;height:18px;margin-top:4px;font-family:monospace;font-size:10.5px;color:#0a0a0a;">
          <span style="position:absolute;left:0;">0</span>
          <span style="position:absolute;left:62.5%;transform:translateX(-50%);font-weight:700;" data-r="wall-lbl">▲ 8B WALL (1024b)</span>
          <span style="position:absolute;right:0;color:#737370;" data-r="max-scale">1.6 × 8B</span>
        </div>

        <div class="zc-legend">
          <span><i class="zc-swatch" style="background:#b45309;"></i>${zh ? "固定开销 25b" : "Fixed 25b"}</span>
          <span><i class="zc-swatch" style="background:#64748b;"></i>${zh ? "证明树头界 (2283b)" : "Header bound (2283b)"}</span>
          <span><i class="zc-swatch" style="background:#0f766e;"></i>${zh ? "证明超额位 / 联合证书" : "Proved excess / certificate"}</span>
          <span><i class="zc-swatch" style="background:#1d4ed8;"></i>${zh ? "真实 C 动态块极值" : "Real-C Dynamic extremum"}</span>
          <span><i class="zc-swatch" style="background:#dc2626;"></i>${zh ? "超出 8B (证明失败!)" : "Exceeds 8B (proof fails!)"}</span>
        </div>
      </div>
      <div class="zc-note" data-role="r-note"></div>
    `;

    const q = (s) => el.querySelector(s);

    const render = () => {
      const d = REGIME_DATA[idx];
      const budget = 8 * d.B;
      const naive = 2283 + Math.ceil(6.257 * (d.B + 2)) + 25;
      const slack = budget - d.proved;
      const realBits = 10 + d.realHE; // v0=7 + tag=3 + H + E
      const realBitGap = budget - realBits;
      const fixedUnreadBits = budget - 10 - 7 * (d.B - 2);
      const fixedUnreadBytes = (d.B + 3 * (d.B - 2)) - 2 * Math.floor((9 + 31 * (d.B - 2)) / 16);

      const scaleMax = budget / 0.625;
      const pct = (v) => Math.min(100, (v / scaleMax) * 100);

      q('[data-r="budget"]').textContent = `${budget.toLocaleString()} bits`;
      q('[data-r="b-bytes"]').textContent = `B = ${d.B.toLocaleString()} B (4B = ${(4 * d.B).toLocaleString()} B)`;
      q('[data-r="proved"]').textContent = `${d.proved.toLocaleString()} bits`;
      q('[data-r="proved-sub"]').textContent = zh ? `证明余量: ${slack.toLocaleString()} bits` : `proof slack: ${slack.toLocaleString()} bits`;
      q('[data-r="real"]').textContent = `${realBits.toLocaleString()} bits`;
      q('[data-r="real-sub"]').textContent = zh ? `最小物理间距: ${d.realGapB.toLocaleString()} B (+${realBitGap.toLocaleString()}b)` : `min gap: ${d.realGapB.toLocaleString()} B (+${realBitGap.toLocaleString()}b)`;
      q('[data-r="fixed-gap"]').textContent = `${fixedUnreadBytes.toLocaleString()} B (+${fixedUnreadBits.toLocaleString()}b)`;

      q('[data-r="thm"]').textContent = d.thm;
      q('[data-r="wall-lbl"]').textContent = `▲ 8B = ${budget.toLocaleString()}b`;
      q('[data-r="max-scale"]').textContent = naive > scaleMax ? `(${Math.round((naive / budget) * 100)}% →)` : `${Math.round(scaleMax).toLocaleString()}b`;

      const nBar = q('[data-r="n-bar"]');
      nBar.style.width = `${pct(naive).toFixed(2)}%`;
      nBar.style.background = naive > budget ? "#dc2626" : "#64748b";
      q('[data-r="bar1-lbl"]').textContent = `${naive.toLocaleString()} / ${budget.toLocaleString()} bits (${((naive / budget) * 100).toFixed(1)}%)`;
      q('[data-r="bar1-lbl"]').className = naive > budget ? "zc-val-danger" : "";

      const wFixed = pct(25);
      const wHdr = d.regime === 3 ? 0 : pct(d.hdr);
      const wExc = d.regime === 3 ? pct(d.comb) : pct(d.excess);

      q('[data-r="p-fixed"]').style.width = `${wFixed.toFixed(2)}%`;
      q('[data-r="p-hdr"]').style.left = `${wFixed.toFixed(2)}%`;
      q('[data-r="p-hdr"]').style.width = `${wHdr.toFixed(2)}%`;
      q('[data-r="p-exc"]').style.left = `${(wFixed + wHdr).toFixed(2)}%`;
      q('[data-r="p-exc"]').style.width = `${wExc.toFixed(2)}%`;
      q('[data-r="bar2-lbl"]').textContent = `${d.proved.toLocaleString()} / ${budget.toLocaleString()} bits (${((d.proved / budget) * 100).toFixed(2)}%)`;

      q('[data-r="c-bar"]').style.width = `${pct(realBits).toFixed(2)}%`;
      q('[data-r="bar3-lbl"]').textContent = `${realBits.toLocaleString()} / ${budget.toLocaleString()} bits (H+E = ${d.realHE.toLocaleString()}b)`;

      if (d.regime === 3) {
        q('[data-role="r-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-warn">对比看清本质 (memLevel ${d.mem})</span> ① 粗放公式爆表到 <code>${naive.toLocaleString()}</code> bits；② 把 316 个树槽位解耦成逐项线性不等式后，连续线性规划极值已达 <code>979.1 + 25 ≈ 1004</code> bits，Lean 定理紧贴在 <code>${d.proved} / ${budget}</code>（0 bit 证明余量）；③ 而在真实 C 里，动态块受 <code>opt_lenb &lt; static_lenb</code> 制约，峰值停在 <code>${realBits}</code> bits（留 <strong>${d.realGapB} 字节 / +${realBitGap} bits</strong>），反倒是强制 <code>Z_FIXED</code> 固定块能逼近到 <strong>${fixedUnreadBytes} 字节 / +${fixedUnreadBits} bits</strong>！`
          : `<span class="zc-badge zc-badge-warn">THREE RULERS AT memLevel ${d.mem}</span> (1) The naive bound explodes to <code>${naive.toLocaleString()}</code> bits; (2) decoupling the 316 tree slots into independent linear inequalities puts the LP ceiling at <code>979.1 + 25 ≈ 1,004</code> bits, and the Lean certificate closes right at <code>${d.proved} / ${budget}</code> (0 proof slack); (3) in real C, <code>opt_lenb &lt; static_lenb</code> caps Dynamic blocks at <code>${realBits}</code> bits (<strong>${d.realGapB} B / +${realBitGap}b</strong> margin), whereas <code>Z_FIXED</code> reaches <strong>${fixedUnreadBytes} B / +${fixedUnreadBits}b</strong>!`;
      } else if (d.regime === 2) {
        q('[data-role="r-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-safe">F(17) = 1597 救场 (memLevel ${d.mem})</span> 粗放公式算得 <code>${naive.toLocaleString()} &gt; ${budget.toLocaleString()}</code>（红条越界！）。靠着 <code>trees.c:577</code> 零截断提前返回，Lean 证明上界压回 <code>${d.proved.toLocaleString()}</code> bits（剩 <code>${slack.toLocaleString()}</code> bits），而真实 C 动态块最多只用到 <code>${realBits.toLocaleString()}</code> bits。`
          : `<span class="zc-badge zc-badge-safe">SAVED BY F(17) = 1597 (memLevel ${d.mem})</span> The naive formula overflows (<code>${naive.toLocaleString()} &gt; ${budget.toLocaleString()}</code>). Proving <code>trees.c:577</code> always returns early drops the Lean bound to <code>${d.proved.toLocaleString()}</code> bits (<code>${slack.toLocaleString()}</code> bits slack), while real C Dynamic blocks peak at <code>${realBits.toLocaleString()}</code> bits.`;
      } else {
        q('[data-role="r-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-safe">渐近宽裕区 (memLevel ${d.mem})</span> 从 <code>B = 2048</code> 起，<code>8B = ${budget.toLocaleString()}</code> bits 足够大，连最粗放的第一区间通用公式也稳稳过关（真实动态块仅消耗 <code>${realBits.toLocaleString()}</code> bits，剩余逾 <code>${d.realGapB.toLocaleString()}</code> 字节空间）。`
          : `<span class="zc-badge zc-badge-safe">ASYMPTOTIC HEADROOM (memLevel ${d.mem})</span> For <code>B ≥ 2048</code>, <code>8B = ${budget.toLocaleString()}</code> bits is wide enough that even the general clamped slope <code>6.257</code> clears the wall with <code>${slack.toLocaleString()}</code> bits to spare.`;
      }
    };

    q('[data-role="r-tabs"]').addEventListener("click", (e) => {
      const btn = e.target.closest("button[data-i]");
      if (!btn) return;
      idx = Number(btn.dataset.i);
      el.querySelectorAll('[data-role="r-tabs"] button').forEach((b) => b.classList.toggle("is-active", b === btn));
      render();
    });

    render();
  };

  const mountAll = () => {
    injectStyles();
    document.querySelectorAll("[data-zc]").forEach((el) => {
      if (el.dataset.zcReady === "v5") return;
      el.dataset.zcReady = "v5";
      const kind = el.dataset.zc;
      if (kind === "pipeline") mountPipeline(el);
      else if (kind === "race") mountRace(el);
      else if (kind === "oob") mountOob(el);
      else if (kind === "fib") mountFib(el);
      else if (kind === "regimes") mountRegimes(el);
    });
  };

  window.__mountZlibChaseV5 = mountAll;
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", mountAll);
  } else {
    mountAll();
  }
  window.addEventListener("spa:navigation", mountAll);
})();
