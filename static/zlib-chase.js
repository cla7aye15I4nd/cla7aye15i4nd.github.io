(() => {
  if (window.__zlibChaseLoaded) {
    window.__mountZlibChase?.();
    return;
  }
  window.__zlibChaseLoaded = true;

  const STYLE_ID = "zc-interactive-styles";
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
  font-size: 15px;
  font-weight: 600;
  font-variant-numeric: tabular-nums;
  color: #0a0a0a;
  white-space: nowrap;
  overflow: hidden;
  text-overflow: ellipsis;
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
  padding: 11px 18px;
  background: #eeeeec;
  border-top: 1px dashed #cfcfcc;
  font-size: 13px;
  line-height: 1.55;
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
  transition: x 140ms cubic-bezier(0.22, 1, 0.36, 1), width 140ms cubic-bezier(0.22, 1, 0.36, 1), fill 140ms ease;
}
.zc-anim-x {
  transition: transform 140ms cubic-bezier(0.22, 1, 0.36, 1);
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
.zc-split {
  display: grid;
  grid-template-columns: 1.15fr 0.85fr;
  gap: 18px;
  align-items: start;
}
.zc-regime-bars {
  display: grid;
  gap: 16px;
}
.zc-bar-track {
  position: relative;
  height: 34px;
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
  gap: 12px 18px;
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
  .zc-split {
    grid-template-columns: 1fr;
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
   * WIDGET 1: THE OVERLAY BUFFER RACE (pending_buf vs sym_buf)
   * ========================================================================== */
  const buildRaceScenarios = (zh) => {
    const B = 128; // memLevel = 1 -> lit_bufsize = 128, 4B = 512 bytes = 4096 bits
    const N = 127; // max symbols = B - 1

    const makeTrace = (headerBits, entryBits, costFn) => {
      const steps = [];
      let rawBits = entryBits + 3 + headerBits;
      for (let k = 0; k <= N; k++) {
        const readBit = 8 * (B + 3 * k);
        const probeBit = rawBits + 15; // 8*pending + bi_valid + 15
        const pendingBytes = Math.floor(rawBits / 16) * 2;
        const biValid = rawBits - pendingBytes * 8;
        steps.push({
          k,
          rawBits,
          probeBit,
          readBit,
          gap: readBit - probeBit,
          pendingBytes,
          biValid,
          nextCost: k < N ? costFn(k) : 0,
        });
        if (k < N) rawBits += costFn(k);
      }
      let minIdx = 0;
      for (let i = 1; i < steps.length; i++) {
        if (steps[i].gap < steps[minIdx].gap) minIdx = i;
      }
      return { B, N, headerBits, entryBits, steps, minIdx };
    };

    return [
      {
        id: "fixed",
        tab: zh ? "01 · 固定编码 (≤31b)" : "01 · Fixed (≤31b/sym)",
        trace: makeTrace(0, 7, () => 31),
        describe: (s, minIdx) => {
          if (zh) {
            return `<span class="zc-badge zc-badge-safe">安全 · 固定树</span> <code>deflate.c</code> 注释里的理想情形：头部仅 3 bit，每个匹配至多耗费 <code>8+5+5+13 = 31</code> bit，相比读指针释放的 24 bit 每步净追近 7 bit。差距单调缩小，最窄处在末尾 <code>k = ${minIdx}</code>（仍剩 <code>+${s.gap}</code> bit 余量）。`;
          }
          return `<span class="zc-badge zc-badge-safe">SAFE · FIXED TREES</span> The exact world of the <code>deflate.c</code> comment: 3-bit header, at most <code>8+5+5+13 = 31</code> bits per match (+7 bits/step net catch-up vs. 24 bits freed). The gap shrinks monotonically and reaches its minimum at the very end (<code>k = ${minIdx}</code>, <code>+${s.gap}</code> bits left).`;
        },
      },
      {
        id: "surge",
        tab: zh ? "02 · 动态块前置突进" : "02 · Dynamic Surge",
        trace: makeTrace(290, 7, (k) => (k < 26 ? 42 : 2)),
        describe: (s, minIdx) => {
          if (zh) {
            if (s.k === 0) {
              return `<span class="zc-badge zc-badge-warn">头部先行</span> 还没读第 0 个符号，<code>send_all_trees</code> 就已经向 <code>pending_buf</code> 写出了 290 bit 树描述！算上入口残留位与 15 bit 缓冲余量，起点已消耗 <code>315 / 1024</code> bit。`;
            }
            if (s.k <= 26) {
              return `<span class="zc-badge zc-badge-warn">前置长码突进</span> 前 26 个符号是罕见长距离匹配（每个 42 bit，每步追近 +18 bit）！差距在块中途 <code>k = ${minIdx}</code> 处骤降到最低点（<code>+241</code> bit）——证明“整块平均码长 &lt; 31”根本推不出中途不撞车。`;
            }
            return `<span class="zc-badge zc-badge-safe">高频短码拉开</span> 后 101 个符号全是 2 bit 的高频字面量（每步反而拉开 22 bit！）。整块平均每符号仅 <code>12.5</code> bit，远优于固定树，因此 <code>_tr_flush_block</code> 必然选中动态块，但最危险的时刻发生在块的前 1/5！`;
          }
          if (s.k === 0) {
            return `<span class="zc-badge zc-badge-warn">UPFRONT HEADER</span> Before symbol 0 is even read, <code>send_all_trees</code> emits 290 bits of Huffman tree tables—consuming <code>315 / 1024</code> bits of the head start right out of the gate.`;
          }
          if (s.k <= 26) {
            return `<span class="zc-badge zc-badge-warn">MID-BLOCK PINCH</span> Front-loaded 42-bit matches gain +18 bits/step on the read cursor! The minimum gap occurs mid-block at <code>k = ${minIdx}</code> (<code>+241</code> bits), refuting the comment's assumption that the end of the block is always the closest point.`;
          }
          return `<span class="zc-badge zc-badge-safe">TAIL RECOVERY</span> The remaining 101 symbols are 2-bit literals (-22 bits/step): the read cursor rockets away! Overall average is just <code>12.5</code> bits/sym—beating fixed codes easily—even though the chaser surged dangerously close at <code>k = 26</code>.`;
        },
      },
      {
        id: "collision",
        tab: zh ? "03 · 假想无约束 48b (撞车!)" : "03 · Unconstrained 48b (Crash!)",
        trace: makeTrace(420, 7, (k) => (k < 36 ? 48 : 1)),
        describe: (s) => {
          if (zh) {
            if (s.gap >= 0) {
              return `<span class="zc-badge zc-badge-warn">逼近追尾</span> 如果攻击者能白拿 48 bit 的动态匹配码（<code>15+5+15+13</code>，每步净追近 +24 bit）而无需支付频率代价：继续向右拖动滑块到 <code>k = 25</code> 看看会发生什么！`;
            }
            return `<span class="zc-badge zc-badge-danger">缓冲区追尾覆盖!</span> 在 <code>k = 25</code> 处写指针越过 <code>B + 3k</code>（余量 <code>${s.gap}</code> bit）！未读的符号三元组被压缩比特流直接覆写，伪造出越界的 16 位 <code>dist</code>，随即击穿静态表 <code>_dist_code[512]</code>！现实中正是 Fibonacci 频率下界阻止了这一幕。`;
          }
          if (s.gap >= 0) {
            return `<span class="zc-badge zc-badge-warn">CLOSING IN</span> What if an attacker could front-load thirty-six 48-bit matches (<code>15+5+15+13</code>, +24 bits/step net catch-up) followed by ninety-one 1-bit literals (still averaging 17.7 bits/sym &lt; 31)? Step past <code>k = 25</code> to watch the crash.`;
          }
          return `<span class="zc-badge zc-badge-danger">OVERLAY COLLISION!</span> At <code>k = 25</code>, the write cursor overtakes <code>B + 3k</code> (margin <code>${s.gap}</code> bits), overwriting unread 3-byte symbols in <code>sym_buf</code> and corrupting <code>dist</code> into an out-of-bounds read on <code>_dist_code[512]</code>! Only Huffman's Fibonacci weight law makes this distribution impossible.`;
        },
      },
    ];
  };

  const mountRace = (el) => {
    const zh = getLang(el) === "zh";
    const scenarios = buildRaceScenarios(zh);
    let scenIdx = 1; // Start on Dynamic Surge — most visually revealing!
    let k = 0;
    let timer = null;

    el.innerHTML = `
      <div class="zc-bar">
        <div class="zc-title-wrap">
          <span class="zc-kicker">${zh ? "交互演示 01 · 同缓冲双指针追逐 (B = 128)" : "INTERACTIVE 01 · TWO CURSORS IN ONE 4B BUFFER (B = 128)"}</span>
          <span class="zc-title">${zh ? "pending_buf 写指针 vs. sym_buf 读指针" : "Write Cursor (pending) Chasing Read Cursor (B + 3k)"}</span>
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
          <div class="zc-metric-label">${zh ? "当前符号 k" : "SYMBOL INDEX k"}</div>
          <div class="zc-metric-val" data-m="k">0 / 127</div>
          <div class="zc-metric-sub" data-m="sx">sx = 0 B</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "写指针包络 (CHASER)" : "WRITE ENVELOPE (CHASER)"}</div>
          <div class="zc-metric-val" data-m="write">0 bits</div>
          <div class="zc-metric-sub" data-m="write-sub">pending = 0 B, bi_valid = 0</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "未读符号起点 (RUNNER)" : "NEXT UNREAD SYM (RUNNER)"}</div>
          <div class="zc-metric-val" data-m="read">1024 bits</div>
          <div class="zc-metric-sub" data-m="read-sub">offset B + 3k = 128 B</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "实时安全余量" : "SAFETY MARGIN"}</div>
          <div class="zc-metric-val" data-m="gap">+709 bits</div>
          <div class="zc-metric-sub" data-m="gap-sub">8(B+3k) − (8·pending+bi_valid+15)</div>
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

          <!-- Top section: Memory Tape [0 .. 4096 bits = 512 bytes] -->
          <text x="20" y="15" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#6b6b66">
            ${zh ? "pending_buf 内存视图 [0 .. 4B = 512 字节 / 4096 bits]" : "pending_buf MEMORY MAP [0 .. 4B = 512 BYTES / 4096 BITS]"}
          </text>
          <text x="860" y="15" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#6b6b66">4B = 4096b</text>

          <!-- Outer buffer frame x=20..860 (width 840), y=44..88 -->
          <rect x="20" y="44" width="840" height="44" fill="url(#zc-hatch-free)" stroke="#111" stroke-width="1.2" />

          <!-- Header bits -->
          <rect data-svg="hdr-rect" class="zc-anim-rect" x="20" y="44" width="0" height="44" fill="#d6d3c9" />
          <!-- Payload written bits -->
          <rect data-svg="pay-rect" class="zc-anim-rect" x="20" y="44" width="0" height="44" fill="#e7cfc8" />
          <!-- bi_buf + 15b active probe -->
          <rect data-svg="probe-rect" class="zc-anim-rect" x="20" y="44" width="4" height="44" fill="#c23b22" />

          <!-- Consumed symbols [B .. B+3k) -->
          <rect data-svg="read-done" class="zc-anim-rect" x="230" y="44" width="0" height="44" fill="#e5e5e0" opacity="0.85" />
          <!-- Unread symbols [B+3k .. B+3n) -->
          <rect data-svg="unread-rect" class="zc-anim-rect" x="230" y="44" width="625" height="44" fill="#dfe7ec" stroke="#334155" stroke-width="0.8" />
          <!-- Overwritten collision zone -->
          <rect data-svg="crash-rect" class="zc-anim-rect" x="230" y="44" width="0" height="44" fill="url(#zc-hatch-danger)" stroke="#b91c1c" stroke-width="1.4" />

          <!-- Offset B marker inside bar (x = 20 + 840 * 0.25 = 230) -->
          <line x1="230" y1="44" x2="230" y2="88" stroke="#52524e" stroke-width="1" stroke-dasharray="3 2" />
          <text x="225" y="69" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#52524e">B=1024b</text>

          <!-- Write cursor pin (TOP RAIL — never collides with bottom runner!) -->
          <g data-svg="write-pin" class="zc-anim-x" transform="translate(20, 0)">
            <line x1="0" y1="38" x2="0" y2="91" stroke="#b91c1c" stroke-width="2.2" />
            <polygon points="-5,38 5,38 0,44" fill="#b91c1c" />
            <text data-svg="write-lbl" x="0" y="33" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10.5" font-weight="700" fill="#b91c1c">
              ${zh ? "▼ 写包络" : "▼ CHASER"}
            </text>
          </g>

          <!-- Read cursor pin (BOTTOM RAIL) -->
          <g data-svg="read-pin" class="zc-anim-x" transform="translate(230, 0)">
            <line x1="0" y1="41" x2="0" y2="94" stroke="#0a0a0a" stroke-width="2.2" />
            <polygon points="-5,94 5,94 0,88" fill="#0a0a0a" />
            <text data-svg="read-lbl" x="0" y="108" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10.5" font-weight="700" fill="#0a0a0a">
              ${zh ? "▲ 读指针 B+3k" : "▲ RUNNER B+3k"}
            </text>
          </g>

          <!-- Bottom section: Synchronized Trajectory Chart (x=54..850, y=150..298) -->
          <text x="54" y="142" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#6b6b66">
            ${zh ? "全程轨迹图：点击或拖动图表任意位置跳转符号 k" : "TRAJECTORY ACROSS BLOCK (CLICK OR DRAG ON CHART TO SCRUB k)"}
          </text>
          <rect data-svg="chart-bg" x="54" y="150" width="796" height="148" fill="#f6f6f3" stroke="#c8c8c4" stroke-width="1" style="cursor: crosshair;" />

          <!-- Horizontal gridlines -->
          <line x1="54" y1="261" x2="850" y2="261" stroke="#deded9" stroke-dasharray="3 3" />
          <text x="48" y="264" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#787874">1024</text>
          <line x1="54" y1="224" x2="850" y2="224" stroke="#deded9" stroke-dasharray="3 3" />
          <text x="48" y="227" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#787874">2048</text>
          <line x1="54" y1="187" x2="850" y2="187" stroke="#deded9" stroke-dasharray="3 3" />
          <text x="48" y="190" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#787874">3072</text>
          <text x="48" y="154" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#787874">4096</text>
          <text x="48" y="300" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#787874">0</text>

          <!-- Shaded area between read & write -->
          <path data-svg="gap-area" d="" fill="rgba(15, 118, 110, 0.09)" />
          <path data-svg="crash-area" d="" fill="rgba(185, 28, 28, 0.18)" />

          <!-- Read line & Write curve -->
          <path data-svg="read-path" d="" fill="none" stroke="#0a0a0a" stroke-width="1.8" stroke-dasharray="5 4" />
          <path data-svg="write-path" d="" fill="none" stroke="#b91c1c" stroke-width="2.2" />

          <!-- Pinch / Minimum gap annotation with clean opaque pill & leader line -->
          <g data-svg="pinch-marker" style="pointer-events: none;">
            <line data-svg="pinch-line" x1="0" y1="0" x2="0" y2="0" stroke="#0f766e" stroke-width="1.4" stroke-dasharray="2 2" />
            <line data-svg="pinch-leader" x1="0" y1="0" x2="0" y2="0" stroke="#0f766e" stroke-width="1" />
            <rect data-svg="pinch-bg" x="0" y="0" width="140" height="20" rx="2" fill="#fbfbfa" stroke="#0f766e" stroke-width="1" />
            <text data-svg="pinch-label" x="0" y="0" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10" font-weight="600" fill="#0f766e"></text>
          </g>

          <!-- Playhead on chart -->
          <line data-svg="playhead" x1="54" y1="150" x2="54" y2="298" stroke="#0a0a0a" stroke-width="1.2" />
          <circle data-svg="dot-read" cx="54" cy="261" r="4" fill="#0a0a0a" />
          <circle data-svg="dot-write" cx="54" cy="288" r="4.5" fill="#b91c1c" stroke="#fff" stroke-width="1" />

          <text x="54" y="316" font-family="Menlo, Consolas, monospace" font-size="10" fill="#6b6b66">k = 0</text>
          <text x="452" y="316" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10" fill="#6b6b66">
            ${zh ? "符号序号 k (每步读出 3 字节 = 24 bits)" : "symbol index k (each step reads 3 bytes = 24 bits)"}
          </text>
          <text x="850" y="316" text-anchor="end" font-family="Menlo, Consolas, monospace" font-size="10" fill="#6b6b66">k = 127</text>
        </svg>
      </div>
      <div class="zc-scrubber-row">
        <label data-role="slider-label">k = 0</label>
        <input type="range" class="zc-range" min="0" max="127" value="0" data-role="slider" />
        <label>${zh ? "下一符号代价:" : "Next sym cost:"} <strong data-role="next-cost">42b</strong></label>
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
      const wPts = st.map((p) => `${chartX(p.k).toFixed(1)},${chartY(p.probeBit).toFixed(1)}`);
      q('[data-svg="read-path"]').setAttribute("d", `M ${rPts.join(" L ")}`);
      q('[data-svg="write-path"]').setAttribute("d", `M ${wPts.join(" L ")}`);

      const safeTop = st.map((p) => `${chartX(p.k).toFixed(1)},${chartY(p.readBit).toFixed(1)}`);
      const safeBot = [...st].reverse().map((p) => `${chartX(p.k).toFixed(1)},${chartY(Math.min(p.readBit, p.probeBit)).toFixed(1)}`);
      q('[data-svg="gap-area"]').setAttribute("d", `M ${safeTop.join(" L ")} L ${safeBot.join(" L ")} Z`);

      const hasCrash = st.some((p) => p.probeBit > p.readBit);
      if (hasCrash) {
        const cTop = st.map((p) => `${chartX(p.k).toFixed(1)},${chartY(Math.max(p.readBit, p.probeBit)).toFixed(1)}`);
        const cBot = [...st].reverse().map((p) => `${chartX(p.k).toFixed(1)},${chartY(p.readBit).toFixed(1)}`);
        q('[data-svg="crash-area"]').setAttribute("d", `M ${cTop.join(" L ")} L ${cBot.join(" L ")} Z`);
      } else {
        q('[data-svg="crash-area"]').setAttribute("d", "");
      }

      const minStep = st[sc.trace.minIdx];
      const px = chartX(minStep.k);
      const py1 = chartY(minStep.readBit);
      const py2 = chartY(minStep.probeBit);
      const pLine = q('[data-svg="pinch-line"]');
      const pLeader = q('[data-svg="pinch-leader"]');
      const pBg = q('[data-svg="pinch-bg"]');
      const pLbl = q('[data-svg="pinch-label"]');
      pLine.setAttribute("x1", px.toFixed(1));
      pLine.setAttribute("x2", px.toFixed(1));
      pLine.setAttribute("y1", py1.toFixed(1));
      pLine.setAttribute("y2", py2.toFixed(1));
      const isNeg = minStep.gap < 0;
      const stroke = isNeg ? "#b91c1c" : "#0f766e";
      const txt = isNeg
        ? (zh ? `撞车! (${minStep.gap}b)` : `COLLISION (${minStep.gap}b)`)
        : (zh ? `最窄 @ k=${minStep.k} (+${minStep.gap}b)` : `min gap @ k=${minStep.k} (+${minStep.gap}b)`);

      // Position badge in clean open space for each scenario
      let bx, by, ax, ay;
      if (scenIdx === 0) {
        bx = 720; by = 196; ax = px; ay = (py1 + py2) / 2;
      } else if (scenIdx === 1) {
        bx = 320; by = 272; ax = px; ay = py2;
      } else {
        bx = 210; by = 172; ax = px; ay = Math.min(py1, py2);
      }
      const bw = Math.max(128, txt.length * 7.2 + 18);
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
      q('[data-m="write"]').textContent = `${s.probeBit} bits`;
      q('[data-m="write-sub"]').textContent = `pending = ${s.pendingBytes} B, bi_valid = ${s.biValid} (+15b)`;
      q('[data-m="read"]').textContent = `${s.readBit} bits`;
      q('[data-m="read-sub"]').textContent = `B + 3k = ${128 + 3 * k} B`;

      const gapEl = q('[data-m="gap"]');
      gapEl.textContent = `${s.gap >= 0 ? "+" : ""}${s.gap} bits`;
      gapEl.className = "zc-metric-val " + (s.gap < 0 ? "zc-val-danger" : s.gap < 280 ? "zc-val-warn" : "zc-val-safe");

      // Tape positions
      const hdrEnd = tapeX(sc.trace.entryBits + 3 + sc.trace.headerBits);
      const rawEnd = tapeX(s.rawBits);
      const probeEnd = tapeX(s.probeBit);
      const bStart = tapeX(1024);
      const readPos = tapeX(s.readBit);
      const symEndPos = tapeX(8 * (128 + 3 * 127));

      q('[data-svg="hdr-rect"]').setAttribute("width", Math.max(0, hdrEnd - 20).toFixed(1));
      q('[data-svg="pay-rect"]').setAttribute("x", hdrEnd.toFixed(1));
      q('[data-svg="pay-rect"]').setAttribute("width", Math.max(0, rawEnd - hdrEnd).toFixed(1));
      q('[data-svg="probe-rect"]').setAttribute("x", rawEnd.toFixed(1));
      q('[data-svg="probe-rect"]').setAttribute("width", Math.max(2, probeEnd - rawEnd).toFixed(1));

      q('[data-svg="read-done"]').setAttribute("x", bStart.toFixed(1));
      q('[data-svg="read-done"]').setAttribute("width", Math.max(0, readPos - bStart).toFixed(1));

      q('[data-svg="unread-rect"]').setAttribute("x", readPos.toFixed(1));
      q('[data-svg="unread-rect"]').setAttribute("width", Math.max(0, symEndPos - readPos).toFixed(1));

      if (s.probeBit > s.readBit) {
        const crashW = Math.min(symEndPos, probeEnd) - readPos;
        q('[data-svg="crash-rect"]').setAttribute("x", readPos.toFixed(1));
        q('[data-svg="crash-rect"]').setAttribute("width", Math.max(0, crashW).toFixed(1));
      } else {
        q('[data-svg="crash-rect"]').setAttribute("width", "0");
      }

      q('[data-svg="write-pin"]').setAttribute("transform", `translate(${probeEnd.toFixed(1)}, 0)`);
      q('[data-svg="write-lbl"]').setAttribute("x", probeEnd < 60 ? String(60 - probeEnd) : probeEnd > 820 ? String(820 - probeEnd) : "0");
      q('[data-svg="read-pin"]').setAttribute("transform", `translate(${readPos.toFixed(1)}, 0)`);
      q('[data-svg="read-lbl"]').setAttribute("x", readPos > 805 ? String(805 - readPos) : "0");

      const cx = chartX(k);
      q('[data-svg="playhead"]').setAttribute("x1", cx.toFixed(1));
      q('[data-svg="playhead"]').setAttribute("x2", cx.toFixed(1));
      q('[data-svg="dot-read"]').setAttribute("cx", cx.toFixed(1));
      q('[data-svg="dot-read"]').setAttribute("cy", chartY(s.readBit).toFixed(1));
      q('[data-svg="dot-write"]').setAttribute("cx", cx.toFixed(1));
      q('[data-svg="dot-write"]').setAttribute("cy", chartY(s.probeBit).toFixed(1));

      q('[data-role="note"]').innerHTML = sc.describe(s, sc.trace.minIdx);
    };

    const stopPlay = () => {
      if (timer) {
        clearInterval(timer);
        timer = null;
      }
      playBtn.textContent = zh ? "▶ 播放" : "▶ Play";
      playBtn.classList.remove("is-active");
    };

    const startPlay = () => {
      if (k >= 127) k = 0;
      playBtn.textContent = zh ? "⏸ 暂停" : "⏸ Pause";
      playBtn.classList.add("is-active");
      timer = setInterval(() => {
        if (k < 127) {
          k++;
          render();
        } else {
          stopPlay();
        }
      }, 45);
    };

    q('[data-role="tabs"]').addEventListener("click", (e) => {
      const btn = e.target.closest("button[data-idx]");
      if (!btn) return;
      stopPlay();
      scenIdx = Number(btn.dataset.idx);
      el.querySelectorAll('[data-role="tabs"] button').forEach((b, i) => b.classList.toggle("is-active", i === scenIdx));
      k = scenIdx === 1 ? 26 : scenIdx === 2 ? 28 : 0;
      drawStaticPaths();
      render();
    });

    playBtn.addEventListener("click", () => (timer ? stopPlay() : startPlay()));
    q('[data-action="prev"]').addEventListener("click", () => { stopPlay(); k = Math.max(0, k - 1); render(); });
    q('[data-action="next"]').addEventListener("click", () => { stopPlay(); k = Math.min(127, k + 1); render(); });
    q('[data-action="reset"]').addEventListener("click", () => { stopPlay(); k = 0; render(); });
    slider.addEventListener("input", () => { stopPlay(); k = Number(slider.value); render(); });

    // Direct chart scrubbing
    const svg = q("svg");
    let dragging = false;
    const scrubFromEvent = (ev) => {
      const pt = svg.createSVGPoint();
      pt.x = ev.clientX;
      pt.y = ev.clientY;
      const ctm = svg.getScreenCTM();
      if (!ctm) return;
      const loc = pt.matrixTransform(ctm.inverse());
      const ratio = Math.max(0, Math.min(1, (loc.x - 54) / 796));
      k = Math.round(ratio * 127);
      render();
    };
    q('[data-svg="chart-bg"]').addEventListener("pointerdown", (ev) => {
      stopPlay();
      dragging = true;
      ev.target.setPointerCapture?.(ev.pointerId);
      scrubFromEvent(ev);
    });
    svg.addEventListener("pointermove", (ev) => { if (dragging) scrubFromEvent(ev); });
    window.addEventListener("pointerup", () => { dragging = false; });

    drawStaticPaths();
    k = 26; // Start right at the dramatic mid-block pinch of Dynamic Surge!
    render();
  };

  /* ==========================================================================
   * WIDGET 2: THE OUT-OF-BOUNDS CASCADE (_dist_code[512])
   * ========================================================================== */
  const mountOob = (el) => {
    const zh = getLang(el) === "zh";
    let dist = 48879; // 0xBEEF — vivid corrupted state by default!

    const presets = [
      { label: zh ? "合法匹配 (18,400)" : "Valid (18,400)", val: 18400 },
      { label: zh ? "最大合法距离 (32,768)" : "Max Valid (32,768)", val: 32768 },
      { label: zh ? "被覆盖符号 (0xBEEF)" : "Overwritten (0xBEEF)", val: 0xbeef },
      { label: zh ? "16 位上限 (0xFFFF)" : "Max uint16 (0xFFFF)", val: 0xffff },
    ];

    el.innerHTML = `
      <div class="zc-bar">
        <div class="zc-title-wrap">
          <span class="zc-kicker">${zh ? "交互演示 02 · 为什么压缩率问题会变成内存越界" : "INTERACTIVE 02 · WHY OVERLAY CORRUPTION BREAKS MEMORY SAFETY"}</span>
          <span class="zc-title">${zh ? "从被覆盖的 sym_buf 到 _dist_code[512] 越界读" : "From Overwritten sym_buf Bytes to _dist_code[512] Out-of-Bounds Read"}</span>
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
            <div class="zc-pipe-detail" data-p="bytes-sub">dist = 48879 (0xbeef)</div>
          </div>
          <div class="zc-pipe-box" data-box="dec">
            <div class="zc-pipe-step">2 · trees.c:929</div>
            <div class="zc-pipe-expr" data-p="dm1">dist-- → 48878</div>
            <div class="zc-pipe-detail" data-p="shift">(dist - 1) &gt;&gt; 7 = 381</div>
          </div>
          <div class="zc-pipe-box" data-box="idx">
            <div class="zc-pipe-step">3 · d_code(dist)</div>
            <div class="zc-pipe-expr" data-p="index">_dist_code[637]</div>
            <div class="zc-pipe-detail" data-p="index-sub">array length = 512!</div>
          </div>
          <div class="zc-pipe-box" data-box="res">
            <div class="zc-pipe-step">4 · Lean Kernel / C</div>
            <div class="zc-pipe-expr" data-p="verdict">Fault.ub (OOB)</div>
            <div class="zc-pipe-detail" data-p="verdict-sub">+126 B past _dist_code</div>
          </div>
        </div>

        <svg class="zc-svg" viewBox="0 0 860 112" role="img" aria-label="_dist_code memory layout">
          <text x="16" y="18" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#6b6b66">
            ${zh ? ".rodata 静态表布局：const uch _dist_code[512] vs. 越界区域 [512 .. 767]" : ".rodata LAYOUT: const uch _dist_code[512] VS. ADJACENT MEMORY [512 .. 767]"}
          </text>
          <!-- [0..255]: width 276 -->
          <rect x="16" y="28" width="276" height="42" fill="#e4ebe8" stroke="#0f766e" stroke-width="1" />
          <text x="154" y="47" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="11" font-weight="600" fill="#065f46">_dist_code[0 .. 255]</text>
          <text x="154" y="61" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#0f766e">dist 1 .. 256 (direct)</text>

          <!-- [256..511]: width 276 -->
          <rect x="292" y="28" width="276" height="42" fill="#d7e6e1" stroke="#0f766e" stroke-width="1" />
          <text x="430" y="47" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="11" font-weight="600" fill="#065f46">_dist_code[256 .. 511]</text>
          <text x="430" y="61" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#0f766e">dist 257 .. 32768 (256 + (d&gt;&gt;7))</text>

          <!-- [512..767]: OOB width 276 -->
          <rect x="568" y="28" width="276" height="42" fill="url(#zc-hatch-danger)" stroke="#b91c1c" stroke-width="1.3" />
          <rect x="568" y="28" width="276" height="42" fill="rgba(254,226,226,0.68)" stroke="#b91c1c" stroke-width="1.3" />
          <text x="706" y="47" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="11" font-weight="700" fill="#991b1b">
            ${zh ? "越界区 [512 .. 767] (OOB!)" : "OUT OF BOUNDS [512 .. 767]"}
          </text>
          <text x="706" y="61" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="9.5" fill="#b91c1c">dist 32769 .. 65535 → Fault.ub</text>

          <!-- Array end wall at 568 -->
          <line x1="568" y1="20" x2="568" y2="82" stroke="#0a0a0a" stroke-width="2" />
          <text x="568" y="95" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="10" font-weight="700" fill="#0a0a0a">sizeof = 512</text>

          <!-- Pointer needle -->
          <g data-svg="needle" class="zc-anim-x" transform="translate(600, 0)">
            <polygon points="-6,22 6,22 0,30" fill="#b91c1c" data-svg="needle-head" />
            <line x1="0" y1="26" x2="0" y2="74" stroke="#b91c1c" stroke-width="2.4" data-svg="needle-line" />
            <text x="0" y="108" text-anchor="middle" font-family="Menlo, Consolas, monospace" font-size="11" font-weight="700" fill="#b91c1c" data-svg="needle-txt">idx = 637</text>
          </g>
        </svg>
      </div>
      <div class="zc-scrubber-row">
        <label>${zh ? "16 位距离字段 dist:" : "16-bit symbol dist:"}</label>
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
      q('[data-p="index-sub"]').textContent = oob ? (zh ? `越过 512 上界 +${idx - 511} 字节!` : `+${idx - 511} B past 512-byte table!`) : (zh ? "在 [0..511] 合法界内" : "within [0..511] bounds");
      q('[data-p="verdict"]').textContent = oob ? "Fault.ub (OOB Read)" : "Safe (< 512)";
      q('[data-p="verdict"]').className = "zc-pipe-expr " + (oob ? "zc-val-danger" : "zc-val-safe");
      q('[data-p="verdict-sub"]').textContent = oob ? (zh ? "再触发 dyn_dtree[code] 二次越界" : "then indexes dtree[code] OOB") : "code < 30 guaranteed";

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
            ? `<span class="zc-badge zc-badge-danger">内存安全事故</span> 一旦写指针覆盖了未读符号，<code>dist</code> 就不再受 <code>MAX_DIST ≤ 32506</code> 约束：任意落在 <code>32769..65535</code> 的 16 位值都会让 <code>d_code(dist - 1)</code> 越界读取 <code>_dist_code[512]</code> 之后的只读段字节，并进一步用脏字节索引 <code>dtree[code]</code>。因此，<strong>纯内存安全证明也必须先证明写指针追不上读指针</strong>。`
            : `<span class="zc-badge zc-badge-danger">MEMORY SAFETY VIOLATION</span> Once compressed output overwrites an unread symbol, <code>dist</code> is no longer bounded by <code>MAX_DIST ≤ 32506</code>: any 16-bit value above <code>32768</code> drives <code>d_code(dist - 1)</code> up to index <code>767</code>—256 bytes past the end of <code>_dist_code[512]</code>—and feeds that garbage byte straight into <code>dtree[code]</code>. Even a pure memory-safety proof cannot dodge the overlay bound.`)
        : (zh
            ? `<span class="zc-badge zc-badge-safe">不追尾即安全</span> 只要不追尾条件保证读出的字节仍是 <code>_tr_tally</code> 当初记录的符号，就有 <code>1 ≤ dist ≤ W - 262 ≤ 32506 ≤ 32768</code>，右移后下标严格落在 <code>0..511</code> 之内，且查出的距离码严格小于 <code>30</code>。`
            : `<span class="zc-badge zc-badge-safe">IN BOUNDS</span> As long as the write cursor never reaches <code>sym_buf + sx</code>, the bytes read are the ones <code>_tr_tally</code> recorded: <code>1 ≤ dist ≤ W - 262 ≤ 32506 ≤ 32768</code>, keeping <code>d_code(dist - 1) ≤ 511</code> and <code>code &lt; 30</code>.`);
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
    let memLevel = 4; // B = 1024 -> W_max = 1026 < 1597!
    let depth = 15;

    el.innerHTML = `
      <div class="zc-bar">
        <div class="zc-title-wrap">
          <span class="zc-kicker">${zh ? "交互演示 03 · 为什么长编码需要指数级的符号总数" : "INTERACTIVE 03 · THE FIBONACCI TAX OF DEEP HUFFMAN CODES"}</span>
          <span class="zc-title">${zh ? "最小 Huffman 树脊柱与 F(17) = 1597 零截断阈值" : "Minimal Huffman Spine & the F(17) = 1597 No-Clamping Wall"}</span>
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
          <div class="zc-metric-label">${zh ? "块容量上限 (W_max = B + 2)" : "MAX TREE WEIGHT (B + 2)"}</div>
          <div class="zc-metric-val" data-f="wmax">1026</div>
          <div class="zc-metric-sub" data-f="bsub">B = 1024 (memLevel 4)</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "目标叶子深度 l" : "TARGET LEAF DEPTH l"}</div>
          <div class="zc-metric-val" data-f="depth">15 bits</div>
          <div class="zc-metric-sub" data-f="fib-eq">F(l+1) + F(l) = F(l+2)</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "达到深度 l 所需最小总频数" : "MIN WEIGHT REQUIRED"}</div>
          <div class="zc-metric-val" data-f="wreq">1597</div>
          <div class="zc-metric-sub" data-f="wreq-sub">F(17) = 1597</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "该 memLevel 最大真实深度" : "MAX TRUE DEPTH AT B"}</div>
          <div class="zc-metric-val" data-f="maxd">14 bits</div>
          <div class="zc-metric-sub" data-f="clamp-sub">gen_bitlen overflow = 0</div>
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
      // For leaf of freq f >= 1 at true depth l:
      // In trees.md: f * F(l + 1) + F(l) <= W => F(l + 2) <= W for used leaf;
      // and for depth 16 overflow in gen_bitlen: W >= F(17) = 1597 (trees.md line 332).
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
      q('[data-f="maxd"]').textContent = canOverflow15 ? (zh ? ">15 (需截断)" : ">15 (clamped to 15)") : `${maxTrueDepth} bits`;
      q('[data-f="clamp-sub"]').textContent = canOverflow15
        ? (zh ? "gen_bitlen 修复可能触发" : "gen_bitlen repair active")
        : (zh ? "gen_bitlen 零截断 (overflow = 0)!" : "gen_bitlen overflow = 0 always!");
      q('[data-f="slider-l"]').textContent = String(depth);
      q('[data-f="status-pill"]').innerHTML = reachable
        ? `<span class="zc-badge zc-badge-safe">${zh ? "可构造" : "POSSIBLE"} (${wReq} ≤ ${Wmax})</span>`
        : `<span class="zc-badge zc-badge-danger">${zh ? "不可达!" : "IMPOSSIBLE!"} (${wReq} &gt; ${Wmax})</span>`;

      // Draw minimal Fibonacci spine across SVG width
      const steps = depth;
      const x0 = 48;
      const x1 = 812;
      const dx = steps > 1 ? (x1 - x0) / steps : 0;
      let svgHtml = `
        <text x="20" y="18" font-family="Menlo, Consolas, monospace" font-size="10.5" fill="#6b6b66">
          ${zh
            ? `深度 l = ${depth} 的最轻 Huffman 树脊柱（左：深度 ${depth} 叶子 → 右：树根，每层兄弟子树至少重 F_i）`
            : `LIGHTEST HUFFMAN SPINE FOR DEPTH l = ${depth} (LEFT: LEAF AT DEPTH ${depth} → RIGHT: ROOT; SIBLINGS WEIGH ≥ F_i)`}
        </text>
      `;

      // Spine edges and sibling branches
      for (let i = 0; i <= steps; i++) {
        const cx = steps === 0 ? 430 : x0 + i * dx;
        const cy = 74;
        if (i < steps) {
          const nx = x0 + (i + 1) * dx;
          svgHtml += `<line x1="${cx.toFixed(1)}" y1="${cy}" x2="${nx.toFixed(1)}" y2="${cy}" stroke="${reachable ? "#0a0a0a" : "#b91c1c"}" stroke-width="2" />`;
          // Sibling leaf hanging below
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
        const nodeW = depth === 16
          ? (i === 0 ? 1 : FIB[i + 2])
          : (i === 0 ? 1 : FIB[i + 2]);
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
          ${zh ? "虚线方框 = 每层合并时必须存在的最小兄弟子树频数 (Fibonacci 数列)" : "Dashed boxes = minimum sibling subtree weights forced by Huffman's greedy merge order"}
        </text>
      `;
      q('[data-svg="spine"]').innerHTML = svgHtml;

      if (memLevel <= 2) {
        q('[data-role="fib-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-ink">memLevel ${memLevel} · 极浅树</span> 当 <code>B = ${B}</code> 时整棵树总权重至多 <code>${Wmax}</code>，连深度 <code>${maxTrueDepth + 1}</code> 所需的最小斐波那契权重 <code>${FIB[maxTrueDepth + 3]}</code> 都凑不够！因此所有编码长度 <code>≤ ${maxTrueDepth}</code>，码长树 <code>bl_tree</code> 里符号 <code>${maxTrueDepth + 1}..15</code> 的出现次数恒为 <strong>0</strong>。`
          : `<span class="zc-badge zc-badge-ink">memLevel ${memLevel} · SHALLOW TREE</span> With <code>B = ${B}</code>, total weight is at most <code>${Wmax} &lt; F(${maxTrueDepth + 3}) = ${FIB[maxTrueDepth + 3]}</code>: every code is at most <strong>${maxTrueDepth} bits</strong> long, so bit-length symbols <code>${maxTrueDepth + 1}..15</code> have frequency <strong>zero</strong> in <code>bl_tree</code>.`;
      } else if (memLevel <= 4) {
        q('[data-role="fib-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-safe">memLevel ${memLevel} · 1597 奇迹</span> <code>W_max = ${Wmax} &lt; F(17) = 1597</code>！要产生深度 16 的结点（触发 <code>gen_bitlen</code> 的 15 位截断修复循环），总权重至少要 <code>1597</code>。因此在 <code>memLevel = 3, 4</code> 下 <code>gen_bitlen</code> 的修复循环是不可达死代码，无失真的 Fibonacci 上界直接救回了安全预算！`
          : `<span class="zc-badge zc-badge-safe">memLevel ${memLevel} · THE 1597 THRESHOLD</span> Because <code>W_max = ${Wmax} &lt; F(17) = 1597</code>, no Huffman tree at this <code>memLevel</code> can ever reach depth 16! <code>gen_bitlen</code>'s 15-bit clamping repair loop never runs, keeping pure Fibonacci bounds intact.`;
      } else {
        q('[data-role="fib-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-warn">memLevel ${memLevel} · 允许 >15 层截断</span> 当 <code>B = ${B}</code> 时 <code>W_max = ${Wmax} ≥ 1597</code>，树深可以超过 15 层并触发 <code>gen_bitlen</code> 的 Kraft 等式修复。但此时 <code>8B = ${(8 * B).toLocaleString()}</code> bit 的起步优势足够宽裕，计入截断损耗后的通用上界 <code>excess ≤ 6.257(n + 3)</code> 依然稳稳落在 <code>8B</code> 之内。`
          : `<span class="zc-badge zc-badge-warn">memLevel ${memLevel} · CLAMPING POSSIBLE</span> Here <code>W_max = ${Wmax} ≥ 1597</code>, so skewed frequencies can exceed depth 15 and trigger <code>gen_bitlen</code>'s Kraft repair. Fortunately <code>8B = ${(8 * B).toLocaleString()}</code> bits is wide enough that the clamped bound <code>excess ≤ 6.257(n + 3)</code> easily fits.`;
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
   * WIDGET 4: THE memLevel 1..9 BUDGET RAZOR (DOWN TO 0 BITS OF SLACK!)
   * ========================================================================== */
  const REGIME_DATA = [
    { mem: 1, B: 128,   hdr: 0,    comb: 999,    proved: 1024,   thm: "header + excess ≤ 999", regime: 3 },
    { mem: 2, B: 256,   hdr: 0,    comb: 2023,   proved: 2048,   thm: "header + excess ≤ 2023", regime: 3 },
    { mem: 3, B: 512,   hdr: 2283, excess: 1777, proved: 4085,   thm: "W ≤ 514 < 1597",   regime: 2 },
    { mem: 4, B: 1024,  hdr: 2283, excess: 3678, proved: 5986,   thm: "W ≤ 1026 < 1597",  regime: 2 },
    { mem: 5, B: 2048,  hdr: 2283, excess: 12827, proved: 15135, thm: "B ≥ 2048",       regime: 1 },
    { mem: 6, B: 4096,  hdr: 2283, excess: 25641, proved: 27949, thm: "B ≥ 2048",       regime: 1 },
    { mem: 7, B: 8192,  hdr: 2283, excess: 51270, proved: 53578, thm: "B ≥ 2048",       regime: 1 },
    { mem: 8, B: 16384, hdr: 2283, excess: 102528, proved: 104836, thm: "B ≥ 2048, default memLevel", regime: 1 },
    { mem: 9, B: 32768, hdr: 2283, excess: 205042, proved: 207350, thm: "B ≥ 2048, max memLevel",    regime: 1 },
  ];

  const mountRegimes = (el) => {
    const zh = getLang(el) === "zh";
    let idx = 0; // Start right on memLevel = 1 (0 bits slack!) or let user click 1..9!

    el.innerHTML = `
      <div class="zc-bar">
        <div class="zc-title-wrap">
          <span class="zc-kicker">${zh ? "交互演示 04 · 全部 9 个 memLevel 的比特预算刀锋" : "INTERACTIVE 04 · BIT BUDGET ACROSS ALL NINE memLevels"}</span>
          <span class="zc-title">${zh ? "header + excess + 25 ≤ 8B：从宽裕到零比特余量" : "header + excess + 25 ≤ 8B: Down to Zero Bits of Slack"}</span>
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
          <div class="zc-metric-label">${zh ? "起步预算 8B" : "AVAILABLE HEAD START (8B)"}</div>
          <div class="zc-metric-val" data-r="budget">1,024 bits</div>
          <div class="zc-metric-sub" data-r="b-bytes">B = 128 B (pending_buf = 512 B)</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "粗放通用公式估值" : "NAIVE REGIME-1 FORMULA"}</div>
          <div class="zc-metric-val" data-r="naive">3,122 bits</div>
          <div class="zc-metric-sub" data-r="naive-sub">2283 + 6.257(B+2) + 25</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "证明给出的上界" : "PROVED BOUND"}</div>
          <div class="zc-metric-val" data-r="proved">1,024 bits</div>
          <div class="zc-metric-sub" data-r="proved-sub">999 + 25 = 1024</div>
        </div>
        <div class="zc-metric">
          <div class="zc-metric-label">${zh ? "剩余证明余量 (SLACK)" : "PROVED SLACK (8B − BOUND)"}</div>
          <div class="zc-metric-val" data-r="slack">0 bits</div>
          <div class="zc-metric-sub" data-r="regime-tag">Regime 3 · Exact Certificate</div>
        </div>
      </div>
      <div class="zc-stage">
        <div class="zc-regime-bars">
          <div>
            <div style="display:flex;justify-content:space-between;font-family:monospace;font-size:11px;margin-bottom:5px;">
              <span>${zh ? "① 仅用通用上界 (2283 + 6.257(B+2) + 25)" : "① General Clamped Formula Alone (2283 + 6.257(B+2) + 25)"}</span>
              <strong data-r="bar1-lbl"></strong>
            </div>
            <div class="zc-bar-track">
              <div class="zc-bar-seg" data-r="n-bar" style="left:0;width:50%;background:#94a3b8;"></div>
              <div class="zc-wall-line" style="left:62.5%;"></div>
            </div>
          </div>

          <div>
            <div style="display:flex;justify-content:space-between;font-family:monospace;font-size:11px;margin-bottom:5px;">
              <span>${zh ? "② 证明给出的上界" : "② Proved bound"} (<code data-r="thm" style="font-size:11px;"></code>)</span>
              <strong data-r="bar2-lbl"></strong>
            </div>
            <div class="zc-bar-track">
              <div class="zc-bar-seg" data-r="p-fixed" style="left:0;background:#b45309;" title="25 bits (entry + tag + register slack)"></div>
              <div class="zc-bar-seg" data-r="p-hdr" style="background:#64748b;" title="Header bound"></div>
              <div class="zc-bar-seg" data-r="p-exc" style="background:#0f766e;" title="Symbol excess bound"></div>
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
          <span><i class="zc-swatch" style="background:#b45309;"></i>${zh ? "固定开销 25b (7+3+15)" : "Fixed 25b (7 entry + 3 tag + 15 slack)"}</span>
          <span><i class="zc-swatch" style="background:#64748b;"></i>${zh ? "头部上界 (2283b)" : "Header bound (2283b)"}</span>
          <span><i class="zc-swatch" style="background:#0f766e;"></i>${zh ? "符号超额位 (excess) / 联合证书" : "Symbol excess / Joint certificate"}</span>
          <span><i class="zc-swatch" style="background:#dc2626;"></i>${zh ? "超出 8B 预算 (证明失败!)" : "Exceeds 8B wall (proof fails!)"}</span>
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
      // Scale where 8B sits at 62.5% of bar width (so up to 1.6 * 8B is visible; clamp visual at 100%)
      const scaleMax = budget / 0.625;
      const pct = (v) => Math.min(100, (v / scaleMax) * 100);

      q('[data-r="budget"]').textContent = `${budget.toLocaleString()} bits`;
      q('[data-r="b-bytes"]').textContent = `B = ${d.B.toLocaleString()} B (pending_buf = ${(4 * d.B).toLocaleString()} B)`;
      q('[data-r="naive"]').textContent = `${naive.toLocaleString()} bits`;
      q('[data-r="naive"]').className = "zc-metric-val " + (naive > budget ? "zc-val-danger" : "zc-val-safe");
      q('[data-r="naive-sub"]').textContent = naive > budget
        ? (zh ? `超支 +${(naive - budget).toLocaleString()} bits!` : `OVERFLOWS by +${(naive - budget).toLocaleString()} bits!`)
        : (zh ? `在 8B 预算内` : `fits within 8B`);

      q('[data-r="proved"]').textContent = `${d.proved.toLocaleString()} bits`;
      q('[data-r="proved-sub"]').textContent = d.regime === 3
        ? `${d.comb} (joint hdr+excess) + 25 = ${d.proved}`
        : `${d.hdr} + ${d.excess.toLocaleString()} + 25 = ${d.proved.toLocaleString()}`;

      const slackEl = q('[data-r="slack"]');
      slackEl.textContent = `${slack.toLocaleString()} bits`;
      slackEl.className = "zc-metric-val " + (slack === 0 ? "zc-val-warn" : "zc-val-safe");
      q('[data-r="regime-tag"]').textContent = d.regime === 3
        ? (zh ? "第三区间 · 零余量联合证书!" : "Regime 3 · ZERO-SLACK CERTIFICATE!")
        : d.regime === 2
        ? (zh ? "第二区间 · F(17)=1597 无截断" : "Regime 2 · F(17)=1597 Unclamped")
        : (zh ? "第一区间 · 渐近斜率 6.257/sym" : "Regime 1 · Asymptotic 6.257b/sym");

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

      const pf = q('[data-r="p-fixed"]');
      const ph = q('[data-r="p-hdr"]');
      const pe = q('[data-r="p-exc"]');
      pf.style.left = "0%";
      pf.style.width = `${wFixed.toFixed(2)}%`;
      ph.style.left = `${wFixed.toFixed(2)}%`;
      ph.style.width = `${wHdr.toFixed(2)}%`;
      pe.style.left = `${(wFixed + wHdr).toFixed(2)}%`;
      pe.style.width = `${wExc.toFixed(2)}%`;

      q('[data-r="bar2-lbl"]').textContent = `${d.proved.toLocaleString()} / ${budget.toLocaleString()} bits (${((d.proved / budget) * 100).toFixed(2)}%)`;

      if (d.regime === 3) {
        q('[data-role="r-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-warn">证明零余量 (${d.proved} / ${budget})</span> 在 <code>memLevel = ${d.mem}</code> 下，单是通用头部上界 <code>2283</code> 就已击穿 <code>8B = ${budget}</code>！线性组合证书同时动用：① 码长上界（<code>≤ ${d.mem === 1 ? 9 : 11}</code>）消去码长树高阶符号；② 对照一组固定的完全参考前缀码给当前块头部精确计费；③ <strong>利用 <code>opt_lenb &lt; static_lenb</code></strong> 消元，证出 <code>header + excess ≤ ${d.comb}</code>，加 25 恰好等于 <strong>${budget}</strong>（证明层零余量；物理上真实 C 执行仍留有约 300+ bit 缓冲，见下一节分析）。`
          : `<span class="zc-badge zc-badge-warn">ZERO PROOF SLACK (${d.proved} / ${budget})</span> At <code>memLevel = ${d.mem}</code>, the 2,283-bit header bound alone blows past <code>8B = ${budget}</code>! The linear certificate combines (1) max code length <code>≤ ${d.mem === 1 ? 9 : 11}</code>, (2) bounding <code>bl_tree</code> against an explicit reference prefix code, and (3) <strong><code>opt_lenb &lt; static_lenb</code></strong>, landing right on <code>${d.comb} + 25 = ${budget} ≤ ${budget}</code> (zero proof slack—though real C retains ~300+ bits of physical margin, as dissected in the next section).`;
      } else if (d.regime === 2) {
        q('[data-role="r-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-safe">仅余 ${slack} bits (${d.proved} / ${budget})</span> 粗放公式在这里算出 <code>${naive} &gt; ${budget}</code>（红条越界！）。但因为 <code>B + 2 = ${d.B + 2} &lt; 1597 = F(17)</code>，<code>gen_bitlen</code> 绝不截断，纯净 Fibonacci 约束把超额位压到 <code>${d.excess}</code> bit。在 <code>memLevel = 3</code> 时，<code>4085 ≤ 4096</code> 只剩 <strong>11 bit</strong>（不到两个字节！）的呼吸空间。`
          : `<span class="zc-badge zc-badge-safe">${slack} BITS TO SPARE (${d.proved} / ${budget})</span> The Regime-1 formula overflows to <code>${naive} &gt; ${budget}</code> (red bar!). Because <code>B + 2 = ${d.B + 2} &lt; 1597 = F(17)</code>, <code>gen_bitlen</code> never clamps a leaf, tightening <code>excess</code> to <code>${d.excess}</code> bits—leaving just <strong>11 bits</strong> of headroom at <code>memLevel = 3</code>!`;
      } else {
        q('[data-role="r-note"]').innerHTML = zh
          ? `<span class="zc-badge zc-badge-safe">渐近安全区 (${d.proved.toLocaleString()} / ${budget.toLocaleString()})</span> 从 <code>B = 2048</code>（<code>memLevel ≥ 5</code>）起，即便算上最坏 2283 bit 树头与 15 位截断修复损耗，每符号超额位 <code>6.257</code> 也远低于每符号腾出的 <code>8</code> bit 头部摊销预算（剩余 <code>${slack.toLocaleString()}</code> bit）。`
          : `<span class="zc-badge zc-badge-safe">ASYMPTOTIC REGIME (${d.proved.toLocaleString()} / ${budget.toLocaleString()})</span> From <code>B = 2048</code> (<code>memLevel ≥ 5</code>) upward, the per-symbol excess slope of <code>6.257</code> bits stays comfortably below the <code>8</code> bits/symbol head-start budget, even with the 2,283-bit worst-case header and 15-bit clamping repair (<code>${slack.toLocaleString()}</code> bits to spare).`;
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
      if (el.dataset.zcReady === "true") return;
      el.dataset.zcReady = "true";
      const kind = el.dataset.zc;
      if (kind === "race") mountRace(el);
      else if (kind === "oob") mountOob(el);
      else if (kind === "fib") mountFib(el);
      else if (kind === "regimes") mountRegimes(el);
    });
  };

  window.__mountZlibChase = mountAll;
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", mountAll);
  } else {
    mountAll();
  }
  window.addEventListener("spa:navigation", mountAll);
})();
