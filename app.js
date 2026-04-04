/* ================================================================
   SVA-Whisperer — Pure JavaScript SVA Parser
   No API key. No network. Runs entirely in the browser.
   ================================================================ */

(function () {
  'use strict';

  /* ── Example Assertions ─────────────────────────────────────────── */
  const EXAMPLES = {
    simple_implication:
`// Simple implication: request must be acknowledged within 4 cycles
property p_req_ack;
  @(posedge clk) disable iff (!rst_n)
  req |-> ##[1:4] ack;
endproperty
assert property (p_req_ack);`,

    consecutive_repeat:
`// Consecutive repetition: bus grant must hold for exactly 3 cycles
property p_grant_hold;
  @(posedge clk) disable iff (rst)
  $rose(bus_grant) |-> bus_grant[*3];
endproperty
assert property (p_grant_hold);`,

    overlapping:
`// Non-overlapping implication with fixed 2-cycle delay
property p_start_done;
  @(posedge clk)
  start_cmd |=> ##2 op_done;
endproperty
assert property (p_start_done);`,

    disable_iff:
`// Reset-aware: write must be acknowledged within 2-8 cycles
property p_write_ack;
  @(posedge clk) disable iff (reset_n == 1'b0)
  (write_en && addr_valid && !fifo_full) |-> ##[2:8] write_ack;
endproperty
assert property (p_write_ack);`,

    sequence_complex:
`// Complex: burst data must be valid; ready must hold throughout
sequence burst_seq;
  burst_start ##1 burst_active[*1:$] ##1 burst_end;
endsequence

property p_burst_valid;
  @(posedge clk) disable iff (!sys_rst_n)
  $rose(burst_start) |->
    (data_valid ##1 data_valid ##1 data_valid)
    intersect (ready throughout burst_seq);
endproperty
assert property (p_burst_valid);`,
  };

  /* ── Section Config ─────────────────────────────────────────────── */
  const SECTION_CONFIG = [
    { key: 'clock_reset',   label: 'Clocking / Reset',        role: 'clock'       },
    { key: 'trigger',       label: 'Trigger',                  role: 'trigger'     },
    { key: 'implication',   label: 'Implication',              role: 'implication' },
    { key: 'expectation',   label: 'Consequent',               role: 'expectation' },
    { key: 'temporal',      label: 'Temporal Operators',       role: 'temporal'    },
    { key: 'warnings',      label: 'Efficiency Notes',         role: 'warnings'    },
    { key: 'edge_case',     label: 'Edge Case',                role: 'edge_case'   },
  ];

  /* ================================================================
     SVA PARSER — Pure JS, zero dependencies
     ================================================================ */

  // ── Text Preprocessing ──────────────────────────────────────────

  function stripComments(text) {
    text = text.replace(/\/\/[^\n]*/g, '');
    text = text.replace(/\/\*[\s\S]*?\*\//g, '');
    return text;
  }

  function norm(text) {
    return text.replace(/\s+/g, ' ').trim();
  }

  // ── Paren-Balanced Extraction ───────────────────────────────────

  // Returns content inside balanced parens starting at index `pos` (which must be '(')
  function extractBalanced(text, pos) {
    if (text[pos] !== '(') return null;
    let depth = 0;
    for (let i = pos; i < text.length; i++) {
      if (text[i] === '(') depth++;
      else if (text[i] === ')') {
        depth--;
        if (depth === 0) return text.slice(pos + 1, i).trim();
      }
    }
    return null;
  }

  // Remove a paren-balanced block starting at a keyword: "keyword (...)"
  function removeKeywordBlock(text, keyword) {
    const re = new RegExp(keyword + '\\s*\\(', 'i');
    const idx = text.search(re);
    if (idx === -1) return text;
    const match = text.match(re);
    const parenStart = idx + match[0].length - 1;
    let depth = 0;
    for (let i = parenStart; i < text.length; i++) {
      if (text[i] === '(') depth++;
      else if (text[i] === ')') {
        depth--;
        if (depth === 0) {
          return text.slice(0, idx) + text.slice(i + 1);
        }
      }
    }
    return text;
  }

  // Extract content inside "keyword (...)"
  function extractKeywordBlock(text, keyword) {
    const re = new RegExp(keyword + '\\s*\\(', 'i');
    const idx = text.search(re);
    if (idx === -1) return null;
    const match = text.match(re);
    const parenStart = idx + match[0].length - 1;
    return extractBalanced(text, parenStart);
  }

  // ── Extract the Assertion Body ──────────────────────────────────

  function extractAssertionBody(rawText) {
    const text = stripComments(rawText);

    // property NAME (...params...) ; ... endproperty
    const propM = text.match(/property\s+\w+\s*(?:\([^)]*\))?\s*;([\s\S]*?)endproperty/i);
    if (propM) {
      return propM[1].replace(/;\s*$/, '').trim();
    }

    // assert/assume/cover/restrict property (...)
    for (const kw of ['assert\\s+property', 'assume\\s+property', 'cover\\s+property', 'restrict\\s+property']) {
      const re = new RegExp(kw + '\\s*\\(', 'i');
      const idx = text.search(re);
      if (idx !== -1) {
        const m = text.match(re);
        const parenStart = idx + m[0].length - 1;
        const inner = extractBalanced(text, parenStart);
        if (inner) return inner;
      }
    }

    // Return as-is, strip trailing semicolon
    return text.replace(/;\s*$/, '').trim();
  }

  // ── Clock Extraction ────────────────────────────────────────────

  function extractClock(body) {
    // @(posedge/negedge/edge signal)
    const m = body.match(/@\s*\(\s*(posedge|negedge|edge)\s+(\w+)(?:\s*,\s*(\w+))?\s*\)/i);
    if (!m) return null;
    return {
      edge:      m[1].toLowerCase(),
      signal:    m[2],
      altSignal: m[3] || null,
      raw:       m[0],
    };
  }

  // ── Disable Iff Extraction ──────────────────────────────────────

  function extractDisableIff(body) {
    return extractKeywordBlock(body, 'disable\\s+iff');
  }

  // ── Local Variable Declaration Extraction ───────────────────────
  // Returns a Set of names declared as `logic [N:0] var;` or `logic var;`

  function extractLocalVars(body) {
    const vars = new Set();
    for (const m of body.matchAll(/\blogic\s+(?:\[\s*\d+\s*:\s*\d+\s*\]\s+)?(\w+)\s*;/gi)) {
      vars.add(m[1]);
    }
    return vars;
  }

  // ── Strip Clock + Disable Iff to Get Assertion Core ────────────

  function extractCore(body) {
    // Remove @(...) clock block
    let core = body.replace(/@\s*\(\s*(?:posedge|negedge|edge)\s+\w+(?:\s*,\s*\w+)?\s*\)/gi, '');
    // Remove disable iff (...)
    core = removeKeywordBlock(core, 'disable\\s+iff');
    // Clean up
    return norm(core).replace(/;$/, '').trim();
  }

  // ── Find Implication Operator at Top Level ──────────────────────

  function findImplicationOp(text) {
    let depth = 0;
    for (let i = 0; i < text.length - 2; i++) {
      const ch = text[i];
      if (ch === '(' || ch === '[') depth++;
      else if (ch === ')' || ch === ']') depth--;
      else if (depth === 0 && ch === '|') {
        if (text[i + 1] === '-' && text[i + 2] === '>') return { pos: i, op: '|->', len: 3 };
        if (text[i + 1] === '=' && text[i + 2] === '>') return { pos: i, op: '|=>', len: 3 };
      }
    }
    return null;
  }

  // ── Expression Humanizer ────────────────────────────────────────

  function humanizeExpr(expr) {
    if (!expr) return '';

    // Strip outer redundant parens
    let e = norm(expr);
    while (/^\([\s\S]+\)$/.test(e)) {
      const inner = extractBalanced(e, 0);
      if (inner && norm(inner) !== e) e = norm(inner);
      else break;
    }

    // System functions → English
    e = e.replace(/\$rose\s*\(\s*([^)]+?)\s*\)/gi,       (_, s) => `${s.trim()} rises (0→1)`);
    e = e.replace(/\$fell\s*\(\s*([^)]+?)\s*\)/gi,       (_, s) => `${s.trim()} falls (1→0)`);
    e = e.replace(/\$stable\s*\(\s*([^)]+?)\s*\)/gi,     (_, s) => `${s.trim()} is stable (unchanged)`);
    e = e.replace(/\$past\s*\(\s*([^,)]+?)\s*,\s*(\d+)\s*\)/gi, (_, s, n) => `${s.trim()} from ${n} cycle${n > 1 ? 's' : ''} ago`);
    e = e.replace(/\$past\s*\(\s*([^)]+?)\s*\)/gi,       (_, s) => `${s.trim()} from the previous cycle`);
    e = e.replace(/\$isunknown\s*\(\s*([^)]+?)\s*\)/gi,  (_, s) => `${s.trim()} has X/Z bits`);
    e = e.replace(/\$onehot0\s*\(\s*([^)]+?)\s*\)/gi,    (_, s) => `${s.trim()} is one-hot or zero`);
    e = e.replace(/\$onehot\s*\(\s*([^)]+?)\s*\)/gi,     (_, s) => `${s.trim()} is one-hot`);
    e = e.replace(/\$countones\s*\(\s*([^)]+?)\s*\)/gi,  (_, s) => `popcount(${s.trim()})`);

    // Delays ##[M:N] and ##N
    e = e.replace(/##\s*\[\s*0\s*:\s*\$\s*\]/g, 'then at any future point (unbounded ⚠️)');
    e = e.replace(/##\s*\[\s*(\d+)\s*:\s*\$\s*\]/g, (_, lo) => `then after ${lo}+ cycles (unbounded)`);
    e = e.replace(/##\s*\[\s*0\s*:\s*(\d+)\s*\]/g, (_, hi) => `then within ${hi} cycles`);
    e = e.replace(/##\s*\[\s*(\d+)\s*:\s*(\d+)\s*\]/g, (_, lo, hi) => `then after ${lo}–${hi} cycles`);
    e = e.replace(/##\s*0\b/g, 'then simultaneously (##0)');
    e = e.replace(/##\s*1\b/g, 'then one cycle later');
    e = e.replace(/##\s*(\d+)/g, (_, n) => `then exactly ${n} cycles later`);

    // Repetition [*N], [->N], [=N]
    e = e.replace(/\[\s*\*\s*0\s*:\s*\$\s*\]/g, '[zero or more times — unbounded ⚠️]');
    e = e.replace(/\[\s*\*\s*\$\s*\]/g, '[indefinitely — unbounded ⚠️]');
    e = e.replace(/\[\s*\*\s*(\d+)\s*:\s*\$\s*\]/g, (_, lo) => `[at least ${lo}× consecutive — unbounded ⚠️]`);
    e = e.replace(/\[\s*\*\s*(\d+)\s*:\s*(\d+)\s*\]/g, (_, lo, hi) => `[${lo}–${hi}× consecutive]`);
    e = e.replace(/\[\s*\*\s*(\d+)\s*\]/g, (_, n) => `[exactly ${n}× consecutive]`);
    e = e.replace(/\[\s*->\s*(\d+)\s*\]/g, (_, n) => `[goto: true ${n}× non-consecutively]`);
    e = e.replace(/\[\s*=\s*(\d+)\s*\]/g,  (_, n) => `[non-consecutive: true ${n}× total]`);

    // Logic operators
    e = e.replace(/\s*&&\s*/g, ' AND ');
    e = e.replace(/\s*\|\|\s*/g, ' OR ');
    e = e.replace(/!(\w)/g, 'NOT $1');
    e = e.replace(/\s*!=\s*/g, ' ≠ ');
    e = e.replace(/\s*==\s*/g, ' = ');

    // Keywords
    e = e.replace(/\bthroughout\b/gi, 'THROUGHOUT');
    e = e.replace(/\bintersect\b/gi, 'INTERSECT');
    e = e.replace(/\bwithin\b/gi, 'WITHIN');
    e = e.replace(/\bfirst_match\b/gi, 'FIRST_MATCH');

    return e.trim();
  }

  // ── Clock/Reset Section ─────────────────────────────────────────

  function buildClockReset(clock, disableIff) {
    let lines = [];

    if (clock) {
      const edgeWord = clock.edge === 'posedge' ? 'rising (positive)' :
                       clock.edge === 'negedge' ? 'falling (negative)' : '';
      lines.push(`Evaluated at every ${edgeWord} edge of ${clock.signal}.`);
    } else {
      lines.push('No explicit clock event (@posedge/@negedge) found in the assertion body. The clock may be defined by an enclosing clocking block or default clocking statement.');
    }

    if (disableIff) {
      lines.push('');
      lines.push(`Reset/Disable condition: disable iff (${disableIff})`);
      lines.push(`While (${disableIff}) is true, the assertion is disabled — it vacuously passes and no evaluation threads are spawned. This prevents false failures during reset. Once the disable condition clears, the assertion resumes normally.`);
    }

    return lines.join('\n');
  }

  // ── Trigger Section ─────────────────────────────────────────────

  function buildTrigger(antecedent, hasImplOp) {
    if (!hasImplOp) {
      return 'No implication operator found. This is either an unconditional sequence assertion (fires every active clock cycle) or a bare sequence/property without an explicit trigger.';
    }
    if (!antecedent || antecedent.trim() === '') {
      return 'Empty antecedent — the assertion fires unconditionally on every active clock cycle.';
    }
    // Sample-and-hold: ($rose/$fell(sig), var = source)
    const captureM = antecedent.match(/^\(\s*\$(rose|fell)\s*\(\s*(\w+)\s*\)\s*,\s*(\w+)\s*=\s*(\w+)\s*\)$/i);
    if (captureM) {
      const edge    = captureM[1].toLowerCase() === 'rose' ? 'rises (0→1)' : 'falls (1→0)';
      const trigSig = captureM[2];
      const capVar  = captureM[3];
      const srcSig  = captureM[4];
      return `Fires when: ${trigSig} ${edge}\nSample-and-hold: ${capVar} captures the current value of ${srcSig} at this clock edge.`;
    }
    const human = humanizeExpr(antecedent);
    return `Fires when: ${human}`;
  }

  // ── Implication Section ─────────────────────────────────────────

  function buildImplication(op) {
    if (!op) {
      return 'No implication operator (|-> or |=>) detected. This may be a sequence assertion or a property without an explicit antecedent/consequent split.';
    }
    if (op === '|->') {
      return 'Overlapping implication (|->).\n\nThe consequent evaluation begins in the SAME clock cycle as the trigger match. If the antecedent matches at cycle N, the expectation must hold starting at cycle N.\n\n💡 "|-> same cycle"';
    }
    return 'Non-overlapping implication (|=>).\n\nEquivalent to |-> ##1. The consequent evaluation begins ONE cycle AFTER the trigger. If the antecedent matches at cycle N, the expectation must hold starting at cycle N+1.\n\n💡 "|=> next cycle"';
  }

  // ── Expectation Section ─────────────────────────────────────────

  function buildExpectation(consequent) {
    if (!consequent) return 'No consequent identified.';
    const cons = extractConsequentInfo(consequent);

    // equality fast-path (data-capture check: out_data == captured_data)
    if (cons.equality) {
      const { lhs, rhs } = cons.equality;
      let timingLine = '';
      if (cons.isUnbounded)        timingLine = `After ${cons.delayLo}+ cycles (unbounded ⚠️):`;
      else if (cons.isRange)       timingLine = `After ${cons.delayLo}–${cons.delayHi} cycles:`;
      else if (cons.delayLo === 1) timingLine = 'One cycle later:';
      else if (cons.delayLo > 1)   timingLine = `Exactly ${cons.delayLo} cycles later:`;
      const boolLines = cons.signals
        .filter(sig => !sig.equalTo)
        .map(sig => sig.negated ? `${sig.label} must be LOW` : `${sig.label} must be HIGH`);
      const condLines = [...boolLines, `${lhs} must equal the value captured in ${rhs} (local variable).`];
      const parts = timingLine ? [timingLine, ...condLines] : condLines;
      return parts.join('\n');
    }

    // throughout fast-path
    if (cons.throughout) {
      const { holdSignal, targetSignal } = cons.throughout;
      const rangeStr = cons.isUnbounded
        ? `${cons.delayLo}+ cycles`
        : `${cons.delayLo}–${cons.delayHi} cycles`;
      return [
        `throughout operator:`,
        `${holdSignal} must remain HIGH continuously from cycle N until ${targetSignal} is asserted.`,
        `${targetSignal} must occur within ${rangeStr}.`,
        `${holdSignal} dropping LOW at any point before ${targetSignal} is seen causes a failure.`,
      ].join('\n');
    }

    // Timing prefix line
    let timingLine = '';
    if (cons.isUnbounded)       timingLine = `After ${cons.delayLo}+ cycles (unbounded ⚠️):`;
    else if (cons.isRange)      timingLine = `After ${cons.delayLo}–${cons.delayHi} cycles:`;
    else if (cons.delayLo === 1) timingLine = 'One cycle later:';
    else if (cons.delayLo > 1)  timingLine = `Exactly ${cons.delayLo} cycles later:`;

    // Per-signal conditions
    const sigLines = cons.signals.map(sig => {
      if (sig.negated) return `${sig.label} must be LOW`;
      if (cons.repeat > 1) return `${sig.label} must stay HIGH for exactly ${cons.repeat} consecutive cycles`;
      return `${sig.label} must be HIGH`;
    });

    if (sigLines.length === 0) return `Must hold: ${humanizeExpr(consequent)}`;

    const parts = timingLine ? [timingLine, ...sigLines] : sigLines;
    return parts.join('\n');
  }

  // ── Temporal Operators Section ──────────────────────────────────

  function buildTemporal(rawText) {
    rawText = stripComments(rawText);
    const found = [];
    const seen = new Set();

    function add(key, text) {
      if (!seen.has(key)) { seen.add(key); found.push(text); }
    }

    // ## delays
    for (const m of rawText.matchAll(/##\s*\[\s*([^\]]+)\s*\]/g)) {
      const range = m[1].trim();
      if (range.includes('$')) add(`##[${range}]`, `##[${range}]  →  Variable/unbounded delay range — expensive; creates evaluation threads for every possible delay value`);
      else {
        const parts = range.split(':').map(s => s.trim());
        if (parts.length === 2) add(`##[${range}]`, `##[${parts[0]}:${parts[1]}]  →  Delay of ${parts[0]} to ${parts[1]} cycles`);
        else add(`##[${range}]`, `##[${range}]  →  Delay range`);
      }
    }
    for (const m of rawText.matchAll(/##\s*(\d+)/g)) {
      const n = m[1];
      if (n === '0') add('##0', '##0  →  Zero-cycle (same-clock-edge) concatenation; both parts must be true simultaneously');
      else if (n === '1') add('##1', '##1  →  One-cycle delay between two sub-sequences');
      else add(`##${n}`, `##${n}  →  Exact ${n}-cycle delay`);
    }

    // Repetitions — look for signal[* ...] pattern
    for (const m of rawText.matchAll(/(\w+)\s*\[\s*\*\s*([^\]]*)\]/g)) {
      const sig = m[1], spec = m[2].trim();
      if (spec.includes('$')) add(`${sig}[*$]`, `${sig}[*${spec}]  →  Consecutive repetition (unbounded) — ${sig} must stay high for ${spec.replace('$', '∞').replace('0:', '')} cycles`);
      else if (spec.includes(':')) {
        const [lo, hi] = spec.split(':').map(s => s.trim());
        add(`${sig}[*${spec}]`, `${sig}[*${lo}:${hi}]  →  ${sig} must be high for ${lo} to ${hi} consecutive cycles`);
      } else {
        add(`${sig}[*${spec}]`, `${sig}[*${spec}]  →  ${sig} must be high for exactly ${spec} consecutive cycles`);
      }
    }
    for (const m of rawText.matchAll(/(\w+)\s*\[\s*->\s*([^\]]*)\]/g)) {
      const sig = m[1], spec = m[2].trim();
      add(`${sig}[->${spec}]`, `${sig}[->${spec}]  →  Goto repeat: ${sig} must be true for exactly ${spec} non-consecutive occurrence(s), with the sequence ending on the last true cycle`);
    }
    for (const m of rawText.matchAll(/(\w+)\s*\[\s*=\s*([^\]]*)\]/g)) {
      const sig = m[1], spec = m[2].trim();
      add(`${sig}[=${spec}]`, `${sig}[=${spec}]  →  Non-consecutive repeat: ${sig} must be true exactly ${spec} time(s) (with possible gaps), then the sequence may continue after the last occurrence`);
    }

    // System functions
    if (/\$rose\b/i.test(rawText)) add('$rose', '$rose(sig)  →  True when sig transitions 0→1 at the active clock edge');
    if (/\$fell\b/i.test(rawText)) add('$fell', '$fell(sig)  →  True when sig transitions 1→0 at the active clock edge');
    if (/\$stable\b/i.test(rawText)) add('$stable', '$stable(sig)  →  True when sig has the same value as the previous active clock edge');
    if (/\$past\b/i.test(rawText)) add('$past', '$past(sig, N)  →  Samples the value of sig from N clock cycles ago');
    if (/\$isunknown\b/i.test(rawText)) add('$isunknown', '$isunknown(sig)  →  True if any bit of sig is X or Z');
    if (/\$onehot0?\b/i.test(rawText)) add('$onehot', '$onehot/$onehot0  →  Checks one-hot encoding (exactly one bit high / zero or one bit high)');

    // Keywords
    if (/\bthroughout\b/i.test(rawText)) add('throughout', 'throughout  →  Requires the left-hand expression to be true at EVERY clock edge for the entire duration of the right-hand sequence. A single false cycle fails the sequence.');
    if (/\bintersect\b/i.test(rawText)) add('intersect', 'intersect  →  Both sequences must match AND must end in exactly the same clock cycle. They must have the same length.');
    if (/\bwithin\b/i.test(rawText)) add('within', 'within  →  The first (shorter) sequence must occur somewhere within the window of the second (longer) sequence.');
    if (/\bfirst_match\b/i.test(rawText)) add('first_match', 'first_match()  →  Of all possible matches for a sequence, only the shortest (first ending) match is considered. Useful to avoid exponential thread explosion in repetition operators.');
    if (/\bended\b/i.test(rawText)) add('ended', 'ended  →  A local variable used as a checkpoint — true in the cycle where a named sequence ends.');

    if (found.length === 0) return null;
    return found.join('\n\n');
  }

  // ── Warnings Section ────────────────────────────────────────────

  function buildWarnings(rawText, antecedent) {
    rawText = stripComments(rawText);
    const w = [];

    // Unbounded ##[0:$]
    if (/##\s*\[\s*0\s*:\s*\$\s*\]/g.test(rawText)) {
      w.push('HIGH COST — ##[0:$]: This is the most expensive temporal operator. A new evaluation thread is forked at every clock cycle indefinitely. In a long simulation this creates O(N) concurrent threads. Strongly prefer a bounded range — e.g., ##[1:MAX_LATENCY] — if you have a known upper bound.');
    }

    // Unbounded ##[M:$]
    const unboundedDelay = rawText.match(/##\s*\[\s*(\d+)\s*:\s*\$\s*\]/g);
    if (unboundedDelay && !rawText.match(/##\s*\[\s*0\s*:\s*\$\s*\]/)) {
      w.push(`HIGH COST — ${unboundedDelay[0].replace(/\s+/g, '')}: Unbounded upper delay. The tool spawns evaluation threads for every clock cycle from the lower bound onward until the consequent is met. Bound the range if possible.`);
    }

    // [*0:$]
    if (/\[\s*\*\s*0\s*:\s*\$\s*\]/g.test(rawText)) {
      w.push('VACUOUS RISK — [*0:$]: "Zero or more" repetition includes the case of zero repetitions, meaning the sequence can match without the repeated signal ever being asserted. This is a frequent source of vacuous success. Consider [*1:$] or a bounded range.');
    }

    // [*$] or [*N:$] without 0
    if (/\[\s*\*\s*\$\s*\]/g.test(rawText)) {
      w.push('CAUTION — [*$] (infinite repeat): A sequence with no upper bound on repetition will never complete on its own. Unless paired with "throughout" or "intersect" to constrain the endpoint, this likely indicates a bug.');
    }

    // Missing disable iff when reset signals present
    if (!/disable\s+iff/i.test(rawText) && /\b(?:rst|reset|arst|srst|rst_n|reset_n)\b/i.test(rawText)) {
      w.push('SUGGESTION — Reset signals detected but no "disable iff" found: Without disable iff, this assertion is active during reset. Signals driving to their reset values may cause spurious failures. Consider adding: disable iff (!rst_n)');
    }

    // Constant-1 antecedent
    if (antecedent && /^\s*1\s*$/.test(antecedent)) {
      w.push('NOTE — Antecedent is constant 1: The assertion triggers every active clock cycle. This is correct for some properties (e.g., bus protocol invariants) but can create many evaluation threads and slow simulation if the consequent involves long temporal ranges.');
    }

    // Vacuous with 0 antecedent (pathological)
    if (antecedent && /^\s*0\s*$/.test(antecedent)) {
      w.push('BUG — Antecedent is constant 0: This assertion will NEVER fire (always vacuously passes). It provides zero coverage. This is almost certainly unintentional.');
    }

    if (w.length === 0) {
      w.push('No significant concerns. The assertion appears well-formed with no obvious performance pitfalls or vacuous success risks.');
    }

    return w.join('\n\n');
  }

  // ── Edge Case Section ───────────────────────────────────────────

  function buildEdgeCase(rawText, clock, disableIff, antecedent, consequent) {
    // Priority: pick the most interesting edge case for this specific assertion

    // Disable iff — reset during in-flight sequence
    if (disableIff) {
      return `Reset mid-sequence: If (${disableIff}) asserts while an evaluation thread is already in-flight (e.g., the antecedent already matched and the tool is counting cycles toward the consequent), that thread is immediately killed and the assertion vacuously passes for that trigger. When reset deasserts, the assertion restarts fresh — it will NOT resume the interrupted sequence. A transaction that straddles a reset boundary may go entirely unchecked.`;
    }

    // $rose in antecedent
    if (/\$rose/i.test(antecedent || '')) {
      const sig = (antecedent.match(/\$rose\s*\(\s*(\w+)/i) || [])[1] || 'the signal';
      return `Glitch on ${sig}: $rose() samples the signal at the active clock edge — it is blind to glitches that occur and settle between edges. In RTL simulation this is benign. However, in gate-level simulation (with SDF back-annotation), combinational glitches between clock edges can produce spurious 0→1→0 transitions that are visible at the gate level but not at the RTL model, causing the assertion to behave differently between simulation levels.`;
    }

    // Bounded range delay — back-to-back triggers
    const rangeM = rawText.match(/##\s*\[(\d+):(\d+)\]/);
    if (rangeM) {
      const lo = rangeM[1], hi = rangeM[2];
      return `Concurrent evaluation threads: If the antecedent fires in two consecutive cycles (cycle N and N+1), two independent threads are spawned simultaneously, each waiting for the consequent within the ##[${lo}:${hi}] window. A single consequent event may satisfy BOTH threads. Conversely, a consequent failure will produce two separate assertion failure messages — one per thread — which can make the waveform-based debug harder to trace back to the original trigger.`;
    }

    // Fixed delay
    const fixedM = rawText.match(/##(\d+)/);
    if (fixedM && fixedM[1] !== '0') {
      const n = fixedM[1];
      return `Pipeline flush scenario: If the design issues a flush or cancel signal ${n} cycle(s) after the trigger fires (i.e., during the exact window the assertion is waiting), the consequent signal may be suppressed intentionally. Without a "disable iff" covering the flush condition, the assertion will fire a spurious failure. Verify whether the consequent can legitimately be absent during a flush and add a disable condition if so.`;
    }

    // throughout
    if (/\bthroughout\b/i.test(rawText)) {
      return '"throughout" with a momentary glitch: The throughout operator requires the condition to be true at EVERY active clock edge during the sequence. A single cycle where the condition drops low — even if it recovers immediately the next cycle — will cause the assertion to fail. In designs where the "throughout" condition is derived from combinational logic, hold-time violations or glitches near the clock edge can trigger spurious failures in gate-level simulation.';
    }

    // intersect
    if (/\bintersect\b/i.test(rawText)) {
      return '"intersect" length mismatch: Both sides of an intersect must begin AND end in the same clock cycle. If one sequence can complete faster or slower than the other under certain stimulus conditions (e.g., a variable-length handshake), the intersect will silently fail to match — the assertion vacuously passes because there is no match, not because it checked and passed. Use cover property with the same sequence to confirm the intersect is actually matching.';
    }

    // [*] repetition
    if (/\[\s*\*/.test(rawText)) {
      return 'Repetition and X-propagation: During simulation, if any bit of the repeated signal becomes X (unknown), the comparison at each cycle becomes X. Depending on your tool settings, an X antecedent may be treated as "not triggered" (tool-dependent), meaning the assertion can vacuously pass when X is present. Run with X-pessimism checks enabled (e.g., xprop mode) to detect these false passes.';
    }

    // No clock
    if (!clock) {
      return 'Implicit clocking: Without an explicit @(posedge clk), this assertion uses whatever the ambient default clocking is. If the assertion is instantiated in a module with multiple clocking blocks, the wrong clock may be used silently. Always prefer an explicit clock event to avoid ambiguity.';
    }

    // Generic fallback
    return `Simulation startup (time zero): In the first few active clock cycles after simulation begins, signals are typically X (uninitialized). If the antecedent evaluates to X, most SVA tools treat it as "not triggering" (so the assertion vacuously passes). This means real violations that occur during initialization go undetected. To ensure the assertion is properly tested from the start, add a reset/enable condition that gates the assertion until the design is fully initialized.`;
  }

  // ── Master Parse Function ───────────────────────────────────────

  function parseSVA(rawInput) {
    if (!rawInput || !rawInput.trim()) {
      throw new Error('Empty input.');
    }

    const body       = extractAssertionBody(rawInput);
    const clock      = extractClock(body);
    const disableIff = extractDisableIff(body);
    const localVars  = extractLocalVars(body);

    // Strip `logic` declarations before implication parsing so they don't
    // land in the antecedent or confuse findImplicationOp.
    const rawCore = extractCore(body);
    const core    = localVars.size > 0
      ? norm(rawCore.replace(/\blogic\s+(?:\[\s*\d+\s*:\s*\d+\s*\]\s+)?\w+\s*;/gi, '')).trim()
      : rawCore;

    const implOp = findImplicationOp(core);

    let antecedent = null;
    let consequent = core;

    if (implOp) {
      antecedent = core.slice(0, implOp.pos).trim();
      consequent = core.slice(implOp.pos + implOp.len).trim();
    }


    const temporal = buildTemporal(rawInput);

    return {
      clock_reset: buildClockReset(clock, disableIff),
      trigger:     buildTrigger(antecedent, !!implOp),
      implication: buildImplication(implOp ? implOp.op : null),
      expectation: buildExpectation(consequent),
      temporal:    temporal,
      warnings:    buildWarnings(rawInput, antecedent),
      edge_case:   buildEdgeCase(rawInput, clock, disableIff, antecedent, consequent),
      // Raw components for TLDR + waveform generation
      _raw: { clock, disableIff, antecedent, implOp: implOp?.op || null, consequent, localVars },
    };
  }

  /* ================================================================
     TLDR + WAVEFORM  (rule-based, no LLM)
     ================================================================ */

  // ── Antecedent Info ─────────────────────────────────────────────

  function extractAntecedentInfo(str) {
    if (!str) return { phrase: null, signal: null };
    const s = str.trim();

    // Sample-and-hold: ($rose/$fell(sig), var = source)
    const captureM = s.match(/^\(\s*\$(rose|fell)\s*\(\s*(\w+)\s*\)\s*,\s*(\w+)\s*=\s*(\w+)\s*\)$/i);
    if (captureM) {
      const edge   = captureM[1].toLowerCase() === 'rose' ? 'rises' : 'falls';
      return { phrase: `${captureM[2]} ${edge} and ${captureM[3]} captures ${captureM[4]}`, signal: captureM[2] };
    }

    const roseM = s.match(/^\$rose\s*\(\s*(\w+)\s*\)$/i);
    if (roseM) return { phrase: `${roseM[1]} rises`, signal: roseM[1] };

    const fellM = s.match(/^\$fell\s*\(\s*(\w+)\s*\)$/i);
    if (fellM) return { phrase: `${fellM[1]} falls`, signal: fellM[1] };

    const singleM = s.match(/^(\w+)$/);
    if (singleM) return { phrase: `${singleM[1]} is asserted`, signal: singleM[1] };

    // sig1 && sig2 (no ||) — compound condition
    if (s.includes('&&') && !s.includes('||')) {
      const parts = s.split('&&').map(p => p.trim().replace(/^!(\w)/, 'NOT $1'));
      const joined = parts.length === 2
        ? `${parts[0]} and ${parts[1]}`
        : `${parts.slice(0, -1).join(', ')}, and ${parts[parts.length - 1]}`;
      return { phrase: `${joined} are asserted`, signal: s.match(/\b(\w+)\b/)?.[1] || null };
    }

    // Fallback: use raw text, extract first word as signal
    return { phrase: s, signal: s.match(/\b(\w+)\b/)?.[1] || null };
  }

  // ── Consequent Info ──────────────────────────────────────────────

  // ── Consequent Signal Parser ─────────────────────────────────────
  // Parses the expression part of a consequent (after stripping ##N prefix).
  // Returns [{ label, negated }] for every individual signal found.

  function parseConsequentSignals(rest) {
    if (!rest) return [];
    let s = rest.trim();

    // Strip outer parens
    if (s[0] === '(' && s[s.length - 1] === ')') {
      const inner = extractBalanced(s, 0);
      if (inner) s = inner.trim();
    }

    // Equality comparison: sig == other (data-capture check)
    const eqM = s.match(/^(\w+)\s*==\s*(\w+)$/);
    if (eqM) return [{ label: eqM[1], negated: false, equalTo: eqM[2] }];

    // Repetition: signal[*N] → single non-negated signal
    const repM = s.match(/^(\w+)\s*\[\s*\*/);
    if (repM) return [{ label: repM[1], negated: false }];

    // $rose / $fell
    const roseM = s.match(/^\$rose\s*\(\s*(\w+)\s*\)$/i);
    if (roseM) return [{ label: roseM[1], negated: false }];
    const fellM = s.match(/^\$fell\s*\(\s*(\w+)\s*\)$/i);
    if (fellM) return [{ label: fellM[1], negated: false }];

    // Single negated: !sig
    const negM = s.match(/^!\s*(\w+)$/);
    if (negM) return [{ label: negM[1], negated: true }];

    // Single bare identifier
    const singleM = s.match(/^(\w+)$/);
    if (singleM) return [{ label: singleM[1], negated: false }];

    // Compound: split on && or ||
    if (s.includes('&&') || s.includes('||')) {
      return s.split(/&&|\|\|/)
        .map(p => p.trim())
        .filter(Boolean)
        .map(p => {
          if (p[0] === '(' && p[p.length - 1] === ')') p = p.slice(1, -1).trim();
          const eqSimple = p.match(/^(\w+)\s*==\s*(\w+)$/);
          if (eqSimple) return { label: eqSimple[1], negated: false, equalTo: eqSimple[2] };
          const negSimple = p.match(/^!\s*(\w+)$/);
          if (negSimple) return { label: negSimple[1], negated: true };
          const negParen  = p.match(/^!\s*\(\s*(\w+)\s*\)$/);
          if (negParen)  return { label: negParen[1],  negated: true };
          const rM = p.match(/\$(?:rose|fell)\s*\(\s*(\w+)\s*\)/i);
          if (rM) return { label: rM[1], negated: false };
          const wM = p.match(/\b(\w+)\b/);
          return wM ? { label: wM[1], negated: false } : null;
        })
        .filter(Boolean);
    }

    // Fallback: first identifier
    const wM = s.match(/\b(\w+)\b/);
    return wM ? [{ label: wM[1], negated: false }] : [];
  }

  function extractConsequentInfo(str) {
    if (!str) return { delayLo: 0, delayHi: 0, isRange: false, isUnbounded: false, signal: null, signals: [], repeat: 1, throughout: null, equality: null };
    const s = str.trim();

    // ── throughout: holdSig throughout (##[lo:hi] targetSig) ────────
    // Strip one level of outer balanced parens (consequent is often wrapped)
    let candidate = s;
    if (candidate[0] === '(' && candidate[candidate.length - 1] === ')') {
      const inner = extractBalanced(candidate, 0);
      if (inner) candidate = inner.trim();
    }
    const thrM = candidate.match(/^(\w+)\s+throughout\s*\(?\s*##\s*\[\s*(\d+)\s*:\s*(\d+|\$)\s*\]\s*(\w+)\s*\)?$/i);
    if (thrM) {
      const holdSignal   = thrM[1];
      const targetSignal = thrM[4];
      const thrLo        = parseInt(thrM[2]);
      const thrUnbounded = thrM[3] === '$';
      const thrHi        = thrUnbounded ? thrLo + 6 : parseInt(thrM[3]);
      return {
        delayLo: thrLo, delayHi: thrHi, isRange: true, isUnbounded: thrUnbounded,
        signal:  holdSignal,
        signals: [{ label: holdSignal, negated: false }, { label: targetSignal, negated: false }],
        repeat:  1,
        throughout: { holdSignal, targetSignal },
        equality: null,
      };
    }

    let delayLo = 0, delayHi = 0, isRange = false, isUnbounded = false;
    let rest = s;

    // Leading ##[M:N] or ##N
    const rangeM = s.match(/^##\s*\[\s*(\d+)\s*:\s*(\d+|\$)\s*\]/);
    const exactM = !rangeM && s.match(/^##\s*(\d+)/);

    if (rangeM) {
      rest = s.slice(rangeM[0].length).trim();
      delayLo = parseInt(rangeM[1]);
      if (rangeM[2] === '$') { delayHi = delayLo + 4; isUnbounded = true; }
      else                    { delayHi = parseInt(rangeM[2]); }
      isRange = (delayHi !== delayLo) || isUnbounded;
    } else if (exactM) {
      rest = s.slice(exactM[0].length).trim();
      delayLo = delayHi = parseInt(exactM[1]);
    }

    // Consecutive repetition [*N]
    const repM = rest.match(/\[\s*\*\s*(\d+)\s*\]/);
    const repeat = repM ? parseInt(repM[1]) : 1;

    const signals  = parseConsequentSignals(rest);
    const signal   = signals[0]?.label ?? null;
    const eqSig    = signals.find(s => s.equalTo);
    const equality = eqSig ? { lhs: eqSig.label, rhs: eqSig.equalTo } : null;

    return { delayLo, delayHi, isRange, isUnbounded, signal, signals, repeat, throughout: null, equality };
  }

  // ── TLDR Builder ─────────────────────────────────────────────────

  function buildTLDR(raw) {
    const { antecedent, implOp, consequent, localVars = new Set() } = raw;
    if (!implOp) return null;

    const ant  = extractAntecedentInfo(antecedent);
    const cons = extractConsequentInfo(consequent);
    const implOffset = implOp === '|=>' ? 1 : 0;

    // equality fast-path (data-capture: out_data == captured_data)
    if (cons.equality && localVars.has(cons.equality.rhs)) {
      const { lhs, rhs } = cons.equality;
      // Resolve the true source: captured_data = bus_in → use "bus_in" in the phrase
      const captureM = antecedent?.match(/,\s*(\w+)\s*=\s*(\w+)/i);
      const srcSig   = (captureM && captureM[1] === rhs) ? captureM[2] : rhs;
      const totalLo  = implOffset + cons.delayLo;
      const totalHi  = implOffset + cons.delayHi;
      const whenPhrase = ant.phrase ? `When ${ant.phrase}` : 'Every active clock cycle';
      let timingPhrase;
      if (totalLo === 0 && totalHi === 0)  timingPhrase = 'in the same cycle';
      else if (totalLo === totalHi)        timingPhrase = totalLo === 1 ? 'one cycle later' : `exactly ${totalLo} cycles later`;
      else if (cons.isUnbounded)           timingPhrase = `${totalLo} or more cycles later`;
      else                                 timingPhrase = `${totalLo}–${totalHi} cycles later`;
      // Include any co-occurring boolean signals (e.g. out_vld && out_data == captured_data)
      const boolSigs = cons.signals.filter(s => !s.equalTo && !localVars.has(s.label));
      const boolPart = boolSigs.length > 0
        ? boolSigs.map(s => s.negated ? `${s.label} must be low` : `${s.label} must be high`).join(' and ') + ', and '
        : '';
      return `${whenPhrase}, ${timingPhrase}, ${boolPart}${lhs} must equal the value of ${srcSig} captured at the trigger cycle.`;
    }

    // throughout fast-path
    if (cons.throughout) {
      const { holdSignal, targetSignal } = cons.throughout;
      const whenPhrase = ant.phrase ? `When ${ant.phrase}` : 'Every active clock cycle';
      const rangeStr   = cons.isUnbounded
        ? `within ${cons.delayLo}+ cycles`
        : `within ${cons.delayLo}–${cons.delayHi} cycles`;
      return `${whenPhrase}, ${holdSignal} must remain high continuously until ${targetSignal} is seen (${rangeStr}).`;
    }

    const totalLo = implOffset + cons.delayLo;
    const totalHi = implOffset + cons.delayHi;

    // "When X" phrase
    const whenPhrase = ant.phrase ? `When ${ant.phrase}` : 'Every active clock cycle';

    // Consequent phrase — all signals
    let thenPhrase;
    if (cons.signals.length > 0) {
      const sigPhrases = cons.signals.map(sig => {
        if (sig.negated)        return `${sig.label} must be low`;
        if (cons.repeat > 1)    return `${sig.label} must stay high for exactly ${cons.repeat} consecutive cycles`;
        return `${sig.label} must be high`;
      });
      thenPhrase = sigPhrases.length === 1
        ? sigPhrases[0]
        : sigPhrases.slice(0, -1).join(', ') + ' and ' + sigPhrases[sigPhrases.length - 1];
    } else {
      thenPhrase = 'the expectation must hold';
    }

    // Timing phrase
    let timingPhrase;
    if (cons.repeat > 1) {
      // Repetition case: "starting immediately / one cycle later / N cycles later"
      if (totalLo === 0)      timingPhrase = 'starting immediately';
      else if (totalLo === 1) timingPhrase = 'starting one cycle later';
      else                    timingPhrase = `starting ${totalLo} cycles later`;
    } else if (totalLo === 0 && totalHi === 0) {
      timingPhrase = 'in the same cycle';
    } else if (totalLo === totalHi) {
      timingPhrase = totalLo === 1 ? 'one cycle later' : `exactly ${totalLo} cycles later`;
    } else if (cons.isUnbounded) {
      timingPhrase = `${totalLo} or more cycles later`;
    } else {
      timingPhrase = `${totalLo}–${totalHi} cycles later`;
    }

    return `${whenPhrase}, ${thenPhrase} ${timingPhrase}.`;
  }

  // ── Antecedent Signal Parser ─────────────────────────────────────
  // Returns array of { label: string, negated: bool } for every
  // individual signal found in the antecedent expression.

  function parseAntecedentSignals(str) {
    const parsed = _parseAntecedentSignals(str);
    console.log('[parseAntecedentSignals] input:', JSON.stringify(str),
                '→', parsed.map(s => `${s.negated ? '!' : ''}${s.label}`).join(', '));
    return parsed;
  }

  function _parseAntecedentSignals(str) {
    if (!str) return [];
    const s = str.trim();

    // Sample-and-hold: ($rose/$fell(sig), var = source) → only the trigger signal
    const captureM = s.match(/^\(\s*\$(?:rose|fell)\s*\(\s*(\w+)\s*\)\s*,\s*\w+\s*=\s*\w+\s*\)$/i);
    if (captureM) return [{ label: captureM[1], negated: false }];

    // Single $rose / $fell
    const roseM = s.match(/^\$rose\s*\(\s*(\w+)\s*\)$/i);
    if (roseM) return [{ label: roseM[1], negated: false }];
    const fellM = s.match(/^\$fell\s*\(\s*(\w+)\s*\)$/i);
    if (fellM) return [{ label: fellM[1], negated: false }];

    // Single bare identifier (possibly negated)
    const negSingle = s.match(/^!\s*(\w+)$/);
    if (negSingle) return [{ label: negSingle[1], negated: true }];
    const singleM = s.match(/^(\w+)$/);
    if (singleM) return [{ label: singleM[1], negated: false }];

    // Compound: split on && or ||
    if (s.includes('&&') || s.includes('||')) {
      // Strip outer balanced parens before splitting so a leading "(" on the first
      // part or a trailing ")" on the last part don't corrupt negation detection.
      let expr = s;
      if (expr[0] === '(' && expr[expr.length - 1] === ')') {
        let d = 0;
        for (let i = 0; i < expr.length; i++) {
          if (expr[i] === '(') d++;
          else if (expr[i] === ')') {
            if (--d === 0) { if (i === expr.length - 1) expr = expr.slice(1, -1).trim(); break; }
          }
        }
      }
      return expr.split(/&&|\|\|/)
        .map(p => p.trim())
        .filter(Boolean)
        .map(p => {
          if (p[0] === '(' && p[p.length - 1] === ')') p = p.slice(1, -1).trim();
          const negSimple = p.match(/^!\s*(\w+)$/);
          if (negSimple) return { label: negSimple[1], negated: true };
          const negParen  = p.match(/^!\s*\(\s*(\w+)\s*\)$/);
          if (negParen)  return { label: negParen[1],  negated: true };
          const rM = p.match(/\$(?:rose|fell)\s*\(\s*(\w+)\s*\)/i);
          if (rM) return { label: rM[1], negated: false };
          const wM = p.match(/\b(\w+)\b/);
          return wM ? { label: wM[1], negated: false } : null;
        })
        .filter(Boolean);
    }

    // Fallback: first identifier
    const wM = s.match(/\b(\w+)\b/);
    return wM ? [{ label: wM[1], negated: false }] : [];
  }

  // ── Waveform SVG Builder ──────────────────────────────────────────

  function buildWaveformSVG(raw) {
    const { antecedent, implOp, consequent, clock, localVars = new Set() } = raw;

    const ant  = extractAntecedentInfo(antecedent);
    const cons = extractConsequentInfo(consequent);
    const implOffset = implOp === '|=>' ? 1 : 0;

    // Cycle positions (all relative to display; trigger shown at cycle TRIG)
    const TRIG     = 1;
    const evalStart = TRIG + implOffset;
    const expectLo  = evalStart + cons.delayLo;
    const expectHi  = evalStart + cons.delayHi;
    const repeatEnd = expectLo + cons.repeat;
    const TOTAL     = Math.min(Math.max(expectHi + 2, repeatEnd + 1, 4), 10);

    // Layout
    const ML = 70, MR = 20, MT = 14, MB = 26;
    const ROW_H = 34, SIG_H = 13, SIG_PAD = 9, CW = 54;

    // Edge alignment: posedge transitions at grid lines; negedge at midpoints
    const isNegedge = clock?.edge === 'negedge';
    const edgeOff   = isNegedge ? CW / 2 : 0;
    const edgeX     = (c) => ML + c * CW + edgeOff;

    // Signal rows
    const antSigs   = parseAntecedentSignals(antecedent);
    const antLabels = new Set(antSigs.map(s => s.label));
    const rows = [];
    rows.push({ label: clock?.signal || 'clk', type: 'clk' });
    for (const sig of antSigs) {
      rows.push({ label: sig.label, type: 'trigger', negated: sig.negated });
    }
    if (cons.throughout) {
      rows.push({ label: cons.throughout.holdSignal,   type: 'expect', negated: false, throughoutRole: 'hold'   });
      rows.push({ label: cons.throughout.targetSignal, type: 'expect', negated: false, throughoutRole: 'target' });
    } else {
      for (const sig of cons.signals) {
        if (localVars.has(sig.label)) continue;           // never draw local var rows
        if (sig.equalTo && localVars.has(sig.equalTo)) {  // data-capture comparison
          if (!antLabels.has(sig.label)) rows.push({ label: sig.label, type: 'expect', negated: false, dataComparison: sig.equalTo });
        } else if (cons.repeat > 1 || !antLabels.has(sig.label)) {
          rows.push({ label: sig.label, type: 'expect', negated: sig.negated });
        }
      }
    }

    const svgW  = ML + TOTAL * CW + MR;
    const svgH  = MT + rows.length * ROW_H + MB;
    const axisY = MT + rows.length * ROW_H;

    // Colors (monochrome + two semantic accents)
    const cGrid = '#2d333b';
    const cClk  = '#3d444d';
    const cText = '#6e7681';
    const cTrig = '#c9970a';   // trigger yellow
    const cExp  = '#388bfd';   // expectation blue
    const cImpl = '#3fb950';   // implication green
    const cWin  = 'rgba(56,139,253,0.07)';

    let s = '';

    // Defs: arrowhead for delay bracket
    s += `<defs>
      <marker id="wf-arr" markerWidth="6" markerHeight="4" refX="5" refY="2" orient="auto">
        <path d="M0,0 L6,2 L0,4Z" fill="${cExp}" opacity="0.55"/>
      </marker>
    </defs>`;

    // Axis line
    s += `<line x1="${ML}" y1="${axisY}" x2="${ML + TOTAL * CW}" y2="${axisY}" stroke="${cGrid}" stroke-width="1"/>`;

    // Vertical grid lines + cycle labels
    const gridMax = isNegedge ? TOTAL - 1 : TOTAL;
    for (let c = 0; c <= gridMax; c++) {
      const x   = edgeX(c);
      const off = c - TRIG;
      const lbl = off === 0 ? 'N' : off < 0 ? `N${off}` : `N+${off}`;
      const isEval    = c === evalStart && implOffset > 0;
      const inWindow  = c >= expectLo && c <= expectHi;
      const lblColor  = isEval ? cImpl : inWindow ? cExp : cText;

      s += `<line x1="${x}" y1="${MT}" x2="${x}" y2="${axisY}" stroke="${cGrid}" stroke-width="1"${c > 0 ? ' stroke-dasharray="2,4"' : ''}/>`;
      s += `<text x="${x}" y="${axisY + 17}" text-anchor="middle" font-size="10" fill="${lblColor}">${escapeHTML(lbl)}</text>`;
    }

    // |=> evaluation start marker (dashed green vertical)
    if (implOffset > 0) {
      const xEval = edgeX(evalStart);
      s += `<line x1="${xEval}" y1="${MT}" x2="${xEval}" y2="${axisY}" stroke="${cImpl}" stroke-width="1" stroke-dasharray="4,3" opacity="0.65"/>`;
      s += `<text x="${xEval + 4}" y="${MT + 11}" font-size="9" fill="${cImpl}">|=></text>`;
    }

    // Wait window + delay bracket — drawn for every expect row
    rows.forEach((expRow, expRowIdx) => {
      if (expRow.type !== 'expect') return;
      const ryH = MT + expRowIdx * ROW_H + SIG_PAD;
      const ryL = ryH + SIG_H;

      if (expRow.throughoutRole === 'hold') {
        // Hold signal: shade the full throughout window (TRIG → expectHi+1)
        const hx1 = edgeX(TRIG);
        const hx2 = edgeX(expectHi + 1);
        s += `<rect x="${hx1}" y="${ryH}" width="${hx2 - hx1}" height="${SIG_H}" fill="${cWin}" rx="1"/>`;
        return;
      }

      // Shaded wait region: evalStart → expectLo
      if (expectLo > evalStart) {
        const wx1 = edgeX(evalStart);
        const wx2 = edgeX(expectLo);
        s += `<rect x="${wx1}" y="${ryH}" width="${wx2 - wx1}" height="${SIG_H}" fill="${cWin}" rx="1"/>`;
        const ay = ryH + SIG_H / 2;
        s += `<line x1="${wx1 + 5}" y1="${ay}" x2="${wx2 - 5}" y2="${ay}" stroke="${cExp}" stroke-width="0.8" stroke-dasharray="3,2" marker-end="url(#wf-arr)" opacity="0.45"/>`;
      }

      // Shaded expect window: expectLo → expectHi+1
      if (cons.isRange) {
        const ex1 = edgeX(expectLo);
        const ex2 = edgeX(expectHi + 1);
        s += `<rect x="${ex1}" y="${ryH}" width="${ex2 - ex1}" height="${SIG_H}" fill="${cWin}" rx="1"/>`;
      }
    });

    // Draw signal waveforms
    rows.forEach((row, idx) => {
      const ry   = MT + idx * ROW_H;
      const yH   = ry + SIG_PAD;
      const yL   = ry + SIG_PAD + SIG_H;
      const xEnd = ML + TOTAL * CW;

      // Signal label (clock appends edge direction; negated antecedent signals prepend "!")
      const rowLabel = (row.type === 'clk' && isNegedge)   ? `${row.label} ↓`
                     : (row.type === 'trigger' && row.negated) ? `!${row.label}`
                     : row.label;
      s += `<text x="${ML - 8}" y="${yH + SIG_H / 2 + 4}" text-anchor="end" font-size="11" fill="${cText}">${escapeHTML(rowLabel)}</text>`;

      if (row.type === 'clk') {
        let d;
        if (isNegedge) {
          // Negedge clk: HIGH → falls at midpoint (active edge) → LOW → rises at grid line
          d = `M${ML},${yH}`;
          for (let c = 0; c < TOTAL; c++) {
            const x0 = ML + c * CW, xM = x0 + CW / 2, x1 = x0 + CW;
            d += ` L${xM},${yH} L${xM},${yL} L${x1},${yL} L${x1},${yH}`;
          }
        } else {
          // Posedge clk: LOW → rises at grid line (active edge) → HIGH → falls at midpoint
          d = `M${ML},${yL} L${ML},${yH}`;
          for (let c = 0; c < TOTAL; c++) {
            const x0 = ML + c * CW, xM = x0 + CW / 2, x1 = x0 + CW;
            d += ` L${xM},${yH} L${xM},${yL} L${x1},${yL} L${x1},${yH}`;
          }
        }
        s += `<path d="${d}" fill="none" stroke="${cClk}" stroke-width="1.5"/>`;

      } else if (row.type === 'trigger') {
        console.log('[waveform trigger row] label:', row.label, 'negated:', row.negated);
        const xTrig = edgeX(TRIG);
        const xNext = edgeX(TRIG + 1);
        if (row.negated) {
          // Active-low (!sig): flat LOW across entire waveform — asserted when low at cycle N
          s += `<path d="M${ML},${yL} L${xEnd},${yL}" fill="none" stroke="${cTrig}" stroke-width="1.5"/>`;
        } else {
          // Active-high: LOW → pulse HIGH at N → LOW after N+1
          s += `<path d="M${ML},${yL} L${xTrig},${yL} L${xTrig},${yH} L${xNext},${yH} L${xNext},${yL} L${xEnd},${yL}" fill="none" stroke="${cTrig}" stroke-width="1.5"/>`;
          s += `<text x="${xTrig + CW / 2}" y="${yH - 3}" text-anchor="middle" font-size="8" fill="${cTrig}" opacity="0.75">trigger</text>`;
        }

      } else if (row.type === 'expect') {
        const xStart = edgeX(expectLo);

        if (row.dataComparison) {
          // Data bus: filled rect inside the hold window, low lines outside
          const xBusStart = edgeX(expectLo);
          const xBusEnd   = cons.isRange ? edgeX(expectHi + 1) : edgeX(expectLo + 1);
          const diag      = Math.min(6, CW / 4);
          // Resolve source signal name from antecedent capture: "var = src" → show "= src@N"
          const captureM  = antecedent?.match(/,\s*(\w+)\s*=\s*(\w+)/i);
          const srcLabel  = (captureM && captureM[1] === row.dataComparison) ? captureM[2] : row.dataComparison;
          // Low lines before and after the window
          s += `<path d="M${ML},${yL} L${xBusStart},${yL}" fill="none" stroke="${cExp}" stroke-width="1.5"/>`;
          s += `<path d="M${xBusEnd},${yL} L${xEnd},${yL}" fill="none" stroke="${cExp}" stroke-width="1.5"/>`;
          // Filled rectangle (the bus value region)
          s += `<rect x="${xBusStart + diag}" y="${yH}" width="${Math.max(0, xBusEnd - xBusStart - 2 * diag)}" height="${SIG_H}" fill="${cExp}" opacity="0.12"/>`;
          // Trapezoid outline edges
          s += `<path d="M${xBusStart},${yL} L${xBusStart + diag},${yH} L${xBusEnd - diag},${yH} L${xBusEnd},${yL}" fill="none" stroke="${cExp}" stroke-width="1.5"/>`;
          // Label inside the bar
          s += `<text x="${(xBusStart + xBusEnd) / 2}" y="${(yH + yL) / 2 + 3}" text-anchor="middle" font-size="8" fill="${cExp}" opacity="0.9">${escapeHTML(`= ${srcLabel}@N`)}</text>`;

        } else if (row.throughoutRole === 'hold') {
          // Sustained HIGH from cycle N through the entire window
          const xHoldStart = edgeX(TRIG);
          const xHoldEnd   = edgeX(expectHi + 1);
          s += `<path d="M${ML},${yL} L${xHoldStart},${yL} L${xHoldStart},${yH} L${xHoldEnd},${yH} L${xHoldEnd},${yL} L${xEnd},${yL}" fill="none" stroke="${cExp}" stroke-width="1.5"/>`;
          const labelX = (xHoldStart + xHoldEnd) / 2;
          s += `<text x="${labelX}" y="${yH - 3}" text-anchor="middle" font-size="8" fill="${cExp}" opacity="0.75">throughout</text>`;

        } else if (row.throughoutRole === 'target') {
          // Representative pulse at midpoint of the window
          const midCycle = Math.round((expectLo + expectHi) / 2);
          const xRep    = edgeX(midCycle);
          const xRepEnd = edgeX(midCycle + 1);
          s += `<path d="M${ML},${yL} L${xRep},${yL} L${xRep},${yH} L${xRepEnd},${yH} L${xRepEnd},${yL} L${xEnd},${yL}" fill="none" stroke="${cExp}" stroke-width="1.5"/>`;
          s += `<text x="${(xRep + xRepEnd) / 2}" y="${yH - 3}" text-anchor="middle" font-size="8" fill="${cExp}" opacity="0.75">example</text>`;

        } else if (row.negated) {
          // Active-low: signal starts HIGH, drops LOW through the expected window
          if (cons.isRange) {
            const xHi = edgeX(expectHi + 1);
            s += `<path d="M${ML},${yH} L${xStart},${yH} L${xStart},${yL}" fill="none" stroke="${cExp}" stroke-width="1.5"/>`;
            s += `<path d="M${xStart},${yL} L${xHi},${yL}" fill="none" stroke="${cExp}" stroke-width="1.5" stroke-dasharray="5,3"/>`;
            s += `<path d="M${xHi},${yL} L${xHi},${yH} L${xEnd},${yH}" fill="none" stroke="${cExp}" stroke-width="1.5"/>`;
            s += `<text x="${(xStart + xHi) / 2}" y="${yH - 3}" text-anchor="middle" font-size="8" fill="${cExp}" opacity="0.75">must be low</text>`;
          } else {
            const xFall = edgeX(repeatEnd);
            s += `<path d="M${ML},${yH} L${xStart},${yH} L${xStart},${yL} L${xFall},${yL} L${xFall},${yH} L${xEnd},${yH}" fill="none" stroke="${cExp}" stroke-width="1.5"/>`;
            s += `<text x="${(xStart + xFall) / 2}" y="${yH - 3}" text-anchor="middle" font-size="8" fill="${cExp}" opacity="0.75">must be low</text>`;
          }
        } else if (cons.isRange) {
          // Active-high, range window: dashed top
          const xHi = edgeX(expectHi + 1);
          s += `<path d="M${ML},${yL} L${xStart},${yL} L${xStart},${yH}" fill="none" stroke="${cExp}" stroke-width="1.5"/>`;
          s += `<path d="M${xStart},${yH} L${xHi},${yH}" fill="none" stroke="${cExp}" stroke-width="1.5" stroke-dasharray="5,3"/>`;
          s += `<path d="M${xHi},${yH} L${xHi},${yL} L${xEnd},${yL}" fill="none" stroke="${cExp}" stroke-width="1.5"/>`;
          s += `<text x="${(xStart + xHi) / 2}" y="${yH - 3}" text-anchor="middle" font-size="8" fill="${cExp}" opacity="0.75">must be high</text>`;
        } else {
          // Active-high, clean pulse
          const xFall = edgeX(repeatEnd);
          s += `<path d="M${ML},${yL} L${xStart},${yL} L${xStart},${yH} L${xFall},${yH} L${xFall},${yL} L${xEnd},${yL}" fill="none" stroke="${cExp}" stroke-width="1.5"/>`;
          s += `<text x="${(xStart + xFall) / 2}" y="${yH - 3}" text-anchor="middle" font-size="8" fill="${cExp}" opacity="0.75">must be high</text>`;
        }
      }
    });

    // Left-side bracket grouping antecedent signals (only when there are 2+)
    const trigIdxFirst = rows.findIndex(r => r.type === 'trigger');
    const trigIdxLast  = rows.map(r => r.type).lastIndexOf('trigger');
    if (trigIdxFirst >= 0 && trigIdxLast > trigIdxFirst) {
      const bx   = 5;
      const yTop = MT + trigIdxFirst * ROW_H + SIG_PAD;
      const yBot = MT + trigIdxLast  * ROW_H + SIG_PAD + SIG_H;
      const midY = (yTop + yBot) / 2;
      s += `<line x1="${bx}" y1="${yTop}" x2="${bx}" y2="${yBot}" stroke="${cTrig}" stroke-width="1.2" opacity="0.45"/>`;
      s += `<line x1="${bx}" y1="${yTop}" x2="${bx + 5}" y2="${yTop}" stroke="${cTrig}" stroke-width="1.2" opacity="0.45"/>`;
      s += `<line x1="${bx}" y1="${yBot}" x2="${bx + 5}" y2="${yBot}" stroke="${cTrig}" stroke-width="1.2" opacity="0.45"/>`;
      s += `<text transform="rotate(-90,${bx - 2},${midY})" x="${bx - 2}" y="${midY + 3}" text-anchor="middle" font-size="7.5" fill="${cTrig}" opacity="0.55">antecedent</text>`;
    }

    return `<svg viewBox="0 0 ${svgW} ${svgH}" xmlns="http://www.w3.org/2000/svg" style="width:100%;height:auto;display:block;overflow:visible;">${s}</svg>`;
  }

  /* ================================================================
     SYNTAX HIGHLIGHTER
     Tokenizes SVA text into colored regions that map to the
     same color scheme as the output section cards.
     ================================================================ */

  // Type IDs → CSS classes
  const HL_PLAIN = 0, HL_COMMENT = 1, HL_DIM = 2, HL_CLOCK = 3,
        HL_TRIGGER = 4, HL_IMPL = 5, HL_EXPECT = 6, HL_TEMPORAL = 7;
  const HL_CLASS = ['hl-plain','hl-comment','hl-dim','hl-clock',
                    'hl-trigger','hl-implication','hl-expectation','hl-temporal'];

  function escapeHTML(s) {
    return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  }

  function fillTypes(arr, start, end, val) {
    const n = arr.length;
    for (let i = start; i < end && i < n; i++) arr[i] = val;
  }

  function highlightSVA(rawText) {
    if (!rawText) return '';
    const N = rawText.length;
    const T = new Uint8Array(N); // all HL_PLAIN by default

    // Comment-stripped clone (same length) for structural analysis
    const S = rawText
      .replace(/\/\/[^\n]*/g,      m => ' '.repeat(m.length))
      .replace(/\/\*[\s\S]*?\*\//g, m => ' '.repeat(m.length));

    // ── PASS 1: Collect all named property bodies ───────────────────
    // Build map: propertyName → { start, end } of its body in S
    const propBodyMap = {};
    for (const m of S.matchAll(/\bproperty\s+(\w+)\s*(?:\([^)]*\))?\s*;/gi)) {
      const name      = m[1];
      const bodyStart = m.index + m[0].length;
      const epM       = S.slice(bodyStart).match(/\bendproperty\b/i);
      if (epM) propBodyMap[name] = { start: bodyStart, end: bodyStart + epM.index };
      fillTypes(T, m.index, m.index + m[0].length, HL_DIM);   // dim "property NAME;"
    }
    for (const m of S.matchAll(/\bendproperty\b/gi)) {
      fillTypes(T, m.index, m.index + m[0].length, HL_DIM);   // dim "endproperty"
    }

    // Dim sequence...endsequence blocks entirely
    for (const m of S.matchAll(/\bsequence\s+\w+\s*;[\s\S]*?endsequence\b/gi)) {
      fillTypes(T, m.index, m.index + m[0].length, HL_DIM);
    }

    // ── PASS 2: Resolve assertion body to highlight ─────────────────
    let aStart = 0, aEnd = N;

    const assertM = S.match(/\b(?:assert|assume|cover|restrict)\s+property\s*\(/i);
    if (assertM) {
      // Extract paren content (balanced)
      const parenOpen = assertM.index + assertM[0].length - 1;
      let depth = 0, contentEnd = parenOpen;
      for (let i = parenOpen; i < N; i++) {
        if (S[i] === '(') depth++;
        else if (S[i] === ')') { depth--; if (depth === 0) { contentEnd = i; break; } }
      }

      const content = S.slice(parenOpen + 1, contentEnd).trim();
      const isNameRef = /^\w+$/.test(content);   // single identifier = named property ref

      if (isNameRef && propBodyMap[content]) {
        // ── Named reference, property body found ──────────────────
        // Dim the entire assert line; highlight tokens inside the property block
        fillTypes(T, assertM.index, contentEnd + 1, HL_DIM);
        aStart = propBodyMap[content].start;
        aEnd   = propBodyMap[content].end;
      } else if (isNameRef) {
        // Named reference but definition not in this buffer — dim & use first body
        fillTypes(T, assertM.index, contentEnd + 1, HL_DIM);
        const first = Object.values(propBodyMap)[0];
        if (first) { aStart = first.start; aEnd = first.end; }
        else        { aStart = aEnd = 0; }   // nothing to highlight
      } else {
        // ── Inline assertion inside assert property(...) ───────────
        fillTypes(T, assertM.index, assertM.index + assertM[0].length, HL_DIM);
        aStart = parenOpen + 1;
        aEnd   = contentEnd;
      }
    } else if (Object.keys(propBodyMap).length > 0) {
      // No assert line — bare property...endproperty block; use first body
      const first = Object.values(propBodyMap)[0];
      aStart = first.start;
      aEnd   = first.end;
    }
    // else: plain inline assertion with no wrappers — aStart=0, aEnd=N

    // ── Clock: @(posedge/negedge ...) ──────────────────────────────
    let clockEnd = aStart;
    const clkSlice = S.slice(aStart, aEnd);
    const clkM = clkSlice.match(/@\s*\(\s*(?:posedge|negedge|edge)\s+\w+(?:\s*,\s*\w+)?\s*\)/i);
    if (clkM) {
      const cs = aStart + clkM.index;
      const ce = cs + clkM[0].length;
      fillTypes(T, cs, ce, HL_CLOCK);
      clockEnd = ce;
    }

    // ── disable iff (...) ──────────────────────────────────────────
    let disEnd = clockEnd;
    const diSlice = S.slice(clockEnd, aEnd);
    const diM = diSlice.match(/disable\s+iff\s*\(/i);
    if (diM) {
      const diAbsStart = clockEnd + diM.index;
      const parenOpen  = clockEnd + diM.index + diM[0].length - 1;
      let depth = 0, diAbsEnd = parenOpen;
      for (let i = parenOpen; i < aEnd; i++) {
        if (S[i] === '(') depth++;
        else if (S[i] === ')') { depth--; if (depth === 0) { diAbsEnd = i + 1; break; } }
      }
      fillTypes(T, diAbsStart, diAbsEnd, HL_CLOCK);
      disEnd = diAbsEnd;
    }

    // ── Implication operator |-> or |=> at top-level ───────────────
    let implPos = -1, implLen = 3;
    {
      let depth = 0;
      for (let i = disEnd; i < aEnd - 2; i++) {
        const c = S[i];
        if (c === '(' || c === '[') depth++;
        else if (c === ')' || c === ']') depth--;
        else if (depth === 0 && c === '|') {
          if (S[i+1] === '-' && S[i+2] === '>') { implPos = i; break; }
          if (S[i+1] === '=' && S[i+2] === '>') { implPos = i; break; }
        }
      }
    }

    if (implPos !== -1) {
      fillTypes(T, disEnd,             implPos,            HL_TRIGGER); // 🟡
      fillTypes(T, implPos,            implPos + implLen,  HL_IMPL);    // 🟢
      fillTypes(T, implPos + implLen,  aEnd,               HL_EXPECT);  // 🔵
    }

    // ── Temporal operators (purple) — overrides trigger & expect ───
    const TEMPORAL_RE = [
      /##\s*\[\s*[^\]]+\]/g,
      /##\s*\d+/g,
      /\[\s*\*\s*[^\]]*\]/g,
      /\[\s*->[^\]]*\]/g,
      /\[\s*=[^\]]*\]/g,
      /\$(?:rose|fell|stable|past|isunknown|onehot0?|countones)\s*\([^)]*\)/gi,
      /\bthroughout\b/gi,
      /\bintersect\b/gi,
      /\bwithin\b/gi,
      /\bfirst_match\b/gi,
    ];
    for (const re of TEMPORAL_RE) {
      for (const m of rawText.matchAll(re)) {
        const t0 = T[m.index];
        if (t0 === HL_TRIGGER || t0 === HL_EXPECT || t0 === HL_PLAIN) {
          fillTypes(T, m.index, m.index + m[0].length, HL_TEMPORAL); // 🟣
        }
      }
    }

    // ── Comments win over everything ───────────────────────────────
    for (const m of rawText.matchAll(/\/\/[^\n]*/g))
      fillTypes(T, m.index, m.index + m[0].length, HL_COMMENT);
    for (const m of rawText.matchAll(/\/\*[\s\S]*?\*\//g))
      fillTypes(T, m.index, m.index + m[0].length, HL_COMMENT);

    // ── Build HTML from runs of same type ─────────────────────────
    // Map type ID → data-role value (null = no role attribute)
    const HL_ROLE = [null, null, null, 'clock', 'trigger', 'implication', 'expectation', 'temporal'];

    let html = '', i = 0;
    while (i < N) {
      const t = T[i];
      let j = i + 1;
      while (j < N && T[j] === t) j++;
      const role = HL_ROLE[t];
      const attr = role ? ` data-role="${role}"` : '';
      html += `<span class="${HL_CLASS[t]}"${attr}>${escapeHTML(rawText.slice(i, j))}</span>`;
      i = j;
    }
    return html;
  }

  /* ================================================================
     UI LOGIC
     ================================================================ */

  let dom = {};
  const state = { lastOutput: null, activeRole: null };

  function cacheDom() {
    dom = {
      highlightLayer:    document.getElementById('highlight-layer'),
      svaInput:          document.getElementById('sva-input'),
      charCount:         document.getElementById('char-count'),
      clearBtn:          document.getElementById('clear-btn'),
      translateBtn:      document.getElementById('translate-btn'),
      outputPlaceholder:  document.getElementById('output-placeholder'),
      outputContent:      document.getElementById('output-content'),
      outputPanelFooter:  document.getElementById('output-panel-footer'),
      reportIssueBtn:     document.getElementById('report-issue-btn'),
      copyBtn:            document.getElementById('copy-btn'),
      exampleBtns:        document.querySelectorAll('.example-btn'),
    };
  }

  function bindEvents() {
    dom.translateBtn.addEventListener('click', handleTranslate);
    dom.clearBtn.addEventListener('click', handleClear);
    dom.copyBtn.addEventListener('click', handleCopy);
    dom.reportIssueBtn.addEventListener('click', (e) => {
      e.preventDefault();
      const subject = encodeURIComponent('SVA-Whisperer: Bad Translation Report');
      const body    = encodeURIComponent(dom.svaInput.value);
      window.location.href = `mailto:menuchabrodie@gmail.com?subject=${subject}&body=${body}`;
    });

    dom.svaInput.addEventListener('input', () => {
      updateCharCount();
      updateHighlight();
      if (!dom.svaInput.value.trim()) {
        clearOutput();
        state.lastOutput = null;
      }
    });

    // Sync scroll: textarea scrolls, highlight layer follows
    dom.svaInput.addEventListener('scroll', () => {
      dom.highlightLayer.scrollTop  = dom.svaInput.scrollTop;
      dom.highlightLayer.scrollLeft = dom.svaInput.scrollLeft;
    });

    dom.svaInput.addEventListener('keydown', (e) => {
      if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
        e.preventDefault();
        handleTranslate();
      }
    });

    dom.exampleBtns.forEach((btn) => {
      btn.addEventListener('click', () => {
        const key = btn.dataset.key;
        if (EXAMPLES[key]) {
          dom.svaInput.value = EXAMPLES[key];
          dom.svaInput.scrollTop = 0;
          dom.svaInput.focus();
          updateCharCount();
          updateHighlight();
        }
      });
    });

    // ── Bidirectional hover linking ───────────────────────────────

    // Code → Card: hit-test the highlight layer through the transparent textarea
    dom.svaInput.addEventListener('mousemove', (e) => {
      // Temporarily give pointer-events to the layer so elementFromPoint hits its spans
      dom.svaInput.style.pointerEvents = 'none';
      dom.highlightLayer.style.pointerEvents = 'auto';
      const el = document.elementFromPoint(e.clientX, e.clientY);
      dom.svaInput.style.pointerEvents = '';
      dom.highlightLayer.style.pointerEvents = '';

      const roleEl = el?.closest('[data-role]');
      setActiveRole(roleEl?.dataset?.role || null);
    });
    dom.svaInput.addEventListener('mouseleave', () => setActiveRole(null));

    // Card → Code: delegate on the cards container
    dom.outputContent.addEventListener('mouseover', (e) => {
      const card = e.target.closest('.output-section');
      setActiveRole(card?.dataset?.role || null);
    });
    dom.outputContent.addEventListener('mouseleave', () => setActiveRole(null));
  }

  // ── Role Linking ─────────────────────────────────────────────────

  function setActiveRole(role) {
    if (role === state.activeRole) return;
    state.activeRole = role;

    // Clear previous state
    dom.highlightLayer.querySelectorAll('.hl-active, .hl-dimmed').forEach(el => {
      el.classList.remove('hl-active', 'hl-dimmed');
    });
    dom.outputContent.querySelectorAll('.card-active, .card-dimmed').forEach(el => {
      el.classList.remove('card-active', 'card-dimmed');
    });

    if (!role) return;

    // Activate matching code spans; dim the others
    dom.highlightLayer.querySelectorAll('[data-role]').forEach(el => {
      if (el.dataset.role === role) el.classList.add('hl-active');
      else el.classList.add('hl-dimmed');
    });

    // Activate matching card; dim the others
    dom.outputContent.querySelectorAll('.output-section').forEach(el => {
      if (el.dataset.role === role) el.classList.add('card-active');
      else el.classList.add('card-dimmed');
    });
  }

  function updateCharCount() {
    const len = dom.svaInput.value.length;
    dom.charCount.textContent = `${len} chars`;
    dom.charCount.classList.toggle('over-limit', len > 4000);
  }

  function updateHighlight() {
    dom.highlightLayer.innerHTML = highlightSVA(dom.svaInput.value);
    // Re-sync scroll position after content reflow
    dom.highlightLayer.scrollTop  = dom.svaInput.scrollTop;
    dom.highlightLayer.scrollLeft = dom.svaInput.scrollLeft;
  }

  // ── Handlers ────────────────────────────────────────────────────

  function handleTranslate() {
    const raw = dom.svaInput.value.trim();
    if (!raw) {
      showToast('Paste an SVA assertion first.', 'error');
      return;
    }

    clearOutput();

    let result;
    try {
      result = parseSVA(raw);
    } catch (err) {
      renderError(`Parser error: ${err.message}`);
      return;
    }

    state.lastOutput = result;
    renderOutput(result, raw);
  }

  function handleClear() {
    dom.svaInput.value = '';
    updateCharCount();
    updateHighlight();
    clearOutput();
    dom.svaInput.focus();
    state.lastOutput = null;
  }

  function handleCopy() {
    if (!state.lastOutput) return;
    const text = formatAsPlainText(state.lastOutput);
    if (navigator.clipboard && navigator.clipboard.writeText) {
      navigator.clipboard.writeText(text).then(flashCopied).catch(() => fallbackCopy(text));
    } else {
      fallbackCopy(text);
    }
  }

  function fallbackCopy(text) {
    const ta = document.createElement('textarea');
    ta.value = text;
    ta.style.cssText = 'position:fixed;opacity:0;';
    document.body.appendChild(ta);
    ta.select();
    try { document.execCommand('copy'); flashCopied(); }
    catch (_) { showToast('Could not copy — select text manually.', 'error'); }
    document.body.removeChild(ta);
  }

  function flashCopied() {
    dom.copyBtn.textContent = 'Copied!';
    setTimeout(() => { dom.copyBtn.textContent = 'Copy Output'; }, 2000);
  }

  // ── Unsupported Construct Detector ───────────────────────────────
  // Scans raw SVA text (comments stripped) for specific constructs that
  // the parser does not handle.  Returns an array of human-readable labels.

  function detectUnsupportedConstructs(rawText) {
    const found = [];
    // Strip comments so keywords inside comments don't trigger false positives
    const s = rawText
      .replace(/\/\/[^\n]*/g, '')
      .replace(/\/\*[\s\S]*?\*\//g, '');

    if (/\bsequence\b[\s\S]*?\bendsequence\b/i.test(s))
      found.push('sequence...endsequence (named sequence bodies are not expanded)');
    if (/\bnot\s*\(/i.test(s))
      found.push('not (...) — property negation operator');
    if (/\bif\s*\(/.test(s))
      found.push('if/else — conditional property');
    if (/\b(?:accept_on|reject_on|sync_accept_on|sync_reject_on)\s*\(/i.test(s))
      found.push('accept_on / reject_on — SVA abort operators');
    if (/\b(?:strong|weak)\s*\(/i.test(s))
      found.push('strong() / weak() — property strength modifiers');

    return found;
  }

  // ── Output Rendering ─────────────────────────────────────────────

  function renderOutput(parsed, rawInput) {
    dom.outputContent.innerHTML = '';
    let count = 0;

    // ── Detect partial parse ──────────────────────────────────────
    // A parse is "partial" when no implication operator was found and no
    // antecedent was isolated — meaning the parser could not decompose the
    // assertion into trigger / consequent.  Clock/reset and temporal
    // operators may still be recognized.
    const { implOp, antecedent, clock } = parsed._raw;
    const isPartial = !implOp && antecedent === null;

    // Detect specific unsupported constructs in the raw text.
    // This can trigger even when the assertion IS structurally parsed.
    const unsupported = detectUnsupportedConstructs(rawInput || '');

    // Show banner when the parse is partial OR specific unsupported constructs
    // are present.
    const showBanner = isPartial || unsupported.length > 0;

    // Keys whose content is unreliable when the parse is partial.
    // clock_reset is only trustworthy when an actual clock was found.
    const UNRECOGNIZED_KEYS = isPartial
      ? new Set(clock
          ? ['trigger', 'implication', 'expectation']
          : ['clock_reset', 'trigger', 'implication', 'expectation'])
      : new Set();

    // ── TLDR + waveform (skip for partial — they'd be misleading) ─
    if (!isPartial) {
      const tldr = buildTLDR(parsed._raw);
      if (tldr) {
        const el = document.createElement('p');
        el.className = 'tldr-section';
        el.textContent = tldr;
        dom.outputContent.appendChild(el);
      }

      const svgMarkup = buildWaveformSVG(parsed._raw);
      if (svgMarkup) {
        const el = document.createElement('div');
        el.className = 'waveform-section';
        el.innerHTML = svgMarkup;
        dom.outputContent.appendChild(el);
      }

      if (tldr || svgMarkup) {
        const sep = document.createElement('div');
        sep.className = 'section-separator';
        dom.outputContent.appendChild(sep);
      }
    }

    // ── Partial-parse / unsupported-construct banner ─────────────
    if (showBanner) {
      const banner = document.createElement('div');
      banner.className = 'partial-parse-banner';

      if (unsupported.length > 0) {
        // Name the specific constructs that were detected
        const intro = document.createElement('div');
        intro.textContent = '⚠️ Unsupported constructs detected — translation may be incomplete:';
        intro.style.marginBottom = '6px';
        banner.appendChild(intro);

        const list = document.createElement('ul');
        list.style.cssText = 'margin:0;padding-left:18px;';
        unsupported.forEach(label => {
          const li = document.createElement('li');
          li.textContent = label;
          list.appendChild(li);
        });
        banner.appendChild(list);

        const hint = document.createElement('div');
        hint.style.cssText = 'margin-top:6px;opacity:0.8;';
        hint.textContent = 'Please use the Report Issue button to send us this snippet.';
        banner.appendChild(hint);
      } else {
        // Generic message for partial parses with no identifiable construct
        banner.textContent = '⚠️ This assertion contains constructs that are not yet supported. Please use the Report Issue button to send us this snippet.';
      }

      dom.outputContent.appendChild(banner);
    }

    // ── Section cards ────────────────────────────────────────────
    SECTION_CONFIG.forEach(({ key, label, role }) => {
      const isUnrecognized = UNRECOGNIZED_KEYS.has(key);
      const text = isUnrecognized ? 'Not recognized.' : parsed[key];
      if (!text) return;

      const section = document.createElement('div');
      section.className = 'output-section';
      section.dataset.role = role;
      section.style.animationDelay = `${count * 55}ms`;

      const labelEl = document.createElement('div');
      labelEl.className = 'section-label';
      labelEl.textContent = label;

      const body = document.createElement('div');
      body.className = isUnrecognized ? 'section-body not-recognized' : 'section-body';
      body.textContent = text;

      section.appendChild(labelEl);
      section.appendChild(body);
      dom.outputContent.appendChild(section);

      requestAnimationFrame(() => section.classList.add('animate-in'));
      count++;
    });

    dom.outputContent.hidden = false;
    dom.outputPlaceholder.hidden = true;
    dom.outputPanelFooter.hidden = false;
    dom.copyBtn.disabled = false;
  }

  function renderError(message) {
    dom.outputContent.innerHTML = '';

    const card = document.createElement('div');
    card.className = 'error-card';

    const title = document.createElement('div');
    title.className = 'error-card-title';
    title.textContent = 'Could not parse assertion';

    const body = document.createElement('div');
    body.className = 'error-card-body';
    body.textContent = message;

    card.appendChild(title);
    card.appendChild(body);
    dom.outputContent.appendChild(card);
    dom.outputContent.hidden = false;
    dom.outputPlaceholder.hidden = true;
  }

  function clearOutput() {
    setActiveRole(null);
    dom.outputContent.innerHTML = '';
    dom.outputContent.hidden = true;
    dom.outputPlaceholder.hidden = false;
    dom.outputPanelFooter.hidden = true;
    dom.copyBtn.disabled = true;
  }

  // ── Utilities ────────────────────────────────────────────────────

  function showToast(message, type = 'info') {
    document.querySelector('.toast')?.remove();
    const t = document.createElement('div');
    t.className = `toast ${type}`;
    t.textContent = message;
    document.body.appendChild(t);
    setTimeout(() => t.remove(), 4200);
  }

  function formatAsPlainText(parsed) {
    return SECTION_CONFIG
      .filter(({ key }) => parsed[key])
      .map(({ key, label }) => `${label.toUpperCase()}\n${'─'.repeat(label.length)}\n${parsed[key]}`)
      .join('\n\n');
  }

  // ── Boot ─────────────────────────────────────────────────────────

  document.addEventListener('DOMContentLoaded', () => {
    cacheDom();
    bindEvents();
    updateCharCount();
    updateHighlight();
  });

})();
