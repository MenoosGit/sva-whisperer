'use strict';
// ── Waveform SVG Builder ──────────────────────────────────────────────
// Tests for buildWaveformSVG: SVG structure, dynamic left margin,
// row labels, trigger rendering, !$isunknown absorption, general
// equality bus rows, color legend, and bracket rendering.

const { _test } = require('../../app.js');
const { buildWaveformSVG, parseSVA } = _test;

// Helper: build SVG from a raw SVA string
const svg = (sva) => buildWaveformSVG(parseSVA(sva)._raw);

// ════════════════════════════════════════════════════════════════════
// ✅  Basic SVG structure
// ════════════════════════════════════════════════════════════════════
describe('SVG structure', () => {
  test('output is a valid SVG element', () => {
    const s = svg('assert property (@(posedge clk) req |-> ##1 ack);');
    expect(s).toMatch(/^<svg /);
    expect(s).toContain('</svg>');
    expect(s).toMatch(/viewBox="0 0 \d+ \d+"/);
  });

  test('wider delay range produces a wider canvas', () => {
    const narrow = svg('assert property (@(posedge clk) req |-> ##1 ack);');
    const wide   = svg('assert property (@(posedge clk) req |-> ##[2:8] ack);');
    const w = (s) => parseInt(s.match(/viewBox="0 0 (\d+)/)[1]);
    expect(w(wide)).toBeGreaterThan(w(narrow));
  });
});

// ════════════════════════════════════════════════════════════════════
// ✅  Dynamic left margin — longest label widens canvas
// ════════════════════════════════════════════════════════════════════
describe('dynamic left margin', () => {
  test('long signal name produces a wider canvas than a short one', () => {
    const short = svg('assert property (@(posedge clk) req |-> ##1 ack);');
    const long  = svg('assert property (@(posedge clk) a_very_long_signal_name |-> ##1 ack);');
    const w = (s) => parseInt(s.match(/viewBox="0 0 (\d+)/)[1]);
    expect(w(long)).toBeGreaterThan(w(short));
  });

  test('trigger label longer than 16 chars is truncated with "…"', () => {
    const s = svg('assert property (@(posedge clk) a_trigger_signal_exceeding_sixteen_chars |-> ##1 ack);');
    expect(s).toContain('…'); // "…"
  });

  test('expect-row label is never truncated even when long', () => {
    const s = svg('assert property (@(posedge clk) req |-> ##1 a_very_long_expect_signal_name_here);');
    expect(s).not.toContain('…');
  });

  test('clock label is never truncated', () => {
    const s = svg('assert property (@(posedge a_long_clock_signal_name) req |-> ##1 ack);');
    expect(s).not.toContain('…');
  });
});

// ════════════════════════════════════════════════════════════════════
// ✅  Row label rendering — prefix / badge / edge decoration
// ════════════════════════════════════════════════════════════════════
describe('row label rendering', () => {
  test('negated bit signal gets "!" prefix in SVG text', () => {
    const s = svg('assert property (@(posedge clk) !fifo_full |-> ##1 ack);');
    expect(s).toContain('!fifo_full');
  });

  test('!$past(sig) row shows "sig @N-1" in SVG text', () => {
    const s = svg('assert property (@(posedge clk) !$past(rst_i) |-> ##1 ack);');
    expect(s).toContain('@N-1');
    // Raw $past label must not appear
    expect(s).not.toContain('$past');
  });

  test('negedge clock shows "↓" decorator in label', () => {
    const s = svg('assert property (@(negedge clk) req |-> ##1 ack);');
    expect(s).toContain('↓'); // ↓
  });
});

// ════════════════════════════════════════════════════════════════════
// ✅  Trigger signal rendering — active-low vs active-high
// ════════════════════════════════════════════════════════════════════
describe('trigger signal rendering', () => {
  test('positive signal renders active-high pulse with "trigger" annotation', () => {
    const s = svg('assert property (@(posedge clk) req |-> ##1 ack);');
    expect(s).toContain('>trigger<');
  });

  test('plain !sig renders flat-LOW — no "trigger" annotation', () => {
    // Active-low: one flat line at yL, no pulse text
    const s = svg('assert property (@(posedge clk) !fifo_full |-> ##1 ack);');
    expect(s).not.toContain('>trigger<');
  });

  test('!$isunknown(sig) (system-fn, parens in label) renders active-high pulse', () => {
    // isunknown has parens → treated as active-high, not flat-low
    const s = svg('assert property (@(posedge clk) !$isunknown(cyc_cnt) |-> ##1 ack);');
    expect(s).toContain('>trigger<');
  });
});

// ════════════════════════════════════════════════════════════════════
// ✅  !$isunknown absorption into bus row
// ════════════════════════════════════════════════════════════════════
describe('!$isunknown absorption', () => {
  // Assertion where !$isunknown(cyc_cnt) is in the antecedent AND
  // cyc_cnt appears as a bus row in the consequent — triggers absorption.
  const ISU_SVA =
    "assert property (@(posedge clk) (us_tick && !$isunknown(cyc_cnt)) |-> (cyc_cnt == (CYCLES_PER_US - 1)));";

  test('isunknown trigger row is suppressed — label does not appear as a row', () => {
    expect(svg(ISU_SVA)).not.toMatch(/>isunknown\(cyc_cnt\)</);
  });

  test('bus row shows "✓ no X/Z" annotation', () => {
    expect(svg(ISU_SVA)).toContain('✓ no X/Z');
  });

  test('bus row shows GTKWave-style bold "X" in X-state region', () => {
    const s = svg(ISU_SVA);
    expect(s).toContain('font-weight="bold"');
    expect(s).toContain('>X<');
  });

  test('bus row shows cleaned value label (CYCLES_PER_US-1)', () => {
    expect(svg(ISU_SVA)).toContain('CYCLES_PER_US-1');
  });

  test('FALLBACK: when !$isunknown target has no bus row, trigger row is kept', () => {
    // cyc_cnt is in the antecedent but ack is the only consequent signal — no absorption
    const s = svg('assert property (@(posedge clk) (us_tick && !$isunknown(cyc_cnt)) |-> ##1 ack);');
    expect(s).toMatch(/isunknown/);
    // No X/Z annotation since there is no absorbed bus row
    expect(s).not.toContain('✓ no X/Z');
  });
});

// ════════════════════════════════════════════════════════════════════
// ✅  General equality bus row — constant / parameter expression RHS
// ════════════════════════════════════════════════════════════════════
describe('general equality bus row', () => {
  test('expression RHS is rendered as a bus value label', () => {
    const s = svg('assert property (@(posedge clk) us_tick |-> (cyc_cnt == (CYCLES_PER_US - 1)));');
    expect(s).toContain('CYCLES_PER_US-1');
  });

  test('outer parens are stripped from the bus value text', () => {
    const s = svg('assert property (@(posedge clk) us_tick |-> (cyc_cnt == (CYCLES_PER_US - 1)));');
    expect(s).not.toContain('(CYCLES_PER_US');
  });

  test('spaces around arithmetic operators are removed for compactness', () => {
    const s = svg('assert property (@(posedge clk) us_tick |-> (cnt == (MAX - 1)));');
    expect(s).toContain('MAX-1');
    expect(s).not.toContain('MAX - 1');
  });
});

// ════════════════════════════════════════════════════════════════════
// ✅  Color legend — presence and correctness
// ════════════════════════════════════════════════════════════════════
describe('color legend', () => {
  test('Clock swatch is always present', () => {
    expect(svg('assert property (@(posedge clk) req |-> ##1 ack);')).toContain('>Clock<');
  });

  test('Antecedent entry present when trigger rows exist', () => {
    expect(svg('assert property (@(posedge clk) req |-> ##1 ack);')).toContain('>Antecedent<');
  });

  test('Consequent entry present when expect rows exist', () => {
    expect(svg('assert property (@(posedge clk) req |-> ##1 ack);')).toContain('>Consequent<');
  });

  test('Unknown/X/Z entry present when hasIsUnknownGate row exists', () => {
    const s = svg("assert property (@(posedge clk) (us_tick && !$isunknown(cyc_cnt)) |-> (cyc_cnt == (CYCLES_PER_US - 1)));");
    expect(s).toContain('>Unknown/X/Z<');
  });

  test('Unknown/X/Z entry absent for plain assertions', () => {
    expect(svg('assert property (@(posedge clk) req |-> ##1 ack);')).not.toContain('Unknown/X/Z');
  });
});

// ════════════════════════════════════════════════════════════════════
// ✅  Square bracket rendering
// ════════════════════════════════════════════════════════════════════
describe('antecedent bracket', () => {
  test('single trigger row: renders a short vertical tick (line at bspine=4)', () => {
    const s = svg('assert property (@(posedge clk) req |-> ##1 ack);');
    expect(s).toMatch(/<line x1="4"/);
  });

  test('multiple trigger rows: renders a square [ bracket path (starts at barm=16)', () => {
    const s = svg('assert property (@(posedge clk) (write_en && addr_valid && !fifo_full) |-> ##1 ack);');
    expect(s).toMatch(/<path d="M16,/);
  });
});
