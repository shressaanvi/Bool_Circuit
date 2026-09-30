/* ==========================================================================
   BOOL( ) CIRCUIT — application logic
   Sections:
   1. Constants & theme / footer / panel wiring
   2. Truth-table input panel builder
   3. Expression parser (tokenizer + recursive-descent, postfix ' and !/~ NOT)
   4. Quine–McCluskey simplification (essential PIs + greedy cover for the rest)
   5. Gate trees: SOP tree -> NAND-only / NOR-only via De Morgan substitution
   6. Circuit diagram layout & SVG rendering (theme-aware, uses CSS vars)
   7. Reading each input mode into a truth vector
   8. Rendering results + verification
   9. Main "generate" handler & event wiring
   ========================================================================== */

const VARNAMES = ['A', 'B', 'C', 'D', 'E', 'F'];

/* -------------------------------------------------------------------------
   1. Theme / footer / panel wiring
   ------------------------------------------------------------------------- */

function setTheme(theme) {
  document.documentElement.setAttribute('data-theme', theme);
  const label = document.getElementById('theme-toggle-label');
  if (label) label.textContent = theme === 'dark' ? 'Dark' : 'Light';
  const toggle = document.getElementById('theme-toggle');
  if (toggle) toggle.setAttribute('aria-pressed', theme === 'light');
  try { localStorage.setItem('bool-circuit-theme', theme); } catch (e) { /* ignore storage errors */ }
}

function showPanel(type) {
  document.querySelectorAll('.input-panel').forEach(p => {
    p.classList.toggle('is-hidden', p.dataset.panel !== type);
  });
}

/* -------------------------------------------------------------------------
   2. Truth-table input panel builder (regenerated when var count changes)
   ------------------------------------------------------------------------- */

function buildTruthTableInputPanel(numVars) {
  const varNames = VARNAMES.slice(0, numVars);
  const table = document.getElementById('truth-table-input');
  if (!table) return;

  const theadRow = table.querySelector('thead tr');
  theadRow.innerHTML = varNames.map(v => `<th scope="col">${v}</th>`).join('') +
    `<th scope="col" class="th-output">F</th>`;

  const tbody = table.querySelector('tbody');
  const total = 1 << numVars;
  let html = '';
  for (let i = 0; i < total; i++) {
    const bits = i.toString(2).padStart(numVars, '0');
    // Allocate the whole row to be clickable with .tt-row
    html += `<tr class="tt-row" data-index="${i}">` + bits.split('').map(b => `<td>${b}</td>`).join('') +
      `<td><button type="button" class="cell-toggle" data-val="0" aria-label="Output for row ${i}">0</button></td></tr>`;
  }
  tbody.innerHTML = html;
}

/* -------------------------------------------------------------------------
   3. Expression parser
   Grammar:
     Expression := Term ('+' Term)*
     Term       := Factor ( ('.' )? Factor )*        (implicit AND)
     Factor     := Primary ("'")*                     (postfix NOT)
     Primary    := ('!'|'~') Primary | VAR | '(' Expression ')'
   AST nodes all use a uniform shape: { type, inputs: [...] } (VAR also has .name)
   ------------------------------------------------------------------------- */

function tokenizeExpression(str) {
  const tokens = [];
  let i = 0;
  while (i < str.length) {
    const c = str[i];
    if (/\s/.test(c)) { i++; continue; }
    if (/[A-Za-z]/.test(c)) { tokens.push({ type: 'VAR', value: c.toUpperCase() }); i++; continue; }
    if (c === "'") { tokens.push({ type: 'NOT' }); i++; continue; }
    if (c === '.' || c === '*') { tokens.push({ type: 'AND' }); i++; continue; }
    if (c === '+') { tokens.push({ type: 'OR' }); i++; continue; }
    if (c === '!' || c === '~') { tokens.push({ type: 'NOTPRE' }); i++; continue; }
    if (c === '(') { tokens.push({ type: 'LPAREN' }); i++; continue; }
    if (c === ')') { tokens.push({ type: 'RPAREN' }); i++; continue; }
    throw new Error(`Unexpected character "${c}" in expression.`);
  }
  return tokens;
}

class ExprParser {
  constructor(tokens) { this.tokens = tokens; this.pos = 0; }
  peek() { return this.tokens[this.pos]; }
  consume() { return this.tokens[this.pos++]; }

  parseExpression() {
    let node = this.parseTerm();
    while (this.peek() && this.peek().type === 'OR') {
      this.consume();
      const right = this.parseTerm();
      node = { type: 'OR', inputs: [node, right] };
    }
    return node;
  }

  parseTerm() {
    let node = this.parseFactor();
    while (this.peek() && ['AND', 'VAR', 'LPAREN', 'NOTPRE'].includes(this.peek().type)) {
      if (this.peek().type === 'AND') this.consume();
      const right = this.parseFactor();
      node = { type: 'AND', inputs: [node, right] };
    }
    return node;
  }

  parseFactor() {
    let node = this.parsePrimary();
    while (this.peek() && this.peek().type === 'NOT') {
      this.consume();
      node = { type: 'NOT', inputs: [node] };
    }
    return node;
  }

  parsePrimary() {
    const tok = this.peek();
    if (!tok) throw new Error('Unexpected end of expression — check for a missing variable or parenthesis.');
    if (tok.type === 'NOTPRE') {
      this.consume();
      return { type: 'NOT', inputs: [this.parsePrimary()] };
    }
    if (tok.type === 'VAR') {
      this.consume();
      return { type: 'VAR', name: tok.value, inputs: [] };
    }
    if (tok.type === 'LPAREN') {
      this.consume();
      const node = this.parseExpression();
      if (!this.peek() || this.peek().type !== 'RPAREN') throw new Error('Missing closing parenthesis ")".');
      this.consume();
      return node;
    }
    throw new Error('Unexpected symbol in expression — check your syntax.');
  }
}

function parseExpressionString(raw) {
  const tokens = tokenizeExpression(raw);
  if (tokens.length === 0) throw new Error('Please enter a Boolean expression.');
  const parser = new ExprParser(tokens);
  const ast = parser.parseExpression();
  if (parser.pos < tokens.length) throw new Error('Could not fully parse the expression — check your syntax.');
  return ast;
}

function collectVars(node, set) {
  if (node.type === 'VAR') { set.add(node.name); return; }
  node.inputs.forEach(c => collectVars(c, set));
}

/* Universal evaluator — works for expression ASTs (VAR/NOT/AND/OR) and for
   the gate trees built later (which add CONST0/CONST1/NAND/NOR). */
function evalNode(node, assign) {
  switch (node.type) {
    case 'VAR': return assign[node.name];
    case 'CONST0': return 0;
    case 'CONST1': return 1;
    case 'NOT': return evalNode(node.inputs[0], assign) ? 0 : 1;
    case 'AND': return (evalNode(node.inputs[0], assign) && evalNode(node.inputs[1], assign)) ? 1 : 0;
    case 'OR': return (evalNode(node.inputs[0], assign) || evalNode(node.inputs[1], assign)) ? 1 : 0;
    case 'NAND': return (evalNode(node.inputs[0], assign) && evalNode(node.inputs[1], assign)) ? 0 : 1;
    case 'NOR': return (evalNode(node.inputs[0], assign) || evalNode(node.inputs[1], assign)) ? 0 : 1;
    default: throw new Error('Unknown node type: ' + node.type);
  }
}

function allAssignments(numVars, varNames) {
  const rows = [];
  const total = 1 << numVars;
  for (let i = 0; i < total; i++) {
    const bits = i.toString(2).padStart(numVars, '0');
    const assign = {};
    for (let v = 0; v < numVars; v++) assign[varNames[v]] = bits[v] === '1' ? 1 : 0;
    rows.push(assign);
  }
  return rows;
}

/* -------------------------------------------------------------------------
   4. Quine–McCluskey simplification
   ------------------------------------------------------------------------- */

function combineBits(a, b) {
  let diffPos = -1, diffCount = 0;
  for (let i = 0; i < a.length; i++) {
    if (a[i] !== b[i]) {
      diffCount++;
      diffPos = i;
      if (diffCount > 1) return null;
    }
  }
  if (diffCount !== 1) return null;
  return a.slice(0, diffPos) + '-' + a.slice(diffPos + 1);
}

function getPrimeImplicants(indices, numVars) {
  let current = indices.map(m => ({ bin: m.toString(2).padStart(numVars, '0'), covers: new Set([m]) }));
  const allPIsMap = new Map();

  while (current.length > 0) {
    const combinedMap = new Map();
    const usedIdx = new Set();

    for (let i = 0; i < current.length; i++) {
      for (let j = i + 1; j < current.length; j++) {
        const combinedBin = combineBits(current[i].bin, current[j].bin);
        if (combinedBin === null) continue;
        usedIdx.add(i); usedIdx.add(j);
        const covers = new Set([...current[i].covers, ...current[j].covers]);
        if (combinedMap.has(combinedBin)) {
          covers.forEach(c => combinedMap.get(combinedBin).covers.add(c));
        } else {
          combinedMap.set(combinedBin, { bin: combinedBin, covers });
        }
      }
    }

    current.forEach((t, i) => { if (!usedIdx.has(i)) allPIsMap.set(t.bin, t); });
    current = Array.from(combinedMap.values());
  }

  return Array.from(allPIsMap.values());
}

/* Essential PIs first, then Petrick's method (exact minimum cover) for
   whatever minterms remain — this is what guarantees the expression that
   comes out is truly minimal, not just "good enough". Petrick's method
   expands a product-of-sums of candidate PIs into a sum-of-products and
   keeps the smallest term (fewest PIs, then fewest literals). Because that
   expansion can blow up on pathological inputs, a capped, pruned search is
   used, falling back to a greedy cover only if the cap is hit. */
function selectEssentialPIs(minterms, dontCares, allPIs) {
  const targets = minterms.filter(m => !dontCares.includes(m));
  if (targets.length === 0) return [];

  const coverMap = new Map();
  targets.forEach(m => coverMap.set(m, []));
  allPIs.forEach((pi, idx) => {
    pi.covers.forEach(c => { if (coverMap.has(c)) coverMap.get(c).push(idx); });
  });

  const selected = new Set();
  targets.forEach(m => {
    const coveringIdx = coverMap.get(m);
    if (coveringIdx.length === 1) selected.add(coveringIdx[0]);
  });

  const covered = new Set();
  selected.forEach(idx => allPIs[idx].covers.forEach(c => { if (targets.includes(c)) covered.add(c); }));

  const remaining = targets.filter(m => !covered.has(m));
  if (remaining.length > 0) {
    const candidateIdx = allPIs
      .map((_, idx) => idx)
      .filter(idx => !selected.has(idx) && remaining.some(m => allPIs[idx].covers.has(m)));
    petricksMethod(remaining, candidateIdx, allPIs).forEach(idx => selected.add(idx));
  }

  return Array.from(selected).map(idx => allPIs[idx]);
}

function literalCountOf(pi) {
  return [...pi.bin].filter(ch => ch !== '-').length;
}

function isSubset(a, b) {
  for (const x of a) if (!b.has(x)) return false;
  return true;
}

/* Drop any candidate set that is a strict superset of another candidate —
   a superset can never be part of a minimum cover, so pruning them keeps
   the product-of-sums expansion from exploding. */
function pruneSupersets(sets) {
  const seen = new Map();
  sets.forEach(s => seen.set([...s].sort((a, b) => a - b).join(','), s));
  const unique = Array.from(seen.values());
  return unique.filter(s => !unique.some(other => other !== s && other.size < s.size && isSubset(other, s)));
}

function greedyCover(remaining, candidateIdx, allPIs) {
  const selected = [];
  let left = remaining.slice();
  while (left.length > 0) {
    let bestIdx = -1, bestCount = -1;
    candidateIdx.forEach(idx => {
      if (selected.includes(idx)) return;
      const count = left.filter(m => allPIs[idx].covers.has(m)).length;
      if (count > bestCount) { bestCount = count; bestIdx = idx; }
    });
    if (bestIdx === -1 || bestCount <= 0) break;
    selected.push(bestIdx);
    left = left.filter(m => !allPIs[bestIdx].covers.has(m));
  }
  return selected;
}

function petricksMethod(remaining, candidateIdx, allPIs) {
  const PETRICK_LIMIT = 4000; // safety cap on the product-of-sums expansion

  // One clause (list of candidate PI indices) per remaining minterm.
  const clauses = remaining.map(m => candidateIdx.filter(idx => allPIs[idx].covers.has(m)));
  if (clauses.some(c => c.length === 0)) return greedyCover(remaining, candidateIdx, allPIs);

  let products = [new Set()];
  for (const clause of clauses) {
    const next = [];
    for (const p of products) {
      for (const idx of clause) {
        if (p.has(idx)) { next.push(p); continue; } // already covers this minterm
        const merged = new Set(p);
        merged.add(idx);
        next.push(merged);
      }
    }
    products = pruneSupersets(next);
    if (products.length > PETRICK_LIMIT) return greedyCover(remaining, candidateIdx, allPIs);
  }

  let best = null;
  products.forEach(p => {
    const literalCount = [...p].reduce((s, idx) => s + literalCountOf(allPIs[idx]), 0);
    if (!best || p.size < best.size || (p.size === best.size && literalCount < best.literalCount)) {
      best = { size: p.size, literalCount, set: p };
    }
  });
  return best ? Array.from(best.set) : greedyCover(remaining, candidateIdx, allPIs);
}

function piTermsToExpression(binList, varNames) {
  if (binList.length === 0) return '0';
  if (binList.some(b => [...b].every(ch => ch === '-'))) return '1';
  const terms = binList.map(bin => {
    let term = '';
    for (let i = 0; i < bin.length; i++) {
      if (bin[i] === '1') term += varNames[i];
      else if (bin[i] === '0') term += varNames[i] + "'";
    }
    return term;
  });
  return terms.join(' + ');
}

/* -------------------------------------------------------------------------
   5. Gate networks: a shared DAG builder (not a tree) so that repeated
   literals — the same variable inverted for use in several product terms —
   are built ONCE and fanned out to every gate that needs them. This is the
   single biggest lever for a genuinely minimal gate count: the previous
   tree-based approach rebuilt a fresh inverter (or worse, a whole cloned
   subtree) for every occurrence.

   Each plan (basic AND/OR/NOT, NAND-only, NOR-only) is built against the
   textbook-minimal two-level identities:
     NAND-NAND : F = NAND(NAND(term1 literals), NAND(term2 literals), ...)
                  (works directly — no extra inverters at the OR level;
                  a term with a single literal must itself be inverted so
                  every operand feeding the top gate is NOT(product))
     NOR-NOR   : AND(l1,l2,...) = NOR(¬l1,¬l2,...)      (no extra inverter)
                 OR(term1,...)  = NOT(NOR(term1,...))    (one final inverter,
                  skipped when there is only a single term)
   A 2-variable XOR/XNOR pattern (the two PI terms use the same two
   variables with opposite polarities) is special-cased to the well-known
   4-gate NAND/NOR XOR construction, which beats the generic expansion.
   ------------------------------------------------------------------------- */

class CircuitBuilder {
  constructor() {
    this.nodes = new Map();
    this._next = 0;
    this._varCache = new Map();
    this._invCache = new Map();
  }
  _id() { return 'n' + (this._next++); }
  addVar(name) {
    if (this._varCache.has(name)) return this._varCache.get(name);
    const id = this._id();
    this.nodes.set(id, { id, type: 'VAR', name, inputs: [] });
    this._varCache.set(name, id);
    return id;
  }
  addConst(bit) {
    const id = this._id();
    this.nodes.set(id, { id, type: bit ? 'CONST1' : 'CONST0', inputs: [] });
    return id;
  }
  addGate(type, inputIds) {
    const id = this._id();
    this.nodes.set(id, { id, type, inputs: inputIds.slice() });
    return id;
  }
  /* A single-input inverter, realized either as a real NOT gate or as a
     self-tied universal gate (NAND/NOR). Cached per (gateType, child) pair
     so the same variable is only ever inverted once and then fanned out. */
  addInverter(gateType, childId) {
    const key = gateType + ':' + childId;
    if (this._invCache.has(key)) return this._invCache.get(key);
    const id = gateType === 'NOT' ? this.addGate('NOT', [childId]) : this.addGate(gateType, [childId, childId]);
    this._invCache.set(key, id);
    return id;
  }
}

/* literalWire  -> the literal's own signal (var, or NOT var if negated) */
function literalWire(builder, invType, varIdx, neg, varNames) {
  const varId = builder.addVar(varNames[varIdx]);
  return neg ? builder.addInverter(invType, varId) : varId;
}
/* complementOfLiteral -> the complement of the literal's signal (NOT var if
   positive, or the bare var if the literal was already negated — no
   double negation) */
function complementOfLiteral(builder, invType, varIdx, neg, varNames) {
  const varId = builder.addVar(varNames[varIdx]);
  return neg ? varId : builder.addInverter(invType, varId);
}

function usedIndices(bin) {
  const idxs = [];
  for (let i = 0; i < bin.length; i++) if (bin[i] !== '-') idxs.push(i);
  return idxs;
}

/* Detects piTerms === exactly two product terms over exactly the same two
   variables with opposite polarities, i.e. an XOR or XNOR in disguise. */
function detectXorPattern(piTerms, varNames) {
  if (piTerms.length !== 2) return null;
  const idxs0 = usedIndices(piTerms[0]);
  const idxs1 = usedIndices(piTerms[1]);
  if (idxs0.length !== 2 || idxs1.length !== 2) return null;
  if (idxs0[0] !== idxs1[0] || idxs0[1] !== idxs1[1]) return null;

  const [i, j] = idxs0;
  const bin0 = piTerms[0], bin1 = piTerms[1];
  if (bin0[i] === bin1[i] || bin0[j] === bin1[j]) return null; // must differ on both bits

  return { a: varNames[i], b: varNames[j], xnor: bin0[i] === bin0[j] };
}

function isConst0(piTerms) { return piTerms.length === 0; }
function isConst1(piTerms) { return piTerms.some(b => [...b].every(ch => ch === '-')); }

function buildBasicPlan(builder, piTerms, varNames) {
  if (isConst0(piTerms)) return builder.addConst(0);
  if (isConst1(piTerms)) return builder.addConst(1);

  const xorInfo = detectXorPattern(piTerms, varNames);
  if (xorInfo) {
    const aId = builder.addVar(xorInfo.a), bId = builder.addVar(xorInfo.b);
    return builder.addGate(xorInfo.xnor ? 'XNOR' : 'XOR', [aId, bId]);
  }

  const termIds = piTerms.map(bin => {
    const idxs = usedIndices(bin);
    if (idxs.length === 0) return builder.addConst(1);
    const literalIds = idxs.map(i => literalWire(builder, 'NOT', i, bin[i] === '0', varNames));
    return literalIds.length === 1 ? literalIds[0] : builder.addGate('AND', literalIds);
  });

  return termIds.length === 1 ? termIds[0] : builder.addGate('OR', termIds);
}

function buildNANDPlan(builder, piTerms, varNames) {
  if (isConst0(piTerms)) return builder.addConst(0);
  if (isConst1(piTerms)) return builder.addConst(1);

  const xorInfo = detectXorPattern(piTerms, varNames);
  if (xorInfo) {
    const aId = builder.addVar(xorInfo.a), bId = builder.addVar(xorInfo.b);
    const n1 = builder.addGate('NAND', [aId, bId]);
    const n2 = builder.addGate('NAND', [aId, n1]);
    const n3 = builder.addGate('NAND', [bId, n1]);
    const out = builder.addGate('NAND', [n2, n3]); // = XOR(a,b), 4 gates
    return xorInfo.xnor ? builder.addInverter('NAND', out) : out; // XNOR = 5 gates
  }

  const terms = piTerms.map(bin => usedIndices(bin).map(i => ({ i, neg: bin[i] === '0' })));

  if (terms.length === 1) {
    const lits = terms[0];
    if (lits.length === 0) return builder.addConst(1);
    if (lits.length === 1) return literalWire(builder, 'NAND', lits[0].i, lits[0].neg, varNames);
    const literalIds = lits.map(l => literalWire(builder, 'NAND', l.i, l.neg, varNames));
    return builder.addInverter('NAND', builder.addGate('NAND', literalIds));
  }

  // >= 2 terms: every term must contribute NOT(product) to the top NAND.
  const termNotIds = terms.map(lits => {
    if (lits.length === 1) return complementOfLiteral(builder, 'NAND', lits[0].i, lits[0].neg, varNames);
    const literalIds = lits.map(l => literalWire(builder, 'NAND', l.i, l.neg, varNames));
    return builder.addGate('NAND', literalIds); // already NOT(product)
  });
  return builder.addGate('NAND', termNotIds);
}

function buildNORPlan(builder, piTerms, varNames) {
  if (isConst0(piTerms)) return builder.addConst(0);
  if (isConst1(piTerms)) return builder.addConst(1);

  const xorInfo = detectXorPattern(piTerms, varNames);
  if (xorInfo) {
    const aId = builder.addVar(xorInfo.a), bId = builder.addVar(xorInfo.b);
    const n1 = builder.addGate('NOR', [aId, bId]);
    const n2 = builder.addGate('NOR', [aId, n1]);
    const n3 = builder.addGate('NOR', [bId, n1]);
    const out = builder.addGate('NOR', [n2, n3]); // = XNOR(a,b), 4 gates
    return xorInfo.xnor ? out : builder.addInverter('NOR', out); // XOR = 5 gates
  }

  const terms = piTerms.map(bin => usedIndices(bin).map(i => ({ i, neg: bin[i] === '0' })));

  const termVals = terms.map(lits => {
    if (lits.length === 0) return { id: builder.addConst(1), single: true };
    if (lits.length === 1) return { id: literalWire(builder, 'NOR', lits[0].i, lits[0].neg, varNames), single: true };
    const compIds = lits.map(l => complementOfLiteral(builder, 'NOR', l.i, l.neg, varNames));
    return { id: builder.addGate('NOR', compIds), single: false }; // = AND(literals) directly
  });

  if (termVals.length === 1) return termVals[0].id;

  const norAll = builder.addGate('NOR', termVals.map(t => t.id));
  return builder.addInverter('NOR', norAll); // OR(...) = NOT(NOR(...))
}

function evalDAGNode(builder, id, assign, memo) {
  if (memo.has(id)) return memo.get(id);
  const node = builder.nodes.get(id);
  const inVal = i => evalDAGNode(builder, node.inputs[i], assign, memo);
  let val;
  switch (node.type) {
    case 'VAR': val = assign[node.name]; break;
    case 'CONST0': val = 0; break;
    case 'CONST1': val = 1; break;
    case 'NOT': val = inVal(0) ? 0 : 1; break;
    case 'AND': val = node.inputs.every((_, i) => inVal(i)) ? 1 : 0; break;
    case 'OR': val = node.inputs.some((_, i) => inVal(i)) ? 1 : 0; break;
    case 'NAND': val = node.inputs.every((_, i) => inVal(i)) ? 0 : 1; break;
    case 'NOR': val = node.inputs.some((_, i) => inVal(i)) ? 0 : 1; break;
    case 'XOR': val = (inVal(0) !== inVal(1)) ? 1 : 0; break;
    case 'XNOR': val = (inVal(0) === inVal(1)) ? 1 : 0; break;
    default: throw new Error('Unknown node type: ' + node.type);
  }
  memo.set(id, val);
  return val;
}

/* -------------------------------------------------------------------------
   6. Circuit diagram layout & SVG rendering (DAG-aware: a node with several
   consumers is drawn once and its output wire fans out to each of them)
   ------------------------------------------------------------------------- */

const CIRCUIT_XSTEP = 160, CIRCUIT_YSTEP = 80, CIRCUIT_LEFT = 70, CIRCUIT_TOP = 40;

function layoutDAG(builder, rootId) {
  const reachable = new Set();
  (function dfs(id) {
    if (reachable.has(id)) return;
    reachable.add(id);
    builder.nodes.get(id).inputs.forEach(dfs);
  })(rootId);

  const leaves = [...reachable].filter(id => builder.nodes.get(id).inputs.length === 0);
  leaves.sort((a, b) => {
    const na = builder.nodes.get(a), nb = builder.nodes.get(b);
    const ra = na.type === 'VAR' ? VARNAMES.indexOf(na.name) : 99;
    const rb = nb.type === 'VAR' ? VARNAMES.indexOf(nb.name) : 99;
    return ra - rb;
  });

  const level = new Map(), y = new Map();
  leaves.forEach((id, i) => { level.set(id, 0); y.set(id, i * CIRCUIT_YSTEP); });

  function getLevel(id) {
    if (level.has(id)) return level.get(id);
    const node = builder.nodes.get(id);
    const lvl = Math.max(...node.inputs.map(getLevel)) + 1;
    level.set(id, lvl);
    return lvl;
  }
  function getY(id) {
    if (y.has(id)) return y.get(id);
    const node = builder.nodes.get(id);
    const uniqueInputs = [...new Set(node.inputs)];
    const val = uniqueInputs.reduce((s, cid) => s + getY(cid), 0) / uniqueInputs.length;
    y.set(id, val);
    return val;
  }
  reachable.forEach(id => { getLevel(id); getY(id); });

  return { reachable, level, y };
}

function shapeFor(type, inputCount) {
  const bigW = 56, smallW = 40;
  const h = type === 'NOT' ? 30 : Math.max(44, (inputCount - 1) * 22 + 30);
  switch (type) {
    case 'AND': return { w: bigW, h, outTip: bigW * 0.55 + h / 2, bubble: false, bubbleR: 0 };
    case 'NAND': return { w: bigW, h, outTip: bigW * 0.55 + h / 2, bubble: true, bubbleR: 5 };
    case 'OR': return { w: bigW, h, outTip: bigW * 0.62, bubble: false, bubbleR: 0 };
    case 'NOR': return { w: bigW, h, outTip: bigW * 0.62, bubble: true, bubbleR: 5 };
    case 'XOR': return { w: bigW, h, outTip: bigW * 0.62, bubble: false, bubbleR: 0 };
    case 'XNOR': return { w: bigW, h, outTip: bigW * 0.62, bubble: true, bubbleR: 5 };
    case 'NOT': return { w: smallW, h, outTip: smallW * 0.75, bubble: true, bubbleR: 5 };
    default: throw new Error('Unknown gate type: ' + type);
  }
}

function drawGate(gx, gy, type, dims) {
  const halfH = dims.h / 2;
  let path = '', extra = '';
  if (type === 'AND' || type === 'NAND') {
    const straightW = dims.w * 0.55;
    path = `M${gx},${gy - halfH} H${gx + straightW} A${halfH},${halfH} 0 0 1 ${gx + straightW},${gy + halfH} H${gx} Z`;
  } else if (type === 'OR' || type === 'NOR' || type === 'XOR' || type === 'XNOR') {
    path = `M${gx},${gy - halfH} Q${gx + dims.w * 0.4},${gy - halfH} ${gx + dims.w * 0.62},${gy} ` +
      `Q${gx + dims.w * 0.4},${gy + halfH} ${gx},${gy + halfH} Q${gx + dims.w * 0.18},${gy} ${gx},${gy - halfH} Z`;
    if (type === 'XOR' || type === 'XNOR') {
      extra = `<path d="M${gx - 6},${gy - halfH} Q${gx + dims.w * 0.18 - 6},${gy} ${gx - 6},${gy + halfH}" class="gwire"/>`;
    }
  } else if (type === 'NOT') {
    path = `M${gx},${gy - halfH} L${gx + dims.w * 0.75},${gy} L${gx},${gy + halfH} Z`;
  }
  let svg = `<path d="${path}" class="gshape"/>` + extra;
  if (dims.bubble) {
    svg += `<circle cx="${gx + dims.outTip + dims.bubbleR}" cy="${gy}" r="${dims.bubbleR}" class="gbubble"/>`;
  }
  return svg;
}

function buildCircuitSVGFromDAG(builder, rootId) {
  const { reachable, level, y } = layoutDAG(builder, rootId);
  const nodes = [...reachable].map(id => builder.nodes.get(id));
  const leafNodes = nodes.filter(n => n.inputs.length === 0);
  const gateNodes = nodes.filter(n => n.inputs.length > 0).sort((a, b) => level.get(a.id) - level.get(b.id));

  const maxLevel = Math.max(...nodes.map(n => level.get(n.id)));
  const maxY = Math.max(...nodes.map(n => y.get(n.id)));
  const width = CIRCUIT_LEFT + maxLevel * CIRCUIT_XSTEP + 170;
  const height = CIRCUIT_TOP * 2 + maxY + 20;

  let svg = `<svg viewBox="0 0 ${width} ${height}" xmlns="http://www.w3.org/2000/svg" class="circuit-svg" role="img" aria-label="Logic circuit diagram">`;
  svg += `<style>
    .gwire{stroke:var(--ink-muted);stroke-width:1.6;fill:none;}
    .gshape{stroke:var(--ink);stroke-width:1.6;fill:var(--surface-raised);}
    .gbubble{stroke:var(--ink);stroke-width:1.6;fill:var(--surface);}
    .glabel{font-family:var(--font-mono);font-size:13px;fill:var(--ink);}
    .goutlabel{font-family:var(--font-mono);font-size:13px;fill:var(--accent);font-weight:600;}
  </style>`;

  const posX = id => CIRCUIT_LEFT + level.get(id) * CIRCUIT_XSTEP;
  const posY = id => CIRCUIT_TOP + y.get(id);
  const outX = new Map();

  leafNodes.forEach(n => {
    const label = n.type === 'VAR' ? n.name : (n.type === 'CONST0' ? '0' : '1');
    const lx = posX(n.id), ly = posY(n.id);
    svg += `<text x="${lx - 10}" y="${ly + 5}" text-anchor="end" class="glabel">${label}</text>`;
    svg += `<line x1="${lx}" y1="${ly}" x2="${lx + 20}" y2="${ly}" class="gwire"/>`;
    outX.set(n.id, lx + 20);
  });

  gateNodes.forEach(n => {
    const dims = shapeFor(n.type, n.inputs.length);
    const gx = posX(n.id), gy = posY(n.id);
    svg += drawGate(gx, gy, n.type, dims);
    outX.set(n.id, gx + dims.outTip + (dims.bubble ? dims.bubbleR * 2 : 0));

    const count = n.inputs.length;
    const inputYs = count === 1 ? [gy] : n.inputs.map((_, idx) => gy - ((count - 1) * 10) + idx * 20);
    n.inputs.forEach((cid, idx) => {
      const py = inputYs[idx];
      const startX = outX.get(cid), startY = posY(cid);
      const midX = (startX + gx) / 2;
      svg += `<path d="M${startX},${startY} H${midX} V${py} H${gx}" class="gwire"/>`;
    });
  });

  const rootX = outX.get(rootId), rootY = posY(rootId);
  svg += `<line x1="${rootX}" y1="${rootY}" x2="${rootX + 30}" y2="${rootY}" class="gwire"/>`;
  svg += `<text x="${rootX + 38}" y="${rootY + 5}" class="goutlabel">F</text>`;
  svg += `</svg>`;
  return svg;
}

/* -------------------------------------------------------------------------
   7. Reading each input mode into a truth vector
   ------------------------------------------------------------------------- */

function parseIndexList(str, maxExclusive, label) {
  if (!str || !str.trim()) return [];
  const parts = str.split(',').map(s => s.trim()).filter(s => s.length > 0);
  const nums = [];
  for (const p of parts) {
    if (!/^\d+$/.test(p)) throw new Error(`Invalid ${label} value "${p}" — please use whole numbers.`);
    const n = parseInt(p, 10);
    if (n < 0 || n >= maxExclusive) throw new Error(`${label} value ${n} is out of range (0–${maxExclusive - 1}).`);
    nums.push(n);
  }
  return nums;
}

function checkOverlap(a, b) {
  const setB = new Set(b);
  const dup = a.find(x => setB.has(x));
  if (dup !== undefined) throw new Error(`Index ${dup} appears in both the term list and the don't-care list.`);
}

function readTruthTableInput(numVars) {
  // Target the new button element instead of text inputs
  const inputs = document.querySelectorAll('#truth-table-input tbody .cell-toggle');
  const total = 1 << numVars;
  if (inputs.length !== total) throw new Error('Truth table size mismatch — try reselecting the number of variables.');
  const vector = [];
  inputs.forEach((el, i) => {
    const v = el.dataset.val.toUpperCase();
    if (v === '0' || v === '1') vector.push(parseInt(v, 10));
    else if (v === 'X') vector.push('X');
    else throw new Error(`Row ${i} of the truth table needs a 0, 1, or X.`);
  });
  return vector;
}

function getFunctionFromInput(inputType, numVars, varNames) {
  const total = 1 << numVars;

  if (inputType === 'expression') {
    const raw = document.getElementById('expression-input').value.trim();
    if (!raw) throw new Error('Please enter a Boolean expression.');
    const ast = parseExpressionString(raw);
    const used = new Set();
    collectVars(ast, used);
    used.forEach(v => {
      if (!varNames.includes(v)) {
        throw new Error(`Variable "${v}" is not among the selected ${numVars} variable(s) (${varNames.join(', ')}).`);
      }
    });
    const rows = allAssignments(numVars, varNames);
    const truthVector = rows.map(r => evalNode(ast, r));
    const minterms = [];
    truthVector.forEach((v, i) => { if (v === 1) minterms.push(i); });
    return { truthVector, minterms, dontCares: [], originalEvalFn: (assign) => evalNode(ast, assign) };
  }

  if (inputType === 'truth-table') {
    const truthVector = readTruthTableInput(numVars);
    const minterms = [], dontCares = [];
    truthVector.forEach((v, i) => { if (v === 1) minterms.push(i); else if (v === 'X') dontCares.push(i); });
    return { truthVector, minterms, dontCares, originalEvalFn: null };
  }

  if (inputType === 'minterms') {
    const minterms = parseIndexList(document.getElementById('minterms-input').value, total, 'minterm');
    const dontCares = parseIndexList(document.getElementById('minterms-dontcare').value, total, "don't-care");
    if (minterms.length === 0) throw new Error('Enter at least one minterm.');
    checkOverlap(minterms, dontCares);
    const truthVector = new Array(total).fill(0);
    minterms.forEach(i => { truthVector[i] = 1; });
    dontCares.forEach(i => { truthVector[i] = 'X'; });
    return { truthVector, minterms: [...new Set(minterms)], dontCares: [...new Set(dontCares)], originalEvalFn: null };
  }

  if (inputType === 'maxterms') {
    const maxterms = parseIndexList(document.getElementById('maxterms-input').value, total, 'maxterm');
    const dontCares = parseIndexList(document.getElementById('maxterms-dontcare').value, total, "don't-care");
    if (maxterms.length === 0) throw new Error('Enter at least one maxterm.');
    checkOverlap(maxterms, dontCares);
    const truthVector = new Array(total).fill(1);
    maxterms.forEach(i => { truthVector[i] = 0; });
    dontCares.forEach(i => { truthVector[i] = 'X'; });
    const minterms = [];
    truthVector.forEach((v, i) => { if (v === 1) minterms.push(i); });
    return { truthVector, minterms, dontCares: [...new Set(dontCares)], originalEvalFn: null };
  }

  throw new Error('Unknown input type.');
}

/* -------------------------------------------------------------------------
   8. Rendering results + verification
   ------------------------------------------------------------------------- */

function escapeHtml(s) {
  return String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
}

function renderSimplifiedExpression(str) {
  document.querySelector('#result-expression .result-body').innerHTML =
    `<p class="mono-result">F = ${escapeHtml(str)}</p>`;
}

function renderTruthTable(vector, varNames, numVars) {
  const rows = allAssignments(numVars, varNames);
  let html = '<div class="table-scroll"><table class="truth-table"><thead><tr>';
  varNames.forEach(v => { html += `<th scope="col">${v}</th>`; });
  html += '<th scope="col" class="th-output">F</th></tr></thead><tbody>';
  rows.forEach((assign, i) => {
    html += '<tr>';
    varNames.forEach(v => { html += `<td>${assign[v]}</td>`; });
    const val = vector[i];
    html += `<td>${val === 'X' ? '<span class="cell-x">X</span>' : val}</td>`;
    html += '</tr>';
  });
  html += '</tbody></table></div>';
  document.querySelector('#result-truth-table .result-body').innerHTML = html;
}

function renderCircuitInto(cardId, builder, rootId) {
  const container = document.querySelector(`#${cardId} .diagram-body`);
  container.innerHTML = buildCircuitSVGFromDAG(builder, rootId);
}

function renderVerification(status, inputType) {
  const items = document.querySelectorAll('#result-verification .verify-item');
  const labels = inputType === 'expression'
    ? ['Original expression', 'Simplified expression', 'NAND-only circuit', 'NOR-only circuit']
    : ['Given input', 'Simplified expression', 'NAND-only circuit', 'NOR-only circuit'];
  const values = [status.origSelfMatch, status.simpMatch, status.nandMatch, status.norMatch];

  items.forEach((li, i) => {
    li.innerHTML = '<span class="verify-dot" aria-hidden="true"></span>' + labels[i];
    li.dataset.status = values[i] ? 'pass' : 'fail';
  });

  const summary = document.querySelector('#result-verification .placeholder-text');
  const allPass = values.every(Boolean);
  summary.textContent = allPass
    ? "All representations match on every input row (don't-cares excluded). ✓"
    : 'Mismatch detected — check the highlighted item(s) above.';
}

function showError(msg) {
  let banner = document.getElementById('error-banner');
  if (!banner) {
    banner = document.createElement('div');
    banner.id = 'error-banner';
    banner.className = 'error-banner';
    const panel = document.getElementById('input-section');
    panel.parentNode.insertBefore(banner, panel);
  }
  banner.textContent = msg;
  banner.style.display = 'block';
}

function clearError() {
  const banner = document.getElementById('error-banner');
  if (banner) banner.style.display = 'none';
}

/* -------------------------------------------------------------------------
   9. Main "generate" handler & event wiring
   ------------------------------------------------------------------------- */

function generate() {
  clearError();
  try {
    const numVars = parseInt(document.getElementById('var-count').value, 10);
    const varNames = VARNAMES.slice(0, numVars);
    const inputType = document.getElementById('input-type').value;

    const { truthVector, minterms, dontCares, originalEvalFn } = getFunctionFromInput(inputType, numVars, varNames);
    const uniqueMinterms = [...new Set(minterms)];
    const uniqueDontCares = [...new Set(dontCares)];

    const allPIs = getPrimeImplicants([...uniqueMinterms, ...uniqueDontCares], numVars);
    const essential = selectEssentialPIs(uniqueMinterms, uniqueDontCares, allPIs);
    const piTerms = essential.map(p => p.bin);
    const simplifiedExprStr = piTermsToExpression(piTerms, varNames);

    const basicBuilder = new CircuitBuilder();
    const basicRoot = buildBasicPlan(basicBuilder, piTerms, varNames);
    const nandBuilder = new CircuitBuilder();
    const nandRoot = buildNANDPlan(nandBuilder, piTerms, varNames);
    const norBuilder = new CircuitBuilder();
    const norRoot = buildNORPlan(norBuilder, piTerms, varNames);

    renderSimplifiedExpression(simplifiedExprStr);
    renderTruthTable(truthVector, varNames, numVars);
    renderCircuitInto('result-basic-gates', basicBuilder, basicRoot);
    renderCircuitInto('result-nand', nandBuilder, nandRoot);
    renderCircuitInto('result-nor', norBuilder, norRoot);

    const rows = allAssignments(numVars, varNames);
    let simpMatch = true, nandMatch = true, norMatch = true, origSelfMatch = true;
    rows.forEach((assign, i) => {
      if (truthVector[i] === 'X') return;
      const target = truthVector[i];
      if (evalDAGNode(basicBuilder, basicRoot, assign, new Map()) !== target) simpMatch = false;
      if (evalDAGNode(nandBuilder, nandRoot, assign, new Map()) !== target) nandMatch = false;
      if (evalDAGNode(norBuilder, norRoot, assign, new Map()) !== target) norMatch = false;
      if (inputType === 'expression' && originalEvalFn(assign) !== target) origSelfMatch = false;
    });

    renderVerification({ origSelfMatch, simpMatch, nandMatch, norMatch }, inputType);
  } catch (err) {
    showError(err.message || 'Something went wrong — please check your input.');
    console.error(err);
  }
}

document.addEventListener('DOMContentLoaded', () => {
  let savedTheme = 'dark';
  try { savedTheme = localStorage.getItem('bool-circuit-theme') || 'dark'; } catch (e) { /* ignore */ }
  setTheme(savedTheme);

  const yearEl = document.getElementById('footer-year');
  if (yearEl) yearEl.textContent = new Date().getFullYear();

  buildTruthTableInputPanel(parseInt(document.getElementById('var-count').value, 10));
  showPanel(document.getElementById('input-type').value);

  document.getElementById('var-count').addEventListener('change', (e) => {
    buildTruthTableInputPanel(parseInt(e.target.value, 10));
  });
  
  document.getElementById('input-type').addEventListener('change', (e) => showPanel(e.target.value));
  
  document.getElementById('theme-toggle').addEventListener('click', () => {
    const current = document.documentElement.getAttribute('data-theme') || 'dark';
    setTheme(current === 'dark' ? 'light' : 'dark');
  });
  
  document.getElementById('generate-btn').addEventListener('click', generate);

  // Handle full-row clicking for the interactive truth table
  document.getElementById('truth-table-input').addEventListener('click', (e) => {
    const row = e.target.closest('.tt-row');
    if (!row) return;
    
    const btn = row.querySelector('.cell-toggle');
    if (btn) {
      const current = btn.dataset.val;
      const next = current === '0' ? '1' : (current === '1' ? 'X' : '0');
      btn.dataset.val = next;
      btn.textContent = next;
    }
  });
});