/*
 * Sudoku engine: solver, unique-solution generator and human-style grader.
 * A direct port of sudoku_board.gd from ../sudoku-godot, using 10-bit candidate
 * masks (bit d set = digit d possible) instead of arrays.
 *
 * Loads as a classic script in a page, a worker (importScripts) or a test page;
 * everything hangs off the global `SudokuEngine`.
 */
var SudokuEngine = (function () {
  "use strict";

  var SIZE = 9;
  var CELLS = 81;
  var ALL = 0x3fe; // bits 1..9 set

  /** Technique tiers, easiest -> hardest. `maxTechnique` indexes this. */
  var TECHNIQUE_NAMES = [
    "Naked single",
    "Hidden single",
    "Naked pair",
    "Hidden pair",
    "Pointing pair/triple",
    "Naked triple",
    "X-Wing",
  ];

  // ---- bit helpers -------------------------------------------------
  var POPCOUNT = new Uint8Array(1024);
  var BIT_TO_DIGIT = new Uint8Array(1024);
  for (var m = 0; m < 1024; m++) {
    var c = 0;
    for (var b = 0; b < 10; b++) if (m & (1 << b)) c++;
    POPCOUNT[m] = c;
  }
  for (var d = 1; d <= 9; d++) BIT_TO_DIGIT[1 << d] = d;

  /** Digits present in a mask, as an array. */
  function maskDigits(mask) {
    var out = [];
    for (var n = 1; n <= 9; n++) if (mask & (1 << n)) out.push(n);
    return out;
  }

  // ---- geometry ----------------------------------------------------
  var ROW_OF = new Uint8Array(CELLS);
  var COL_OF = new Uint8Array(CELLS);
  var BOX_OF = new Uint8Array(CELLS);
  for (var i = 0; i < CELLS; i++) {
    ROW_OF[i] = (i / 9) | 0;
    COL_OF[i] = i % 9;
    BOX_OF[i] = (((i / 9) | 0) / 3 | 0) * 3 + ((i % 9) / 3 | 0);
  }

  // 27 units (9 rows, 9 columns, 9 boxes), each an array of 9 cell indices.
  var UNITS = [];
  var BOX_UNITS_START = 18;
  for (var r = 0; r < 9; r++) {
    var row = [];
    for (var x = 0; x < 9; x++) row.push(r * 9 + x);
    UNITS.push(row);
  }
  for (var col = 0; col < 9; col++) {
    var cl = [];
    for (var y = 0; y < 9; y++) cl.push(y * 9 + col);
    UNITS.push(cl);
  }
  for (var by = 0; by < 3; by++) {
    for (var bx = 0; bx < 3; bx++) {
      var box = [];
      for (var dy = 0; dy < 3; dy++)
        for (var dx = 0; dx < 3; dx++) box.push((by * 3 + dy) * 9 + bx * 3 + dx);
      UNITS.push(box);
    }
  }

  // The 20 cells that share a row, column or box with each cell.
  var PEERS = [];
  for (var p = 0; p < CELLS; p++) {
    var seen = {};
    var list = [];
    for (var u = 0; u < UNITS.length; u++) {
      if (UNITS[u].indexOf(p) === -1) continue;
      for (var k = 0; k < 9; k++) {
        var q = UNITS[u][k];
        if (q !== p && !seen[q]) {
          seen[q] = true;
          list.push(q);
        }
      }
    }
    PEERS.push(list);
  }

  // ---- small utilities ---------------------------------------------
  function shuffle(arr) {
    for (var n = arr.length - 1; n > 0; n--) {
      var j = (Math.random() * (n + 1)) | 0;
      var t = arr[n];
      arr[n] = arr[j];
      arr[j] = t;
    }
    return arr;
  }

  function clueCount(grid) {
    var n = 0;
    for (var i = 0; i < CELLS; i++) if (grid[i]) n++;
    return n;
  }

  function difficultyName(tier) {
    if (tier <= 1) return "Easy";
    if (tier <= 3) return "Medium";
    if (tier <= 5) return "Hard";
    return "Expert";
  }

  function techniqueName(tier) {
    return tier < 0 || tier >= TECHNIQUE_NAMES.length ? "unknown" : TECHNIQUE_NAMES[tier];
  }

  /** "53..7...." style, '.' or '0' = empty. */
  function loadLine(s) {
    var g = new Uint8Array(CELLS);
    for (var i = 0; i < CELLS; i++) {
      var ch = s.charAt(i);
      g[i] = ch === "." || ch === "0" ? 0 : parseInt(ch, 10);
    }
    return g;
  }

  function toLine(grid) {
    var s = "";
    for (var i = 0; i < CELLS; i++) s += grid[i];
    return s;
  }

  /** All k-sized combinations of `items`, order-independent. */
  function combinations(items, k) {
    var result = [];
    var combo = [];
    (function rec(start) {
      if (combo.length === k) {
        result.push(combo.slice());
        return;
      }
      if (items.length - start < k - combo.length) return;
      for (var i = start; i < items.length; i++) {
        combo.push(items[i]);
        rec(i + 1);
        combo.pop();
      }
    })(0);
    return result;
  }

  // ==================================================================
  // Brute force: solution counting and random filling
  // ==================================================================

  /** Counts solutions, stopping at `limit`. Does not mutate the input. */
  function countSolutions(grid, limit) {
    if (limit === undefined) limit = 2;
    var g = Uint8Array.from(grid);
    var rowM = new Int16Array(9);
    var colM = new Int16Array(9);
    var boxM = new Int16Array(9);
    for (var i = 0; i < CELLS; i++) {
      var v = g[i];
      if (v) {
        var bit = 1 << v;
        rowM[ROW_OF[i]] |= bit;
        colM[COL_OF[i]] |= bit;
        boxM[BOX_OF[i]] |= bit;
      }
    }
    var count = 0;

    function rec() {
      if (count >= limit) return;
      // MRV: the empty cell with the fewest candidates.
      var best = -1;
      var bestMask = 0;
      var bestCount = 10;
      for (var i = 0; i < CELLS; i++) {
        if (g[i]) continue;
        var mask = ALL & ~(rowM[ROW_OF[i]] | colM[COL_OF[i]] | boxM[BOX_OF[i]]);
        var c = POPCOUNT[mask];
        if (c === 0) return; // dead end
        if (c < bestCount) {
          bestCount = c;
          best = i;
          bestMask = mask;
          if (c === 1) break;
        }
      }
      if (best < 0) {
        count++;
        return;
      }
      var rr = ROW_OF[best];
      var cc = COL_OF[best];
      var bb = BOX_OF[best];
      var m = bestMask;
      while (m) {
        var bit = m & -m;
        m ^= bit;
        g[best] = BIT_TO_DIGIT[bit];
        rowM[rr] |= bit;
        colM[cc] |= bit;
        boxM[bb] |= bit;
        rec();
        g[best] = 0;
        rowM[rr] ^= bit;
        colM[cc] ^= bit;
        boxM[bb] ^= bit;
        if (count >= limit) return;
      }
    }

    rec();
    return count;
  }

  /** A random complete solution grid. */
  function fillRandom() {
    var g = new Uint8Array(CELLS);
    var rowM = new Int16Array(9);
    var colM = new Int16Array(9);
    var boxM = new Int16Array(9);

    function rec(i) {
      if (i === CELLS) return true;
      var rr = ROW_OF[i];
      var cc = COL_OF[i];
      var bb = BOX_OF[i];
      var digits = shuffle(maskDigits(ALL & ~(rowM[rr] | colM[cc] | boxM[bb])));
      for (var k = 0; k < digits.length; k++) {
        var n = digits[k];
        var bit = 1 << n;
        g[i] = n;
        rowM[rr] |= bit;
        colM[cc] |= bit;
        boxM[bb] |= bit;
        if (rec(i + 1)) return true;
        g[i] = 0;
        rowM[rr] ^= bit;
        colM[cc] ^= bit;
        boxM[bb] ^= bit;
      }
      return false;
    }

    return rec(0) ? g : null;
  }

  // ==================================================================
  // Logical (human-style) solver
  // ==================================================================

  function Board(grid) {
    this.grid = grid ? Uint8Array.from(grid) : new Uint8Array(CELLS);
    this.cand = new Int16Array(CELLS);
    this.lastMove = null;
  }

  Board.prototype.load = function (grid) {
    this.grid.set(grid);
    this.lastMove = null;
    return this;
  };

  Board.prototype.isSolved = function () {
    for (var i = 0; i < CELLS; i++) if (!this.grid[i]) return false;
    return true;
  };

  /** Seeds candidate masks from row/column/box usage. */
  Board.prototype.initCandidates = function () {
    var rowM = new Int16Array(9);
    var colM = new Int16Array(9);
    var boxM = new Int16Array(9);
    var g = this.grid;
    for (var i = 0; i < CELLS; i++) {
      var v = g[i];
      if (v) {
        var bit = 1 << v;
        rowM[ROW_OF[i]] |= bit;
        colM[COL_OF[i]] |= bit;
        boxM[BOX_OF[i]] |= bit;
      }
    }
    for (var j = 0; j < CELLS; j++) {
      this.cand[j] = g[j] ? 0 : ALL & ~(rowM[ROW_OF[j]] | colM[COL_OF[j]] | boxM[BOX_OF[j]]);
    }
  };

  Board.prototype.place = function (i, n) {
    this.grid[i] = n;
    this.cand[i] = 0;
    var bit = ~(1 << n);
    var peers = PEERS[i];
    for (var k = 0; k < peers.length; k++) this.cand[peers[k]] &= bit;
    this.lastMove = { index: i, value: n };
  };

  /** Erases candidate n from cell i; true if something was actually removed. */
  Board.prototype.eraseCand = function (i, n) {
    var bit = 1 << n;
    if (this.cand[i] & bit) {
      this.cand[i] &= ~bit;
      return true;
    }
    return false;
  };

  Board.prototype.hasContradiction = function () {
    var i, u, n;
    for (i = 0; i < CELLS; i++) if (!this.grid[i] && !this.cand[i]) return true;
    for (u = 0; u < UNITS.length; u++) {
      var unit = UNITS[u];
      for (n = 1; n <= 9; n++) {
        var bit = 1 << n;
        var placed = false;
        var spots = 0;
        for (var k = 0; k < 9; k++) {
          var c = unit[k];
          if (this.grid[c] === n) {
            placed = true;
            break;
          }
          if (!this.grid[c] && this.cand[c] & bit) spots++;
        }
        if (!placed && spots === 0) return true;
      }
    }
    return false;
  };

  // ---- techniques ---------------------------------------------------

  Board.prototype.techNakedSingle = function () {
    for (var i = 0; i < CELLS; i++) {
      if (!this.grid[i] && POPCOUNT[this.cand[i]] === 1) {
        this.place(i, BIT_TO_DIGIT[this.cand[i]]);
        return true;
      }
    }
    return false;
  };

  Board.prototype.techHiddenSingle = function () {
    for (var u = 0; u < UNITS.length; u++) {
      var unit = UNITS[u];
      for (var n = 1; n <= 9; n++) {
        var bit = 1 << n;
        var spot = -1;
        var count = 0;
        var placed = false;
        for (var k = 0; k < 9; k++) {
          var c = unit[k];
          if (this.grid[c] === n) {
            placed = true;
            break;
          }
          if (!this.grid[c] && this.cand[c] & bit) {
            count++;
            spot = c;
            if (count > 1) break;
          }
        }
        if (!placed && count === 1) {
          this.place(spot, n);
          return true;
        }
      }
    }
    return false;
  };

  /** k cells sharing exactly k candidates lock those digits out of the unit. */
  Board.prototype._tryNakedCombo = function (unit, combo, k) {
    var union = 0;
    for (var a = 0; a < combo.length; a++) union |= this.cand[combo[a]];
    if (POPCOUNT[union] !== k) return false;
    var changed = false;
    for (var j = 0; j < 9; j++) {
      var c = unit[j];
      if (this.grid[c] || combo.indexOf(c) !== -1) continue;
      if (this.cand[c] & union) {
        this.cand[c] &= ~union;
        changed = true;
      }
    }
    return changed;
  };

  Board.prototype.techNakedSubset = function (k) {
    for (var u = 0; u < UNITS.length; u++) {
      var unit = UNITS[u];
      var pool = [];
      for (var j = 0; j < 9; j++) {
        var c = unit[j];
        var pc = POPCOUNT[this.cand[c]];
        if (!this.grid[c] && pc > 1 && pc <= k) pool.push(c);
      }
      if (pool.length < k) continue;
      if (k === 2) {
        for (var a = 0; a < pool.length; a++)
          for (var b = a + 1; b < pool.length; b++)
            if (this._tryNakedCombo(unit, [pool[a], pool[b]], 2)) return true;
      } else {
        var combos = combinations(pool, k);
        for (var ci = 0; ci < combos.length; ci++)
          if (this._tryNakedCombo(unit, combos[ci], k)) return true;
      }
    }
    return false;
  };

  Board.prototype.techHiddenPair = function () {
    for (var u = 0; u < UNITS.length; u++) {
      var unit = UNITS[u];
      var pos = {}; // digit -> cells
      for (var j = 0; j < 9; j++) {
        var c = unit[j];
        if (this.grid[c]) continue;
        for (var n = 1; n <= 9; n++)
          if (this.cand[c] & (1 << n)) (pos[n] = pos[n] || []).push(c);
      }
      var digits = Object.keys(pos).map(Number);
      for (var a = 0; a < digits.length; a++) {
        var da = digits[a];
        if (pos[da].length !== 2) continue;
        for (var b = a + 1; b < digits.length; b++) {
          var db = digits[b];
          // Both digits must be confined to exactly the same two cells.
          if (pos[db].length !== 2) continue;
          if (pos[da][0] !== pos[db][0] || pos[da][1] !== pos[db][1]) continue;
          var keep = (1 << da) | (1 << db);
          var changed = false;
          for (var q = 0; q < 2; q++) {
            var cell = pos[da][q];
            if (this.cand[cell] & ~keep) {
              this.cand[cell] &= keep;
              changed = true;
            }
          }
          if (changed) return true;
        }
      }
    }
    return false;
  };

  Board.prototype.techPointing = function () {
    for (var bi = 0; bi < 9; bi++) {
      var box = UNITS[BOX_UNITS_START + bi];
      for (var n = 1; n <= 9; n++) {
        var bit = 1 << n;
        var spots = [];
        var placed = false;
        for (var j = 0; j < 9; j++) {
          var c = box[j];
          if (this.grid[c] === n) {
            placed = true;
            break;
          }
          if (!this.grid[c] && this.cand[c] & bit) spots.push(c);
        }
        if (placed || spots.length < 2 || spots.length > 3) continue;
        var sameRow = true;
        var sameCol = true;
        for (var s = 1; s < spots.length; s++) {
          if (ROW_OF[spots[s]] !== ROW_OF[spots[0]]) sameRow = false;
          if (COL_OF[spots[s]] !== COL_OF[spots[0]]) sameCol = false;
        }
        var changed = false;
        var k, cell;
        if (sameRow) {
          for (k = 0; k < 9; k++) {
            cell = ROW_OF[spots[0]] * 9 + k;
            if (BOX_OF[cell] !== bi && !this.grid[cell] && this.eraseCand(cell, n)) changed = true;
          }
        }
        if (sameCol) {
          for (k = 0; k < 9; k++) {
            cell = k * 9 + COL_OF[spots[0]];
            if (BOX_OF[cell] !== bi && !this.grid[cell] && this.eraseCand(cell, n)) changed = true;
          }
        }
        if (changed) return true;
      }
    }
    return false;
  };

  Board.prototype.techXWing = function () {
    for (var n = 1; n <= 9; n++) {
      var bit = 1 << n;
      var y, x, i, j, changed;

      // Rows: two rows where n sits in the same two columns -> clear n from
      // those columns in every other row.
      var rowHits = [];
      for (y = 0; y < 9; y++) {
        var cols = [];
        for (x = 0; x < 9; x++) {
          var c = y * 9 + x;
          if (!this.grid[c] && this.cand[c] & bit) cols.push(x);
        }
        if (cols.length === 2) rowHits.push([y, cols]);
      }
      for (i = 0; i < rowHits.length; i++) {
        for (j = i + 1; j < rowHits.length; j++) {
          var ca = rowHits[i][1];
          var cb = rowHits[j][1];
          if (ca[0] !== cb[0] || ca[1] !== cb[1]) continue;
          changed = false;
          for (var q = 0; q < 2; q++) {
            for (y = 0; y < 9; y++) {
              if (y === rowHits[i][0] || y === rowHits[j][0]) continue;
              var cell = y * 9 + ca[q];
              if (!this.grid[cell] && this.eraseCand(cell, n)) changed = true;
            }
          }
          if (changed) return true;
        }
      }

      // Columns: mirror image of the above.
      var colHits = [];
      for (x = 0; x < 9; x++) {
        var rows = [];
        for (y = 0; y < 9; y++) {
          var cc = y * 9 + x;
          if (!this.grid[cc] && this.cand[cc] & bit) rows.push(y);
        }
        if (rows.length === 2) colHits.push([x, rows]);
      }
      for (i = 0; i < colHits.length; i++) {
        for (j = i + 1; j < colHits.length; j++) {
          var ra = colHits[i][1];
          var rb = colHits[j][1];
          if (ra[0] !== rb[0] || ra[1] !== rb[1]) continue;
          changed = false;
          for (var w = 0; w < 2; w++) {
            for (x = 0; x < 9; x++) {
              if (x === colHits[i][0] || x === colHits[j][0]) continue;
              var cel = ra[w] * 9 + x;
              if (!this.grid[cel] && this.eraseCand(cel, n)) changed = true;
            }
          }
          if (changed) return true;
        }
      }
    }
    return false;
  };

  /** One pass of the ladder. Returns the tier applied, or -1 if stuck. */
  Board.prototype.applyOneTechnique = function (capTier) {
    if (capTier === undefined) capTier = 99;
    if (this.techNakedSingle()) return 0;
    if (this.techHiddenSingle()) return 1;
    if (capTier < 2) return -1;
    if (this.techNakedSubset(2)) return 2;
    if (capTier < 3) return -1;
    if (this.techHiddenPair()) return 3;
    if (capTier < 4) return -1;
    if (this.techPointing()) return 4;
    if (capTier < 5) return -1;
    if (this.techNakedSubset(3)) return 5;
    if (capTier < 6) return -1;
    if (this.techXWing()) return 6;
    return -1;
  };

  /**
   * Mutates the grid: on success it holds the solution, so copy beforehand.
   * `checkContradictions` costs a full 27-unit scan per iteration and only
   * matters for grids a player typed into.
   */
  Board.prototype.solveLogically = function (capTier, checkContradictions) {
    if (capTier === undefined) capTier = 99;
    if (checkContradictions === undefined) checkContradictions = true;
    this.initCandidates();
    var maxTier = -1;
    for (;;) {
      if (this.isSolved()) return { solved: true, maxTechnique: maxTier };
      if (checkContradictions && this.hasContradiction())
        return { solved: false, maxTechnique: maxTier };
      var tier = this.applyOneTechnique(capTier);
      if (tier < 0) return { solved: false, maxTechnique: maxTier }; // needs guessing
      if (tier > maxTier) maxTier = tier;
    }
  };

  /**
   * The next cell a human could logically fill in the current grid.
   * Returns {x, y, index, value, tier, technique} or null when finished,
   * contradictory (the player erred) or beyond the repertoire.
   */
  Board.prototype.findNextMove = function () {
    this.initCandidates();
    this.lastMove = null;
    for (var step = 0; step < 400; step++) {
      if (this.isSolved() || this.hasContradiction()) return null;
      var tier = this.applyOneTechnique(99);
      if (tier < 0) return null;
      if (this.lastMove) {
        var i = this.lastMove.index;
        return {
          index: i,
          x: COL_OF[i],
          y: ROW_OF[i],
          value: this.lastMove.value,
          tier: tier,
          technique: techniqueName(tier),
        };
      }
    }
    return null;
  };

  // ==================================================================
  // Generation
  // ==================================================================

  var _scratch = new Board();

  function solvableWithin(grid, capTier) {
    _scratch.load(grid);
    return _scratch.solveLogically(capTier, false).solved;
  }

  /**
   * Removes clues while the puzzle stays solvable by the implemented human
   * techniques within `capTier`. Every technique makes only forced deductions,
   * so a grid the logical solver finishes has exactly one solution - no
   * brute-force count is needed in this hot loop.
   */
  function carveHoles(grid, targetClues, capTier) {
    var cells = [];
    for (var i = 0; i < CELLS; i++) cells.push(i);
    shuffle(cells);
    var clues = CELLS;
    for (var k = 0; k < cells.length; k++) {
      if (clues <= targetClues) break;
      var cell = cells[k];
      var backup = grid[cell];
      grid[cell] = 0;
      if (solvableWithin(grid, capTier)) {
        clues--;
      } else {
        grid[cell] = backup; // too hard for this difficulty
      }
    }
  }

  /**
   * `targetClues` is a floor, `capTier` a hard ceiling, `minTier` a preference:
   * attempts grading below it are retried, but the hardest puzzle seen is
   * returned rather than nothing.
   */
  function generate(targetClues, capTier, minTier, attempts) {
    if (targetClues === undefined) targetClues = 24;
    if (capTier === undefined) capTier = 6;
    if (minTier === undefined) minTier = -1;
    if (attempts === undefined) attempts = 6;
    var best = null;
    for (var a = 0; a < attempts; a++) {
      var solution = fillRandom();
      if (!solution) continue;
      var puzzle = Uint8Array.from(solution);
      carveHoles(puzzle, targetClues, capTier);

      var probe = new Board(puzzle);
      var grade = probe.solveLogically(99, false);
      if (!grade.solved) continue;
      var tier = grade.maxTechnique;
      if (tier > capTier) continue;
      if (countSolutions(puzzle, 2) !== 1) continue; // safety net

      var result = {
        puzzle: puzzle,
        solution: solution,
        clues: clueCount(puzzle),
        maxTechnique: tier,
        difficulty: difficultyName(tier),
      };
      if (tier >= minTier) return result;
      if (!best || tier > best.maxTechnique || (tier === best.maxTechnique && result.clues < best.clues))
        best = result;
    }
    return best;
  }

  return {
    SIZE: SIZE,
    CELLS: CELLS,
    UNITS: UNITS,
    PEERS: PEERS,
    ROW_OF: ROW_OF,
    COL_OF: COL_OF,
    BOX_OF: BOX_OF,
    TECHNIQUE_NAMES: TECHNIQUE_NAMES,
    Board: Board,
    generate: generate,
    countSolutions: countSolutions,
    fillRandom: fillRandom,
    clueCount: clueCount,
    difficultyName: difficultyName,
    techniqueName: techniqueName,
    loadLine: loadLine,
    toLine: toLine,
    combinations: combinations,
    maskDigits: maskDigits,
  };
})();

if (typeof module !== "undefined" && module.exports) module.exports = SudokuEngine;
