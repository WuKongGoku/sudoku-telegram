/*
 * Sudoku Mini App - UI, input and Telegram integration.
 * Game rules and generation live in engine.js; this file only drives them.
 *
 * Runs fine as a plain web page too: every Telegram call is feature-detected,
 * so opening index.html directly gives the same game with a fallback palette
 * and localStorage instead of CloudStorage.
 */
(function () {
  "use strict";

  var E = SudokuEngine;
  var tg = (window.Telegram && window.Telegram.WebApp) || null;
  var inTelegram = !!(tg && tg.initData !== undefined && tg.platform && tg.platform !== "unknown");

  // target clues is a floor; cap/min bound the hardest technique required.
  var DIFFICULTIES = [
    { name: "Easy",   clues: 34, cap: 1, min: -1, tries: 4 },
    { name: "Medium", clues: 28, cap: 3, min: 2,  tries: 30 },
    { name: "Hard",   clues: 24, cap: 5, min: 4,  tries: 40 },
    { name: "Expert", clues: 20, cap: 6, min: 5,  tries: 80 }
  ];

  var SAVE_KEY = "game";
  var SAVE_VERSION = 1;

  // ---- state -------------------------------------------------------
  var puzzle = new Uint8Array(81);
  var solution = new Uint8Array(81);
  var player = new Uint8Array(81);
  var notes = new Uint16Array(81); // bit d set = pencil mark d
  var hinted = {};
  var wrong = {};
  var conflicts = {};
  var undoStack = [];
  var selected = 40;
  var notesMode = false;
  var mistakes = 0;
  var hintsUsed = 0;
  var elapsed = 0;
  var running = false;
  var solved = false;
  var generating = false;
  var difficultyIndex = 0;
  var puzzleLabel = "";
  var colors = {};

  // ---- elements ----------------------------------------------------
  var $ = function (id) { return document.getElementById(id); };
  var canvas = $("board");
  var ctx = canvas.getContext("2d");
  var elInfo = $("info"), elTimer = $("timer"), elStatus = $("status");
  var elOverlay = $("overlay"), elOverlayTitle = $("overlay-title"), elOverlayText = $("overlay-text");
  var elOverlayButton = $("overlay-button"), elNotes = $("btn-notes"), elDifficulty = $("difficulty");
  var keys = [].slice.call(document.querySelectorAll(".key"));

  // ==================================================================
  // Theme - derive a full board palette from Telegram's theme params
  // ==================================================================

  function hexToRgb(h) {
    if (!h) return null;
    h = String(h).replace("#", "");
    if (h.length === 3) h = h[0] + h[0] + h[1] + h[1] + h[2] + h[2];
    if (h.length !== 6 || /[^0-9a-f]/i.test(h)) return null;
    return [parseInt(h.slice(0, 2), 16), parseInt(h.slice(2, 4), 16), parseInt(h.slice(4, 6), 16)];
  }

  function rgbToHex(c) {
    return "#" + c.map(function (v) {
      return Math.max(0, Math.min(255, Math.round(v))).toString(16).padStart(2, "0");
    }).join("");
  }

  /** Blend b into a by t (0..1). */
  function mix(a, b, t) {
    var ca = hexToRgb(a), cb = hexToRgb(b);
    if (!ca || !cb) return a;
    return rgbToHex([0, 1, 2].map(function (i) { return ca[i] + (cb[i] - ca[i]) * t; }));
  }

  function applyTheme() {
    var tp = (tg && tg.themeParams) || {};
    var dark = tg && tg.colorScheme
      ? tg.colorScheme === "dark"
      : !window.matchMedia || window.matchMedia("(prefers-color-scheme: dark)").matches;

    var bg = hexToRgb(tp.bg_color) ? tp.bg_color : (dark ? "#14171f" : "#f2f4f8");
    var text = hexToRgb(tp.text_color) ? tp.text_color : (dark ? "#e9eef8" : "#0f1420");
    var dim = hexToRgb(tp.hint_color) ? tp.hint_color : (dark ? "#93a0b8" : "#707a8c");
    var accent = hexToRgb(tp.button_color) ? tp.button_color
      : (hexToRgb(tp.link_color) ? tp.link_color : "#3a8fe0");
    var cell = hexToRgb(tp.secondary_bg_color) ? tp.secondary_bg_color : mix(bg, text, 0.07);

    colors = {
      bg: bg,
      panel: cell,
      cell: cell,
      cellPeer: mix(cell, accent, 0.16),
      cellSame: mix(cell, accent, 0.32),
      cellSel: mix(cell, accent, 0.62),
      cellErr: mix(cell, "#ff3b30", dark ? 0.38 : 0.28),
      lineThin: mix(bg, text, 0.2),
      lineThick: mix(bg, text, 0.5),
      text: text,
      dim: dim,
      accent: accent,
      given: text,
      user: accent,
      hint: mix(cell, "#2ecc71", 0.85),
      error: mix(cell, "#ff3b30", 0.9),
      note: dim
    };

    var root = document.documentElement.style;
    root.setProperty("--bg", colors.bg);
    root.setProperty("--panel", colors.panel);
    root.setProperty("--cell", colors.cell);
    root.setProperty("--line-thin", colors.lineThin);
    root.setProperty("--line-thick", colors.lineThick);
    root.setProperty("--text", colors.text);
    root.setProperty("--dim", colors.dim);
    root.setProperty("--accent", colors.accent);
    root.setProperty("--cell-peer", colors.cellPeer);
    root.setProperty("--cell-same", colors.cellSame);
    root.setProperty("--cell-sel", colors.cellSel);
    root.setProperty("--cell-err", colors.cellErr);
    draw();
  }

  // ==================================================================
  // Telegram helpers (all optional)
  // ==================================================================

  function haptic(kind) {
    if (!tg || !tg.HapticFeedback) return;
    try {
      if (kind === "error") tg.HapticFeedback.notificationOccurred("error");
      else if (kind === "success") tg.HapticFeedback.notificationOccurred("success");
      else tg.HapticFeedback.impactOccurred(kind || "light");
    } catch (e) { /* older clients */ }
  }

  function storageSet(key, value) {
    if (tg && tg.CloudStorage && tg.CloudStorage.setItem) {
      try { tg.CloudStorage.setItem(key, value, function () {}); return; } catch (e) { /* fall through */ }
    }
    try { localStorage.setItem("sudoku:" + key, value); } catch (e) { /* private mode */ }
  }

  function storageGet(key, cb) {
    if (tg && tg.CloudStorage && tg.CloudStorage.getItem) {
      try {
        tg.CloudStorage.getItem(key, function (err, val) { cb(err ? null : val || null); });
        return;
      } catch (e) { /* fall through */ }
    }
    var v = null;
    try { v = localStorage.getItem("sudoku:" + key); } catch (e) { /* private mode */ }
    cb(v);
  }

  // ==================================================================
  // Persistence
  // ==================================================================

  function saveState() {
    if (generating) return;
    var data = {
      v: SAVE_VERSION,
      p: E.toLine(puzzle),
      s: E.toLine(solution),
      u: E.toLine(player),
      n: Array.prototype.slice.call(notes),
      hi: Object.keys(hinted).map(Number),
      d: difficultyIndex,
      l: puzzleLabel,
      t: Math.round(elapsed),
      m: mistakes,
      h: hintsUsed,
      done: solved
    };
    storageSet(SAVE_KEY, JSON.stringify(data));
  }

  function restoreState(raw) {
    if (!raw) return false;
    try {
      var d = JSON.parse(raw);
      if (!d || d.v !== SAVE_VERSION || d.done) return false;
      if (!d.p || d.p.length !== 81 || !d.s || d.s.length !== 81) return false;
      puzzle = E.loadLine(d.p);
      solution = E.loadLine(d.s);
      player = E.loadLine(d.u);
      notes = Uint16Array.from(d.n && d.n.length === 81 ? d.n : new Uint16Array(81));
      hinted = {};
      (d.hi || []).forEach(function (i) { hinted[i] = true; });
      wrong = {};
      undoStack = [];
      difficultyIndex = d.d || 0;
      puzzleLabel = d.l || "";
      elapsed = d.t || 0;
      mistakes = d.m || 0;
      hintsUsed = d.h || 0;
      solved = false;
      running = true;
      selected = 40;
      elDifficulty.value = String(difficultyIndex);
      return true;
    } catch (e) {
      return false;
    }
  }

  // ==================================================================
  // Game flow
  // ==================================================================

  function resetState() {
    puzzle = new Uint8Array(81);
    solution = new Uint8Array(81);
    player = new Uint8Array(81);
    notes = new Uint16Array(81);
    hinted = {};
    wrong = {};
    conflicts = {};
    undoStack = [];
    mistakes = 0;
    hintsUsed = 0;
    elapsed = 0;
    running = false;
    solved = false;
  }

  function newGame() {
    if (generating) return;
    generating = true;
    showOverlay("Generating…", "Carving a " + DIFFICULTIES[difficultyIndex].name +
      " puzzle with a unique solution.", false);
    // Let the overlay paint before the (synchronous) generator blocks.
    requestAnimationFrame(function () {
      requestAnimationFrame(function () {
        var d = DIFFICULTIES[difficultyIndex];
        var res = E.generate(d.clues, d.cap, d.min, d.tries) || E.generate(34, 6, -1, 12);
        generating = false;
        if (!res) {
          showOverlay("Hmm", "Could not build a puzzle. Try again.", true);
          return;
        }
        resetState();
        puzzle = res.puzzle;
        solution = res.solution;
        player = Uint8Array.from(res.puzzle);
        puzzleLabel = d.name + " · " + res.clues + " clues · hardest step: " +
          E.techniqueName(res.maxTechnique);
        selected = 40;
        running = true;
        hideOverlay();
        setStatus(inTelegram ? "Tap a cell, then a number below." : "Click a cell, then type 1-9.");
        refresh();
        saveState();
      });
    });
  }

  function showOverlay(title, text, showButton) {
    elOverlayTitle.textContent = title;
    elOverlayText.textContent = text;
    elOverlayButton.hidden = !showButton;
    elOverlay.hidden = false;
  }

  function hideOverlay() { elOverlay.hidden = true; }

  // ==================================================================
  // Moves
  // ==================================================================

  function pushUndo(i) {
    undoStack.push({ i: i, value: player[i], notes: notes[i], mistakes: mistakes, hinted: !!hinted[i] });
    if (undoStack.length > 500) undoStack.shift();
  }

  function clearPeerNotes(i, n) {
    var bit = ~(1 << n);
    var peers = E.PEERS[i];
    for (var k = 0; k < peers.length; k++) notes[peers[k]] &= bit;
  }

  /** True if the digit in cell i repeats in its row, column or box. */
  function peersConflict(i) {
    var v = player[i];
    if (!v) return false;
    var peers = E.PEERS[i];
    for (var k = 0; k < peers.length; k++) if (player[peers[k]] === v) return true;
    return false;
  }

  function conflictMap() {
    var out = {};
    for (var i = 0; i < 81; i++) if (player[i] && peersConflict(i)) out[i] = true;
    return out;
  }

  function enterDigit(n) {
    if (solved || generating || selected < 0) return;
    var i = selected;
    if (puzzle[i]) { setStatus("That cell is a given clue."); haptic("rigid"); return; }
    pushUndo(i);
    wrong = {};

    if (notesMode && n !== 0) {
      player[i] = 0;
      notes[i] ^= 1 << n;
      haptic("light");
    } else if (n === 0) {
      player[i] = 0;
      notes[i] = 0;
      delete hinted[i];
      haptic("light");
    } else if (player[i] === n) {
      player[i] = 0; // tapping the same digit clears it
      delete hinted[i];
      haptic("light");
    } else {
      player[i] = n;
      notes[i] = 0;
      delete hinted[i];
      clearPeerNotes(i, n);
      if (peersConflict(i)) {
        mistakes++;
        setStatus("That breaks a row, column or box.");
        haptic("error");
      } else {
        setStatus("");
        haptic("light");
      }
    }
    refresh();
    saveState();
    checkWin();
  }

  function undo() {
    if (solved || !undoStack.length) return;
    var s = undoStack.pop();
    player[s.i] = s.value;
    notes[s.i] = s.notes;
    mistakes = s.mistakes;
    if (s.hinted) hinted[s.i] = true; else delete hinted[s.i];
    wrong = {};
    selected = s.i;
    setStatus("Undone.");
    haptic("light");
    refresh();
    saveState();
  }

  function checkBoard() {
    if (solved) return;
    wrong = {};
    var filled = 0;
    for (var i = 0; i < 81; i++) {
      if (!player[i]) continue;
      filled++;
      if (player[i] !== solution[i]) wrong[i] = true;
    }
    var bad = Object.keys(wrong).length;
    setStatus(bad === 0
      ? "All " + filled + " filled cells are correct."
      : bad + " wrong cell" + (bad === 1 ? "" : "s") + " highlighted.");
    haptic(bad === 0 ? "success" : "error");
    refresh();
  }

  function hint() {
    if (solved || generating) return;
    // A wrong entry poisons the logic, so flag that first.
    for (var i = 0; i < 81; i++) {
      if (player[i] && player[i] !== solution[i]) {
        checkBoard();
        setStatus("Fix the highlighted mistakes first.");
        return;
      }
    }
    var move = new E.Board(player).findNextMove();
    if (!move) { setStatus("No further logical step found."); return; }

    pushUndo(move.index);
    player[move.index] = move.value;
    notes[move.index] = 0;
    hinted[move.index] = true;
    hintsUsed++;
    selected = move.index;
    clearPeerNotes(move.index, move.value);
    wrong = {};
    setStatus(move.technique + ": r" + (move.y + 1) + "c" + (move.x + 1) + " must be " + move.value + ".");
    haptic("medium");
    refresh();
    saveState();
    checkWin();
  }

  function checkWin() {
    for (var i = 0; i < 81; i++) if (player[i] !== solution[i]) return;
    solved = true;
    running = false;
    var msg = "Time " + formatTime(elapsed) + " · " + plural(mistakes, "mistake") +
      " · " + plural(hintsUsed, "hint");
    showOverlay("Solved!", msg, true);
    setStatus(msg);
    haptic("success");
    saveState();
  }

  function plural(n, word) { return n + " " + word + (n === 1 ? "" : "s"); }

  function formatTime(sec) {
    var t = Math.floor(sec);
    return String(Math.floor(t / 60)).padStart(2, "0") + ":" + String(t % 60).padStart(2, "0");
  }

  // ==================================================================
  // Rendering
  // ==================================================================

  var cellSize = 0, originX = 0, originY = 0, boardPx = 0;

  function layout() {
    var wrap = $("boardwrap");
    var avail = Math.min(wrap.clientWidth, wrap.clientHeight);
    if (avail <= 0) return;
    boardPx = Math.floor(avail);
    cellSize = Math.floor(boardPx / 9);
    boardPx = cellSize * 9;
    var dpr = window.devicePixelRatio || 1;
    canvas.style.width = boardPx + "px";
    canvas.style.height = boardPx + "px";
    canvas.width = Math.round(boardPx * dpr);
    canvas.height = Math.round(boardPx * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    originX = 0;
    originY = 0;
    draw();
  }

  function draw() {
    if (!cellSize || !colors.bg) return;
    ctx.clearRect(0, 0, boardPx, boardPx);
    ctx.fillStyle = colors.panel;
    ctx.fillRect(0, 0, boardPx, boardPx);

    var selValue = selected >= 0 ? player[selected] : 0;
    var selRow = selected >= 0 ? E.ROW_OF[selected] : -1;
    var selCol = selected >= 0 ? E.COL_OF[selected] : -1;
    var selBox = selected >= 0 ? E.BOX_OF[selected] : -1;
    var i, x, y;

    // cell backgrounds
    for (i = 0; i < 81; i++) {
      x = E.COL_OF[i];
      y = E.ROW_OF[i];
      var col = colors.cell;
      if (selected >= 0 && (x === selCol || y === selRow || E.BOX_OF[i] === selBox)) col = colors.cellPeer;
      if (selValue && player[i] === selValue) col = colors.cellSame;
      if (conflicts[i] || wrong[i]) col = colors.cellErr;
      if (i === selected) col = colors.cellSel;
      ctx.fillStyle = col;
      ctx.fillRect(x * cellSize, y * cellSize, cellSize, cellSize);
    }

    // grid lines
    for (i = 0; i <= 9; i++) {
      var thick = i % 3 === 0;
      ctx.strokeStyle = thick ? colors.lineThick : colors.lineThin;
      ctx.lineWidth = thick ? 2 : 1;
      var p = i * cellSize + (thick ? 0 : 0.5);
      ctx.beginPath();
      ctx.moveTo(p, 0); ctx.lineTo(p, boardPx);
      ctx.moveTo(0, p); ctx.lineTo(boardPx, p);
      ctx.stroke();
    }

    // digits and pencil marks
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    var digitFont = Math.round(cellSize * 0.62);
    var noteFont = Math.round(cellSize * 0.26);
    for (i = 0; i < 81; i++) {
      x = E.COL_OF[i];
      y = E.ROW_OF[i];
      var cx = x * cellSize + cellSize / 2;
      var cy = y * cellSize + cellSize / 2;
      if (player[i]) {
        var c = colors.user;
        if (puzzle[i]) c = colors.given;
        else if (hinted[i]) c = colors.hint;
        if (conflicts[i] || wrong[i]) c = colors.error;
        ctx.fillStyle = c;
        ctx.font = (puzzle[i] ? "600 " : "400 ") + digitFont + "px system-ui, sans-serif";
        ctx.fillText(String(player[i]), cx, cy + cellSize * 0.02);
      } else if (notes[i]) {
        ctx.fillStyle = colors.note;
        ctx.font = noteFont + "px system-ui, sans-serif";
        for (var n = 1; n <= 9; n++) {
          if (!(notes[i] & (1 << n))) continue;
          var idx = n - 1;
          ctx.fillText(String(n),
            x * cellSize + ((idx % 3) + 0.5) * (cellSize / 3),
            y * cellSize + (Math.floor(idx / 3) + 0.5) * (cellSize / 3));
        }
      }
    }

    // selection outline + outer frame
    if (selected >= 0) {
      ctx.strokeStyle = colors.accent;
      ctx.lineWidth = 2;
      ctx.strokeRect(E.COL_OF[selected] * cellSize + 1, E.ROW_OF[selected] * cellSize + 1,
        cellSize - 2, cellSize - 2);
    }
    ctx.strokeStyle = colors.lineThick;
    ctx.lineWidth = 2;
    ctx.strokeRect(1, 1, boardPx - 2, boardPx - 2);
  }

  function refresh() {
    conflicts = conflictMap();
    elInfo.textContent = puzzleLabel;
    elTimer.textContent = formatTime(elapsed);
    var counts = {};
    for (var i = 0; i < 81; i++) if (player[i]) counts[player[i]] = (counts[player[i]] || 0) + 1;
    keys.forEach(function (b) {
      b.classList.toggle("done", (counts[+b.dataset.digit] || 0) >= 9);
    });
    draw();
  }

  function setStatus(text) {
    var extra = "Mistakes: " + mistakes;
    elStatus.textContent = text ? text + "  ·  " + extra : extra;
  }

  // ==================================================================
  // Input
  // ==================================================================

  canvas.addEventListener("pointerdown", function (ev) {
    if (solved || generating) return;
    var rect = canvas.getBoundingClientRect();
    var lx = ev.clientX - rect.left;
    var ly = ev.clientY - rect.top;
    if (lx < 0 || ly < 0 || lx >= boardPx || ly >= boardPx) return;
    selected = Math.floor(ly / cellSize) * 9 + Math.floor(lx / cellSize);
    haptic("light");
    refresh();
    ev.preventDefault();
  });

  keys.forEach(function (b) {
    b.addEventListener("click", function () { enterDigit(+b.dataset.digit); });
  });
  $("btn-erase").addEventListener("click", function () { enterDigit(0); });
  $("btn-undo").addEventListener("click", undo);
  $("btn-hint").addEventListener("click", hint);
  $("btn-check").addEventListener("click", checkBoard);
  $("btn-new").addEventListener("click", newGame);
  elOverlayButton.addEventListener("click", newGame);
  elNotes.addEventListener("click", toggleNotes);
  elDifficulty.addEventListener("change", function () {
    difficultyIndex = +elDifficulty.value;
    newGame();
  });

  function toggleNotes() {
    notesMode = !notesMode;
    elNotes.classList.toggle("on", notesMode);
    elNotes.querySelector("small").textContent = notesMode ? "on" : "off";
    haptic("light");
  }

  document.addEventListener("keydown", function (ev) {
    if (generating) return;
    var k = ev.key;
    if (k >= "1" && k <= "9") enterDigit(+k);
    else if (k === "0" || k === "Backspace" || k === "Delete") enterDigit(0);
    else if (k === "ArrowLeft") moveSel(-1, 0);
    else if (k === "ArrowRight") moveSel(1, 0);
    else if (k === "ArrowUp") moveSel(0, -1);
    else if (k === "ArrowDown") moveSel(0, 1);
    else if (k === "n" || k === "N") toggleNotes();
    else if (k === "h" || k === "H") hint();
    else if (k === "c" || k === "C") checkBoard();
    else if (k === "z" || k === "Z") undo();
    else return;
    ev.preventDefault();
  });

  function moveSel(dx, dy) {
    if (selected < 0) { selected = 40; }
    else {
      var x = Math.min(8, Math.max(0, E.COL_OF[selected] + dx));
      var y = Math.min(8, Math.max(0, E.ROW_OF[selected] + dy));
      selected = y * 9 + x;
    }
    refresh();
  }

  // ==================================================================
  // Boot
  // ==================================================================

  setInterval(function () {
    if (running && !solved) {
      elapsed++;
      elTimer.textContent = formatTime(elapsed);
      if (elapsed % 10 === 0) saveState();
    }
  }, 1000);

  window.addEventListener("resize", layout);
  document.addEventListener("visibilitychange", function () { if (document.hidden) saveState(); });
  window.addEventListener("pagehide", saveState);

  if (tg) {
    try { tg.ready(); } catch (e) {}
    try { tg.expand(); } catch (e) {}
    // Stop a downward swipe on the board from dismissing the Mini App.
    try { if (tg.disableVerticalSwipes) tg.disableVerticalSwipes(); } catch (e) {}
    try { if (tg.setHeaderColor) tg.setHeaderColor("bg_color"); } catch (e) {}
    try { tg.onEvent("themeChanged", applyTheme); } catch (e) {}
    try { tg.onEvent("viewportChanged", layout); } catch (e) {}
  }
  if (window.matchMedia) {
    try { window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", applyTheme); }
    catch (e) { /* Safari < 14 */ }
  }

  applyTheme();
  layout();
  setStatus("");

  storageGet(SAVE_KEY, function (raw) {
    if (restoreState(raw)) {
      hideOverlay();
      setStatus("Resumed your saved game.");
      layout();
      refresh();
    } else {
      newGame();
    }
  });
})();
