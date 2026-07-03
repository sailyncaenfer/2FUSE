"use strict";

/* ============================================================
   Speed + Combo Scoring
   Speed (how quickly you chain matches) is the dominant factor.
   Combo length only ever grants a slight bonus on top of that.
   ============================================================ */
const SPEED_BASE_SCORE = 50; // flat score per match before multipliers
const SPEED_REFERENCE_MS = 450; // interval that maps to a neutral 1x speed multiplier
const SPEED_MULT_MIN = 0.6; // slow matches are still worth something
const SPEED_MULT_MAX = 8; // very fast matches are worth a lot more

const COMBO_BONUS_PER_STEP = 0.15; // +10% per combo step beyond the first
const COMBO_BONUS_MAX = 5.0; // combo bonus caps out at +500%

function getSpeedMultiplier(intervalMs) {
  // No prior match to compare against yet: neutral baseline.
  if (intervalMs === null) return 1;
  const raw = SPEED_REFERENCE_MS / intervalMs;
  return Math.min(SPEED_MULT_MAX, Math.max(SPEED_MULT_MIN, raw));
}

function getComboBonus(combo) {
  const steps = Math.max(0, combo - 1);
  return Math.min(COMBO_BONUS_MAX, 1 + steps * COMBO_BONUS_PER_STEP);
}

/* ============================================================
   Constants
   ============================================================ */
const BOARD_SIZE = 4;
const CELL_COUNT = BOARD_SIZE * BOARD_SIZE;
const COLORS = ["red", "green", "blue"];
const ROUND_LENGTH = 60; // seconds
const RESPAWN_DELAY = 3; // seconds (normal, non-green)
const EFFECT_DURATION = 7; // seconds (real-time)
const COMBO_GAP_MAX_MS = 1000; // grace period at combo 0 (no combo yet)
const COMBO_GAP_MIN_MS = 500; // grace period once combo reaches the ramp cap
const COMBO_GAP_RAMP_STEPS = 50; // combo count at which the grace period bottoms out
const COMBO_SLOWDOWN_FACTOR = 3; // combo dies if gap >= 3x recent average
const COMBO_HISTORY_LEN = 5; // "last 5 tile matches"

// Grace period (ms) allowed between matches before the combo breaks,
// based on the combo count going into the next match. Linearly shrinks
// from COMBO_GAP_MAX_MS at combo 0 down to COMBO_GAP_MIN_MS at combo
// COMBO_GAP_RAMP_STEPS, then stays capped at COMBO_GAP_MIN_MS beyond that.
function getComboGapMs(combo) {
  const t = Math.min(COMBO_GAP_RAMP_STEPS, Math.max(0, combo)) / COMBO_GAP_RAMP_STEPS;
  return COMBO_GAP_MAX_MS - t * (COMBO_GAP_MAX_MS - COMBO_GAP_MIN_MS);
}

// tier multipliers for scoring
const TIER_MULTIPLIER = {
  "1": 1,   // 1 + 1 -> 2
  "2": 3,   // 2 + 2 -> star
  "star": 10 // star + star -> effect trigger
};

function randomColor() {
  return COLORS[Math.floor(Math.random() * COLORS.length)];
}

/* ============================================================
   Tile
   ============================================================ */
class Tile {
  constructor(value, color) {
    this.value = value; // "1" | "2" | "star"
    this.color = color; // "red" | "green" | "blue"
  }
  static spawn() {
    // ALL SPAWNS ARE 1's.
    return new Tile("1", randomColor());
  }
}

/* ============================================================
   Game
   ============================================================ */
class Game {
  constructor(dom) {
    this.dom = dom;
    this.settings = { zen: false, stride: false, instant: false, quickRematch: false };
    this.reset();
    this._bindEvents();
    this.isSpawning = false;
    this.dom.readyOverlay = document.getElementById("ready-overlay");
  }

  reset() {
    if (this.cellEls) {
      this.cellEls.forEach(el => el.classList.remove("tilting-active"));
    }
    this.isInitialSpawn = true;

    // 1. Clear the grid entirely
    this.grid = new Array(CELL_COUNT).fill(null);
    this.emptiedAt = new Array(CELL_COUNT).fill(null);
    this.selected = [];
    this.mismatchSelected = [];
    this.score = 0;
    this.timeLeft = ROUND_LENGTH;
    this.running = false; // Game logic is paused
    this._lastFrameTs = null;
    this.tiltPlayed = false;
    this.inputLocked = false;
    clearTimeout(this._mismatchLockTimeout);
    clearTimeout(this._mismatchShakeTimeout);
    clearTimeout(this._timesUpTimeout);
    if (this._spawnCleanupTimeouts) {
      Object.values(this._spawnCleanupTimeouts).forEach((t) => clearTimeout(t));
    }
    this._spawnCleanupTimeouts = {};
    if (this.dom.timesUpOverlay) this.dom.timesUpOverlay.classList.add("hidden");

    // 2. Update the DOM to reflect the empty state
    this._buildBoardDom(); 
    
    // 3. Show the overlay
    this.dom.readyOverlay.classList.remove("hidden");
    
    // 4. Trigger the spawning sequence after 1 second
    setTimeout(() => {
        this.dom.readyOverlay.classList.add("hidden");
        this._animateSpawnSequence();
    }, 1000);
    
    // 5. Reset combos and effects
    this.currentCombo = 0;
    this.maxCombo = 0;
    this.lastMatchTime = null;
    this.matchIntervals = [];
    this._lastMatchInterval = null;
    this.effectTimers = { red: 0, green: 0, blue: 0 };

    this._hideGameOver();
    this.render();
    }

  _buildInitialTiles() {
    // Normally every cell spawns as a random-color "1" tile.
    // With "stride" enabled, force at least 8 of the 16 cells to be green.
    if (!this.settings.stride) {
      return Array.from({ length: CELL_COUNT }, () => Tile.spawn());
    }

    const MIN_GREEN = 8;
    const indices = Array.from({ length: CELL_COUNT }, (_, i) => i);
    // shuffle
    for (let i = indices.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [indices[i], indices[j]] = [indices[j], indices[i]];
    }
    const greenIndices = new Set(indices.slice(0, MIN_GREEN));

    return Array.from({ length: CELL_COUNT }, (_, i) =>
      greenIndices.has(i) ? new Tile("1", "green") : Tile.spawn()
    );
  }

  _flagSpawning(index) {
    const el = this.cellEls[index];
    // The "spawning" class is transient: leaving it on the element forever
    // would let it fight over the shared `animation` CSS property with
    // other transient classes (like mismatch-shake), causing the scale-in
    // animation to unexpectedly replay later. Clean it up once it's done.
    el.classList.add("spawning");
    clearTimeout(this._spawnCleanupTimeouts[index]);
    this._spawnCleanupTimeouts[index] = setTimeout(() => {
      el.classList.remove("spawning");
    }, 220); // matches the 0.2s spawnTile animation, plus a small buffer
  }

  _animateSpawnSequence() {
    const tiles = this._buildInitialTiles();

    if (this.settings.instant) {
      // "instant" spawns everything immediately, no stagger.
      for (let i = 0; i < CELL_COUNT; i++) {
        this.grid[i] = tiles[i];
        this._flagSpawning(i);
      }
      this.render();
      this.isInitialSpawn = false;
      this.running = true;
      return;
    }

    const spawnTime = 1000;
    const delayPerCell = spawnTime / CELL_COUNT;

    for (let i = 0; i < CELL_COUNT; i++) {
      setTimeout(() => {
        this.grid[i] = tiles[i];
        this._flagSpawning(i);
        this.render();
        
        if (i === CELL_COUNT- 1) {
          this.isInitialSpawn = false; // Disable the flag after sequence
          this.running = true;
        }
      }, i * delayPerCell);
    }
  }

  /* ---------------- DOM setup ---------------- */

  _buildBoardDom() {
    this.dom.board.innerHTML = "";
    this.cellEls = [];
    for (let i = 0; i < CELL_COUNT; i++) {
      const el = document.createElement("div");
      el.className = "cell empty";
      el.dataset.index = i;
      el.addEventListener("pointerdown", (e) => {
        e.preventDefault();
        this.handleCellClick(i);
      });
      this.dom.board.appendChild(el);
      this.cellEls.push(el);
    }
  }

  _bindEvents() {
    this.dom.restartBtn.addEventListener("click", () => this.reset());
    this.dom.restartBtnTop.addEventListener("click", () => this.reset());

    this.dom.settingsBtn.addEventListener("click", () => {
      this.dom.settingsOverlay.classList.remove("hidden");
    });
    this.dom.settingsCloseBtn.addEventListener("click", () => {
      this.dom.settingsOverlay.classList.add("hidden");
    });
    this.dom.settingsOverlay.addEventListener("click", (e) => {
      if (e.target === this.dom.settingsOverlay) {
        this.dom.settingsOverlay.classList.add("hidden");
      }
    });

    this.dom.settingZen.addEventListener("change", (e) => {
      this.settings.zen = e.target.checked;
      this.render();
    });
    this.dom.settingStride.addEventListener("change", (e) => {
      this.settings.stride = e.target.checked;
    });
    this.dom.settingInstant.addEventListener("change", (e) => {
      this.settings.instant = e.target.checked;
    });
    this.dom.settingQuickRematch.addEventListener("change", (e) => {
      this.settings.quickRematch = e.target.checked;
      if (this.settings.quickRematch) {
        // If the lock is currently active, lift it immediately.
        clearTimeout(this._mismatchLockTimeout);
        this.inputLocked = false;
        this.mismatchSelected = [];
        this.render();
      }
    });
  }

  /* ---------------- Main loop ---------------- */

  start() {
    requestAnimationFrame((ts) => this._loop(ts));
  }

  _loop(ts) {
    if (this.running) {
      if (this._lastFrameTs === null) this._lastFrameTs = ts;
      const dt = (ts - this._lastFrameTs) / 1000;
      this._lastFrameTs = ts;

      this._tick(dt, ts);
      this.render();
    } else {
      // Not running (pre-spawn, game over, etc). Keep the loop alive so it
      // can resume ticking once running flips back to true, but reset the
      // frame timestamp so we don't get a huge dt on resume.
      this._lastFrameTs = null;
    }

    requestAnimationFrame((nts) => this._loop(nts));
  }

  _tick(dt, ts) {
    if (!this.running) return;

    // 1. Star power-up timers always count down in REAL time.
    for (const color of COLORS) {
      if (this.effectTimers[color] > 0) {
        this.effectTimers[color] = Math.max(0, this.effectTimers[color] - dt);
      }
    }

    // 2. Round timer: scaled by blue effect (x0.8 speed while active).
    // "zen" mode disables the timer entirely.
    if (!this.settings.zen) {
      const blueActive = this.effectTimers.blue > 0;
      const timerSpeed = blueActive ? 0.8 : 1;

      this.timeLeft = Math.max(0, this.timeLeft - dt * timerSpeed);

      // 3. Trigger tilt once when hitting 5 seconds. Actual class
      // application happens in render() so every currently-active tile
      // (and any that spawn afterward) is guaranteed to tilt.
      if (this.timeLeft <= 5 && !this.tiltPlayed) {
        this.tiltPlayed = true;
      }

      if (this.timeLeft <= 0) {
        this.endGame();
        return;
      }
    }

    // 4. Respawns
    // "instant" mode always spawns tiles immediately, same as green's effect.
    const greenActive = this.effectTimers.green > 0 || this.settings.instant;
    for (let i = 0; i < CELL_COUNT; i++) {
      if (this.grid[i] === null) {
        const elapsed = (ts - this.emptiedAt[i]) / 1000;
        if (greenActive || elapsed >= RESPAWN_DELAY) {
          this.grid[i] = Tile.spawn();
          this.emptiedAt[i] = null;
        }
      }
    }
  }

  /* ---------------- Input handling ---------------- */

  handleCellClick(index) {
    if (!this.running) return;
    if (this.inputLocked) return; // mismatch lock in effect
    if (this.grid[index] === null) return; // empty cell, ignore

    // Tap same cell again -> deselect
    if (this.selected.includes(index)) {
      this.selected = this.selected.filter((i) => i !== index);
      this.render();
      return;
    }

    this.selected.push(index);

    if (this.selected.length < 2) {
      this.render();
      return;
    }

    // two cells selected: check match
    const [i, j] = this.selected; // i = first selected, j = latter selected
    const a = this.grid[i];
    const b = this.grid[j];

    const isMatch = a.value === b.value && a.color === b.color;

    if (isMatch) {
      // Match: clear selection immediately so the circle disappears at once.
      this.selected = [];
      this.mismatchSelected = [];
      this._performMerge(i, j);
    } else {
      this._breakCombo();
      // Keep the selection circles visible on both cells for the duration
      // of the mismatch lock, independent of `this.selected`.
      this.mismatchSelected = [i, j];
      this.selected = [];
      this._triggerMismatchShake(i, j);
    }

    this.render();
  }

  /* ---------------- Mismatch feedback ---------------- */

  _triggerMismatchShake(i, j) {
    const SHAKE_DURATION = 400; // ms, matches the CSS animation length
    const LOCK_DURATION = 500; // ms

    const elA = this.cellEls[i];
    const elB = this.cellEls[j];

    // Restart the animation even if triggered again quickly.
    elA.classList.remove("mismatch-shake");
    elB.classList.remove("mismatch-shake");
    void elA.offsetWidth; // force reflow
    elA.classList.add("mismatch-shake");
    elB.classList.add("mismatch-shake");

    clearTimeout(this._mismatchShakeTimeout);
    this._mismatchShakeTimeout = setTimeout(() => {
      elA.classList.remove("mismatch-shake");
      elB.classList.remove("mismatch-shake");
    }, SHAKE_DURATION);

    clearTimeout(this._mismatchLockTimeout);
    this._mismatchLockTimeout = setTimeout(() => {
      this.inputLocked = false;
      this.mismatchSelected = [];
      this.render();
    }, LOCK_DURATION);

    if (!this.settings.quickRematch) {
      this.inputLocked = true;
    }
  }

  /* ---------------- Merge / scoring ---------------- */

  _performMerge(loserIdx, winnerIdx) {
    const now = performance.now();
    const tile = this.grid[loserIdx]; // same value/color as winner tile
    const tier = tile.value; // "1" | "2" | "star"
    const color = tile.color;

    // Determine combo value to use for this match, and update combo state.
    const comboForScoring = this._updateComboOnMatch(now);

    const redActive = this.effectTimers.red > 0;
    const speedMultiplier = getSpeedMultiplier(this._lastMatchInterval);
    const comboBonus = getComboBonus(comboForScoring);
    const tierMult = TIER_MULTIPLIER[tier];
    const redMult = redActive ? 3 : 1;
    const gained = Math.round(SPEED_BASE_SCORE * speedMultiplier * comboBonus * tierMult * redMult);
    if (!this.settings.zen) {
      this.score += gained;
      this._showScorePopup(gained);
    }

    if (tier === "1") {
      this.grid[winnerIdx] = new Tile("2", color);
      this.grid[loserIdx] = null;
      this.emptiedAt[loserIdx] = now;
    } else if (tier === "2") {
      this.grid[winnerIdx] = new Tile("star", color);
      this.grid[loserIdx] = null;
      this.emptiedAt[loserIdx] = now;
    } else {
      // star + star: both cells clear, no upgraded tile. Trigger power-up.
      this.grid[winnerIdx] = null;
      this.grid[loserIdx] = null;
      this.emptiedAt[winnerIdx] = now;
      this.emptiedAt[loserIdx] = now;
      this._triggerStarEffect(color);
    }
  }

  _triggerStarEffect(color) {
    const cur = this.effectTimers[color];
    if (cur > 0) {
      // "additional time is seconds left / 7", capped at 7 total.
      const addition = cur / EFFECT_DURATION;
      this.effectTimers[color] = Math.min(EFFECT_DURATION, cur + addition);
    } else {
      this.effectTimers[color] = EFFECT_DURATION;
    }
  }

  /* ---------------- Combo logic ---------------- */

  _updateComboOnMatch(now) {
    let comboToUse;
    let interval = null;

    if (this.lastMatchTime === null) {
      comboToUse = 1;
    } else {
      interval = now - this.lastMatchTime;
      const avg = this.matchIntervals.length
        ? this.matchIntervals.reduce((a, b) => a + b, 0) / this.matchIntervals.length
        : null;

      // 1. Dynamic grace period: shrinks as the combo grows.
      const brokenByGap = interval >= getComboGapMs(this.currentCombo);
      
      // 2. Dynamic speed check (only applies if we have history)
      const brokenBySlowdown = avg !== null && interval >= COMBO_SLOWDOWN_FACTOR * avg;

      // Combo breaks if EITHER condition is true
      if (brokenByGap || brokenBySlowdown) {
        comboToUse = 1;
        this.matchIntervals = []; 
      } else {
        comboToUse = this.currentCombo + 1;
        this.matchIntervals.push(interval);
        if (this.matchIntervals.length > COMBO_HISTORY_LEN) {
          this.matchIntervals.shift();
        }
      }
    }

    this.currentCombo = comboToUse;
    this.maxCombo = Math.max(this.maxCombo, comboToUse);
    this.lastMatchTime = now;
    // The raw time since the previous match, used to reward fast play
    // regardless of whether it was fast enough to keep the combo alive.
    this._lastMatchInterval = interval;
    return comboToUse;
  }

  _breakCombo() {
    this.currentCombo = 0;
    this.lastMatchTime = null;
    this.matchIntervals = [];

    // Mismatch penalty: reduce remaining power-up time by 50%
    for (const color of COLORS) {
      if (this.effectTimers[color] > 0) {
        // Multiply current time by 0.5 to keep 50%
        this.effectTimers[color] = this.effectTimers[color] * 0.5;
      }
    }
  }

  /* ---------------- Game over ---------------- */

  endGame() {
    this.running = false;

    // Lock out further interaction and clear any pending mismatch state.
    this.selected = [];
    this.mismatchSelected = [];
    this.inputLocked = true;
    clearTimeout(this._mismatchLockTimeout);
    clearTimeout(this._mismatchShakeTimeout);
    this.cellEls.forEach((el) => el.classList.remove("mismatch-shake", "tilting-active"));

    // Remove all tiles from the board so no matches can be made while
    // the "TIME'S UP" message is shown.
    this.grid = new Array(CELL_COUNT).fill(null);
    this.emptiedAt = new Array(CELL_COUNT).fill(null);
    this.render();

    this.dom.timesUpOverlay.classList.remove("hidden");

    clearTimeout(this._timesUpTimeout);
    this._timesUpTimeout = setTimeout(() => {
      this.dom.timesUpOverlay.classList.add("hidden");
      this.dom.finalScore.textContent = Math.floor(this.score);
      this.dom.finalCombo.textContent = this.maxCombo;
      this.dom.gameOverOverlay.classList.remove("hidden");
    }, 2000);
  }

  _hideGameOver() {
    this.dom.gameOverOverlay.classList.add("hidden");
  }

  /* ---------------- Rendering ---------------- */

  render() {
    for (let i = 0; i < CELL_COUNT; i++) {
      const el = this.cellEls[i];
      const tile = this.grid[i];

      el.classList.remove("tile-red", "tile-green", "tile-blue", "star", "selected", "empty", "respawning");

      if (tile === null) {
        el.classList.add("empty");
        el.classList.remove("tilting-active");
      
        // Add the condition: Only show respawn animation if it's NOT the initial spawn
        if (this.effectTimers.green <= 0 && !this.isInitialSpawn) {
          el.classList.add("respawning");
        }
      
        el.textContent = "";
        continue;
      }

      el.classList.add(`tile-${tile.color}`);
      if (tile.value === "star") {
        el.classList.add("star");
        el.innerHTML = '<span class="star-icon">&#9733;</span>';
      } else {
        el.textContent = tile.value;
      }

      // Once triggered, every currently-active tile tilts — including ones
      // that spawn after the trigger point (e.g. respawns near time's up).
      if (this.tiltPlayed) {
        el.classList.add("tilting-active");
      } else {
        el.classList.remove("tilting-active");
      }

      if (this.selected.includes(i) || this.mismatchSelected.includes(i)) {
        el.classList.add("selected");
      }
    }

    // HUD
    this.dom.scoreEl.textContent = Math.floor(this.score);
    this.dom.timeEl.textContent = this.settings.zen ? "\u221E" : this.timeLeft.toFixed(2);
    this.dom.comboEl.textContent = this.currentCombo;

    // effect badges
    for (const color of COLORS) {
      const remaining = this.effectTimers[color];
      const badge = this.dom.effectBadges[color];
      const fill = this.dom.effectFills[color];
      if (remaining > 0) {
        badge.classList.add("active");
        fill.style.width = `${(remaining / EFFECT_DURATION) * 100}%`;
      } else {
        badge.classList.remove("active");
        fill.style.width = "0%";
      }
    }
  }

  _showScorePopup(amount) {
    const popup = this.dom.scorePopup;
    popup.textContent = `+${amount}`;
    popup.classList.remove("hidden");
    // restart the CSS transition
    popup.classList.remove("show");
    void popup.offsetWidth; // force reflow
    popup.classList.add("show");
    clearTimeout(this._popupTimeout);
    this._popupTimeout = setTimeout(() => {
      popup.classList.remove("show");
    }, 400);
  }
}

/* ============================================================
   Bootstrap
   ============================================================ */
window.addEventListener("DOMContentLoaded", () => {
  const dom = {
    board: document.getElementById("board"),
    scoreEl: document.getElementById("score"),
    timeEl: document.getElementById("time"),
    comboEl: document.getElementById("combo"),
    scorePopup: document.getElementById("last-score-popup"),
    gameOverOverlay: document.getElementById("game-over-overlay"),
    finalScore: document.getElementById("final-score"),
    finalCombo: document.getElementById("final-combo"),
    restartBtn: document.getElementById("restart-btn"),
    restartBtnTop: document.getElementById("restart-btn-top"),
    readyOverlay: document.getElementById("ready-overlay"),
    timesUpOverlay: document.getElementById("timesup-overlay"),
    settingsBtn: document.getElementById("settings-btn"),
    settingsOverlay: document.getElementById("settings-overlay"),
    settingsCloseBtn: document.getElementById("settings-close-btn"),
    settingZen: document.getElementById("setting-zen"),
    settingStride: document.getElementById("setting-stride"),
    settingInstant: document.getElementById("setting-instant"),
    settingQuickRematch: document.getElementById("setting-quick-rematch"),
    effectBadges: {
      red: document.getElementById("effect-red"),
      green: document.getElementById("effect-green"),
      blue: document.getElementById("effect-blue"),
    },
    effectFills: {
      red: document.getElementById("effect-fill-red"),
      green: document.getElementById("effect-fill-green"),
      blue: document.getElementById("effect-fill-blue"),
    },
  };

  const game = new Game(dom);
  game.start();
});
