/* =========================================================
   3D 贪吃蛇 · 小小探险
   three.js r158 / 单文件 / 无外部资源
   ========================================================= */
(function () {
  'use strict';

  /* ---------------- 基础工具 ---------------- */
  var TAU = Math.PI * 2, DEG = Math.PI / 180;
  function clamp(v, a, b) { return v < a ? a : (v > b ? b : v); }
  function lerp(a, b, t) { return a + (b - a) * t; }
  function rand(a, b) { return a + Math.random() * (b - a); }
  function ri(a, b) { return Math.floor(a + Math.random() * (b - a + 1)); }

  /* ---------------- 配置 ---------------- */
  var MS = 35;                      // 网格边长（所有地图共用同一包围盒 35×35 = 1225 格）
  var CELL = 1;
  var MC = (MS - 1) / 2;            // 17：中心格
  var WALL = MS * 0.5;              // 17.5：包围盒边缘

  /* 相机：场地变大时不是把画面越缩越远，而是视野跟着蛇头走、格子始终看得清 */
  var TARGET_CELL_PX = 19;          // 一个格子希望占多少屏幕像素
  var VIEW_MIN = 13, VIEW_MAX = 37; // 画面窄边最少 / 最多能看到多少格（屏幕够大时正好装下整张地图）
  var CAM_ELEV = 46 * DEG;          // 俯角

  var DIFFS = {
    easy:   { step: 0.300, min: 0.190 },
    normal: { step: 0.235, min: 0.140 },
    hard:   { step: 0.180, min: 0.108 }
  };
  var ACCEL_STEP = 0.0055;
  var MAX_SEG = MS * MS;

  var GOLD_EVERY = 4;               // 每吃这么多口，下一个是金苹果
  var GOLD_SCORE = 30;
  var BASE_SCORE = 10;
  /* 分数到这些值时，地图上会多来一只怪兽（easy 不来） */
  var REINFORCE_AT = { easy: 0, normal: 90, hard: 60 };
  /* 开局保护：前几个 tick 内怪兽还在「巡逻」，不会把蛇撞死。
     孩子刚开局还在找方向，不该被这么冤枉地结束。 */
  var GUARD_TICKS = 7;

  /* =========================================================
     地图系统：17×17 包围盒内的任意形状
     cells[z*MS+x] === 1 表示可通行
     ========================================================= */
  function makeCells(fn) {
    var a = new Uint8Array(MS * MS);
    for (var z = 0; z < MS; z++) {
      for (var x = 0; x < MS; x++) {
        a[z * MS + x] = fn(x, z) ? 1 : 0;
      }
    }
    return a;
  }

  function cellFree(cells, x, z) {
    if (x < 0 || x >= MS || z < 0 || z >= MS) return false;
    return cells[z * MS + x] === 1;
  }

  /* 离中心最近的可通行格 */
  function centerFree(cells) {
    var best = null, bestD = 1e9;
    for (var z = 0; z < MS; z++) {
      for (var x = 0; x < MS; x++) {
        if (!cellFree(cells, x, z)) continue;
        var d = Math.abs(x - MC) + Math.abs(z - MC);
        if (d < bestD) { bestD = d; best = { x: x, z: z }; }
      }
    }
    return best;
  }

  /* 从起点 BFS，剔除不可达的孤岛，保证食物不会生成在进不去的区域 */
  function pruneIslands(cells, sx, sz) {
    if (!cellFree(cells, sx, sz)) return cells;
    var seen = new Uint8Array(MS * MS);
    var stack = [sz * MS + sx];
    seen[sz * MS + sx] = 1;
    var NB = [[1, 0], [-1, 0], [0, 1], [0, -1]];
    while (stack.length) {
      var k = stack.pop();
      var x = k % MS, z = (k - x) / MS;
      for (var i = 0; i < 4; i++) {
        var nx = x + NB[i][0], nz = z + NB[i][1];
        if (!cellFree(cells, nx, nz)) continue;
        var nk = nz * MS + nx;
        if (seen[nk]) continue;
        seen[nk] = 1;
        stack.push(nk);
      }
    }
    for (var j = 0; j < cells.length; j++) if (!seen[j]) cells[j] = 0;
    return cells;
  }

  /* 在形状内找一段 3 格直线作为出生位，返回蛇身（头在前）与朝向 */
  var DIR4 = [{ x: 1, z: 0 }, { x: -1, z: 0 }, { x: 0, z: 1 }, { x: 0, z: -1 }];

  /* 从某格沿某方向连续可走的格数（不含起点） */
  function runway(cells, x, z, d, max) {
    var n = 0;
    while (n < max && cellFree(cells, x + d.x * (n + 1), z + d.z * (n + 1))) n++;
    return n;
  }

  /* 选出生位：头要尽量居中，但前方要有足够跑道，身后要放得下 2 节身体
     —— 否则一开局 1 秒内就撞墙，小朋友来不及反应。 */
  function findSpawn(cells) {
    var best = null, bestScore = -1e9;
    var BEST_RUN = 6;

    for (var z = 0; z < MS; z++) {
      for (var x = 0; x < MS; x++) {
        if (!cellFree(cells, x, z)) continue;
        for (var i = 0; i < 4; i++) {
          var d = DIR4[i];
          var back = runway(cells, x, z, { x: -d.x, z: -d.z }, 2);
          if (back < 2) continue;                       /* 身体放不下就换方向 */
          var ahead = runway(cells, x, z, d, BEST_RUN + 4);
          if (ahead < 2) continue;
          var centerness = 1 - (Math.abs(x - MC) + Math.abs(z - MC)) / (MS * 2);
          /* 跑道权重远高于居中，跑道相同时才看谁更靠中间 */
          var score = Math.min(ahead, BEST_RUN) * 10 + centerness * 6;
          if (score > bestScore) {
            bestScore = score;
            best = { x: x, z: z, dir: d };
          }
        }
      }
    }

    if (best) {
      return {
        cells: [
          { x: best.x, z: best.z },
          { x: best.x - best.dir.x, z: best.z - best.dir.z },
          { x: best.x - best.dir.x * 2, z: best.z - best.dir.z * 2 }
        ],
        dir: { x: best.dir.x, z: best.dir.z }
      };
    }

    /* 极端窄地图：退化为 1 格 */
    var cf = centerFree(cells);
    return { cells: [{ x: cf.x, z: cf.z }], dir: { x: 1, z: 0 } };
  }

  /* ---------- 五张地图（全部 35×35 画布，尽量用满） ---------- */
  /* 迷宫障碍用矩形块描述：[x0, z0, x1, z1] 含边界
     设计原则：墙都是 1~2 格厚、通道至少 2 格宽，孩子转弯不会卡住；中央留一个四门房间做地标 */
  var MAZE_BLOCKS = [
    /* 四角房间 5×5 */
    [2, 2, 6, 6], [28, 2, 32, 6], [2, 28, 6, 32], [28, 28, 32, 32],
    /* 四边中段的长墙（靠内一格，留出外圈跑道） */
    [14, 1, 20, 2], [14, 32, 20, 33], [1, 14, 2, 20], [32, 14, 33, 20],
    /* 中央房间：上下左右各两段墙，中间留一个门洞 */
    [11, 11, 16, 11], [18, 11, 23, 11],
    [11, 23, 16, 23], [18, 23, 23, 23],
    [11, 12, 11, 16], [11, 18, 11, 22],
    [23, 12, 23, 16], [23, 18, 23, 22],
    /* 四条放射短柱 */
    [8, 17, 9, 17], [25, 17, 26, 17], [17, 8, 17, 9], [17, 25, 17, 26]
  ];

  function inMazeBlock(x, z) {
    for (var i = 0; i < MAZE_BLOCKS.length; i++) {
      var b = MAZE_BLOCKS[i];
      if (x >= b[0] && x <= b[2] && z >= b[1] && z <= b[3]) return true;
    }
    return false;
  }

  var MAPS = [
    {
      id: 'classic',
      name: '经典方形',
      note: '35×35 满格 · 无障碍 · 无怪兽',
      cells: makeCells(function () { return true; }),
      monsters: 0, extraMon: 0, monSpd: 0, speedK: 1.00, accelEvery: 4,
      monColors: []
    },
    {
      id: 'plus',
      name: '十字广场',
      note: '双向长廊 · 5 只怪兽',
      cells: makeCells(function (x, z) {
        return (Math.abs(z - MC) <= 6) || (Math.abs(x - MC) <= 6);
      }),
      monsters: 5, extraMon: 1, monSpd: 2.5, speedK: 1.06, accelEvery: 3,
      monColors: [0xa06be0, 0x4ec7d8, 0xe2745a, 0xffb03a, 0x7ad46f]
    },
    {
      id: 'diamond',
      name: '菱形花园',
      note: '四角消失 · 4 只怪兽',
      cells: makeCells(function (x, z) {
        return Math.abs(x - MC) + Math.abs(z - MC) <= MC;
      }),
      monsters: 4, extraMon: 1, monSpd: 2.4, speedK: 1.10, accelEvery: 3,
      monColors: [0xa06be0, 0xe2745a, 0x4ec7d8, 0xffb03a]
    },
    {
      id: 'ring',
      name: '环形赛道',
      note: '中间留空 · 5 只怪兽',
      cells: makeCells(function (x, z) {
        var dx = Math.abs(x - MC), dz = Math.abs(z - MC);
        return !(dx <= 7 && dz <= 7);
      }),
      monsters: 5, extraMon: 2, monSpd: 2.3, speedK: 1.08, accelEvery: 3,
      monColors: [0xe2745a, 0xa06be0, 0x4ec7d8, 0xffb03a, 0x7ad46f]
    },
    {
      id: 'maze',
      name: '糖果迷宫',
      note: '中央四门房间 · 5 只怪兽',
      cells: makeCells(function (x, z) { return !inMazeBlock(x, z); }),
      monsters: 5, extraMon: 1, monSpd: 2.2, speedK: 1.12, accelEvery: 3,
      monColors: [0xa06be0, 0x4ec7d8, 0xe2745a, 0xffb03a, 0x7ad46f]
    }
  ];

  /* 把形状里「走不到的孤岛」剪掉，避免食物生成在进不去的角落 */
  function prepareMap(m) {
    if (m.ready) return m.ready;
    var c = new Uint8Array(m.cells);
    var cf = centerFree(c);
    if (cf) pruneIslands(c, cf.x, cf.z);
    m.ready = c;
    var n = 0;
    for (var i = 0; i < c.length; i++) if (c[i]) n++;
    m.freeCount = n;
    return c;
  }

  function applyMap(id) {
    var m = null;
    for (var i = 0; i < MAPS.length; i++) if (MAPS[i].id === id) m = MAPS[i];
    if (!m) m = MAPS[0];
    prepareMap(m);
    G.map = m;
    G.mapId = m.id;
    G.cells = new Uint8Array(m.ready);
    return m;
  }

  /* ---------------- 运行状态 ---------------- */
  var G = {
    state: 'menu',        // menu | playing | paused | over
    diff: 'normal',
    mapId: 'classic',
    map: MAPS[0],
    cells: null,          // 当前地图的可通行表（激活时复制一份）
    score: 0,
    best: 0,
    eaten: 0,
    stepDur: DIFFS.normal.step,
    minDur: DIFFS.normal.min,
    stepT: 0,
    tMix: 1,
    monT: 0,
    monDur: 1,
    monFreeze: false,
    reinforced: false,
    guard: 0,             // 开局保护剩余 tick（>0 时怪兽撞不死蛇）
    time: 0,
    shake: 0,
    dead: 'wall',
    soundOn: true
  };

  var snake = { cells: [], prev: [], dir: { x: 1, z: 0 }, queue: [] };
  var food = { gx: 0, gz: 0, group: null, type: 'apple', gold: false };
  var monsters = [];

  var errors = [];
  window.addEventListener('error', function (e) {
    errors.push(String(e.message || e.error));
  });
  window.addEventListener('unhandledrejection', function (e) {
    errors.push('promise: ' + String(e.reason));
  });

  /* ---------------- 坐标换算 ---------------- */
  function gx2w(g) { return (g - MC) * CELL; }
  function cellKey(x, z) { return x + ',' + z; }

  /* =========================================================
     音效（WebAudio 实时合成，无音频文件）
     ========================================================= */
  var Snd = {
    ctx: null, master: null, musicBus: null, timer: null, step: 0, ok: false,

    init: function () {
      if (this.ctx) return;
      var AC = window.AudioContext || window.webkitAudioContext;
      if (!AC) return;
      try { this.ctx = new AC(); } catch (e) { return; }
      this.master = this.ctx.createGain();
      this.master.gain.value = 0.62;
      this.master.connect(this.ctx.destination);
      this.musicBus = this.ctx.createGain();
      this.musicBus.gain.value = 0;
      this.musicBus.connect(this.master);
      this.ok = true;
    },

    resume: function () {
      if (!this.ctx) return;
      if (this.ctx.state === 'suspended') { this.ctx.resume(); }
    },

    tone: function (freq, dur, type, vol, slideTo, dest) {
      if (!this.ok || !G.soundOn) return;
      var t0 = this.ctx.currentTime;
      var o = this.ctx.createOscillator();
      var g = this.ctx.createGain();
      o.type = type || 'sine';
      o.frequency.setValueAtTime(freq, t0);
      if (slideTo) {
        o.frequency.exponentialRampToValueAtTime(Math.max(24, slideTo), t0 + dur);
      }
      g.gain.setValueAtTime(0.0001, t0);
      g.gain.exponentialRampToValueAtTime(Math.max(0.0002, vol || 0.2), t0 + 0.012);
      g.gain.exponentialRampToValueAtTime(0.0001, t0 + dur);
      o.connect(g);
      g.connect(dest || this.master);
      o.start(t0);
      o.stop(t0 + dur + 0.03);
    },

    eat: function () {
      this.tone(784, 0.09, 'triangle', 0.30);
      var self = this;
      setTimeout(function () { self.tone(1174.7, 0.13, 'triangle', 0.26); }, 62);
      setTimeout(function () { self.tone(1568, 0.10, 'sine', 0.16); }, 128);
    },
    /* 金苹果：更亮更长的上行琶音 */
    gold: function () {
      this.tone(880, 0.10, 'triangle', 0.30);
      var self = this;
      setTimeout(function () { self.tone(1318.5, 0.10, 'triangle', 0.26); }, 70);
      setTimeout(function () { self.tone(1760, 0.12, 'triangle', 0.24); }, 140);
      setTimeout(function () { self.tone(2637, 0.16, 'sine', 0.14); }, 215);
    },
    /* 怪兽增援：两声低沉的警告 */
    warn: function () {
      this.tone(196, 0.18, 'square', 0.20, 160);
      var self = this;
      setTimeout(function () { self.tone(147, 0.26, 'square', 0.18, 108); }, 175);
    },
    turn: function () {
      this.tone(520, 0.05, 'sine', 0.07);
    },
    over: function () {
      this.tone(392, 0.20, 'sawtooth', 0.20, 300);
      var self = this;
      setTimeout(function () { self.tone(311, 0.22, 'sawtooth', 0.18, 240); }, 150);
      setTimeout(function () { self.tone(233, 0.34, 'sawtooth', 0.16, 110); }, 320);
    },
    start: function () {
      this.tone(523.25, 0.10, 'triangle', 0.22);
      var self = this;
      setTimeout(function () { self.tone(659.25, 0.10, 'triangle', 0.22); }, 90);
      setTimeout(function () { self.tone(783.99, 0.16, 'triangle', 0.22); }, 180);
    },

    /* 轻快的五声音阶循环 */
    startMusic: function () {
      if (!this.ok || this.timer) return;
      var self = this;
      var NOTES = [
        523.25, 659.25, 783.99, 659.25, 587.33, 698.46, 880.00, 698.46,
        523.25, 659.25, 783.99, 1046.50, 880.00, 783.99, 698.46, 587.33
      ];
      if (this.musicBus) this.musicBus.gain.setTargetAtTime(1, this.ctx.currentTime, 0.4);
      var tick = function () {
        if (!self.ok) return;
        if (G.state === 'playing') {
          var n = NOTES[self.step % NOTES.length];
          self.tone(n, 0.20, 'triangle', 0.052, null, self.musicBus);
          if (self.step % 8 === 0) self.tone(n / 2, 0.34, 'sine', 0.075, null, self.musicBus);
        }
        self.step++;
        self.timer = setTimeout(tick, 300);
      };
      this.timer = setTimeout(tick, 340);
    },

    stopMusic: function () {
      if (this.timer) { clearTimeout(this.timer); this.timer = null; }
      if (this.ok && this.musicBus) {
        this.musicBus.gain.setTargetAtTime(0, this.ctx.currentTime, 0.25);
      }
    }
  };

  /* =========================================================
     三维基础
     ========================================================= */
  var canvas = document.getElementById('c');
  var scene, camera, renderer, clock;
  var sunLight;
  /* 相机偏移：游玩时跟随蛇头并保持格子可读；菜单时退到能看清整张地图的距离 */
  var camOffPlay = new THREE.Vector3(0, 26, 20);
  var camOffMenu = new THREE.Vector3(0, 26, 20);
  var camMenuLookZ = 3;               /* 菜单注视点前移量：把场地推到画面偏上，别被卡片压住 */
  var camViewCells = 19;              /* 当前画面窄边能看到多少格 */
  var camHalfX = 20, camHalfZNear = 20, camHalfZFar = 20;  /* 实测可见半宽/半深（格） */
  var camLimX = 8, camLimZmin = -8, camLimZmax = 8;        /* 注视点允许的偏移范围 */
  var camPos = new THREE.Vector3(0, 26, 20);
  var camLook = new THREE.Vector3(0, 0, 0);
  var lookTarget = new THREE.Vector3();
  var v3a = new THREE.Vector3();
  var v3b = new THREE.Vector3();

  /* ---------------- 材质库 ---------------- */
  var MAT = {};

  function initMaterials() {
    MAT.ground = new THREE.MeshLambertMaterial({ color: 0x6fb84b });
    MAT.outer  = new THREE.MeshLambertMaterial({ color: 0x63ab42 });
    MAT.post   = new THREE.MeshLambertMaterial({ color: 0xffffff });
    MAT.rail   = new THREE.MeshLambertMaterial({ color: 0xff9fc0 });
    MAT.kerb   = new THREE.MeshLambertMaterial({ color: 0x4e9438 });
    /* 内部障碍格用的实心糖果块：底色留白，颜色由每个实例自己的 instanceColor 决定 */
    MAT.block  = new THREE.MeshLambertMaterial({ color: 0xffffff });
    MAT.trunk  = new THREE.MeshLambertMaterial({ color: 0x8b5a34 });
    MAT.crown  = new THREE.MeshLambertMaterial({ color: 0x3f9e46 });
    MAT.cloud  = new THREE.MeshLambertMaterial({ color: 0xffffff, emissive: 0x9fbfd8, emissiveIntensity: 0.18 });
    MAT.hill   = new THREE.MeshLambertMaterial({ color: 0x5fa93f });

    MAT.snakeHead = new THREE.MeshLambertMaterial({ color: 0x46dd7c });
    MAT.eyeWhite  = new THREE.MeshLambertMaterial({ color: 0xffffff });
    MAT.eyePupil  = new THREE.MeshLambertMaterial({ color: 0x20303f });
    MAT.blush     = new THREE.MeshLambertMaterial({ color: 0xff9db4, transparent: true, opacity: 0.9 });
    MAT.tongue    = new THREE.MeshLambertMaterial({ color: 0xf0485f });

    MAT.apple  = new THREE.MeshPhongMaterial({ color: 0xe8453f, shininess: 55, specular: 0x552222 });
    MAT.stem   = new THREE.MeshLambertMaterial({ color: 0x80552f });
    MAT.leaf   = new THREE.MeshPhongMaterial({ color: 0x4fbd52, shininess: 35 });
    MAT.star   = new THREE.MeshPhongMaterial({ color: 0xffcf3d, shininess: 90, specular: 0xfff2c0, emissive: 0x6a4a00, emissiveIntensity: 0.35 });
    MAT.donut  = new THREE.MeshPhongMaterial({ color: 0xff9dc4, shininess: 40 });
    MAT.icing  = new THREE.MeshPhongMaterial({ color: 0xffe1ee, shininess: 70 });
    MAT.cherry = new THREE.MeshPhongMaterial({ color: 0xe0304f, shininess: 80, specular: 0x661122 });
    /* 金苹果：整颗换成金属金，一眼就能认出来 */
    MAT.gold   = new THREE.MeshPhongMaterial({
      color: 0xffc21c, shininess: 120, specular: 0xfff3bf,
      emissive: 0x8a5200, emissiveIntensity: 0.55
    });

    MAT.glow = new THREE.MeshBasicMaterial({
      color: 0xfff8c8, transparent: true, opacity: 0.10,
      side: THREE.DoubleSide, depthWrite: false, blending: THREE.AdditiveBlending
    });
    MAT.ring = new THREE.MeshBasicMaterial({
      color: 0xffd23f, transparent: true, opacity: 0.85,
      side: THREE.DoubleSide, depthWrite: false
    });
    MAT.disc = new THREE.MeshBasicMaterial({
      color: 0xfff3a8, transparent: true, opacity: 0.30,
      side: THREE.DoubleSide, depthWrite: false
    });
    /* 怪兽的危险范围：用普通混合而不是加色，否则在亮绿台面上会发白看不出红色 */
    MAT.dangerRing = new THREE.MeshBasicMaterial({
      color: 0xf2402f, transparent: true, opacity: 0.80,
      side: THREE.DoubleSide, depthWrite: false
    });
    MAT.dangerDisc = new THREE.MeshBasicMaterial({
      color: 0xff5c3d, transparent: true, opacity: 0.22,
      side: THREE.DoubleSide, depthWrite: false
    });
  }

  /* ---------------- 天空 ---------------- */
  function buildSky() {
    var geo = new THREE.SphereGeometry(190, 32, 20);
    var pos = geo.attributes.position;
    var arr = new Float32Array(pos.count * 3);
    var top = new THREE.Color(0x3f9fe4);
    var mid = new THREE.Color(0xa4dcf6);
    var bot = new THREE.Color(0xe6f7ff);
    var c = new THREE.Color();
    for (var i = 0; i < pos.count; i++) {
      var y = pos.getY(i) / 190;
      if (y > 0) { c.copy(mid).lerp(top, Math.pow(clamp(y, 0, 1), 0.8)); }
      else { c.copy(mid).lerp(bot, Math.pow(clamp(-y, 0, 1), 0.85)); }
      arr[i * 3] = c.r; arr[i * 3 + 1] = c.g; arr[i * 3 + 2] = c.b;
    }
    geo.setAttribute('color', new THREE.BufferAttribute(arr, 3));
    var sky = new THREE.Mesh(geo, new THREE.MeshBasicMaterial({
      vertexColors: true, side: THREE.BackSide, fog: false, depthWrite: false
    }));
    sky.renderOrder = -10;
    sky.name = 'sky';
    scene.add(sky);
  }

  /* ---------------- 棋盘纹理（按地图形状遮罩，形状外透明） ---------------- */
  function makeBoardTexture(cells) {
    var n = MS;
    var TXC = 40;                   /* 每格 40 像素：35×35 → 1400² 画布，手机上也不至于吃内存 */
    var S = n * TXC;
    var cv = document.createElement('canvas');
    cv.width = cv.height = S;
    var g = cv.getContext('2d');
    var s = S / n;
    var x, z;

    /* 1. 棋盘格：只画可通行格 */
    for (z = 0; z < n; z++) {
      for (x = 0; x < n; x++) {
        if (!cellFree(cells, x, z)) continue;
        g.fillStyle = ((x + z) & 1) ? '#a5e870' : '#8ad456';
        g.fillRect(x * s, z * s, s, s);
      }
    }

    /* 以下全部裁剪在形状内部，避免溢出到透明区域 */
    g.save();
    g.beginPath();
    for (z = 0; z < n; z++) {
      for (x = 0; x < n; x++) {
        if (cellFree(cells, x, z)) g.rect(x * s, z * s, s, s);
      }
    }
    g.clip();

    /* 2. 草叶噪点（随画布面积缩放，密度保持一致） */
    var nNoise = Math.round(S * 2.4);
    for (var k = 0; k < nNoise; k++) {
      var px = Math.random() * S, py = Math.random() * S;
      g.fillStyle = Math.random() < 0.5 ? 'rgba(255,255,255,0.10)' : 'rgba(40,110,30,0.08)';
      g.fillRect(px, py, 2, 3);
    }

    /* 3. 细网格 */
    g.strokeStyle = 'rgba(255,255,255,0.15)';
    g.lineWidth = Math.max(1, s * 0.05);
    for (z = 0; z < n; z++) {
      for (x = 0; x < n; x++) {
        if (!cellFree(cells, x, z)) continue;
        g.strokeRect(x * s + 1, z * s + 1, s - 2, s - 2);
      }
    }

    /* 4. 边界内侧压暗一圈，让孩子看清「这边过不去」 */
    g.strokeStyle = 'rgba(44,104,36,0.40)';
    g.lineWidth = s * 0.16;
    g.beginPath();
    for (z = 0; z < n; z++) {
      for (x = 0; x < n; x++) {
        if (!cellFree(cells, x, z)) continue;
        if (!cellFree(cells, x + 1, z)) { g.moveTo((x + 1) * s, z * s); g.lineTo((x + 1) * s, (z + 1) * s); }
        if (!cellFree(cells, x - 1, z)) { g.moveTo(x * s, z * s); g.lineTo(x * s, (z + 1) * s); }
        if (!cellFree(cells, x, z + 1)) { g.moveTo(x * s, (z + 1) * s); g.lineTo((x + 1) * s, (z + 1) * s); }
        if (!cellFree(cells, x, z - 1)) { g.moveTo(x * s, z * s); g.lineTo((x + 1) * s, z * s); }
      }
    }
    g.stroke();
    g.restore();

    var tex = new THREE.CanvasTexture(cv);
    tex.colorSpace = THREE.SRGBColorSpace;
    tex.anisotropy = renderer.capabilities.getMaxAnisotropy();
    return tex;
  }

  /* ---------------- 世界搭建 ---------------- */
  var decor = { clouds: null, butterflies: [], trees: [] };

  function makeGrassTexture() {
    var S = 256;
    var cv = document.createElement('canvas');
    cv.width = cv.height = S;
    var g = cv.getContext('2d');
    g.fillStyle = '#6cba49';
    g.fillRect(0, 0, S, S);
    /* 大色斑，避免整片死板 */
    for (var k = 0; k < 30; k++) {
      var cx = Math.random() * S, cy = Math.random() * S, r = 12 + Math.random() * 34;
      var grd = g.createRadialGradient(cx, cy, 0, cx, cy, r);
      grd.addColorStop(0, Math.random() < 0.5 ? 'rgba(220,255,170,0.13)' : 'rgba(46,120,44,0.10)');
      grd.addColorStop(1, 'rgba(0,0,0,0)');
      g.fillStyle = grd;
      g.beginPath(); g.arc(cx, cy, r, 0, TAU); g.fill();
    }
    /* 草叶 */
    for (var i = 0; i < 3600; i++) {
      var x = Math.random() * S, y = Math.random() * S;
      g.fillStyle = Math.random() < 0.5 ? 'rgba(255,255,220,0.10)' : 'rgba(38,100,36,0.12)';
      g.fillRect(x, y, 1.6, 3.4);
    }
    var t = new THREE.CanvasTexture(cv);
    t.wrapS = t.wrapT = THREE.RepeatWrapping;
    t.repeat.set(26, 26);
    t.colorSpace = THREE.SRGBColorSpace;
    t.anisotropy = renderer.capabilities.getMaxAnisotropy();
    return t;
  }

  /* 竞技场（随地图重建） */
  var arenaGroup = null;

  function disposeArena() {
    if (!arenaGroup) return;
    scene.remove(arenaGroup);
    arenaGroup.traverse(function (o) {
      if (!o.isMesh) return;
      if (o.geometry) o.geometry.dispose();
      /* 只销毁本场自建的材质（MAT.* 是全局共享的，不能碰） */
      if (o.material && o.material.userData && o.material.userData.own) {
        if (o.material.map) o.material.map.dispose();
        o.material.dispose();
      }
    });
    arenaGroup = null;
  }

  function buildArena() {
    disposeArena();
    arenaGroup = new THREE.Group();
    arenaGroup.name = 'arena';
    scene.add(arenaGroup);

    var cells = G.cells;
    var x, z, i;
    var d = new THREE.Object3D();

    /* ---------- 0. 把「不可通行格」分成两类 ----------
       A 形状外部：从 17×17 边框上的不可通行格出发能走到的那些 → 属于场地的外轮廓，用围栏收边
       B 内部障碍：被可通行格完全围住、从外面走不到的那些 → 立起实心糖果块，一眼看出「过不去」
       只有分开处理，孩子才不会把「围起来的小院」误当成能走的路。 */
    var outside = new Uint8Array(MS * MS);
    var bfs = [];
    for (z = 0; z < MS; z++) {
      for (x = 0; x < MS; x++) {
        var onRim = (x === 0 || z === 0 || x === MS - 1 || z === MS - 1);
        if (onRim && !cellFree(cells, x, z)) { outside[z * MS + x] = 1; bfs.push(z * MS + x); }
      }
    }
    for (var bi = 0; bi < bfs.length; bi++) {
      var cur = bfs[bi], bx = cur % MS, bz = (cur - bx) / MS;
      for (i = 0; i < 4; i++) {
        var nx = bx + DIR4[i].x, nz = bz + DIR4[i].z;
        if (nx < 0 || nz < 0 || nx >= MS || nz >= MS) continue;
        var idxN = nz * MS + nx;
        if (outside[idxN] || cellFree(cells, nx, nz)) continue;
        outside[idxN] = 1;
        bfs.push(idxN);
      }
    }

    /* 内部障碍格 + 连通分量编号（同一个块用同一种颜色，看起来才像一整块） */
    var innerIdx = [];
    var compId = new Int16Array(MS * MS);
    for (i = 0; i < compId.length; i++) compId[i] = -1;
    var nComp = 0;
    for (z = 0; z < MS; z++) {
      for (x = 0; x < MS; x++) {
        if (cellFree(cells, x, z) || outside[z * MS + x] || compId[z * MS + x] >= 0) continue;
        var head = z * MS + x;
        compId[head] = nComp;
        bfs.length = 0; bfs.push(head);
        for (var ci = 0; ci < bfs.length; ci++) {
          var c0 = bfs[ci], c0x = c0 % MS, c0z = (c0 - c0x) / MS;
          innerIdx.push({ x: c0x, z: c0z, c: nComp });
          for (i = 0; i < 4; i++) {
            var mx = c0x + DIR4[i].x, mz = c0z + DIR4[i].z;
            if (mx < 0 || mz < 0 || mx >= MS || mz >= MS) continue;
            var mi = mz * MS + mx;
            if (compId[mi] >= 0 || outside[mi] || cellFree(cells, mx, mz)) continue;
            compId[mi] = nComp;
            bfs.push(mi);
          }
        }
        nComp++;
      }
    }
    var isInnerWall = function (wx, wz) {
      if (wx < 0 || wz < 0 || wx >= MS || wz >= MS) return false;
      if (cellFree(cells, wx, wz)) return false;
      return !outside[wz * MS + wx];
    };

    /* ---------- 1. 台面：可通行格各自一块厚板，拼出形状 ---------- */
    var slabGeo = new THREE.BoxGeometry(CELL * 1.004, 0.54, CELL * 1.004);
    var nFree = 0;
    for (z = 0; z < MS; z++) for (x = 0; x < MS; x++) if (cellFree(cells, x, z)) nFree++;

    var slabs = new THREE.InstancedMesh(slabGeo, MAT.kerb, nFree);
    slabs.receiveShadow = true;
    slabs.castShadow = false;
    slabs.frustumCulled = false;
    var si = 0;
    for (z = 0; z < MS; z++) {
      for (x = 0; x < MS; x++) {
        if (!cellFree(cells, x, z)) continue;
        d.position.set(gx2w(x), -0.275, gx2w(z));
        d.rotation.set(0, 0, 0);
        d.scale.set(1, 1, 1);
        d.updateMatrix();
        slabs.setMatrixAt(si++, d.matrix);
      }
    }
    arenaGroup.add(slabs);

    /* ---------- 2. 棋盘面：形状外 alpha 裁掉 ---------- */
    var boardMat = new THREE.MeshLambertMaterial({
      map: makeBoardTexture(cells), alphaTest: 0.5, transparent: false
    });
    boardMat.userData.own = true;
    var board = new THREE.Mesh(new THREE.PlaneGeometry(MS * CELL, MS * CELL, 1, 1), boardMat);
    board.rotation.x = -Math.PI / 2;
    board.position.y = 0.002;
    board.receiveShadow = true;
    board.name = 'board';
    arenaGroup.add(board);

    /* ---------- 2.5 内部障碍：立起实心糖果块 ---------- */
    if (innerIdx.length) {
      var blockGeo = new THREE.BoxGeometry(CELL * 0.96, 0.95, CELL * 0.96);
      var blocks = new THREE.InstancedMesh(blockGeo, MAT.block, innerIdx.length);
      blocks.castShadow = true;
      blocks.receiveShadow = true;
      blocks.frustumCulled = false;
      blocks.name = 'blocks';
      var palette = [0xff9ab8, 0xffc978, 0xa8d8ff, 0xc3a6ff, 0x8fe0c0, 0xffb0d8];
      var base = new THREE.Color(), tmpc = new THREE.Color();
      for (i = 0; i < innerIdx.length; i++) {
        var ic = innerIdx[i];
        d.position.set(gx2w(ic.x), 0.475, gx2w(ic.z));
        d.rotation.set(0, 0, 0);
        d.scale.set(1, 1, 1);
        d.updateMatrix();
        blocks.setMatrixAt(i, d.matrix);
        /* 同一个连通块同色；相邻格轻微深浅交替，看得出是一格一格拼的 */
        base.setHex(palette[ic.c % palette.length]);
        var shade = ((ic.x + ic.z) & 1) ? 1.0 : 0.94;
        tmpc.setRGB(base.r * shade, base.g * shade, base.b * shade);
        blocks.setColorAt(i, tmpc);
      }
      blocks.instanceColor.needsUpdate = true;
      arenaGroup.add(blocks);
    }

    /* ---------- 3. 找出真正的外轮廓：可通行格 → 形状外部 的交界 ---------- */
    var edges = [];          /* 每条边界边：位置中点 + 外法线 */
    for (z = 0; z < MS; z++) {
      for (x = 0; x < MS; x++) {
        if (!cellFree(cells, x, z)) continue;
        for (i = 0; i < 4; i++) {
          var nrm = DIR4[i];
          if (cellFree(cells, x + nrm.x, z + nrm.z)) continue;
          if (isInnerWall(x + nrm.x, z + nrm.z)) continue;   /* 内部障碍由糖果块自己表达，不再插围栏 */
          edges.push({
            px: gx2w(x) + nrm.x * CELL * 0.5,
            pz: gx2w(z) + nrm.z * CELL * 0.5,
            nx: nrm.x, nz: nrm.z
          });
        }
      }
    }

    /* ---------- 4. 围栏柱子 + 顶球（每条边界边中点一根） ---------- */
    var nE = edges.length;
    if (nE) {
      var postGeo = new THREE.CylinderGeometry(0.075, 0.085, 0.85, 8);
      var ballGeo = new THREE.SphereGeometry(0.105, 10, 8);
      var railGeo = new THREE.BoxGeometry(CELL + 0.06, 0.062, 0.062);

      var posts = new THREE.InstancedMesh(postGeo, MAT.post, nE);
      var balls = new THREE.InstancedMesh(ballGeo, MAT.post, nE);
      var rails = new THREE.InstancedMesh(railGeo, MAT.rail, nE);
      posts.castShadow = false; balls.castShadow = false; rails.castShadow = false;
      posts.frustumCulled = false; balls.frustumCulled = false; rails.frustumCulled = false;

      var colW = new THREE.Color(0xffffff);
      var colP = new THREE.Color(0xffa8c6);

      for (i = 0; i < nE; i++) {
        var e = edges[i];
        d.position.set(e.px, 0.425, e.pz);
        d.rotation.set(0, 0, 0);
        d.scale.set(1, 1, 1);
        d.updateMatrix();
        posts.setMatrixAt(i, d.matrix);
        posts.setColorAt(i, (i & 1) ? colW : colP);

        d.position.set(e.px, 0.88, e.pz);
        d.updateMatrix();
        balls.setMatrixAt(i, d.matrix);
        balls.setColorAt(i, (i & 1) ? colP : colW);

        /* 横杆沿着边的方向铺：法线是 X 时沿 Z，法线是 Z 时沿 X */
        d.position.set(e.px, 0.60, e.pz);
        d.rotation.set(0, e.nx !== 0 ? Math.PI / 2 : 0, 0);
        d.updateMatrix();
        rails.setMatrixAt(i, d.matrix);
      }
      posts.instanceColor.needsUpdate = true;
      balls.instanceColor.needsUpdate = true;

      arenaGroup.add(posts); arenaGroup.add(balls); arenaGroup.add(rails);
    }

    return { edges: nE, free: nFree, blocks: innerIdx.length };
  }

  function buildWorld() {
    /* 外圈草地 */
    var outer = new THREE.Mesh(
      new THREE.PlaneGeometry(300, 300),
      new THREE.MeshLambertMaterial({ map: makeGrassTexture() })
    );
    outer.rotation.x = -Math.PI / 2;
    outer.position.y = -0.06;
    outer.receiveShadow = true;
    scene.add(outer);

    buildArena();

    /* 树 */
    buildTrees();
    /* 小花 */
    buildFlowers();
    /* 云 */
    buildClouds();
    /* 山丘 */
    buildHills();
    /* 蝴蝶 */
    for (var b = 0; b < 4; b++) { makeButterfly([0xffd166, 0xff8fb1, 0xa8e6ff, 0xb9f2c0][b]); }
  }

  /* 圆滚滚的果冻树 */
  function buildTrees() {
    /* 数量跟着场地周长走：树太密会挡住场地，太稀又显得荒 */
    var N = Math.round(WALL * 1.9);
    var trunkGeo = new THREE.CylinderGeometry(0.19, 0.27, 1.0, 8);
    var crownGeo = new THREE.SphereGeometry(1, 16, 12);
    var trunks = new THREE.InstancedMesh(trunkGeo, MAT.trunk, N);
    var crowns = new THREE.InstancedMesh(crownGeo, MAT.crown, N * 2);
    trunks.castShadow = true; crowns.castShadow = true;
    crowns.receiveShadow = true;
    var d = new THREE.Object3D();
    var c = new THREE.Color();

    /* 环绕场地外圈散布（相机是跟随的，所以只按场地边界排，不跟相机走） */
    var near = WALL + 3.5;
    var far = WALL + 17.0;

    for (var i = 0; i < N; i++) {
      var ang = (i / N) * TAU + rand(-0.24, 0.24);
      var rad = rand(near, far);
      var x = Math.cos(ang) * rad, z = Math.sin(ang) * rad;
      var s = rand(0.85, 1.45);

      /* 树干（矮而粗，被画面边缘裁到时不会只剩一根柱子） */
      d.position.set(x, 0.5 * s, z);
      d.rotation.set(0, rand(0, TAU), 0);
      d.scale.set(s, s, s);
      d.updateMatrix();
      trunks.setMatrixAt(i, d.matrix);

      /* 下层大球 */
      d.position.set(x, 1.55 * s, z);
      d.rotation.set(0, rand(0, TAU), 0);
      d.scale.set(1.45 * s, 1.15 * s, 1.45 * s);
      d.updateMatrix();
      crowns.setMatrixAt(i * 2, d.matrix);
      c.setHSL(rand(0.255, 0.315), rand(0.52, 0.68), rand(0.42, 0.52));
      crowns.setColorAt(i * 2, c);

      /* 上层小球 */
      d.position.set(x + rand(-0.2, 0.2) * s, 2.25 * s, z + rand(-0.2, 0.2) * s);
      d.scale.set(0.95 * s, 0.86 * s, 0.95 * s);
      d.updateMatrix();
      crowns.setMatrixAt(i * 2 + 1, d.matrix);
      c.setHSL(rand(0.26, 0.32), rand(0.56, 0.72), rand(0.46, 0.56));
      crowns.setColorAt(i * 2 + 1, c);
    }
    if (crowns.instanceColor) crowns.instanceColor.needsUpdate = true;
    scene.add(trunks); scene.add(crowns);
  }

  /* 场外小花点缀 */
  function buildFlowers() {
    var N = Math.round(WALL * 18);
    var geo = new THREE.SphereGeometry(0.085, 6, 5);
    var mat = new THREE.MeshLambertMaterial({ color: 0xffffff });
    var mesh = new THREE.InstancedMesh(geo, mat, N);
    mesh.frustumCulled = false;
    var d = new THREE.Object3D();
    var c = new THREE.Color();
    var palette = [0xfff4f8, 0xffe36b, 0xff9ec4, 0xffb46b, 0xffffff, 0xc9a7ff];
    for (var i = 0; i < N; i++) {
      var a = rand(0, TAU);
      var r = rand(WALL + 0.6, WALL + 16);
      d.position.set(Math.cos(a) * r, 0.06, Math.sin(a) * r);
      d.rotation.set(0, 0, 0);
      var s = rand(0.7, 1.5);
      d.scale.set(s, s * 0.8, s);
      d.updateMatrix();
      mesh.setMatrixAt(i, d.matrix);
      c.setHex(palette[i % palette.length]);
      mesh.setColorAt(i, c);
    }
    mesh.instanceColor.needsUpdate = true;
    scene.add(mesh);
  }

  function buildClouds() {
    var N = 26;
    var geo = new THREE.SphereGeometry(1, 10, 8);
    var mesh = new THREE.InstancedMesh(geo, MAT.cloud, N);
    mesh.name = 'clouds';
    var d = new THREE.Object3D();
    var i = 0;
    for (var g = 0; g < 7; g++) {
      var cx = rand(-52, 52), cy = rand(15, 27), cz = rand(-58, -16);
      var nb = 3 + (g % 3);
      for (var k = 0; k < nb && i < N; k++) {
        var s = rand(2.0, 4.2);
        d.position.set(cx + rand(-4.5, 4.5), cy + rand(-0.8, 1.2), cz + rand(-2.2, 2.2));
        d.scale.set(s, s * 0.72, s * 0.86);
        d.rotation.set(0, rand(0, TAU), 0);
        d.updateMatrix();
        mesh.setMatrixAt(i, d.matrix);
        i++;
      }
    }
    mesh.count = i;
    mesh.castShadow = false;
    scene.add(mesh);
    decor.clouds = mesh;
  }

  function buildHills() {
    var geo = new THREE.SphereGeometry(1, 18, 12);
    for (var i = 0; i < 7; i++) {
      var a = (i / 7) * TAU + 0.4;
      var r = rand(58, 78);
      var s = rand(10, 20);
      var m = new THREE.Mesh(geo, MAT.hill);
      m.position.set(Math.cos(a) * r, rand(-3, 1), Math.sin(a) * r);
      m.scale.set(s * 1.7, s * 0.55, s);
      scene.add(m);
    }
  }

  function makeButterfly(color) {
    var g = new THREE.Group();
    /* 翅膀水平展开（俯视时才看得出是蝴蝶），绕前后轴上下扇动 */
    var wingGeo = new THREE.SphereGeometry(0.30, 10, 8);
    wingGeo.scale(0.66, 0.14, 1.15);
    var wm = new THREE.MeshLambertMaterial({ color: color, side: THREE.DoubleSide });
    var wl = new THREE.Mesh(wingGeo, wm);
    var wr = new THREE.Mesh(wingGeo, wm);
    wl.castShadow = false; wr.castShadow = false;
    wl.position.x = -0.30; wr.position.x = 0.30;
    var body = new THREE.Mesh(
      new THREE.CapsuleGeometry(0.05, 0.2, 3, 6),
      new THREE.MeshLambertMaterial({ color: 0x7c8b9c })
    );
    body.rotation.z = Math.PI / 2;
    g.add(wl); g.add(wr); g.add(body);
    g.userData = {
      wl: wl, wr: wr,
      r: rand(WALL + 2.0, WALL + 7.5), a: rand(0, TAU), sp: rand(0.22, 0.44), y: rand(4.6, 7.2)
    };
    scene.add(g);
    decor.butterflies.push(g);
  }

  /* =========================================================
     蛇
     ========================================================= */
  var bodyMesh = null;
  var headGroup = null;
  var tongueGroup = null;
  var dummy = new THREE.Object3D();
  var tmpColor = new THREE.Color();
  var segPos = [];
  var headYaw = Math.PI / 2;
  var headPulse = 0;
  var lastColorLen = -1;

  function buildSnake() {
    var geo = new THREE.SphereGeometry(1, 16, 12);
    var mat = new THREE.MeshLambertMaterial({ color: 0xffffff });
    bodyMesh = new THREE.InstancedMesh(geo, mat, MAX_SEG * 2);
    bodyMesh.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
    bodyMesh.castShadow = true;
    bodyMesh.receiveShadow = true;
    bodyMesh.frustumCulled = false;
    bodyMesh.count = 0;
    bodyMesh.setColorAt(0, tmpColor.setHex(0xffffff));
    scene.add(bodyMesh);

    headGroup = new THREE.Group();
    var skull = new THREE.Mesh(new THREE.SphereGeometry(0.62, 22, 16), MAT.snakeHead);
    skull.castShadow = true;
    skull.scale.set(1, 0.96, 1.06);
    headGroup.add(skull);

    /* 眼睛 */
    var eyeGeo = new THREE.SphereGeometry(0.20, 14, 12);
    var pupGeo = new THREE.SphereGeometry(0.118, 12, 10);
    [-1, 1].forEach(function (s) {
      var e = new THREE.Mesh(eyeGeo, MAT.eyeWhite);
      e.position.set(0.275 * s, 0.20, 0.43);
      e.scale.set(1, 1.06, 1);
      headGroup.add(e);
      var p = new THREE.Mesh(pupGeo, MAT.eyePupil);
      p.position.set(0.295 * s, 0.21, 0.555);
      p.scale.set(1, 1, 0.62);
      headGroup.add(p);
    });

    /* 腮红 */
    var blushGeo = new THREE.SphereGeometry(0.125, 10, 8);
    [-1, 1].forEach(function (s) {
      var b = new THREE.Mesh(blushGeo, MAT.blush);
      b.position.set(0.445 * s, -0.05, 0.35);
      b.scale.set(1, 0.62, 0.42);
      headGroup.add(b);
    });

    /* 舌头 */
    tongueGroup = new THREE.Group();
    var tg1 = new THREE.Mesh(new THREE.BoxGeometry(0.038, 0.022, 0.17), MAT.tongue);
    var tg2 = new THREE.Mesh(new THREE.BoxGeometry(0.038, 0.022, 0.12), MAT.tongue);
    var tg3 = new THREE.Mesh(new THREE.BoxGeometry(0.038, 0.022, 0.12), MAT.tongue);
    tg2.position.set(-0.055, 0, 0.14); tg2.rotation.y = 0.55;
    tg3.position.set(0.055, 0, 0.14); tg3.rotation.y = -0.55;
    tongueGroup.add(tg1); tongueGroup.add(tg2); tongueGroup.add(tg3);
    tongueGroup.position.set(0, -0.18, 0.55);
    headGroup.add(tongueGroup);

    headGroup.position.set(0, 0.68, 0);
    scene.add(headGroup);
  }

  function hueAt(i) {
    /* 从头部的亮绿过渡到黄—橙—粉—紫—蓝，形成彩虹蛇 */
    return ((0.145 - i * 0.048) % 1 + 1) % 1;
  }
  function radiusAt(i, n) {
    var k = i / Math.max(1, n - 1);
    var t = clamp((k - 0.55) / 0.45, 0, 1);
    return lerp(0.51, 0.26, t * t);
  }

  /* 计算插值后的各节位置 */
  function layoutSnake() {
    var n = snake.cells.length;
    var t = G.tMix;
    segPos.length = 0;
    for (var i = 0; i < n; i++) {
      var to = snake.cells[i];
      var from = snake.prev[i] || snake.prev[snake.prev.length - 1] || to;
      var tx = gx2w(to.x), tz = gx2w(to.z);
      var fx = gx2w(from.x), fz = gx2w(from.z);
      segPos.push({ x: lerp(fx, tx, t), z: lerp(fz, tz, t) });
    }
  }

  function refreshBodyColors(n) {
    if (n === lastColorLen) return;
    lastColorLen = n;
    var idx = 0;
    for (var i = 1; i < n; i++) {
      tmpColor.setHSL(hueAt(i), 0.80, 0.54);
      bodyMesh.setColorAt(idx, tmpColor);
      idx++;
    }
    for (var j = 0; j < n - 1; j++) {
      tmpColor.setHSL(hueAt(j + 0.5), 0.76, 0.60);
      bodyMesh.setColorAt(idx, tmpColor);
      idx++;
    }
    if (bodyMesh.instanceColor) bodyMesh.instanceColor.needsUpdate = true;
  }

  function renderSnake() {
    var n = snake.cells.length;
    var time = G.time;
    var idx = 0;

    refreshBodyColors(n);

    for (var i = 1; i < n; i++) {
      var p = segPos[i];
      var r = radiusAt(i, n);
      var y = 0.52 + Math.sin(time * 3.3 - i * 0.42) * 0.045;
      dummy.position.set(p.x, y, p.z);
      dummy.rotation.set(0, 0, 0);
      dummy.scale.set(r, r * 0.96, r);
      dummy.updateMatrix();
      bodyMesh.setMatrixAt(idx, dummy.matrix);
      idx++;
    }
    for (var j = 0; j < n - 1; j++) {
      var A = segPos[j], B = segPos[j + 1];
      var ra = radiusAt(j, n), rb = radiusAt(j + 1, n);
      var rr = Math.min(ra, rb) * 0.94;
      var yy = 0.52 + Math.sin(time * 3.3 - (j + 0.5) * 0.42) * 0.045;
      dummy.position.set((A.x + B.x) / 2, yy, (A.z + B.z) / 2);
      dummy.rotation.set(0, 0, 0);
      dummy.scale.set(rr, rr * 0.96, rr);
      dummy.updateMatrix();
      bodyMesh.setMatrixAt(idx, dummy.matrix);
      idx++;
    }

    bodyMesh.count = Math.min(idx, MAX_SEG * 2);
    bodyMesh.instanceMatrix.needsUpdate = true;

    /* 头 */
    var h = segPos[0] || { x: 0, z: 0 };
    var bob = Math.sin(time * 3.0) * 0.03;
    headGroup.position.set(h.x, 0.68 + bob, h.z);

    var targetYaw = Math.atan2(snake.dir.x, snake.dir.z);
    var delta = ((targetYaw - headYaw + Math.PI * 3) % TAU) - Math.PI;
    headYaw += delta * 0.28;
    headGroup.rotation.y = headYaw;

    if (headPulse > 0) headPulse = Math.max(0, headPulse - 0.045);
    var sc = 1 + headPulse * 0.22;
    headGroup.scale.set(sc, sc, sc);

    /* 舌头 */
    var cyc = time % 2.7;
    var ext = cyc < 0.30 ? Math.sin((cyc / 0.30) * Math.PI) : 0;
    tongueGroup.position.z = 0.47 + ext * 0.22;
    tongueGroup.scale.set(1, 1, 0.35 + ext * 1.5);
  }

  /* =========================================================
     食物
     ========================================================= */
  var foodGeoCache = {};

  function buildFoodMesh(type) {
    var g = new THREE.Group();

    if (type === 'apple') {
      var body = new THREE.Mesh(new THREE.SphereGeometry(0.38, 20, 16), MAT.apple);
      body.scale.set(1, 0.95, 1);
      body.position.y = 0.4;
      body.castShadow = true;
      g.add(body);
      var stem = new THREE.Mesh(new THREE.CylinderGeometry(0.032, 0.048, 0.19, 7), MAT.stem);
      stem.position.set(0, 0.79, 0);
      stem.rotation.z = 0.2;
      g.add(stem);
      var leaf = new THREE.Mesh(new THREE.SphereGeometry(0.17, 12, 9), MAT.leaf);
      leaf.scale.set(1.45, 0.28, 0.85);
      leaf.position.set(0.19, 0.8, 0);
      leaf.rotation.z = -0.42;
      g.add(leaf);

    } else if (type === 'star') {
      if (!foodGeoCache.star) {
        var shape = new THREE.Shape();
        var pts = 5, ro = 0.44, rIn = 0.185;
        for (var i = 0; i < pts * 2; i++) {
          var a = (i / (pts * 2)) * TAU - Math.PI / 2;
          var rr = (i % 2) ? rIn : ro;
          var x = Math.cos(a) * rr, y = Math.sin(a) * rr;
          if (i === 0) shape.moveTo(x, y); else shape.lineTo(x, y);
        }
        shape.closePath();
        var eg = new THREE.ExtrudeGeometry(shape, {
          depth: 0.13, bevelEnabled: true, bevelSize: 0.045,
          bevelThickness: 0.045, bevelSegments: 2, curveSegments: 4
        });
        eg.center();
        foodGeoCache.star = eg;
      }
      var star = new THREE.Mesh(foodGeoCache.star, MAT.star);
      star.position.y = 0.62;
      star.castShadow = true;
      g.add(star);

    } else if (type === 'donut') {
      var tor = new THREE.Mesh(new THREE.TorusGeometry(0.31, 0.155, 14, 26), MAT.donut);
      tor.rotation.x = -Math.PI / 2;
      tor.position.y = 0.55;
      tor.castShadow = true;
      g.add(tor);
      var ic = new THREE.Mesh(new THREE.TorusGeometry(0.315, 0.115, 12, 26), MAT.icing);
      ic.rotation.x = -Math.PI / 2;
      ic.position.y = 0.645;
      g.add(ic);
      if (!MAT.sprinkle) {
        MAT.sprinkle = [0xff6b9d, 0x4ecdc4, 0xffd93d, 0x9b7bff, 0x6be07e].map(function (c) {
          return new THREE.MeshLambertMaterial({ color: c });
        });
        foodGeoCache.sprinkle = new THREE.SphereGeometry(0.045, 6, 5);
      }
      for (var si = 0; si < 9; si++) {
        var sa = (si / 9) * TAU;
        var sp = new THREE.Mesh(foodGeoCache.sprinkle, MAT.sprinkle[si % MAT.sprinkle.length]);
        sp.position.set(Math.cos(sa) * 0.315, 0.70, Math.sin(sa) * 0.315);
        sp.scale.set(1.4, 0.7, 1.4);
        g.add(sp);
      }

    } else { /* cherry */
      var cg = new THREE.SphereGeometry(0.215, 16, 13);
      [-1, 1].forEach(function (s) {
        var c = new THREE.Mesh(cg, MAT.cherry);
        c.position.set(0.19 * s, 0.28, 0);
        c.castShadow = true;
        g.add(c);
      });
      var st1 = new THREE.Mesh(new THREE.CylinderGeometry(0.022, 0.022, 0.34, 6), MAT.leaf);
      st1.position.set(0.1, 0.62, 0); st1.rotation.z = 0.34;
      g.add(st1);
      var st2 = new THREE.Mesh(new THREE.CylinderGeometry(0.022, 0.022, 0.34, 6), MAT.leaf);
      st2.position.set(-0.1, 0.62, 0); st2.rotation.z = -0.34;
      g.add(st2);
      var lf = new THREE.Mesh(new THREE.SphereGeometry(0.15, 10, 8), MAT.leaf);
      lf.scale.set(1.5, 0.25, 0.8);
      lf.position.set(0, 0.8, 0);
      g.add(lf);
    }

    /* 地面魔法光圈：淡黄圆盘 + 亮边环，指示位置但不遮挡食物 */
    var disc = new THREE.Mesh(new THREE.CircleGeometry(0.46, 26), MAT.disc);
    disc.rotation.x = -Math.PI / 2;
    disc.position.y = 0.028;
    g.add(disc);

    var ring = new THREE.Mesh(new THREE.RingGeometry(0.50, 0.64, 34), MAT.ring);
    ring.rotation.x = -Math.PI / 2;
    ring.position.y = 0.032;
    g.add(ring);
    g.userData.ring = ring;

    return g;
  }

  var SHARED_GEO = [];
  function disposeGroup(g) {
    g.traverse(function (o) {
      if (o.isMesh && o.geometry) {
        if (SHARED_GEO.indexOf(o.geometry) >= 0) return;
        if (o.geometry === foodGeoCache.star || o.geometry === foodGeoCache.sprinkle) return;
        o.geometry.dispose();
      }
    });
  }

  var FOOD_TYPES = ['apple', 'star', 'donut', 'cherry'];

  function buildFood() {
    if (food.group) {
      scene.remove(food.group);
      disposeGroup(food.group);
      food.group = null;
    }
    food.type = FOOD_TYPES[ri(0, FOOD_TYPES.length - 1)];
    var g = buildFoodMesh(food.type);

    if (food.gold) {
      /* 整颗镀金，并且放大一圈 */
      g.traverse(function (o) {
        if (!o.isMesh) return;
        if (o.material === MAT.glow || o.material === MAT.ring ||
            o.material === MAT.disc || o.material === MAT.gold) return;
        o.material = MAT.gold;
      });
      g.scale.setScalar(1.42);
    } else {
      g.scale.setScalar(1.14);
    }

    g.position.set(gx2w(food.gx), 0.06, gx2w(food.gz));
    scene.add(g);
    food.group = g;
  }

  /* 食物生成：按「环带」抽距离 + 强制远离最近出现过的位置。
     教训：上一版用 pow(rand,2.2) 把距离压得太偏近（44% 落在蛇头 6 格内），
     蛇头一直在动，苹果就永远追在屁股后面，看起来像「总在同一个地方、没有随机」。
     现在两个措施：
     1) 环带（annulus）而不是圆盘 —— 每个距离段内的落点真的落在该段，不会层层叠加偏近；
     2) 排斥最近 FOOD_HIST_N 个食物 —— 同一个角落绝不会连续刷。 */
  var FOOD_BANDS = [
    [3, 7], [5, 10], [8, 14], [11, 18], [14, 24]
  ];
  var FOOD_BAND_W = [0.16, 0.24, 0.26, 0.19, 0.15];
  var FOOD_HIST_N = 6;
  var FOOD_AVOID = [7, 5, 3];   // 排斥半径，逐个放宽，最后不限
  var foodHist = [];

  function pickBand() {
    var r = Math.random(), acc = 0;
    for (var i = 0; i < FOOD_BAND_W.length; i++) {
      acc += FOOD_BAND_W[i];
      if (r <= acc) return i;
    }
    return FOOD_BAND_W.length - 1;
  }

  function farFromHist(x, z, rad) {
    for (var i = 0; i < foodHist.length; i++) {
      var h = foodHist[i];
      if (Math.abs(x - h.x) + Math.abs(z - h.z) < rad) return false;
    }
    return true;
  }

  function placeFood() {
    var occ = {};
    for (var i = 0; i < snake.cells.length; i++) {
      occ[cellKey(snake.cells[i].x, snake.cells[i].z)] = 1;
    }
    /* 怪兽脚下也不放食物，免得孩子为了吃苹果被撞 */
    for (var m = 0; m < monsters.length; m++) {
      occ[cellKey(monsters[m].gx, monsters[m].gz)] = 1;
    }
    var head = snake.cells[0] || { x: MC, z: MC };
    var b0 = pickBand();

    var chosen = null;
    /* 外层：排斥半径从紧到松（最后一轮不排斥）；内层：从抽中的环带向外轮转。
       这样既能保证「离上次远」，又不会因为窄地形某个环带全空而卡死。 */
    for (var pass = 0; pass <= FOOD_AVOID.length && !chosen; pass++) {
      var rad = pass < FOOD_AVOID.length ? FOOD_AVOID[pass] : 0;
      for (var k = 0; k < FOOD_BANDS.length && !chosen; k++) {
        var band = FOOD_BANDS[(b0 + k) % FOOD_BANDS.length];
        var lo = band[0], hi = band[1];
        var list = [];
        for (var z = 0; z < MS; z++) {
          for (var x = 0; x < MS; x++) {
            if (!cellFree(G.cells, x, z)) continue;
            if (occ[cellKey(x, z)]) continue;
            var d = Math.abs(x - head.x) + Math.abs(z - head.z);
            if (d < lo || d > hi) continue;
            if (rad && !farFromHist(x, z, rad)) continue;
            list.push({ x: x, z: z });
          }
        }
        if (list.length) chosen = list[(Math.random() * list.length) | 0];
      }
    }

    /* 兜底：蛇长得几乎铺满、所有环带都挑不出来时，全图任选一个空格 */
    if (!chosen) {
      var all = [];
      for (var z2 = 0; z2 < MS; z2++) {
        for (var x2 = 0; x2 < MS; x2++) {
          if (!cellFree(G.cells, x2, z2)) continue;
          if (occ[cellKey(x2, z2)]) continue;
          all.push({ x: x2, z: z2 });
        }
      }
      if (!all.length) return;
      chosen = all[(Math.random() * all.length) | 0];
    }

    food.gx = chosen.x;
    food.gz = chosen.z;
    /* 每 GOLD_EVERY 口之后的那个是金苹果 */
    food.gold = ((G.eaten + 1) % GOLD_EVERY === 0);

    foodHist.push({ x: chosen.x, z: chosen.z });
    if (foodHist.length > FOOD_HIST_N) foodHist.shift();

    buildFood();
  }

  function updateFood() {
    var g = food.group;
    if (!g) return;
    g.position.y = 0.06 + Math.sin(G.time * 2.3) * 0.05;
    g.rotation.y = G.time * 1.15;
    var ring = g.userData.ring;
    if (ring) {
      var s = 1 + Math.sin(G.time * 3.1) * 0.14;
      ring.scale.setScalar(s);
      ring.rotation.z = G.time * 0.8;
    }
  }

  /* =========================================================
     粒子
     ========================================================= */
  var particles = [];
  var partPool = [];
  var partGeo = null;

  function spawnBurst(x, y, z, colorHex, n) {
    if (!partGeo) partGeo = new THREE.SphereGeometry(0.085, 8, 6);
    /* 护栏：吃得太快时不要无限制堆粒子（每个粒子是一次 draw call） */
    if (particles.length > 260) n = Math.min(n, 4);
    for (var i = 0; i < n; i++) {
      var m = partPool.pop();
      if (!m) {
        m = new THREE.Mesh(partGeo, new THREE.MeshBasicMaterial({ transparent: true }));
      }
      m.material.color.setHex(colorHex);
      m.material.opacity = 1;
      m.material.transparent = true;
      m.position.set(x + rand(-0.12, 0.12), y + rand(-0.1, 0.25), z + rand(-0.12, 0.12));
      m.scale.setScalar(rand(0.6, 1.25));
      m.visible = true;
      scene.add(m);
      var a = rand(0, TAU), sp = rand(2.0, 5.0);
      particles.push({
        m: m, vx: Math.cos(a) * sp, vy: rand(3.2, 7.4), vz: Math.sin(a) * sp,
        life: 0, max: rand(0.45, 0.85),
        spin: rand(-8, 8)
      });
    }
  }

  function updateParticles(dt) {
    for (var i = particles.length - 1; i >= 0; i--) {
      var p = particles[i];
      p.life += dt;
      if (p.life >= p.max) {
        scene.remove(p.m);
        partPool.push(p.m);
        particles.splice(i, 1);
        continue;
      }
      p.vy -= 15 * dt;
      p.m.position.x += p.vx * dt;
      p.m.position.y += p.vy * dt;
      p.m.position.z += p.vz * dt;
      if (p.m.position.y < 0.09) { p.m.position.y = 0.09; p.vy *= -0.42; p.vx *= 0.72; p.vz *= 0.72; }
      p.m.rotation.x += p.spin * dt;
      p.m.rotation.y += p.spin * 0.7 * dt;
      var k = 1 - p.life / p.max;
      p.m.material.opacity = k * k;
      p.m.scale.setScalar(0.35 + k * 1.05);
    }
  }

  /* =========================================================
     怪兽：果冻小怪
     - 在自己的格子网络上巡逻，靠近蛇头时改为追踪
     - 蛇头撞到（或它撞到蛇头）就结束
     ========================================================= */
  var MON = { geoBody: null, geoEye: null, geoPup: null, geoRing: null, geoDisc: null };
  var monsterRoot = null;
  var CHASE_RANGE = 5;          /* 曼哈顿距离小于这个值开始追 */
  var HIT_RADIUS = 0.66;

  function ensureMonsterAssets() {
    if (MON.geoBody) return;
    MON.geoBody = new THREE.SphereGeometry(0.46, 20, 14);
    MON.geoEye = new THREE.SphereGeometry(0.155, 12, 10);
    MON.geoPup = new THREE.SphereGeometry(0.088, 10, 8);
    MON.geoRing = new THREE.RingGeometry(0.50, 0.63, 30);
    MON.geoDisc = new THREE.CircleGeometry(0.50, 26);
  }

  function buildMonsterMesh(colorHex) {
    var g = new THREE.Group();
    var mat = new THREE.MeshPhongMaterial({
      color: colorHex, shininess: 26, specular: 0x2b2b2b,
      emissive: colorHex, emissiveIntensity: 0.10
    });

    var body = new THREE.Mesh(MON.geoBody, mat);
    body.castShadow = true;
    body.receiveShadow = true;
    body.scale.set(1, 0.88, 1);
    g.add(body);

    /* 眼睛朝 +Z，随朝向一起转 */
    [-1, 1].forEach(function (s) {
      var e = new THREE.Mesh(MON.geoEye, MAT.eyeWhite);
      e.position.set(0.180 * s, 0.130, 0.340);
      e.scale.set(1, 1.05, 0.92);
      g.add(e);
      var p = new THREE.Mesh(MON.geoPup, MAT.eyePupil);
      p.position.set(0.190 * s, 0.140, 0.430);
      p.scale.set(1, 1.10, 0.55);
      g.add(p);
    });

    /* 地面警戒圈：让小朋友一眼看到危险范围 */
    var disc = new THREE.Mesh(MON.geoDisc, MAT.dangerDisc);
    disc.rotation.x = -Math.PI / 2;
    g.add(disc);
    var ring = new THREE.Mesh(MON.geoRing, MAT.dangerRing);
    ring.rotation.x = -Math.PI / 2;
    g.add(ring);

    g.userData.body = body;
    g.userData.ring = ring;
    g.userData.disc = disc;
    g.userData.mat = mat;
    return g;
  }

  function disposeMonsters() {
    for (var i = 0; i < monsters.length; i++) {
      var m = monsters[i];
      if (m.group && m.group.userData.mat) m.group.userData.mat.dispose();
    }
    monsters.length = 0;
    if (monsterRoot) {
      scene.remove(monsterRoot);
      monsterRoot = null;
    }
  }

  /* 找一个离蛇头足够远的空位（避开蛇身、其他怪兽、食物点） */
  function findMonsterSpawn(minDist, sep) {
    if (sep === undefined) sep = 3;
    var head = snake.cells[0] || { x: MC, z: MC };
    var occ = {};
    for (var i = 0; i < snake.cells.length; i++) {
      occ[cellKey(snake.cells[i].x, snake.cells[i].z)] = 1;
    }
    for (var m = 0; m < monsters.length; m++) {
      occ[cellKey(monsters[m].gx, monsters[m].gz)] = 1;
    }
    var list = [];
    for (var z = 0; z < MS; z++) {
      for (var x = 0; x < MS; x++) {
        if (!cellFree(G.cells, x, z)) continue;
        if (occ[cellKey(x, z)]) continue;
        var d = Math.abs(x - head.x) + Math.abs(z - head.z);
        if (d < minDist) continue;
        /* 别让两只怪兽叠在一起出生 */
        var tooClose = false;
        if (sep > 0) {
          for (var q = 0; q < monsters.length; q++) {
            if (Math.abs(x - monsters[q].gx) + Math.abs(z - monsters[q].gz) < sep) { tooClose = true; break; }
          }
        }
        if (tooClose) continue;
        list.push({ x: x, z: z });
      }
    }
    if (!list.length) return null;
    return list[Math.floor(Math.random() * list.length)];
  }

  function ensureMonsterRoot() {
    ensureMonsterAssets();
    if (!monsterRoot) {
      monsterRoot = new THREE.Group();
      monsterRoot.name = 'monsters';
      scene.add(monsterRoot);
    }
  }

  /* 造一只怪兽放到场上（开局布阵与中途增援共用） */
  function spawnOneMonster() {
    ensureMonsterRoot();
    /* 出生点离蛇头远一点：地图放大了，起手不该有怪兽杵在正前方跑道上 */
    var minD = Math.max(5, Math.round(MS * 0.4));
    var sp = findMonsterSpawn(minD, 4) || findMonsterSpawn(4, 2) || findMonsterSpawn(1, 0);
    if (!sp) return false;

    var i = monsters.length;
    var color = G.map.monColors[i % G.map.monColors.length];
    var grp = buildMonsterMesh(color);
    monsterRoot.add(grp);

    /* 初始朝向：优先选一个能往前走的反向 */
    var dir = null;
    for (var k = 0; k < 4; k++) {
      var d4 = DIR4[(i + k) % 4];
      if (cellFree(G.cells, sp.x + d4.x, sp.z + d4.z)) { dir = { x: d4.x, z: d4.z }; break; }
    }
    if (!dir) dir = { x: 1, z: 0 };

    monsters.push({
      gx: sp.x, gz: sp.z,
      px: sp.x, pz: sp.z,
      wx: gx2w(sp.x), wz: gx2w(sp.z),
      dir: dir, yaw: Math.atan2(dir.x, dir.z),
      t: 0, dur: Math.max(0.12, G.monDur),
      seed: rand(0, TAU),
      group: grp, color: color
    });
    return true;
  }

  function spawnMonsters() {
    disposeMonsters();
    if (!G.map || !G.map.monsters) return;
    ensureMonsterAssets();
    for (var i = 0; i < G.map.monsters; i++) {
      if (!spawnOneMonster()) break;
    }
    updateMonsterTransforms();
  }

  /* 分数到线了，就多来一只怪兽（一张图最多多一只） */
  function maybeReinforce() {
    if (!G.map || !G.map.monsters) return;
    if (G.reinforced) return;
    var at = REINFORCE_AT[G.diff] || 0;
    if (!at || G.score < at) return;
    var cap = G.map.monsters + (G.map.extraMon || 0);
    if (monsters.length >= cap) return;
    if (!spawnOneMonster()) return;
    G.reinforced = true;
    updateMonsterTransforms();
    updateMapTag();
    toast('又来了一只小怪兽！', 'warn');
    Snd.warn();
  }

  function monsterStep(m) {
    m.px = m.gx; m.pz = m.gz;

    var opts = [];
    for (var i = 0; i < 4; i++) {
      var d = DIR4[i];
      if (d.x === -m.dir.x && d.z === -m.dir.z) continue;   /* 不原地掉头 */
      if (!cellFree(G.cells, m.gx + d.x, m.gz + d.z)) continue;
      opts.push(d);
    }
    if (!opts.length) {                                    /* 死胡同才允许回头 */
      for (var j = 0; j < 4; j++) {
        var dj = DIR4[j];
        if (cellFree(G.cells, m.gx + dj.x, m.gz + dj.z)) opts.push(dj);
      }
    }
    if (!opts.length) return;

    var pick = opts[ri(0, opts.length - 1)];

    /* 靠近蛇头就追：选能缩短距离的方向，但有 28% 概率仍随机走（留出逃生机会） */
    var head = snake.cells[0];
    if (head) {
      var dist = Math.abs(head.x - m.gx) + Math.abs(head.z - m.gz);
      if (dist <= CHASE_RANGE && Math.random() > 0.28) {
        var best = null, bestD = 1e9;
        for (var k = 0; k < opts.length; k++) {
          var nd = Math.abs(head.x - (m.gx + opts[k].x)) + Math.abs(head.z - (m.gz + opts[k].z));
          if (nd < bestD) { bestD = nd; best = opts[k]; }
        }
        if (best) pick = best;
      }
    }

    m.dir = { x: pick.x, z: pick.z };
    m.gx += pick.x;
    m.gz += pick.z;
  }

  function updateMonsters(dt) {
    var live = (G.state === 'playing' || G.state === 'menu') && !G.monFreeze;
    for (var i = 0; i < monsters.length; i++) {
      var m = monsters[i];
      if (live) {
        m.t += dt;
        var guard = 0;
        while (m.t >= m.dur && guard++ < 2) { m.t -= m.dur; monsterStep(m); }
      }
      var k = clamp(m.t / m.dur, 0, 1);
      m.wx = lerp(gx2w(m.px), gx2w(m.gx), k);
      m.wz = lerp(gx2w(m.pz), gx2w(m.gz), k);

      var yawT = Math.atan2(m.dir.x, m.dir.z);
      var dy = ((yawT - m.yaw + Math.PI * 3) % TAU) - Math.PI;
      m.yaw += dy * Math.min(1, dt * 9);
    }
    updateMonsterTransforms();
  }

  function updateMonsterTransforms() {
    for (var i = 0; i < monsters.length; i++) {
      var m = monsters[i];
      var g = m.group;
      if (!g) continue;
      var hop = Math.abs(Math.sin(G.time * 4.2 + m.seed));
      var y = 0.40 + hop * 0.075;
      g.position.set(m.wx, y, m.wz);
      g.rotation.y = m.yaw;

      /* 果冻挤压：只缩放身体，警戒圈保持在水平面 */
      var jig = Math.sin(G.time * 6.6 + m.seed) * 0.10 + hop * 0.05;
      g.userData.body.scale.set(1 - jig * 0.55, 0.88 + jig, 1 - jig * 0.55);

      var rs = 1 + Math.sin(G.time * 3.4 + m.seed) * 0.10;
      g.userData.ring.scale.setScalar(rs);
      g.userData.disc.scale.setScalar(rs);
      g.userData.ring.position.y = 0.030 - y;
      g.userData.disc.position.y = 0.026 - y;
    }
  }

  /* 蛇头与怪兽的距离判定（用插值位置，过门口相遇也算撞上） */
  function checkMonsterHit() {
    if (G.state !== 'playing' || !monsters.length) return;
    if (G.guard > 0) return;
    var h = segPos[0] || { x: gx2w(snake.cells[0].x), z: gx2w(snake.cells[0].z) };
    for (var i = 0; i < monsters.length; i++) {
      var m = monsters[i];
      var dx = m.wx - h.x, dz = m.wz - h.z;
      if (Math.sqrt(dx * dx + dz * dz) < HIT_RADIUS) { die('monster'); return; }
    }
  }

  /* =========================================================
     游戏逻辑
     ========================================================= */
  function resetGame() {
    /* 当前地图的可通行表（按形状复制一份） */
    prepareMap(G.map);
    G.cells = new Uint8Array(G.map.ready);

    var sp = findSpawn(G.cells);
    if (sp) {
      snake.cells = sp.cells.map(function (c) { return { x: c.x, z: c.z }; });
      snake.dir = { x: sp.dir.x, z: sp.dir.z };
    } else {
      snake.cells = [{ x: MC, z: MC }];
      snake.dir = { x: 1, z: 0 };
    }
    snake.prev = snake.cells.map(function (c) { return { x: c.x, z: c.z }; });
    snake.queue = [];
    headYaw = Math.atan2(snake.dir.x, snake.dir.z);
    headPulse = 0;
    lastColorLen = -1;
    segPos.length = 0;

    G.score = 0;
    G.eaten = 0;
    G.stepDur = DIFFS[G.diff].step / (G.map.speedK || 1);
    G.minDur = DIFFS[G.diff].min / (G.map.speedK || 1);
    G.stepT = 0;
    G.tMix = 1;
    G.shake = 0;
    G.dead = 'wall';
    G.reinforced = false;
    G.guard = GUARD_TICKS;

    /* 怪兽节奏跟着难度走：简单档更慢，孩子来得及躲 */
    var k = clamp(G.stepDur / DIFFS.normal.step, 0.80, 1.35);
    G.monDur = G.map.monsters ? (1 / G.map.monSpd) * k : 1;

    spawnMonsters();
    foodHist.length = 0;   // 新的一局，不带着上一局的食物历史做排斥
    placeFood();
    updateHud();
    updateMapTag();
    rebuildMiniMask();
  }

  /* 换地图：重建场地 + 重开一局（菜单里选图时调用） */
  function setMap(id) {
    if (!applyMap(id)) return false;
    loadBest();
    buildArena();
    resetGame();
    saveMapId();
    syncMapUI();
    return true;
  }

  function saveMapId() {
    try { localStorage.setItem('snake3d_map', G.mapId); } catch (e) {}
  }
  function loadMapId() {
    var id = 'classic';
    try {
      var v = localStorage.getItem('snake3d_map');
      if (v) id = v;
    } catch (e) {}
    for (var i = 0; i < MAPS.length; i++) if (MAPS[i].id === id) return id;
    return 'classic';
  }

  function setDir(dx, dz) {
    if (G.state !== 'playing') return;
    var last = snake.queue.length ? snake.queue[snake.queue.length - 1] : snake.dir;
    if (dx === -last.x && dz === -last.z) return;   // 不能 180 度掉头
    if (dx === last.x && dz === last.z) return;     // 同方向忽略
    if (snake.queue.length >= 2) return;
    snake.queue.push({ x: dx, z: dz });
    Snd.turn();
  }

  function stepOnce() {
    if (snake.queue.length) {
      var nd = snake.queue.shift();
      if (!(nd.x === -snake.dir.x && nd.z === -snake.dir.z)) snake.dir = nd;
    }

    var head = snake.cells[0];
    var nx = head.x + snake.dir.x;
    var nz = head.z + snake.dir.z;

    if (!cellFree(G.cells, nx, nz)) { die('wall'); return false; }

    /* 一头撞进怪兽所在的格子（开局保护期内不算） */
    if (G.guard <= 0) {
      for (var q = 0; q < monsters.length; q++) {
        if (monsters[q].gx === nx && monsters[q].gz === nz) { die('monster'); return false; }
      }
    }

    var willGrow = (nx === food.gx && nz === food.gz);
    var limit = willGrow ? snake.cells.length : snake.cells.length - 1;
    for (var i = 0; i < limit; i++) {
      if (snake.cells[i].x === nx && snake.cells[i].z === nz) { die('self'); return false; }
    }

    snake.prev = snake.cells.map(function (c) { return { x: c.x, z: c.z }; });
    snake.cells.unshift({ x: nx, z: nz });
    if (!willGrow) {
      snake.cells.pop();
    } else {
      onEat();
    }
    if (G.guard > 0) G.guard--;
    return true;
  }

  function onEat() {
    var wasGold = food.gold;
    G.score += wasGold ? GOLD_SCORE : BASE_SCORE;
    G.eaten++;

    if (G.eaten % (G.map.accelEvery || 4) === 0) {
      G.stepDur = Math.max(G.minDur, G.stepDur - ACCEL_STEP);
    }

    var h = snake.cells[0];
    var px = gx2w(h.x), pz = gx2w(h.z);
    if (wasGold) {
      spawnBurst(px, 1.0, pz, 0xffd23f, 20);
      spawnBurst(px, 0.9, pz, 0xfff6cc, 10);
      toast('金苹果  +' + GOLD_SCORE, 'gold');
      Snd.gold();
    } else {
      spawnBurst(px, 1.0, pz, 0xffd93d, 13);
      spawnBurst(px, 0.85, pz, 0xffffff, 6);
      Snd.eat();
    }
    headPulse = 1;
    updateHud();
    bumpScore();

    placeFood();
    if (G.score > G.best) {
      G.best = G.score;
      saveBest();
    }

    maybeReinforce();
  }

  function die(type) {
    if (G.state !== 'playing') return;
    G.dead = type;
    G.state = 'over';
    G.shake = 0.62;
    Snd.over();
    flash();
    updateHud();

    var isNew = false;
    if (G.score > 0 && G.score >= G.best) { isNew = true; }
    saveBest();

    setTimeout(function () { showOver(isNew); }, 820);
  }

  /* =========================================================
     主循环
     ========================================================= */
  function update(dt) {
    G.time += dt;

    if (G.state === 'playing') {
      G.stepT += dt;
      var guard = 0;
      while (G.stepT >= G.stepDur && guard++ < 4) {
        var dur = G.stepDur;
        G.stepT -= dur;
        if (!stepOnce()) { G.stepT = 0; break; }
      }
      G.tMix = clamp(G.stepT / G.stepDur, 0, 1);
    }

    layoutSnake();
    renderSnake();
    updateMonsters(dt);
    checkMonsterHit();
    updateFood();
    updateParticles(dt);
    updateCamera(dt, G.time);
    updateDecor(dt);
    if (G.state !== 'menu') { mini.t += dt; drawMini(); }
    updateFoodArrow();
  }

  function updateCamera(dt, time) {
    var hp = segPos.length ? segPos[0] : { x: gx2w(MC), z: gx2w(MC) };
    var k = 1 - Math.pow(0.0009, dt);

    if (G.state === 'menu') {
      /* 菜单：拉远到能看清整张地图，并轻微摆动突出立体感 */
      var ang = Math.sin(time * 0.24) * 0.20;
      var ca = Math.cos(ang), sa = Math.sin(ang);
      v3a.set(camOffMenu.x * ca - camOffMenu.z * sa, camOffMenu.y, camOffMenu.x * sa + camOffMenu.z * ca);
      lookTarget.set(0, 0.35, camMenuLookZ);
    } else {
      /* 游玩 / 暂停 / 结束：跟着蛇头走，但眼界不越出场地边界 */
      var tx = clamp(hp.x, -camLimX, camLimX);
      var tz = clamp(hp.z, camLimZmin, camLimZmax);
      lookTarget.set(tx, 0.35, tz);
      v3a.set(tx + camOffPlay.x, camOffPlay.y, tz + camOffPlay.z);
    }

    camPos.lerp(v3a, k);
    lookTarget.set(lookTarget.x, 0.35, lookTarget.z);
    camLook.lerp(lookTarget, k);
    camera.position.copy(camPos);
    camera.lookAt(camLook);

    /* 阴影相机跟着视野走，否则跑到远处影子会消失 */
    if (sunLight) {
      sunLight.position.set(camLook.x + 12, 24, camLook.z + 14);
      sunLight.target.position.set(camLook.x, 0, camLook.z);
      sunLight.target.updateMatrixWorld();
    }

    if (G.shake > 0.001) {
      G.shake = Math.max(0, G.shake - dt * 1.7);
      var amp = G.shake * G.shake * 1.5;
      camera.position.x += rand(-amp, amp);
      camera.position.y += rand(-amp, amp);
      camera.position.z += rand(-amp, amp);
    }
  }

  /* 相机瞬移到位（开局 / 回菜单时用，避免从上一个位置慢慢飘过去） */
  function snapCameraToHead() {
    var c0 = snake.cells[0] || { x: MC, z: MC };
    var hx = clamp(gx2w(c0.x), -camLimX, camLimX);
    var hz = clamp(gx2w(c0.z), camLimZmin, camLimZmax);
    camPos.set(hx + camOffPlay.x, camOffPlay.y, hz + camOffPlay.z);
    camLook.set(hx, 0.35, hz);
    camera.position.copy(camPos);
    camera.lookAt(camLook);
  }

  function snapCameraToMenu() {
    camPos.copy(camOffMenu);
    camLook.set(0, 0.35, camMenuLookZ);
    camera.position.copy(camPos);
    camera.lookAt(camLook);
  }

  /* =========================================================
     小地图（左下角）
     35×35 之后相机只能看到局部，苹果和怪兽常在视野外，
     没有小地图孩子会以为「场上什么都没有」。
     ========================================================= */
  var mini = { mask: null, t: 0, px: 0 };

  function rebuildMiniMask() {
    var cv = el.mini;
    if (!cv) return;
    /* 4 倍超采样：缩到 92px 时边缘不至于糊成一团 */
    var box = MS * 4;
    var off = document.createElement('canvas');
    off.width = off.height = box;
    var g = off.getContext('2d');
    g.clearRect(0, 0, box, box);
    g.fillStyle = '#54a866';
    for (var z = 0; z < MS; z++) {
      for (var x = 0; x < MS; x++) {
        if (cellFree(G.cells, x, z)) g.fillRect(x * 4, z * 4, 4, 4);
      }
    }
    mini.mask = off;
    mini.t = 1;
    sizeMiniCanvas();
    drawMini();
  }

  /* 画布后备尺寸对齐 devicePixelRatio（别让它停在默认的 300×150） */
  function sizeMiniCanvas() {
    var cv = el.mini;
    if (!cv) return 0;
    var dpr = Math.min(window.devicePixelRatio || 1, 2);
    var css = cv.clientWidth || 92;
    var px = Math.max(32, Math.round(css * dpr));
    if (cv.width !== px) { cv.width = px; cv.height = px; mini.px = 0; }
    return px;
  }

  function drawMini() {
    var cv = el.mini;
    if (!cv || !mini.mask) return;
    var px = sizeMiniCanvas();
    if (!px) return;
    if (mini.px === px && mini.t < 0.1) return;   /* 限流，别每帧重画 */
    mini.px = px;
    mini.t = 0;

    var g = cv.getContext('2d');
    var pad = px * 0.075;
    var box = px - pad * 2;
    var k = box / MS;
    g.clearRect(0, 0, px, px);
    g.drawImage(mini.mask, pad, pad, box, box);
    g.strokeStyle = 'rgba(30, 80, 45, .28)';
    g.lineWidth = Math.max(1, px * 0.014);
    g.strokeRect(pad, pad, box, box);

    /* 蛇身 */
    g.fillStyle = '#d8ffae';
    var r = Math.max(1, k);
    for (var i = snake.cells.length - 1; i >= 0; i--) {
      var c = snake.cells[i];
      g.fillRect(pad + c.x * k, pad + c.z * k, r, r);
    }
    /* 食物：白点 + 红/金描边 + 呼吸光晕（食物可能落到 20 多格外，得让它一眼就跳出来） */
    if (food.gx !== undefined) {
      var fx = pad + (food.gx + 0.5) * k;
      var fz = pad + (food.gz + 0.5) * k;
      var pulse = 0.86 + 0.28 * Math.sin(G.time * 4.2);
      g.beginPath();
      g.arc(fx, fz, Math.max(4.6, k * 2.0) * pulse, 0, TAU);
      g.fillStyle = food.gold ? 'rgba(255,183,3,.34)' : 'rgba(232,69,63,.28)';
      g.fill();
      g.beginPath();
      g.arc(fx, fz, Math.max(3.0, k * 1.2), 0, TAU);
      g.fillStyle = '#ffffff';
      g.fill();
      g.lineWidth = Math.max(1.1, k * 0.48);
      g.strokeStyle = food.gold ? '#ffb703' : '#e8453f';
      g.stroke();
    }
    /* 怪兽：红点 */
    for (var m = 0; m < monsters.length; m++) {
      var mo = monsters[m];
      g.beginPath();
      g.arc(pad + (mo.gx + 0.5) * k, pad + (mo.gz + 0.5) * k, Math.max(2.3, k * 0.92), 0, TAU);
      g.fillStyle = '#ff3b30';
      g.fill();
    }
    /* 蛇头：白圈加深色边，永远最显眼 */
    if (snake.cells.length) {
      var h = snake.cells[0];
      g.beginPath();
      g.arc(pad + (h.x + 0.5) * k, pad + (h.z + 0.5) * k, Math.max(3.3, k * 1.4), 0, TAU);
      g.fillStyle = '#ffffff';
      g.fill();
      g.lineWidth = Math.max(1.2, k * 0.5);
      g.strokeStyle = '#1d7a3f';
      g.stroke();
    }
  }

  /* 食物落到视野外时，在屏幕上给一个指向箭头。
     食物位置随机散开后，经常落在横向视野之外（相机竖屏只显示约 19 列），
     没有指引孩子只会看到一片空草地。 */
  var _fproj = new THREE.Vector3();
  var arrowOn = false;
  function updateFoodArrow() {
    var a = el.foodArrow;
    if (!a) return;
    var hide = G.state === 'menu' || G.state === 'over' || food.gx === undefined;
    if (!hide) {
      var w = window.innerWidth, h = window.innerHeight;
      _fproj.set(gx2w(food.gx), 0.25, gx2w(food.gz)).project(camera);
      var behind = _fproj.z > 1;
      var ndx = behind ? -_fproj.x : _fproj.x;
      var ndy = behind ? -_fproj.y : _fproj.y;
      /* 留出一点边距：贴近屏幕边缘时也算「看不见」，免得箭头和食物一起闪烁 */
      var off = Math.abs(ndx) > 0.88 || Math.abs(ndy) > 0.84;
      if (off) {
        var dx = ndx, dy = -ndy;
        var len = Math.sqrt(dx * dx + dy * dy) || 1;
        dx /= len; dy /= len;
        var R = Math.min(w, h) * 0.30;
        var x = w / 2 + dx * R, y = h / 2 + dy * R;
        var deg = Math.atan2(dy, dx) * 180 / Math.PI + 90;  /* svg 箭头默认朝上 */
        var half = a.offsetWidth ? a.offsetWidth / 2 : 19;
        a.style.transform = 'translate(' + (x - half).toFixed(1) + 'px,' +
          (y - half).toFixed(1) + 'px) rotate(' + deg.toFixed(1) + 'deg)';
        a.classList.toggle('gold', !!food.gold);
        if (!arrowOn) { a.classList.add('show'); arrowOn = true; }
        return;
      }
    }
    if (arrowOn) { a.classList.remove('show'); arrowOn = false; }
  }

  function updateDecor(dt) {
    var t = G.time;
    for (var i = 0; i < decor.butterflies.length; i++) {
      var b = decor.butterflies[i];
      var u = b.userData;
      u.a += u.sp * dt;
      b.position.set(
        Math.cos(u.a) * u.r,
        u.y + Math.sin(t * 1.8 + u.a * 2) * 0.35,
        Math.sin(u.a) * u.r
      );
      b.rotation.y = -u.a + Math.PI / 2;
      var flap = Math.sin(t * 14 + u.a) * 0.62;
      u.wl.rotation.x = flap;
      u.wr.rotation.x = flap;
    }
    if (decor.clouds) {
      decor.clouds.position.x = Math.sin(t * 0.035) * 6;
    }
  }

  /* =========================================================
     相机：二分求「恰好装下 N 格」的距离
     场地从 17×17 放到 35×35，如果还是把整张地图塞进屏幕，手机上每格只剩 11px，
     蛇会变成一个看不清的小点。所以游玩时改为跟随蛇头、只保证「格子看得清」，
     整张地图的方位交给小地图。
     ========================================================= */
  function viewCells() {
    var w = window.innerWidth, h = Math.max(1, window.innerHeight);
    var shortSide = Math.min(w, h);
    /* 让一个格子大约占 TARGET_CELL_PX 个屏幕像素 */
    return clamp(Math.round(shortSide * 0.94 / TARGET_CELL_PX), VIEW_MIN, VIEW_MAX);
  }

  /* 求出「画面窄边恰好看到 span 格」时的相机距离（复用二分投影法，俯角/宽高比自动适配） */
  var _fitP = new THREE.Vector3();
  function solveCamDist(span) {
    var half = span * 0.5 * CELL;
    var lo = 4, hi = 260;
    var corners = [[-1, -1], [1, -1], [-1, 1], [1, 1]];
    for (var it = 0; it < 30; it++) {
      var d = (lo + hi) / 2;
      camera.position.set(0, Math.sin(CAM_ELEV) * d, Math.cos(CAM_ELEV) * d);
      camera.lookAt(0, 0, 0);
      camera.updateMatrixWorld(true);
      camera.matrixWorldInverse.copy(camera.matrixWorld).invert();
      var ok = true;
      for (var c = 0; c < 4; c++) {
        _fitP.set(corners[c][0] * half, 1.05, corners[c][1] * half).project(camera);
        if (Math.abs(_fitP.x) > 0.96 || Math.abs(_fitP.y) > 0.94) { ok = false; break; }
      }
      if (ok) hi = d; else lo = d;
    }
    return hi;
  }

  function fitCamera() {
    var w = window.innerWidth, h = Math.max(1, window.innerHeight);
    camera.aspect = w / h;
    camera.updateProjectionMatrix();

    /* 游玩：窄边看 camViewCells 格；菜单：尽量看到整张地图 */
    camViewCells = viewCells();
    var dPlay = solveCamDist(camViewCells);
    camOffPlay.set(0, Math.sin(CAM_ELEV) * dPlay, Math.cos(CAM_ELEV) * dPlay);

    var shortSide = Math.min(w, h);
    var menuSpan = Math.min(MS + 2, Math.round(shortSide * 0.94 / 18));
    var dMenu = solveCamDist(menuSpan);
    camOffMenu.set(0, Math.sin(CAM_ELEV) * dMenu, Math.cos(CAM_ELEV) * dMenu);
    camMenuLookZ = menuSpan * 0.16;

    measureView();

    /* 允许的注视点偏移：
       视野装得下整个场地 → 固定居中，不乱飘；
       装不下 → 跟着蛇头走，但最多在场地边缘外露 GRASS_MARGIN 格草地，
       这样即使蛇贴到墙边，画面也不会大半张都是草地。 */
    var GRASS = 4;
    camLimX = Math.max(0, WALL + GRASS - camHalfX);
    camLimZmax = Math.max(0, WALL + GRASS - camHalfZNear);
    camLimZmin = Math.min(0, camHalfZFar - WALL - GRASS);

    /* 阴影范围跟着可见范围走：太大影子会糊，太小远处没影子 */
    if (sunLight) {
      var sc = sunLight.shadow.camera;
      var half2 = camViewCells * 0.62 + 4;
      sc.left = -half2; sc.right = half2; sc.top = half2; sc.bottom = -half2;
      sc.near = 2; sc.far = 84;
      sc.updateProjectionMatrix();
    }
  }

  /* 实测「游玩相机在注视点处能看多远」：
     X 半宽（左右）、Z 近侧半深（屏幕下方，朝相机一侧）、Z 远侧半深（屏幕上方）。
     用射线的「屏幕边缘 → 地面 y=0」求交，解析解，不做二分
     （二分会在点越过相机、投影翻转时跑飞）。 */
  var _mv = new THREE.Vector3();
  function measureView() {
    camera.position.copy(camOffPlay);
    camera.lookAt(0, 0.35, 0);
    camera.updateMatrixWorld(true);
    camera.matrixWorldInverse.copy(camera.matrixWorld).invert();

    /* 以注视点为原点的地面交点（相机在 (+z, +y) 一侧） */
    var ground = function (nx, ny) {
      _mv.set(nx, ny, 0.5).unproject(camera).sub(camera.position).normalize();
      if (_mv.y >= -1e-4) return null;                    /* 朝上/水平：打不到地面 */
      var t = -camera.position.y / _mv.y;
      return { x: camera.position.x + _mv.x * t, z: camera.position.z + _mv.z * t };
    };

    var near = ground(0, -0.94);      /* 屏幕下方 = 靠近相机的一侧 */
    var far = ground(0, 0.94);        /* 屏幕上方 = 远端（可能直接看到地平线） */
    var right = ground(0.95, 0);

    camHalfZNear = near ? Math.max(1, near.z) : 20;
    camHalfZFar = far ? Math.max(1, -far.z) : 300;
    camHalfX = right ? Math.max(1, right.x) : 20;
  }

  /* =========================================================
     界面
     ========================================================= */
  var el = {};

  function cacheEls() {
    el.menu = document.getElementById('menu');
    el.pause = document.getElementById('pause');
    el.over = document.getElementById('over');
    el.hud = document.getElementById('hud');
    el.score = document.getElementById('score');
    el.best = document.getElementById('best');
    el.chipScore = document.getElementById('chipScore');
    el.statScore = document.getElementById('statScore');
    el.statBest = document.getElementById('statBest');
    el.newBest = document.getElementById('newBest');
    el.overTitle = document.getElementById('overTitle');
    el.overSub = document.getElementById('overSub');
    el.btnSound = document.getElementById('btnSound');
    el.icoOn = document.getElementById('icoSoundOn');
    el.icoOff = document.getElementById('icoSoundOff');
    el.maps = document.getElementById('maps');
    el.mini = document.getElementById('mini');
    el.foodArrow = document.getElementById('foodArrow');
    el.mapNote = document.getElementById('mapNote');
    el.mapTag = document.getElementById('mapTag');
    el.toast = document.getElementById('toast');
  }

  function updateHud() {
    el.score.textContent = G.score;
    el.best.textContent = G.best;
  }

  function updateMapTag() {
    if (!el.mapTag) return;
    var n = Math.max(monsters.length, G.map.monsters);
    el.mapTag.textContent = G.map.name + (n ? ' · ' + n + ' 怪兽' : ' · 无怪兽');
  }

  /* 用可通行表直接画一张迷你形状图，保证和真实场地完全一致。
     35×35 逐格会生成上千个 <rect>，所以按行做游程合并（连续的可通行格并成一条）。 */
  function mapSvg(m) {
    var c = m.ready || m.cells;
    var g = 100 / MS;
    /* 每条矩形多画 0.08，盖住相邻条之间的抗锯齿接缝（否则缩略图会布满细纹） */
    var OV = 0.08;
    var s = '<svg viewBox="0 0 100 100" shape-rendering="crispEdges" aria-hidden="true">';
    for (var z = 0; z < MS; z++) {
      var x = 0;
      while (x < MS) {
        if (!cellFree(c, x, z)) { x++; continue; }
        var x0 = x;
        while (x < MS && cellFree(c, x, z)) x++;
        s += '<rect x="' + (x0 * g).toFixed(2) + '" y="' + (z * g).toFixed(2) +
          '" width="' + (((x - x0) * g) + OV).toFixed(2) +
          '" height="' + (g + OV).toFixed(2) + '"/>';
      }
    }
    return s + '</svg>';
  }

  function buildMapUI() {
    if (!el.maps) return;
    var html = '';
    for (var i = 0; i < MAPS.length; i++) {
      var m = MAPS[i];
      prepareMap(m);
      html += '<button class="mapcard" data-map="' + m.id + '" type="button">' +
        '<span class="mpv">' + mapSvg(m) + '</span>' +
        '<span class="mpn">' + m.name + '</span></button>';
    }
    el.maps.innerHTML = html;

    var cards = el.maps.querySelectorAll('.mapcard');
    for (var k = 0; k < cards.length; k++) {
      (function (btn) {
        btn.addEventListener('click', function () {
          if (G.state === 'playing' || G.state === 'paused') return;
          if (btn.getAttribute('data-map') === G.mapId) return;
          setMap(btn.getAttribute('data-map'));
        });
      })(cards[k]);
    }
    syncMapUI();
  }

  function syncMapUI() {
    if (el.maps) {
      var cards = el.maps.querySelectorAll('.mapcard');
      for (var i = 0; i < cards.length; i++) {
        cards[i].classList.toggle('active', cards[i].getAttribute('data-map') === G.mapId);
      }
    }
    if (el.mapNote) el.mapNote.textContent = G.map.note;
    updateMapTag();
  }

  function bumpScore() {
    el.chipScore.classList.remove('bump');
    void el.chipScore.offsetWidth;
    el.chipScore.classList.add('bump');
  }

  /* 屏幕中间的短提示：金苹果、怪兽增援 */
  var toastTimer = null;
  function toast(text, kind) {
    var t = el.toast;
    if (!t) return;
    t.textContent = text;
    t.className = 't-' + (kind || 'info');
    void t.offsetWidth;
    t.classList.add('show');
    if (toastTimer) clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { t.classList.remove('show'); }, 1600);
  }

  function flash() {
    var f = document.createElement('div');
    f.style.cssText = 'position:fixed;inset:0;z-index:15;pointer-events:none;' +
      'background:radial-gradient(circle at 50% 50%, rgba(255,90,90,0.05), rgba(255,60,60,0.55));' +
      'opacity:0;transition:opacity .06s';
    document.body.appendChild(f);
    requestAnimationFrame(function () { f.style.opacity = '1'; });
    setTimeout(function () {
      f.style.transition = 'opacity .55s';
      f.style.opacity = '0';
    }, 110);
    setTimeout(function () {
      if (f.parentNode) f.parentNode.removeChild(f);
    }, 800);
  }

  /* 最高分按地图分别记：每张图的难度差别很大，混在一起不公平 */
  function bestKey() { return 'snake3d_best_' + G.mapId; }

  function saveBest() {
    try { localStorage.setItem(bestKey(), String(G.best)); } catch (e) {}
  }
  function loadBest() {
    var v = 0;
    try {
      var raw = localStorage.getItem(bestKey());
      /* 经典方形兼容旧版的存档键 */
      if (raw === null && G.mapId === 'classic') raw = localStorage.getItem('snake3d_best');
      v = parseInt(raw || '0', 10);
    } catch (e) { v = 0; }
    G.best = isNaN(v) ? 0 : v;
  }

  function startGame() {
    Snd.init();
    Snd.resume();
    Snd.startMusic();
    Snd.start();

    resetGame();
    el.menu.classList.add('hidden');
    el.over.classList.add('hidden');
    el.pause.classList.add('hidden');
    el.hud.classList.add('show');
    G.state = 'playing';
    /* 相机立刻归位到蛇头，避免从菜单摆动角度慢慢飘过来 */
    snapCameraToHead();
  }

  function pauseGame() {
    if (G.state !== 'playing') return;
    G.state = 'paused';
    el.hud.classList.remove('show');
    el.pause.classList.remove('hidden');
  }

  function resumeGame() {
    if (G.state !== 'paused') return;
    G.state = 'playing';
    el.pause.classList.add('hidden');
    el.hud.classList.add('show');
    Snd.resume();
  }

  function toMenu() {
    G.state = 'menu';
    el.pause.classList.add('hidden');
    el.over.classList.add('hidden');
    el.hud.classList.remove('show');
    el.menu.classList.remove('hidden');
    resetGame();
  }

  function showOver(isNew) {
    if (G.state !== 'over') return;
    el.statScore.textContent = G.score;
    el.statBest.textContent = G.best;
    el.newBest.classList.toggle('show', !!isNew);
    el.hud.classList.remove('show');
    if (G.dead === 'wall') {
      el.overTitle.textContent = '哎呀，撞到墙了';
      el.overSub.textContent = '下次记得提前转弯哦';
    } else if (G.dead === 'monster') {
      el.overTitle.textContent = '被小怪兽碰到了';
      el.overSub.textContent = '看到红色圈圈要绕开哦';
    } else {
      el.overTitle.textContent = '哎呀，吃到自己了';
      el.overSub.textContent = '身体越长，越要小心呀';
    }
    el.over.classList.remove('hidden');
  }

  /* ---------------- 事件 ---------------- */
  function bindEvents() {
    /* 难度选择 */
    var pills = document.querySelectorAll('.pill');
    for (var i = 0; i < pills.length; i++) {
      (function (btn) {
        btn.addEventListener('click', function () {
          for (var k = 0; k < pills.length; k++) pills[k].classList.remove('active');
          btn.classList.add('active');
          G.diff = btn.getAttribute('data-diff');
        });
      })(pills[i]);
    }

    document.getElementById('btnStart').addEventListener('click', startGame);
    document.getElementById('btnRetry').addEventListener('click', startGame);
    document.getElementById('btnHome').addEventListener('click', toMenu);
    document.getElementById('btnQuit').addEventListener('click', toMenu);
    document.getElementById('btnResume').addEventListener('click', resumeGame);
    document.getElementById('btnPause').addEventListener('click', function () {
      if (G.state === 'playing') pauseGame();
      else if (G.state === 'paused') resumeGame();
    });
    el.btnSound.addEventListener('click', function () {
      G.soundOn = !G.soundOn;
      el.icoOn.style.display = G.soundOn ? '' : 'none';
      el.icoOff.style.display = G.soundOn ? 'none' : '';
      if (!G.soundOn) { Snd.stopMusic(); }
      else { Snd.resume(); if (G.state === 'playing') { Snd.timer = null; Snd.startMusic(); } }
    });

    /* 键盘 */
    window.addEventListener('keydown', function (e) {
      var k = e.key;
      if (k === 'ArrowUp' || k === 'w' || k === 'W') { setDir(0, -1); e.preventDefault(); }
      else if (k === 'ArrowDown' || k === 's' || k === 'S') { setDir(0, 1); e.preventDefault(); }
      else if (k === 'ArrowLeft' || k === 'a' || k === 'A') { setDir(-1, 0); e.preventDefault(); }
      else if (k === 'ArrowRight' || k === 'd' || k === 'D') { setDir(1, 0); e.preventDefault(); }
      else if (k === ' ' || k === 'Escape' || k === 'p' || k === 'P') {
        e.preventDefault();
        if (G.state === 'playing') pauseGame();
        else if (G.state === 'paused') resumeGame();
      }
      else if (k === 'Enter') {
        if (G.state === 'menu' || G.state === 'over') { e.preventDefault(); startGame(); }
      }
    }, { passive: false });

    /* 触摸滑动 */
    var startPt = null;
    canvas.addEventListener('touchstart', function (e) {
      if (e.touches.length > 1) { e.preventDefault(); return; }
      startPt = { x: e.touches[0].clientX, y: e.touches[0].clientY };
    }, { passive: false });

    canvas.addEventListener('touchmove', function (e) {
      if (e.touches.length > 1) e.preventDefault();
    }, { passive: false });

    canvas.addEventListener('touchend', function (e) {
      if (!startPt) return;
      var t = e.changedTouches[0];
      var dx = t.clientX - startPt.x;
      var dy = t.clientY - startPt.y;
      startPt = null;
      if (Math.sqrt(dx * dx + dy * dy) < 22) return;
      if (Math.abs(dx) > Math.abs(dy)) setDir(dx > 0 ? 1 : -1, 0);
      else setDir(0, dy > 0 ? 1 : -1);
    });

    /* 方向按钮 */
    var dpads = document.querySelectorAll('.dpad');
    var MAP = { u: [0, -1], d: [0, 1], l: [-1, 0], r: [1, 0] };
    for (var j = 0; j < dpads.length; j++) {
      (function (btn) {
        var d = btn.getAttribute('data-d');
        btn.addEventListener('pointerdown', function (e) {
          e.preventDefault();
          setDir(MAP[d][0], MAP[d][1]);
          btn.classList.add('on');
          setTimeout(function () { btn.classList.remove('on'); }, 110);
        });
      })(dpads[j]);
    }

    /* 尺寸变化（防抖，避免 iOS 软键盘抖动） */
    var rzTimer = null;
    function onResize() {
      if (rzTimer) clearTimeout(rzTimer);
      rzTimer = setTimeout(applySize, 180);
    }
    window.addEventListener('resize', onResize);
    window.addEventListener('orientationchange', onResize);

    /* 页面隐藏时自动暂停 */
    document.addEventListener('visibilitychange', function () {
      if (document.hidden && G.state === 'playing') pauseGame();
    });

    /* 阻止 iOS 双指缩放与手势 */
    document.addEventListener('gesturestart', function (e) { e.preventDefault(); }, { passive: false });
    document.addEventListener('dblclick', function (e) { e.preventDefault(); }, { passive: false });
  }

  function applySize() {
    var w = window.innerWidth, h = Math.max(1, window.innerHeight);
    renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
    renderer.setSize(w, h, false);
    fitCamera();
    /* 菜单态直接归位；游玩态交给插值平滑过渡，避免手机地址栏收起时画面跳一下 */
    if (G.state === 'menu') snapCameraToMenu();
    rebuildMiniMask();
  }

  /* =========================================================
     启动
     ========================================================= */
  function boot() {
    renderer = new THREE.WebGLRenderer({
      canvas: canvas, antialias: true, alpha: false, powerPreference: 'high-performance'
    });
    renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
    renderer.setSize(window.innerWidth, window.innerHeight, false);
    renderer.shadowMap.enabled = true;
    renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    renderer.outputColorSpace = THREE.SRGBColorSpace;

    scene = new THREE.Scene();
    scene.fog = new THREE.Fog(0xcde9f8, 92, 230);
    scene.background = null;

    camera = new THREE.PerspectiveCamera(50, window.innerWidth / window.innerHeight, 0.2, 420);

    /* 灯光（r155+ 物理光照单位，强度需比旧版明显更高） */
    scene.add(new THREE.HemisphereLight(0xd8f0ff, 0x7dc455, 1.18));
    scene.add(new THREE.AmbientLight(0xffffff, 0.26));

    sunLight = new THREE.DirectionalLight(0xfff8e8, 1.95);
    sunLight.position.set(14, 24, 16);
    sunLight.castShadow = true;
    sunLight.shadow.mapSize.set(2048, 2048);
    var sc = sunLight.shadow.camera;
    sc.left = -16; sc.right = 16; sc.top = 16; sc.bottom = -16;
    sc.near = 2; sc.far = 78;
    sunLight.shadow.bias = -0.0004;
    sunLight.shadow.normalBias = 0.006;
    scene.add(sunLight);
    scene.add(sunLight.target);
    sunLight.target.position.set(0, 0, 0);

    initMaterials();
    buildSky();
    fitCamera();          /* 先算出相机距离，树木分布据此自适应 */
    applyMap(loadMapId());
    buildWorld();
    buildSnake();

    clock = new THREE.Clock();
    cacheEls();
    buildMapUI();
    bindEvents();
    loadBest();
    updateHud();

    /* 触屏设备显示方向键 */
    var coarse = false;
    try { coarse = window.matchMedia('(pointer: coarse)').matches; } catch (e) { coarse = false; }
    if (coarse || /Android|iPhone|iPad|iPod|Mobile/i.test(navigator.userAgent)) {
      document.body.classList.add('touch');
    }

    applySize();
    resetGame();
    G.state = 'menu';

    loop();
    window.SNAKE.ready = true;

    var bootEl = document.getElementById('boot');
    if (bootEl) {
      bootEl.classList.add('done');
      setTimeout(function () {
        if (bootEl.parentNode) bootEl.parentNode.removeChild(bootEl);
      }, 600);
    }
  }

  function loop() {
    requestAnimationFrame(loop);
    var dt = Math.min(clock.getDelta(), 0.1);
    update(dt);
    renderer.render(scene, camera);
  }

  /* =========================================================
     调试接口（自动化验收用）
     ========================================================= */
  window.SNAKE = {
    errs: errors,
    ready: false,
    get state() { return G.state; },
    get score() { return G.score; },
    get best() { return G.best; },
    get len() { return snake.cells.length; },
    get head() { return { x: snake.cells[0].x, z: snake.cells[0].z }; },
    get dir() { return { x: snake.dir.x, z: snake.dir.z }; },
    get foodCell() { return { gx: food.gx, gz: food.gz }; },
    get foodGold() { return !!food.gold; },
    get foodScale() { return food.group ? +food.group.scale.x.toFixed(3) : 0; },
    get reinforced() { return G.reinforced; },
    get stepDur() { return G.stepDur; },
    get tMix() { return G.tMix; },
    get mapId() { return G.mapId; },
    get mapName() { return G.map.name; },
    get monsterCount() { return monsters.length; },
    get dead() { return G.dead; },

    maps: function () {
      return MAPS.map(function (m) {
        return { id: m.id, name: m.name, monsters: m.monsters, speedK: m.speedK, free: m.freeCount };
      });
    },
    mapInfo: function () {
      return {
        id: G.mapId, name: G.map.name, monsters: G.map.monsters,
        ms: MS, free: G.map.freeCount, total: MS * MS,
        cells: Array.prototype.slice.call(G.cells)
      };
    },
    isFree: function (x, z) { return cellFree(G.cells, x, z); },
    setMap: function (id) {
      if (G.state === 'playing' || G.state === 'paused') toMenu();
      return setMap(id);
    },
    monsters: function () {
      return monsters.map(function (m) {
        return {
          gx: m.gx, gz: m.gz, x: +m.wx.toFixed(3), z: +m.wz.toFixed(3),
          dir: { x: m.dir.x, z: m.dir.z }
        };
      });
    },
    freezeMonsters: function (v) {
      G.monFreeze = v !== false;
      return G.monFreeze;
    },
    /* 提前结束开局保护（测试"蛇真的会撞死"时用） */
    clearGuard: function () { G.guard = 0; return G.guard; },
    /* 把第 i 只怪兽直接摆到某格（测试碰撞用） */
    putMonster: function (i, x, z) {
      var m = monsters[i];
      if (!m) return null;
      m.gx = m.px = x; m.gz = m.pz = z;
      m.wx = gx2w(x); m.wz = gx2w(z);
      m.t = 0;
      updateMonsterTransforms();
      return { gx: m.gx, gz: m.gz };
    },
    /* 确定性驱动：直接推进怪兽 n 步（路径合法性测试用） */
    stepMonsters: function (n) {
      var trace = [];
      for (var k = 0; k < (n || 1); k++) {
        for (var i = 0; i < monsters.length; i++) monsterStep(monsters[i]);
        for (var j = 0; j < monsters.length; j++) trace.push({ x: monsters[j].gx, z: monsters[j].gz });
      }
      updateMonsterTransforms();
      return trace;
    },
    clearMonsters: function () {
      disposeMonsters();
      return monsters.length;
    },
    addMonster: function (x, z) {
      ensureMonsterAssets();
      /* 落到墙里就修正到最近的可通行格，避免怪兽卡死不动 */
      if (!cellFree(G.cells, x, z)) {
        var best = null, bestD = 1e9;
        for (var zz = 0; zz < MS; zz++) {
          for (var xx = 0; xx < MS; xx++) {
            if (!cellFree(G.cells, xx, zz)) continue;
            var dd = Math.abs(xx - x) + Math.abs(zz - z);
            if (dd < bestD) { bestD = dd; best = { x: xx, z: zz }; }
          }
        }
        if (best) { x = best.x; z = best.z; }
      }
      if (!monsterRoot) {
        monsterRoot = new THREE.Group();
        monsterRoot.name = 'monsters';
        scene.add(monsterRoot);
      }
      var grp = buildMonsterMesh(0xa06be0);
      monsterRoot.add(grp);
      monsters.push({
        gx: x, gz: z, px: x, pz: z, wx: gx2w(x), wz: gx2w(z),
        dir: { x: 1, z: 0 }, yaw: Math.PI / 2, t: 0,
        dur: Math.max(0.12, G.monDur), seed: 0, group: grp, color: 0xa06be0
      });
      updateMonsterTransforms();
      return monsters.length;
    },

    stats: function () {
      return {
        state: G.state,
        map: G.mapId,
        score: G.score,
        best: G.best,
        dead: G.dead,
        len: snake.cells.length,
        head: { x: snake.cells[0].x, z: snake.cells[0].z },
        dir: { x: snake.dir.x, z: snake.dir.z },
        food: { gx: food.gx, gz: food.gz, gold: !!food.gold },
        stepDur: +G.stepDur.toFixed(4),
        minDur: +G.minDur.toFixed(4),
        monsters: monsters.length,
        reinforced: G.reinforced,
        reinforceAt: REINFORCE_AT[G.diff] || 0,
        guard: G.guard,
        guardTicks: GUARD_TICKS,
        monsterPos: monsters.map(function (m) { return { x: m.gx, z: m.gz }; }),
        cam: {
          x: +camera.position.x.toFixed(2),
          y: +camera.position.y.toFixed(2),
          z: +camera.position.z.toFixed(2)
        },
        viewCells: camViewCells,
        view: {
          cells: camViewCells,
          halfX: +camHalfX.toFixed(1),
          halfZn: +camHalfZNear.toFixed(1),
          halfZf: +camHalfZFar.toFixed(1),
          limX: +camLimX.toFixed(1),
          limZmin: +camLimZmin.toFixed(1),
          limZmax: +camLimZmax.toFixed(1),
          dist: +camOffPlay.length().toFixed(1)
        },
        look: { x: +camLook.x.toFixed(2), z: +camLook.z.toFixed(2) },
        mini: {
          on: !!el.mini,
          w: el.mini ? el.mini.width : 0,
          h: el.mini ? el.mini.height : 0
        },
        tris: renderer.info.render.triangles,
        calls: renderer.info.render.calls,
        geo: renderer.info.memory.geometries,
        tex: renderer.info.memory.textures,
        particles: particles.length,
        errs: errors.slice()
      };
    },

    setDir: setDir,
    start: function (d) {
      if (d) {
        G.diff = d;
        var pills = document.querySelectorAll('.pill');
        for (var i = 0; i < pills.length; i++) {
          pills[i].classList.toggle('active', pills[i].getAttribute('data-diff') === d);
        }
      }
      startGame();
      return G.state;
    },
    pause: pauseGame,
    resume: resumeGame,
    menu: toMenu,
    forceFood: function (x, z) {
      if (food.gx === x && food.gz === z && food.group) return { gx: food.gx, gz: food.gz };
      food.gx = x; food.gz = z; buildFood();
      return { gx: food.gx, gz: food.gz };
    },
    /* 重新抽一颗食物（测试用：连续调用即可采样分布） */
    regenFood: function () { placeFood(); return { gx: food.gx, gz: food.gz }; },
    foodHistory: function () { return foodHist.slice(); },
    resetFoodHistory: function () { foodHist.length = 0; return foodHist.length; },
    setCells: function (arr, dx, dz) {
      snake.cells = arr.map(function (c) { return { x: c[0], z: c[1] }; });
      snake.prev = snake.cells.map(function (c) { return { x: c.x, z: c.z }; });
      snake.dir = { x: dx || 0, z: dz || 0 };
      snake.queue = [];
      headYaw = Math.atan2(snake.dir.x, snake.dir.z);
      lastColorLen = -1;
      return snake.cells.length;
    },
    step: function () { return G.state === 'playing' ? stepOnce() : false; },
    setStepDur: function (v) { G.stepDur = v; return G.stepDur; },
    setScore: function (v) { G.score = v; updateHud(); return G.score; },
    /* 让下一颗食物变成金苹果 / 恢复普通（测试用） */
    setFoodGold: function (v) { food.gold = !!v; buildFood(); return food.gold; },
    audio: function () {
      return { ctx: Snd.ctx ? Snd.ctx.state : null, ok: Snd.ok, music: !!Snd.timer, on: G.soundOn };
    },
    placeHead: function (x, z, dx, dz) {
      snake.cells = [{ x: x, z: z }];
      for (var i = 1; i < 3; i++) snake.cells.push({ x: x - (dx || 1) * i, z: z - (dz || 0) * i });
      snake.prev = snake.cells.map(function (c) { return { x: c.x, z: c.z }; });
      snake.dir = { x: dx || 1, z: dz || 0 };
      snake.queue = [];
      lastColorLen = -1;
      return snake.cells[0];
    },
    cells: function () {
      return snake.cells.map(function (c) { return { x: c.x, z: c.z }; });
    },
    scene: function () { return scene; },
    camera: function () { return camera; },
    renderer: function () { return renderer; }
  };

  /* 启动 */
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', boot);
  } else {
    boot();
  }
})();
