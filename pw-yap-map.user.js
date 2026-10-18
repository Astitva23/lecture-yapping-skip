// ==UserScript==
// @name         PW Yap Map (community)
// @namespace    local
// @version      1.0
// @description  Community-marked "yapping" regions on the PW player seek bar
// @match        *://*.pw.live/*
// @grant        GM_xmlhttpRequest
// @grant        GM_getValue
// @grant        GM_setValue
// @connect      firestore.googleapis.com
// @connect      identitytoolkit.googleapis.com
// @connect      securetoken.googleapis.com
// ==/UserScript==

(function () {
  'use strict';

  // ---------- CONFIG (fill in from your Firebase project settings) ----------
  const CFG = {
    apiKey: 'AIzaSyAjLZDqrOx74GG4nShSZRLsE5q805K3Bf4',
    projectId: 'rababa-10bc5',
  };
  const BIN = 10;              // seconds per vote bucket
  const MIN_VOTERS = 3;        // community map appears once this many people have marked
  const SHOW_RATIO = 0.5;      // share of contributors who must mark a bucket for it to turn red
  const MIN_RUN_S = 20;        // ignore red regions shorter than this
  const REFRESH_MS = 3 * 60 * 1000;
  const SYNC_DELAY_MS = 3000;
  const MAX_TRANSFORMS = 400;  // Firestore limit is 500 per commit

  const DB = `projects/${CFG.projectId}/databases/(default)/documents`;
  const BASE = `https://firestore.googleapis.com/v1/${DB}`;

  // ---------- state ----------
  let lid = null;
  let agg = { voters: 0, yap: {} };
  let runs = [];
  let myBins = new Set();
  let syncedBins = new Set();
  let undoStack = [];
  let markStart = null;
  let autoSkip = false;
  let syncTimer = null;
  let syncing = false;
  let pendingSync = false;
  let panel = null;

  const getVideo = () => document.querySelector('video');
  const getHolder = () => document.querySelector('.vjs-progress-holder');

  const fmt = (s) => {
    s = Math.floor(s);
    const h = Math.floor(s / 3600);
    const m = Math.floor((s % 3600) / 60);
    const x = String(s % 60).padStart(2, '0');
    return h ? `${h}:${String(m).padStart(2, '0')}:${x}` : `${m}:${x}`;
  };

  // The lecture is identified by query params (the path is always /watch/)
  function getKey() {
    const p = new URLSearchParams(location.search);
    return p.get('scheduleId') || p.get('childId') || null;
  }

  // ---------- network ----------
  function http(method, url, { headers = {}, body } = {}) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method,
        url,
        headers,
        data: body,
        timeout: 20000,
        onload: (r) => resolve({ status: r.status, text: r.responseText }),
        onerror: () => reject(new Error('network error')),
        ontimeout: () => reject(new Error('timeout')),
      });
    });
  }

  // Anonymous Firebase auth via REST; the identity is kept in Tampermonkey storage
  async function getAuth() {
    let a = GM_getValue('auth', null);
    const now = Date.now();
    if (a && a.exp > now + 60000) return a;
    if (a && a.refreshToken) {
      const r = await http('POST', `https://securetoken.googleapis.com/v1/token?key=${CFG.apiKey}`, {
        headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
        body: `grant_type=refresh_token&refresh_token=${encodeURIComponent(a.refreshToken)}`,
      });
      if (r.status === 200) {
        const j = JSON.parse(r.text);
        a = {
          uid: j.user_id,
          idToken: j.id_token,
          refreshToken: j.refresh_token,
          exp: now + Number(j.expires_in) * 1000,
        };
        GM_setValue('auth', a);
        return a;
      }
    }
    const r = await http('POST', `https://identitytoolkit.googleapis.com/v1/accounts:signUp?key=${CFG.apiKey}`, {
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify({ returnSecureToken: true }),
    });
    if (r.status !== 200) throw new Error('auth failed: ' + r.text.slice(0, 200));
    const j = JSON.parse(r.text);
    a = {
      uid: j.localId,
      idToken: j.idToken,
      refreshToken: j.refreshToken,
      exp: now + Number(j.expiresIn) * 1000,
    };
    GM_setValue('auth', a);
    return a;
  }

  async function fsGet(path) {
    const a = await getAuth();
    const r = await http('GET', `${BASE}/${path}`, { headers: { Authorization: `Bearer ${a.idToken}` } });
    if (r.status === 404) return null;
    if (r.status !== 200) throw new Error(`read ${path}: ${r.status}`);
    return JSON.parse(r.text).fields || {};
  }

  async function fsCommit(writes) {
    const a = await getAuth();
    const r = await http('POST', `https://firestore.googleapis.com/v1/${DB}:commit`, {
      headers: { Authorization: `Bearer ${a.idToken}`, 'Content-Type': 'application/json' },
      body: JSON.stringify({ writes }),
    });
    if (r.status !== 200) throw new Error(`commit: ${r.status} ${r.text.slice(0, 200)}`);
  }

  function parseAgg(f) {
    if (!f) return { voters: 0, yap: {} };
    const voters = Number(f.voters?.integerValue || 0);
    const yap = {};
    const m = f.yap?.mapValue?.fields || {};
    for (const k in m) yap[k.slice(1)] = Number(m[k].integerValue || 0); // "b12" -> "12"
    return { voters, yap };
  }

  // ---------- buckets and consensus ----------
  function binsFromRange(a, b) {
    const s = new Set();
    const from = Math.floor(a / BIN);
    const to = Math.max(from, Math.ceil(b / BIN) - 1);
    for (let i = from; i <= to; i++) s.add(i);
    return s;
  }

  function binRuns(set) {
    const arr = [...set].sort((x, y) => x - y);
    const out = [];
    for (const b of arr) {
      const last = out[out.length - 1];
      if (last && b === last[1] + 1) last[1] = b;
      else out.push([b, b]);
    }
    return out;
  }

  function computeRuns() {
    runs = [];
    const v = getVideo();
    if (!v || !isFinite(v.duration) || !v.duration || agg.voters < MIN_VOTERS) return;
    const n = Math.ceil(v.duration / BIN);
    let start = null;
    let sum = 0;
    let cnt = 0;
    const close = (endBin) => {
      const s = start * BIN;
      const e = Math.min(endBin * BIN, v.duration);
      if (e - s >= MIN_RUN_S) runs.push({ start: s, end: e, strength: sum / cnt });
      start = null;
      sum = 0;
      cnt = 0;
    };
    for (let i = 0; i < n; i++) {
      const ratio = Math.min(1, (agg.yap[i] || 0) / agg.voters);
      if (ratio >= SHOW_RATIO) {
        if (start === null) start = i;
        sum += ratio;
        cnt++;
      } else if (start !== null) {
        close(i);
      }
    }
    if (start !== null) close(n);
  }

  // ---------- seek bar rendering ----------
  function seg(cls, s, e, css) {
    const v = getVideo();
    const d = document.createElement('div');
    d.className = 'pwy ' + cls;
    d.style.cssText =
      `position:absolute;pointer-events:none;z-index:1;` +
      `left:${(s / v.duration) * 100}%;width:${((e - s) / v.duration) * 100}%;${css}`;
    return d;
  }

  function render() {
    const v = getVideo();
    const h = getHolder();
    if (!v || !h || !isFinite(v.duration) || !v.duration) return;
    h.querySelectorAll('.pwy').forEach((e) => e.remove());
    for (const r of runs) {
      const a = 0.35 + 0.5 * Math.min(1, r.strength);
      h.appendChild(seg('c', r.start, r.end, `top:0;height:100%;background:rgba(255,40,40,${a});`));
    }
    // your own marks: yellow strip along the bottom of the bar
    for (const [a, b] of binRuns(myBins)) {
      h.appendChild(
        seg('m', a * BIN, Math.min((b + 1) * BIN, v.duration), 'bottom:0;height:35%;background:rgba(255,205,0,.95);')
      );
    }
    updatePanel();
  }

  // ---------- panel ----------
  function setStatus(msg) {
    const el = panel && panel.querySelector('.pwy-status');
    if (el) el.textContent = msg;
  }

  function updatePanel() {
    if (!panel) return;
    const info = panel.querySelector('.pwy-info');
    const people = `${agg.voters} contributor${agg.voters === 1 ? '' : 's'}`;
    info.textContent =
      agg.voters < MIN_VOTERS
        ? `Yap Map: ${people} (map shows at ${MIN_VOTERS})`
        : `Yap Map: ${people}, ${runs.length} yap region${runs.length === 1 ? '' : 's'}`;
    panel.querySelector('.pwy-mark').textContent = markStart === null ? 'Mark yap (Y)' : 'End mark (Y)';
    panel.querySelector('.pwy-auto').textContent = `Auto-skip: ${autoSkip ? 'on' : 'off'}`;
  }

  function ensurePanel() {
    const v = getVideo();
    if (!v) return;
    const root = v.closest('.video-js') || document.body;
    if (panel && panel.isConnected && panel.parentElement === root) return;
    if (panel) panel.remove();
    panel = document.createElement('div');
    panel.style.cssText =
      'position:absolute;top:8px;left:8px;z-index:2147483000;font:12px/1.4 system-ui,sans-serif;' +
      'color:#fff;background:rgba(0,0,0,.65);padding:6px 8px;border-radius:8px;opacity:.35;' +
      'transition:opacity .2s;max-width:360px;';
    panel.innerHTML =
      '<div class="pwy-info"></div>' +
      '<div class="pwy-row" style="display:flex;gap:4px;flex-wrap:wrap;margin-top:4px"></div>' +
      '<div class="pwy-status" style="margin-top:4px;opacity:.85"></div>';
    panel.onmouseenter = () => (panel.style.opacity = '1');
    panel.onmouseleave = () => (panel.style.opacity = '.35');
    ['click', 'mousedown', 'touchstart', 'dblclick'].forEach((ev) =>
      panel.addEventListener(ev, (e) => e.stopPropagation())
    );
    const row = panel.querySelector('.pwy-row');
    const btn = (label, cls, fn) => {
      const b = document.createElement('button');
      b.textContent = label;
      b.className = cls;
      b.style.cssText =
        'font:inherit;color:#fff;background:#444;border:1px solid #666;border-radius:6px;padding:2px 6px;cursor:pointer;';
      b.onclick = fn;
      row.appendChild(b);
    };
    btn('Mark yap (Y)', 'pwy-mark', toggleMark);
    btn('Skip yap (N)', 'pwy-skip', skipYap);
    btn('Auto-skip: off', 'pwy-auto', () => {
      autoSkip = !autoSkip;
      updatePanel();
    });
    btn('Undo', 'pwy-undo', undoMark);
    btn('Clear mine', 'pwy-clear', clearMine);
    root.appendChild(panel);
    updatePanel();
  }

  // ---------- marking ----------
  function toggleMark() {
    const v = getVideo();
    if (!v || !lid) return setStatus('No lecture ID found in the URL.');
    if (markStart === null) {
      markStart = v.currentTime;
      setStatus(`Marking since ${fmt(markStart)}... press Y when the yapping ends`);
    } else {
      let a = markStart;
      let b = v.currentTime;
      markStart = null;
      if (b < a) [a, b] = [b, a];
      if (b - a < 3) {
        setStatus('Mark too short, ignored.');
      } else {
        const fresh = [...binsFromRange(a, b)].filter((x) => !myBins.has(x));
        fresh.forEach((x) => myBins.add(x));
        if (fresh.length) undoStack.push(fresh);
        setStatus(`Marked ${fmt(a)} to ${fmt(b)}. Saving...`);
        scheduleSync();
      }
    }
    render();
  }

  function undoMark() {
    const last = undoStack.pop();
    if (!last) return setStatus('Nothing to undo this session.');
    last.forEach((x) => myBins.delete(x));
    setStatus('Last mark removed. Saving...');
    scheduleSync();
    render();
  }

  function clearMine() {
    if (!myBins.size) return;
    if (!confirm('Remove all of your marks for this lecture?')) return;
    myBins.clear();
    undoStack = [];
    setStatus('Your marks cleared. Saving...');
    scheduleSync();
    render();
  }

  function skipYap() {
    const v = getVideo();
    if (!v) return;
    const t = v.currentTime;
    const r = runs.find((x) => t >= x.start && t < x.end);
    if (r) {
      v.currentTime = r.end;
      setStatus(`Skipped ${fmt(r.start)} to ${fmt(r.end)}`);
    } else {
      setStatus('Not inside a community yap region.');
    }
  }

  // ---------- sync ----------
  function scheduleSync(delay = SYNC_DELAY_MS) {
    pendingSync = true;
    clearTimeout(syncTimer);
    syncTimer = setTimeout(syncMarks, delay);
  }

  async function syncMarks() {
    if (!lid) return;
    if (syncing) return scheduleSync(2000);
    pendingSync = false;
    syncing = true;
    try {
      const next = new Set(myBins);
      const prev = syncedBins;
      const added = [...next].filter((b) => !prev.has(b));
      const removed = [...prev].filter((b) => !next.has(b));
      if (!added.length && !removed.length) return;

      const a = await getAuth();
      const transforms = [
        ...added.map((b) => ({ fieldPath: `yap.b${b}`, increment: { integerValue: '1' } })),
        ...removed.map((b) => ({ fieldPath: `yap.b${b}`, increment: { integerValue: '-1' } })),
      ];
      const voterDelta = prev.size === 0 && next.size > 0 ? 1 : prev.size > 0 && next.size === 0 ? -1 : 0;
      if (voterDelta) transforms.push({ fieldPath: 'voters', increment: { integerValue: String(voterDelta) } });

      const aggName = `${DB}/lectures/${lid}`;
      const voteWrite = {
        update: {
          name: `${DB}/lectures/${lid}/votes/${a.uid}`,
          fields: { bins: { arrayValue: { values: [...next].map((b) => ({ integerValue: String(b) })) } } },
        },
      };
      for (let i = 0; i * MAX_TRANSFORMS < transforms.length; i++) {
        const writes = [];
        if (i === 0) writes.push(voteWrite);
        writes.push({
          update: { name: aggName, fields: {} },
          updateMask: { fieldPaths: [] },
          updateTransforms: transforms.slice(i * MAX_TRANSFORMS, (i + 1) * MAX_TRANSFORMS),
        });
        await fsCommit(writes);
      }
      syncedBins = next;
      setStatus('Saved. Thanks for contributing!');
      await refreshAgg();
    } catch (e) {
      console.warn('[Yap] sync failed', e);
      setStatus('Save failed, retrying shortly...');
      scheduleSync(15000);
    } finally {
      syncing = false;
    }
  }

  // ---------- loading ----------
  async function refreshAgg() {
    if (!lid) return;
    try {
      agg = parseAgg(await fsGet(`lectures/${lid}`));
      computeRuns();
      render();
    } catch (e) {
      console.warn('[Yap] refresh failed', e);
    }
  }

  async function startLecture(key) {
    if (pendingSync) {
      try {
        await syncMarks();
      } catch (e) {
        /* ignore */
      }
    }
    lid = key;
    agg = { voters: 0, yap: {} };
    runs = [];
    myBins = new Set();
    syncedBins = new Set();
    undoStack = [];
    markStart = null;
    render();
    if (!key) return setStatus('No lecture ID found in the URL.');
    try {
      const a = await getAuth();
      const [aggF, voteF] = await Promise.all([fsGet(`lectures/${key}`), fsGet(`lectures/${key}/votes/${a.uid}`)]);
      if (lid !== key) return; // navigated away meanwhile
      agg = parseAgg(aggF);
      const mine = (voteF?.bins?.arrayValue?.values || []).map((v) => Number(v.integerValue));
      myBins = new Set(mine);
      syncedBins = new Set(mine);
      computeRuns();
      render();
      setStatus('Ready. Press Y to start/end a yap mark.');
    } catch (e) {
      console.warn('[Yap] load failed', e);
      setStatus('Could not load (check Firebase config / rules).');
    }
  }

  // ---------- events ----------
  let hooked = null;
  function hookVideo() {
    const v = getVideo();
    if (!v || hooked === v) return;
    hooked = v;
    v.addEventListener('durationchange', () => {
      computeRuns();
      render();
    });
    v.addEventListener('timeupdate', () => {
      if (markStart !== null) setStatus(`Marking since ${fmt(markStart)}... press Y when the yapping ends`);
      if (!autoSkip) return;
      const t = v.currentTime;
      const r = runs.find((x) => t >= x.start && t < x.end - 0.5);
      if (r) {
        v.currentTime = r.end;
        setStatus(`Skipped yap ${fmt(r.start)} to ${fmt(r.end)}`);
      }
    });
  }

  window.addEventListener(
    'keydown',
    (e) => {
      if (e.ctrlKey || e.metaKey || e.altKey) return;
      const t = e.target;
      if (t && (t.tagName === 'INPUT' || t.tagName === 'TEXTAREA' || t.isContentEditable)) return;
      if (e.key === 'y' || e.key === 'Y') {
        e.preventDefault();
        toggleMark();
      } else if (e.key === 'n' || e.key === 'N') {
        e.preventDefault();
        skipYap();
      }
    },
    true
  );

  window.addEventListener('pagehide', () => {
    if (pendingSync) syncMarks();
  });

  setInterval(() => {
    if (!getVideo()) return;
    hookVideo();
    ensurePanel();
    const key = getKey();
    if (key !== lid) startLecture(key);
    const h = getHolder();
    if (h && !h.querySelector('.pwy') && (runs.length || myBins.size)) render();
  }, 2000);

  setInterval(refreshAgg, REFRESH_MS);
})();
