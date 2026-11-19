/* Hard Proof study page. Zdog draws the two padlocks of the gap example. The page has no other script:
   each chart is HTML that site/build_page.py writes from the data files. */
(function () {
  'use strict';
  var css = getComputedStyle(document.documentElement);
  var C = {
    ink: css.getPropertyValue('--ink').trim() || '#ece8de',
    gold: css.getPropertyValue('--gold').trim() || '#c9a95c',
    goldHi: css.getPropertyValue('--gold-hi').trim() || '#ecd391',
    goldDeep: css.getPropertyValue('--gold-deep').trim() || '#8a6d34'
  };
  var still = window.matchMedia('(prefers-reduced-motion: reduce)').matches;

  function ease(t) { return 1 - Math.pow(1 - t, 4); }
  /* The one timing helper. Calls step(0..1) each frame, then done(). */
  function run(ms, step, done) {
    if (still) { step(1); if (done) done(); return; }
    var t0 = performance.now();
    function frame(now) {
      var t = Math.min(1, (now - t0) / ms);
      step(ease(t));
      if (t < 1) requestAnimationFrame(frame); else if (done) done();
    }
    requestAnimationFrame(frame);
  }
  function wait(ms, fn) { setTimeout(fn, still ? 0 : ms); }
  function onView(el, fn) {
    if (!el) return;
    if (!('IntersectionObserver' in window)) { fn(); return; }
    var io = new IntersectionObserver(function (entries) {
      entries.forEach(function (e) { if (e.isIntersecting) { io.disconnect(); fn(); } });
    }, { threshold: 0.35 });
    io.observe(el);
  }
  function $(id) { return document.getElementById(id); }

  /* ---------- Zdog padlock ---------- */
  function makeLock(canvas, zoom) {
    if (!canvas || !window.Zdog) return null;
    var Z = window.Zdog;
    var illo = new Z.Illustration({ element: canvas, zoom: zoom || 1.6, rotate: { x: -0.18, y: -0.5 } });
    var body = new Z.Box({ addTo: illo, width: 78, height: 62, depth: 26, translate: { y: 26 }, stroke: 6,
      color: C.gold, leftFace: C.goldDeep, rightFace: C.goldDeep, topFace: C.goldHi, bottomFace: C.goldDeep,
      frontFace: C.gold, rearFace: C.goldDeep });
    new Z.Ellipse({ addTo: body, diameter: 14, translate: { y: -6, z: 16 }, stroke: 4, color: '#17130a', fill: true });
    new Z.Rect({ addTo: body, width: 4, height: 16, translate: { y: 8, z: 16 }, stroke: 4, color: '#17130a', fill: true });
    var hinge = new Z.Anchor({ addTo: illo, translate: { x: -24, y: -6 } });
    new Z.Shape({ addTo: hinge, translate: { x: 24 }, stroke: 11, color: C.ink, closed: false, fill: false,
      path: [{ x: -24, y: 4 }, { x: -24, y: -22 }, { arc: [{ x: -24, y: -48 }, { x: 0, y: -48 }] },
        { arc: [{ x: 24, y: -48 }, { x: 24, y: -22 }] }, { x: 24, y: 4 }] });
    var open = 0, sway = Math.random() * 6, visible = false, raf = 0;
    function draw() {
      hinge.translate.y = -6 - 18 * open;
      hinge.rotate.z = -0.62 * open;
      illo.rotate.y = -0.5 + (still ? 0 : Math.sin(sway) * 0.16);
      illo.updateRenderGraph();
    }
    function loop() {
      sway += 0.02; draw();
      raf = visible && !still ? requestAnimationFrame(loop) : 0;
    }
    if ('IntersectionObserver' in window) {
      new IntersectionObserver(function (entries) {
        visible = entries[0].isIntersecting;
        if (visible && !raf) loop();
      }).observe(canvas);
    } else { visible = true; loop(); }
    draw();
    return {
      setOpen: function (target, instant) {
        var from = open;
        if (instant) { open = target ? 1 : 0; draw(); return; }
        run(700, function (t) { open = from + ((target ? 1 : 0) - from) * t; draw(); });
      }
    };
  }

  /* ---------- The gap example: two lock designs on one trace ---------- */
  function duel() {
    var a = makeLock($('hp-lock-a'), 1.25), b = makeLock($('hp-lock-b'), 1.25);
    var steps = [
      { ev: 'spawn 1', a: false, b: false, sa: 'free', sb: 'free' },
      { ev: 'acquire 1', a: true, b: true, sa: 'held by process 1', sb: 'held by process 1' },
      { ev: 'release 1', a: false, b: true, sa: 'free', sb: 'held by process 1' }
    ];
    var chips = document.querySelectorAll('#hp-trace span');
    var stA = $('hp-state-a'), stB = $('hp-state-b'), verdict = $('hp-verdict');
    var btn = $('hp-step'), reset = $('hp-reset');
    var i = 0;
    function show(state, held) { return held ? 'Lock: <b>' + state + '</b>' : 'Lock: ' + state; }
    function paint(instant) {
      chips.forEach(function (c, k) {
        c.classList.toggle('is-done', k < i - 1);
        c.classList.toggle('is-now', k === i - 1);
      });
      var s = i === 0 ? { a: false, b: false, sa: 'free', sb: 'free' } : steps[i - 1];
      if (a) a.setOpen(!s.a, instant);
      if (b) b.setOpen(!s.b, instant);
      if (stA) stA.innerHTML = show(s.sa, s.a);
      if (stB) stB.innerHTML = show(s.sb, s.b);
      if (verdict) verdict.classList.toggle('is-on', i === steps.length);
      if (btn) { btn.disabled = i === steps.length; btn.textContent = i === steps.length ? 'End of trace' : 'Next event: ' + steps[i].ev; }
    }
    if (btn) btn.addEventListener('click', function () { if (i < steps.length) { i++; paint(false); } });
    if (reset) reset.addEventListener('click', function () { i = 0; paint(false); });
    paint(true);
    var auto = $('hp-duel');
    onView(auto, function () {
      if (still) return;
      function next() { if (i < steps.length) { i++; paint(false); wait(1500, next); } }
      wait(700, next);
    });
  }

  function start() { duel(); }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start); else start();
})();
