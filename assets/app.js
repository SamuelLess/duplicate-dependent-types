// the list of duplicate groups (window.GROUPS) with search, filters and sorting, and one group's
// view; `#<id>` shows a group, any other hash is the list's state
(function () {
  var D = window.GROUPS || [], META = window.META || {};
  function esc(s) { return String(s).replace(/[&<>"]/g, function (c) { return {'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;'}[c]; }); }
  function $(id) { return document.getElementById(id); }

  $('theme').addEventListener('click', function () {
    var t = document.documentElement.getAttribute('data-theme') === 'light' ? 'dark' : 'light';
    document.documentElement.setAttribute('data-theme', t);
    try { localStorage.setItem('theme', t); } catch (e) {}
  });

  // Lean source → spans: k keyword, t term keyword, tc tactic, hl a member of the group, c/d comment,
  // s string, n number, a attribute, o operator
  var KW = words('theorem lemma def abbrev instance example structure class inductive where extends deriving namespace section end open variable universe import noncomputable private protected partial unsafe mutual set_option attribute local scoped macro syntax macro_rules elab notation infix infixl infixr prefix postfix alias export termination_by decreasing_by opaque axiom omit include in');
  var TERM = words('fun λ by have show from let if then else match with do at calc return for suffices obtain nomatch nofun Type Prop Sort');
  var TAC = words("exact exacts intro intros apply refine refine' rw rwa rewrite simp simp_all simpa dsimp norm_num omega decide rfl cases rcases induction use constructor ext funext subst congr gcongr linarith nlinarith positivity ring ring_nf field_simp aesop tauto trivial assumption contradiction exfalso by_contra by_cases split_ifs split left right exists existsi specialize generalize revert clear rename_i unfold change convert apply_fun push_neg push_cast norm_cast exact_mod_cast infer_instance first try repeat all_goals any_goals case next nth_rewrite nth_rw symm trans grind bv_decide fin_cases interval_cases filter_upwards refine_lift simp_rw simp? exact? mono continuity measurability fun_prop injection show_term subst_vars cases' induction' rintro");
  var TOKEN = /(--.*)|("(?:[^"\\]|\\.)*")|('(?:[^'\\]|\\.)')|(@\[)|(\b\d+(?:\.\d+)?\b)|([A-Za-z_À-ɏͰ-Ͽἀ-῿℀-⅏\u{1d400}-\u{1d7ff}«][\p{L}\p{N}_'!?À-ɏͰ-Ͽἀ-῿₀-ₜ℀-⅏\u{1d400}-\u{1d7ff}₀-₉ᵢ-ᵪ.»«]*)|(:=|=>|<;>|[←→↔∀∃λ⟨⟩▸∘⁻¹≤≥≠∈∉⊆⊂∩∪×·•∣¬∧∨⊤⊥]|<->|->|<-)/uy;
  var CLS = [null, 'c', 's', 's', 'a', 'n', null, 'o'];
  function words(s) { var o = {}; s.split(' ').forEach(function (w) { o[w] = 1; }); return o; }
  function span(c, s) { return c ? '<span class="' + c + '">' + esc(s) + '</span>' : esc(s); }
  function highlight(code, names) {
    var out = '', i = 0, n = code.length;
    while (i < n) {
      if (code.startsWith('/-', i)) {
        var d = 1, j = i + 2;
        while (j < n && d) {
          if (code.startsWith('/-', j)) { d++; j += 2; } else if (code.startsWith('-/', j)) { d--; j += 2; } else j++;
        }
        out += span(code.startsWith('/--', i) || code.startsWith('/-!', i) ? 'd' : 'c', code.slice(i, j));
        i = j; continue;
      }
      TOKEN.lastIndex = i;
      var m = TOKEN.exec(code);
      if (!m) { var ch = String.fromCodePoint(code.codePointAt(i)); out += esc(ch); i += ch.length; continue; }
      var g = m.findIndex(function (x, k) { return k > 0 && x !== undefined; }), tok = m[0];
      if (g === 4) { var e = code.indexOf(']', i); e = e < 0 ? n : e + 1; out += span('a', code.slice(i, e)); i = e; continue; }
      if (g === 6) {
        out += span(KW[tok] ? 'k' : TERM[tok] ? 't' : TAC[tok] ? 'tc' :
          names.some(function (x) { return x === tok || x.endsWith('.' + tok); }) ? 'hl' : null, tok);
      } else out += span(CLS[g], tok);
      i += tok.length;
    }
    return out;
  }

  // the header
  var title = 'Duplicate theorems' + (META.project ? ' in ' + META.project : '');
  $('title').textContent = title;
  function rev(name, rev, url) {
    var c = '<code>' + esc(rev) + '</code>';
    return esc(name) + ' ' + (url ? '<a href="' + esc(url) + '">' + c + '</a>' : c);
  }
  $('versions').innerHTML = [rev('Lean', 'v' + META.lean, 'https://github.com/leanprover/lean4/tree/v' + META.lean)].concat(
    (META.versions || []).map(function (v) {
      return rev(v.name, v.rev.slice(0, 7), v.url ? v.url.replace(/\.git$/, '') + '/tree/' + v.rev : '');
    })).concat([esc(META.analysed.toLocaleString('en-US')) + ' of ' +
      esc(META.extracted.toLocaleString('en-US')) + ' theorems compared']).join('\n· ');

  // the list
  var byId = {};
  D.forEach(function (c) { byId[c.id] = c; });
  var pks = Object.keys(D.reduce(function (o, c) { o[c.pk] = 1; return o; }, {})).sort(function (x, y) {
    return x.split('↔').length - y.split('↔').length || (x.indexOf('core') === 0 ? 0 : 1) - (y.indexOf('core') === 0 ? 0 : 1) || (x < y ? -1 : x > y ? 1 : 0);
  });
  $('f-pk').innerHTML += pks.map(function (p) { return '<option>' + esc(p) + '</option>'; }).join('');
  // tw: probable API pairs are hidden by default (the hash then says tw=0)
  var F, shown = 100, rows = [], listHash = '';
  var ids = ['pk', 'loc', 'sk', 'tr', 'u'], sortK, sortDir;
  var tb = document.querySelector('#cls tbody');
  function readHash(h) {
    F = {q: '', pk: '', loc: '', sk: '', tr: '', u: '', tw: true}; sortK = 'r'; sortDir = 1;
    decodeURIComponent(h.slice(1)).split('&').forEach(function (kv) {
      var i = kv.indexOf('='); if (i < 0) return;
      var k = kv.slice(0, i), v = kv.slice(i + 1);
      if (k === 'sort') { sortK = v.replace(/^-/, ''); sortDir = v[0] === '-' ? -1 : 1; }
      else if (k === 'tw') F.tw = v === '1'; else if (k in F) F[k] = v;
    });
  }
  function writeHash() {
    var p = [];
    Object.keys(F).forEach(function (k) { if (k !== 'tw' && F[k]) p.push(k + '=' + F[k]); });
    if (!F.tw) p.push('tw=0');
    if (sortK !== 'r' || sortDir !== 1) p.push('sort=' + (sortDir < 0 ? '-' : '') + sortK);
    listHash = p.length ? '#' + encodeURIComponent(p.join('&')) : '';
    history.replaceState(null, '', listHash || location.pathname + location.search);
  }
  function match(c) {
    var hay = (c.a + ' ' + c.b + ' ' + c.m.join(' ')).toLowerCase();
    return !(F.tw && c.tw) && F.q.toLowerCase().split(/\s+/).every(function (w) { return hay.indexOf(w) >= 0; }) &&
      ids.every(function (k) { return !F[k] || (k === 'sk' ? c.sk.indexOf(F.sk) >= 0 : c[k] === F[k]); });
  }
  var SK = {'same': 'syntactically equal', 'defeq': 'definitionally equal', 'not defeq': 'up to isomorphism'};
  // columns with a natural order sort by it, most interesting first; the default
  // order is triviality, then location, then usage, then the rank
  var ORD = {tr: ['substantive', 'some trivial', 'all trivial'],
    loc: ['cross-area', 'cross-package', 'cross-file', 'same file'],
    u: ['all used', 'one side unused', 'none used']};
  var DEFAULT = ['tr', 'loc', 'u'];
  function key(c, k) { var v = c[k]; return ORD[k] ? ORD[k].indexOf(v) : Array.isArray(v) ? v.join(',') : v; }
  function cmpBy(k, x, y) { var a = key(x, k), b = key(y, k); return a < b ? -1 : a > b ? 1 : 0; }
  function cmpDefault(x, y) {
    for (var i = 0; i < DEFAULT.length; i++) { var d = cmpBy(DEFAULT[i], x, y); if (d) return d; }
    return x.r - y.r;
  }
  function filterSort() {
    rows = D.filter(match);
    rows.sort(function (x, y) { return sortK === 'r' ? cmpDefault(x, y) : cmpBy(sortK, x, y) * sortDir || cmpDefault(x, y); });
  }
  function row(c) {
    return '<tr data-id="' + esc(c.id) + '"><td><a href="#' + esc(c.id) + '"><code>' + esc(c.a) + '</code></a><br><code>' + esc(c.b) + '</code>' +
      (c.n > 2 ? ' <span class="more">+' + (c.n - 2) + ' more</span>' : '') +
      '<span class="meta">' + esc(c.m.join(' · ')) + '</span></td>' +
      '<td>' + c.sk.map(function (g) { return '<span class="pill ' + g.replace(' ', '') + '">' + esc(SK[g] || g) + '</span>'; }).join(' ') + '</td>' +
      '<td>' + esc(c.loc) + '</td><td>' + esc(c.pk) + '</td><td>' + esc(c.tr) + '</td><td>' + esc(c.u) + '</td></tr>';
  }
  function render() {
    filterSort();
    tb.innerHTML = rows.slice(0, shown).map(row).join('');
    document.querySelectorAll('#cls th').forEach(function (th) {
      th.classList.remove('asc', 'desc');
      if (th.getAttribute('data-k') === sortK) th.classList.add(sortDir > 0 ? 'asc' : 'desc');
    });
    $('count').textContent = rows.length + ' of ' + D.length + ' groups' + (rows.length > shown ? ' · showing ' + shown : '');
    $('more').hidden = rows.length <= shown;
    document.title = title;
    writeHash();
  }
  function sync() {
    $('q').value = F.q;
    ids.forEach(function (k) { $('f-' + k).value = F[k]; });
    $('f-tw').checked = F.tw;
  }
  var timer = null;
  $('q').addEventListener('input', function (e) {
    clearTimeout(timer); timer = setTimeout(function () { F.q = e.target.value.trim(); shown = 100; render(); }, 120);
  });
  ids.forEach(function (k) {
    $('f-' + k).addEventListener('change', function (e) { F[k] = e.target.value; shown = 100; render(); });
  });
  $('f-tw').addEventListener('change', function (e) { F.tw = e.target.checked; shown = 100; render(); });
  $('reset').addEventListener('click', function () { readHash(''); shown = 100; sync(); render(); });
  document.querySelectorAll('#cls th').forEach(function (th) {
    th.addEventListener('click', function () {
      var k = th.getAttribute('data-k');
      if (sortK === k) sortDir = -sortDir; else { sortK = k; sortDir = 1; }
      render();
    });
  });
  tb.addEventListener('click', function (e) {
    if (e.target.closest('a')) return;
    var tr = e.target.closest('tr'); if (tr) location.hash = tr.getAttribute('data-id');
  });
  $('more').addEventListener('click', function () { shown += 300; render(); });

  // one group: the independent proofs with statement and source, then the other members
  function link(m) {
    if (m.url) return m.url;
    var f = m.file.charAt(0) === '/' ? m.file : META.root + '/' + m.file;
    return 'vscode://file' + encodeURI(f) + ':' + m.line;
  }
  function source(m, names) {
    return m.src.split('\n').map(function (l, k) {
      var n = m.from + k;
      return '<span class="ln ' + (n >= m.line && n <= m.end ? 'in' : 'ctx') + '" data-n="' + n + '">' + highlight(l, names) + '</span>';
    }).join('');
  }
  function view(id) {
    var c = byId[id], out = $('out');
    window.scrollTo(0, 0);
    $('back').href = listHash || '#';
    if (!c) { out.innerHTML = '<p class="muted">No such duplicate. <a href="#">Browse all</a>.</p>'; return; }
    var i = rows.map(function (r) { return r.id; }).indexOf(id);
    [['prev', i - 1], ['next', i + 1]].forEach(function (p) {
      var a = $(p[0]);
      if (i >= 0 && p[1] >= 0 && p[1] < rows.length) { a.href = '#' + rows[p[1]].id; a.classList.remove('off'); }
      else a.classList.add('off');
    });
    var all = c.members.map(function (m) { return m.name; });
    var ind = c.members.filter(function (m) { return !m.dep; }), also = c.members.filter(function (m) { return m.dep; });
    var html = ind.map(function (m) {
      return '<section class="proof"><h3><code>' + esc(m.name) + '</code></h3>' +
        (m.file ? '<p class="facts"><a href="' + esc(link(m)) + '">' + esc(m.module + ':' + m.line) + '</a></p>' : '') +
        '<div class="label">statement</div><pre class="code sig">' + highlight(m.sig, all) + '</pre>' +
        (m.file ? '<div class="label">source</div><pre class="code src">' + source(m, all) + '</pre>' : '') + '</section>';
    }).join('');
    if (also.length) html += '<p class="also">Also in this group, not proved independently:</p><ul class="also">' + also.map(function (m) {
      return '<li><code>' + esc(m.name) + '</code> <span class="muted">(' + esc(m.dep) + ')</span></li>';
    }).join('') + '</ul>';
    document.title = ind[0].name + ' · duplicate-dependent-types';
    out.innerHTML = '<h1>' + ind.map(function (m) { return '<code>' + esc(m.name) + '</code>'; }).join('<br>') + '</h1>' + html;
  }

  function route() {
    var id = decodeURIComponent(location.hash.slice(1)), isView = /^\d+$/.test(id);
    $('list').hidden = isView; $('view').hidden = !isView;
    if (isView) { if (!F) { readHash(''); filterSort(); } view(id); }
    else { readHash(location.hash); shown = 100; sync(); render(); }
  }
  window.addEventListener('hashchange', route);
  route();
})();
