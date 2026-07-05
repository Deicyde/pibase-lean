#!/usr/bin/env python3
"""
build_review_pibase.py — human review UI over the felixpernegger/pibase-lean
formalization. For each formalized property / theorem it shows the informal
π-Base statement beside the Lean definition/proof from that repo, so a human can
check faithfulness at a glance. Reuses the WikiLean review aesthetic.

Reads:  the pi-base data blob (informal statements) + a checkout of
        felixpernegger/pibase-lean (the Lean).
Writes: <out>/index.html
"""
import html
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PIBASE_DATA = "/Users/jack/Desktop/LEAN/pi-base-lean/data/pibase.json"
FELIX = os.environ.get("FELIX_REPO", "/Users/jack/Desktop/LEAN/pibase-lean")
OUT = os.path.join(FELIX, "site", "index.html")
PIBASE = "https://topology.pi-base.org"
GH = "https://github.com/Deicyde/pibase-lean/blob/add-counterexample-spaces"

# ---------- Lean syntax highlighting (VS Code Light+ token classes) ----------
KEYWORDS = {
    "import", "module", "public", "open", "namespace", "end", "section",
    "variable", "abbrev", "def", "theorem", "lemma", "instance", "example",
    "structure", "class", "where", "fun", "by", "do", "let", "have", "show",
    "from", "intro", "intros", "exact", "refine", "apply", "rw", "simp",
    "rcases", "obtain", "constructor", "cases", "induction", "at", "with",
    "deriving", "opaque", "attribute", "convert", "refine'", "sorry",
}


def lean_html(code):
    out, i, n = [], 0, len(code)
    esc = html.escape
    while i < n:
        if code[i:i + 2] == "/-":
            # consume a whole (possibly nested) block comment in one shot
            j, d = i + 2, 1
            while j < n and d > 0:
                if code[j:j + 2] == "/-":
                    d += 1; j += 2
                elif code[j:j + 2] == "-/":
                    d -= 1; j += 2
                else:
                    j += 1
            out.append(f'<span class="c1">{esc(code[i:j])}</span>'); i = j; continue
        if code[i:i + 2] == "--":
            j = code.find("\n", i)
            j = n if j == -1 else j
            out.append(f'<span class="c1">{esc(code[i:j])}</span>'); i = j; continue
        if code[i] == '"':
            j = i + 1
            while j < n and code[j] != '"':
                j += 1
            out.append(f'<span class="s">{esc(code[i:j + 1])}</span>'); i = j + 1; continue
        m = re.match(r"[A-Za-z_][A-Za-z0-9_\.\'ₙ]*", code[i:])
        if m:
            w = m.group(0)
            cls = "kn" if w in KEYWORDS else ("kt" if w[0].isupper() else "nf")
            out.append(f'<span class="{cls}">{esc(w)}</span>'); i += len(w); continue
        if code[i].isdigit():
            m = re.match(r"\d+", code[i:])
            if m:
                out.append(f'<span class="mi">{esc(m.group(0))}</span>')
                i += len(m.group(0)); continue
        out.append(esc(code[i])); i += 1
    return "".join(out)


# ---------- pi-base macro substitution in informal text ----------
def clean_informal(text, pname, sname):
    if not text:
        return ""
    text = text.split("----")[0].strip()  # drop the meta-properties tail
    text = re.sub(r"\{\{[^}]*\}\}", "[ref]", text)
    text = re.sub(r"\{S0*(\d+)\|P0*\d+\}",
                  lambda m: f"[{sname.get('S'+m.group(1).zfill(6), 'S'+m.group(1))}]({PIBASE}/spaces/S{m.group(1).zfill(6)})", text)
    text = re.sub(r"\{P0*(\d+)\}",
                  lambda m: f"[{pname.get('P'+m.group(1).zfill(6), 'P'+m.group(1))}]({PIBASE}/properties/P{m.group(1).zfill(6)})", text)
    text = re.sub(r"\{S0*(\d+)\}",
                  lambda m: f"[{sname.get('S'+m.group(1).zfill(6), 'S'+m.group(1))}]({PIBASE}/spaces/S{m.group(1).zfill(6)})", text)
    return text.strip()


def render_statement(formula, pname):
    """Render a pi-base when/then formula as linked, math-y markdown."""
    k = formula["kind"]
    if k == "atom":
        uid = formula["property"]
        nm = pname.get(uid, uid)
        lit = f"[{nm}]({PIBASE}/properties/{uid})"
        return lit if formula["value"] else f"¬ {lit}"
    sep = " ∧ " if k == "and" else " ∨ "
    return sep.join(render_statement(s, pname) for s in formula["subs"])


def read_lean(path):
    """Read a Lean file, stripping module/import/expose boilerplate so the card
    focuses on the actual definition or proof."""
    if not os.path.exists(path):
        return None
    lines = open(path).read().splitlines()
    out, i = [], 0
    boiler = re.compile(r"^\s*(module\b|public\s+import\b|import\b|@\[expose\]\s*public\s+section\b)")
    for ln in lines:
        if boiler.match(ln):
            continue
        out.append(ln)
    text = "\n".join(out)
    text = re.sub(r"\n{3,}", "\n\n", text).strip("\n")
    return text


def main():
    data = json.load(open(PIBASE_DATA))
    P = {p["uid"]: p for p in data["properties"]}
    T = {t["uid"]: t for t in data["theorems"]}
    pname = {p["uid"]: p["name"] for p in data["properties"]}
    sname = {s["uid"]: s["name"] for s in data["spaces"]}

    propdir = os.path.join(FELIX, "PiBaseLean", "Properties")
    thmdir = os.path.join(FELIX, "PiBaseLean", "Theorems")

    # ----- property cards -----
    pids = sorted((int(d[1:]) for d in os.listdir(propdir)
                   if re.fullmatch(r"P\d+", d)))
    pcards = []
    for n in pids:
        uid = f"P{n:06d}"
        p = P.get(uid, {})
        nm = p.get("name", f"P{n}")
        desc = clean_informal(p.get("description", ""), pname, sname)
        d = os.path.join(propdir, f"P{n}")
        defs = read_lean(os.path.join(d, "Defs.lean"))
        lemmas = read_lean(os.path.join(d, "Lemmas.lean"))
        lean = defs or "-- (no Defs.lean)"
        extra = (f'<details class="more"><summary>+ Lemmas.lean</summary>'
                 f'<pre class="lean">{lean_html(lemmas)}</pre></details>' if lemmas else "")
        pcards.append(f'''<div class="entry" data-kind="prop"
  data-search="{html.escape((uid + ' P' + str(n) + ' ' + nm).lower())}">
  <header>
    <span class="uid"><a href="{PIBASE}/properties/{uid}" target="_blank" rel="noopener">P{n}</a></span>
    <span class="name" data-math>{html.escape(nm)}</span>
    <a class="gh" href="{GH}/PiBaseLean/Properties/P{n}/Defs.lean" target="_blank" rel="noopener">source ↗</a>
    <span class="rev-controls"></span>
  </header>
  <div class="panes">
    <div class="informal">
      <div class="md" data-md>{html.escape(desc) if desc else '<span class="empty">No informal description.</span>'}</div>
      <p class="src-link"><a href="{PIBASE}/properties/{uid}" target="_blank" rel="noopener">View on π-Base ↗</a></p>
    </div>
    <div class="lean-pane"><pre class="lean">{lean_html(lean)}</pre>{extra}</div>
  </div>
</div>''')

    # ----- theorem cards -----
    tids = sorted((int(d[1:]) for d in os.listdir(thmdir)
                   if re.fullmatch(r"T\d+", d)))
    tcards = []
    for n in tids:
        uid = f"T{n:06d}"
        t = T.get(uid)
        stmt = (render_statement(t["when"], pname) + " &nbsp;⟹&nbsp; "
                + render_statement(t["then"], pname)) if t else "(statement unavailable)"
        just = clean_informal((t or {}).get("description", ""), pname, sname)
        d = os.path.join(thmdir, f"T{n}")
        thm = read_lean(os.path.join(d, "Theorem.lean")) or "-- (no Theorem.lean)"
        lemmas = read_lean(os.path.join(d, "Lemmas.lean"))
        extra = (f'<details class="more"><summary>+ Lemmas.lean</summary>'
                 f'<pre class="lean">{lean_html(lemmas)}</pre></details>' if lemmas else "")
        just_banner = (f'<div class="thm-just" data-md>{html.escape(just)}</div>'
                       if just else "")
        tcards.append(f'''<div class="entry thm" data-kind="thm"
  data-search="{html.escape(('t'+str(n)+' '+re.sub(r'[^a-z0-9 ]','',(stmt).lower())))}">
  <header>
    <span class="uid"><a href="{PIBASE}/theorems/{uid}" target="_blank" rel="noopener">T{n}</a></span>
    <span class="name" data-md-inline>{stmt}</span>
    <a class="gh" href="{PIBASE}/theorems/{uid}" target="_blank" rel="noopener">π-Base ↗</a>
    <a class="gh" href="{GH}/PiBaseLean/Theorems/T{n}/Theorem.lean" target="_blank" rel="noopener">source ↗</a>
    <span class="rev-controls"></span>
  </header>
  {just_banner}
  <div class="lean-pane"><pre class="lean">{lean_html(thm)}</pre>{extra}</div>
</div>''')

    # ----- space cards -----
    S = {s["uid"]: s for s in data["spaces"]}
    tpath = os.path.join(FELIX, "data", "traits.json")
    traits = json.load(open(tpath)) if os.path.exists(tpath) else {}
    spdir = os.path.join(FELIX, "PiBaseLean", "Spaces")
    sids = sorted(int(d[1:]) for d in os.listdir(spdir)
                  if re.fullmatch(r"S\d+", d)
                  and os.path.exists(os.path.join(spdir, d, "Defs.lean")))
    STAT = {"proven": ("proven", "st-g"), "asserted": ("asserted", "st-a"),
            "derivable": ("derivable", "st-b")}
    scards = []
    for n in sids:
        uid = f"S{n:06d}"
        s = S.get(uid, {})
        nm = s.get("name", f"S{n}")
        desc = clean_informal(s.get("description", ""), pname, sname)
        lean = read_lean(os.path.join(spdir, f"S{n}", "Defs.lean")) or "-- (no Defs.lean)"
        rows = traits.get(uid, {}).get("traits", [])
        cnt = {"proven": 0, "asserted": 0, "derivable": 0}
        trlines = []
        for r in rows:
            cnt[r["status"]] = cnt.get(r["status"], 0) + 1
            icon = '<span class="yes">✓</span>' if r["value"] else '<span class="no">✗</span>'
            lbl, cls = STAT.get(r["status"], (r["status"], ""))
            pn = int(r["property"][1:])
            trlines.append(
                f'<tr><td>{icon}</td><td><a href="{PIBASE}/properties/{r["property"]}" '
                f'target="_blank" rel="noopener" data-math>{html.escape(r["name"])}</a></td>'
                f'<td><span class="stbadge {cls}">{lbl}</span></td></tr>')
        tsummary = (f'{len(rows)} traits · <b>{cnt["proven"]}</b> proven · '
                    f'{cnt["asserted"]} asserted · {cnt["derivable"]} derivable') if rows else "no trait data"
        traits_block = (
            f'<details class="traits"><summary>{tsummary}</summary>'
            f'<table class="trtab"><tbody>{"".join(trlines)}</tbody></table></details>'
            if rows else "")
        scards.append(f'''<div class="entry" data-kind="space"
  data-search="{html.escape((uid + ' S' + str(n) + ' ' + nm).lower())}">
  <header>
    <span class="uid"><a href="{PIBASE}/spaces/{uid}" target="_blank" rel="noopener">S{n}</a></span>
    <span class="name" data-math>{html.escape(nm)}</span>
    <a class="gh" href="{PIBASE}/spaces/{uid}" target="_blank" rel="noopener">π-Base ↗</a>
    <a class="gh" href="{GH}/PiBaseLean/Spaces/S{n}/Defs.lean" target="_blank" rel="noopener">source ↗</a>
    <span class="rev-controls"></span>
  </header>
  <div class="panes">
    <div class="informal">
      <div class="md" data-md>{html.escape(desc) if desc else '<span class="empty">No informal description.</span>'}</div>
      <p class="src-link"><a href="{PIBASE}/spaces/{uid}" target="_blank" rel="noopener">View on π-Base ↗</a></p>
    </div>
    <div class="lean-pane"><pre class="lean">{lean_html(lean)}</pre></div>
  </div>
  {traits_block}
</div>''')

    page = TEMPLATE.format(
        n_props=len(pcards), n_thms=len(tcards), n_spaces=len(scards),
        prop_cards="\n".join(pcards), thm_cards="\n".join(tcards),
        space_cards="\n".join(scards))
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, "w").write(page)
    print(f"wrote {OUT}: {len(pcards)} properties, {len(scards)} spaces, {len(tcards)} theorems")


TEMPLATE = r'''<!doctype html>
<html lang="en"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>π-Base Lean — review</title>
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css">
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/contrib/auto-render.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/marked/marked.min.js"></script>
<style>
:root{{--bg:#faf7f1;--card:#fffdf9;--rule:#e3dccb;--ink:#1f1d1a;--muted:#6b6457;--accent:#7a3d2a;
 --code:#f3efe6;--g:#2d7a4a;--r:#a02828;--gb:#e8f4ec;}}
*{{box-sizing:border-box}}
body{{font:15px/1.55 -apple-system,BlinkMacSystemFont,"Segoe UI",system-ui,sans-serif;color:var(--ink);
 background:var(--bg);margin:0 auto;max-width:1180px;padding:1.5rem 1rem 5rem}}
h1{{font-size:1.5rem;margin:0 0 .25rem}}
.lede{{color:var(--muted);margin:0 0 1rem;max-width:75ch}} .lede a{{color:var(--accent)}}
#controls{{position:sticky;top:0;z-index:5;background:var(--bg);padding:.7rem 0;margin:0 0 1rem;
 display:flex;gap:.6rem;align-items:center;flex-wrap:wrap;border-bottom:1px solid var(--rule)}}
#controls input{{font:inherit;padding:.4rem .6rem;border:1px solid var(--rule);border-radius:6px;background:#fff;min-width:250px}}
.seg{{display:inline-flex;border:1px solid var(--rule);border-radius:6px;overflow:hidden}}
.seg button{{font:inherit;font-size:.88rem;padding:.4rem .8rem;border:0;background:#fff;color:var(--ink);cursor:pointer}}
.seg button.on{{background:var(--accent);color:#fff}}
.count{{font-size:.85rem;color:var(--muted);margin-left:auto}}
.sec-title{{font-size:1.05rem;margin:1.4rem 0 .6rem;color:var(--accent);font-weight:600}}
.entry{{background:var(--card);border:1px solid var(--rule);border-left:5px solid var(--rule);
 border-radius:7px;margin:.8rem 0;overflow:hidden}}
.entry[data-rev=ok]{{border-left-color:var(--g)}} .entry[data-rev=flag]{{border-left-color:var(--r)}}
.entry header{{display:flex;gap:.55rem;align-items:baseline;flex-wrap:wrap;padding:.55rem .9rem;
 background:#f6f2e9;border-bottom:1px solid var(--rule)}}
.entry header .uid a{{font-family:"JuliaMono","SF Mono",Menlo,monospace;color:var(--accent);text-decoration:none;font-size:.82rem}}
.entry header .name{{font-weight:600}}
a.gh{{color:var(--accent);text-decoration:none;font-size:.76rem;border:1px solid #e0c8ba;border-radius:5px;padding:.03rem .4rem;margin-left:.2rem}}
a.gh:hover{{background:#fbf6ec}}
.rev-controls{{margin-left:auto;display:flex;gap:.3rem}}
.rev-controls button{{font:inherit;font-size:.78rem;padding:.15rem .5rem;border:1px solid var(--rule);background:#fff;border-radius:5px;cursor:pointer;color:var(--muted)}}
.rev-controls button.on[data-v=ok]{{background:var(--gb);color:var(--g);border-color:#bfe0cb}}
.rev-controls button.on[data-v=flag]{{background:#fbe8e8;color:var(--r);border-color:#e6b8b8}}
.panes{{display:grid;grid-template-columns:1fr 1fr}}
.informal{{padding:.75rem .9rem;border-right:1px solid var(--rule);background:#fdfcf8}}
.informal .md{{font-size:.92rem;line-height:1.5}} .informal .md p{{margin:.2rem 0 .6rem}}
.informal .md a,.name a{{color:var(--accent)}} .informal .empty{{color:var(--muted);font-style:italic}}
.src-link{{font-size:.82rem;margin:.5rem 0 0}} .src-link a{{color:var(--accent);text-decoration:none}}
.lean-pane{{overflow:auto}}
/* code blocks: dark mode with standard Lean (VS Code Dark+) syntax colors */
pre.lean{{font-family:"JuliaMono","JetBrains Mono","SF Mono",Menlo,Consolas,monospace;font-size:.79rem;
 background:#1e1e1e;color:#d4d4d4;margin:0;padding:.7rem .9rem;overflow:auto;white-space:pre-wrap;line-height:1.5}}
details.more summary{{cursor:pointer;font-size:.78rem;color:var(--accent);padding:.35rem .9rem;background:#f6f2e9;border-top:1px solid var(--rule)}}
.entry.thm .thm-just{{font-size:.88rem;line-height:1.5;padding:.55rem .9rem;background:#fbf6ec;border-bottom:1px solid var(--rule);color:#3a2a20;font-style:italic}}
.entry.thm .thm-just p{{margin:.15rem 0}} .entry.thm .thm-just a{{color:var(--accent);font-style:normal}}
.entry.thm .lean-pane{{border-top:none}} .entry.thm header .name{{font-weight:600}}
pre.lean .c1{{color:#6a9955;font-style:italic}} pre.lean .kn{{color:#569cd6}} pre.lean .kt{{color:#4ec9b0}}
pre.lean .nf{{color:#d4d4d4}} pre.lean .s{{color:#ce9178}} pre.lean .mi{{color:#b5cea8}}
/* trait table (spaces) */
details.traits summary{{cursor:pointer;font-size:.82rem;color:var(--muted);padding:.45rem .9rem;background:#f6f2e9;border-top:1px solid var(--rule)}}
details.traits summary b{{color:var(--g)}}
table.trtab{{width:100%;border-collapse:collapse;font-size:.86rem;background:#fdfcf8}}
table.trtab td{{padding:.2rem .5rem;border-top:1px solid #efe9dc;vertical-align:middle}}
table.trtab td:first-child{{width:1.4rem;text-align:center}}
table.trtab td:last-child{{width:6rem;text-align:right}}
table.trtab a{{color:var(--ink);text-decoration:none}} table.trtab a:hover{{color:var(--accent)}}
.yes{{color:var(--g);font-weight:700}} .no{{color:var(--r);font-weight:700}}
.stbadge{{font-size:.68rem;padding:.03rem .4rem;border-radius:10px;border:1px solid var(--rule)}}
.st-g{{color:var(--g);background:var(--gb);border-color:#bfe0cb}}
.st-a{{color:var(--y);background:#fbf3e0;border-color:#e8d5a8}}
.st-b{{color:#2b6cb0;background:#e8f0fb;border-color:#b8d0ec}}
:root{{--y:#b77a14}}
@media (max-width:820px){{.panes{{grid-template-columns:1fr}}.informal{{border-right:none;border-bottom:1px solid var(--rule)}}}}
.hidden{{display:none}}
</style></head><body>
<h1>π-Base Lean — review</h1>
<p class="lede">The <a href="https://github.com/felixpernegger/pibase-lean" target="_blank" rel="noopener">felixpernegger/pibase-lean</a>
formalization, for human review. Each card shows the informal
<a href="https://topology.pi-base.org" target="_blank" rel="noopener">π-Base</a> statement beside the Lean
definition/proof. Review marks are saved in your browser.</p>
<div id="controls">
  <input id="q" type="search" placeholder="filter by id / name / statement…" autocomplete="off">
  <span class="seg" id="seg">
    <button data-f="spaces" class="on">Spaces ({n_spaces})</button>
    <button data-f="props">Properties ({n_props})</button>
    <button data-f="thms">Theorems ({n_thms})</button>
  </span>
  <span class="count" id="count"></span>
</div>
<div id="sec-spaces"><div class="sec-title">Spaces — {n_spaces} formalized (carrier + topology; trait tables from the deduction closure)</div>{space_cards}</div>
<div id="sec-props" class="hidden"><div class="sec-title">Properties — {n_props} formalized</div>{prop_cards}</div>
<div id="sec-thms" class="hidden"><div class="sec-title">Theorems — {n_thms} formalized (implications, all proven)</div>{thm_cards}</div>
<script>
const KEY='pbl-felix-review';const marks=JSON.parse(localStorage.getItem(KEY)||'{{}}');
function idOf(e){{return e.dataset.kind+e.querySelector('.uid a').textContent;}}
function applyMark(e){{const v=marks[idOf(e)];if(v)e.dataset.rev=v;else delete e.dataset.rev;
 e.querySelectorAll('.rev-controls button').forEach(b=>b.classList.toggle('on',b.dataset.v===v));}}
document.querySelectorAll('.entry').forEach(e=>{{
 const rc=e.querySelector('.rev-controls');
 rc.innerHTML='<button data-v="ok">✓ ok</button><button data-v="flag">⚑ flag</button>';
 rc.querySelectorAll('button').forEach(b=>b.onclick=()=>{{const id=idOf(e);
  marks[id]=(marks[id]===b.dataset.v)?undefined:b.dataset.v;if(!marks[id])delete marks[id];
  localStorage.setItem(KEY,JSON.stringify(marks));applyMark(e);update();}});applyMark(e);}});
document.querySelectorAll('[data-md]').forEach(el=>{{try{{el.innerHTML=marked.parse(el.textContent);}}catch(e){{}}}});
document.querySelectorAll('[data-md-inline]').forEach(el=>{{try{{el.innerHTML=marked.parseInline(el.textContent);}}catch(e){{}}}});
function typeset(){{if(window.renderMathInElement)renderMathInElement(document.body,{{
 delimiters:[{{left:'$$',right:'$$',display:true}},{{left:'$',right:'$',display:false}}],throwOnError:false}});}}
window.addEventListener('load',typeset);
let filter='spaces';const q=document.getElementById('q');
const SEC={{spaces:'sec-spaces',props:'sec-props',thms:'sec-thms'}};
function update(){{
 for(const k in SEC) document.getElementById(SEC[k]).classList.toggle('hidden',filter!==k);
 const term=q.value.trim().toLowerCase();let shown=0,rev=0;
 const sec=document.getElementById(SEC[filter]);
 sec.querySelectorAll('.entry').forEach(e=>{{const ok=!term||e.dataset.search.includes(term);
  e.classList.toggle('hidden',!ok);if(ok){{shown++;if(marks[idOf(e)])rev++;}}}});
 const tot=sec.querySelectorAll('.entry').length;
 document.getElementById('count').textContent=shown+' shown · '+rev+'/'+tot+' reviewed';}}
document.querySelectorAll('#seg button').forEach(b=>b.onclick=()=>{{
 document.querySelectorAll('#seg button').forEach(x=>x.classList.remove('on'));
 b.classList.add('on');filter=b.dataset.f;update();}});
q.oninput=update;update();
</script></body></html>'''


if __name__ == "__main__":
    main()
