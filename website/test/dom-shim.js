// A minimal DOM for rendering the Preact page under node (ui-smoke.test.js):
// just enough of Document / Element / Text for preact's diff, a small selector
// matcher, and stubs for the browser globals ui.js touches (matchMedia,
// location, Worker, fetch, innerHeight).  It is not a browser: no layout, no
// CSS, and events are delivered only to listeners registered on the element
// itself (preact attaches its handlers there, so that is what the page needs).

class ShimNode {
  constructor() { this.parentNode = null; }
  get nextSibling() {
    const p = this.parentNode;
    if (!p) return null;
    return p.childNodes[p.childNodes.indexOf(this) + 1] ?? null;
  }
  remove() { this.parentNode?.removeChild(this); }
}

class ShimText extends ShimNode {
  constructor(data) { super(); this.nodeType = 3; this.data = String(data); }
  get textContent() { return this.data; }
  set textContent(v) { this.data = String(v); }
  get nodeValue() { return this.data; }
}

const makeStyle = () => {
  const style = { cssText: '' };
  style.setProperty = (k, v) => { style[k] = v; };
  style.removeProperty = k => { delete style[k]; };
  return style;
};

class ShimElement extends ShimNode {
  constructor(tag, namespaceURI = null) {
    super();
    this.nodeType = 1;
    this.localName = tag.toLowerCase();
    this.tagName = tag.toUpperCase();
    this.namespaceURI = namespaceURI;
    this.attributes = new Map();
    this.childNodes = [];
    this.listeners = new Map();
    this.style = makeStyle();
    this.value = '';
    this.disabled = false;
    this.hidden = false;
    this.open = false;
    this.scrollTop = 0; this.scrollLeft = 0; this.scrollHeight = 0;
    this._html = null;                 // set by dangerouslySetInnerHTML
    // `'onclick' in dom` etc. is how preact decides the event name's casing
    this.onclick = null; this.oninput = null; this.onchange = null; this.onkeydown = null; this.onscroll = null;
  }
  get id() { return this.attributes.get('id') ?? ''; }
  set id(v) { this.attributes.set('id', String(v)); }
  get className() { return this.attributes.get('class') ?? ''; }
  set className(v) { this.attributes.set('class', String(v)); }
  get classList() {
    const list = () => this.className.split(/\s+/).filter(Boolean);
    return { contains: c => list().includes(c), toString: () => this.className };
  }
  /** A live view of the data-* attributes (reads, writes and deletes). */
  get dataset() {
    const attr = k => 'data-' + k.replace(/[A-Z]/g, c => '-' + c.toLowerCase());
    const attrs = this.attributes;
    return new Proxy({}, {
      get: (_, k) => (typeof k === 'string' ? attrs.get(attr(k)) : undefined),
      set: (_, k, v) => { attrs.set(attr(k), String(v)); return true; },
      deleteProperty: (_, k) => { attrs.delete(attr(k)); return true; },
      has: (_, k) => attrs.has(attr(k)),
    });
  }
  get firstChild() { return this.childNodes[0] ?? null; }
  get lastChild() { return this.childNodes[this.childNodes.length - 1] ?? null; }
  get children() { return this.childNodes.filter(c => c.nodeType === 1); }
  appendChild(n) { return this.insertBefore(n, null); }
  insertBefore(n, ref) {
    if (n.parentNode) n.parentNode.removeChild(n);
    const i = ref ? this.childNodes.indexOf(ref) : -1;
    if (i < 0) this.childNodes.push(n); else this.childNodes.splice(i, 0, n);
    n.parentNode = this;
    return n;
  }
  removeChild(n) {
    const i = this.childNodes.indexOf(n);
    if (i >= 0) this.childNodes.splice(i, 1);
    n.parentNode = null;
    return n;
  }
  setAttribute(k, v) { this.attributes.set(k, String(v)); }
  getAttribute(k) { return this.attributes.has(k) ? this.attributes.get(k) : null; }
  hasAttribute(k) { return this.attributes.has(k); }
  removeAttribute(k) { this.attributes.delete(k); }
  addEventListener(type, fn) { this.listeners.set(type, [...(this.listeners.get(type) ?? []), fn]); }
  removeEventListener(type, fn) { this.listeners.set(type, (this.listeners.get(type) ?? []).filter(f => f !== fn)); }
  /** Deliver an event to this element's listeners (no bubbling). */
  dispatch(type, extra = {}) {
    const ev = { type, target: this, currentTarget: this, preventDefault() {}, stopPropagation() {}, ...extra };
    for (const fn of this.listeners.get(type) ?? []) fn.call(this, ev);
    return ev;
  }
  click() { this.dispatch('click'); }
  select() {}
  focus() {}
  get innerHTML() { return this._html ?? this.childNodes.map(c => (c.nodeType === 3 ? c.data : c.outerHTML)).join(''); }
  set innerHTML(v) { this.childNodes = []; this._html = String(v); }
  get textContent() { return this._html ?? this.childNodes.map(c => c.textContent).join(''); }
  set textContent(v) { this._html = null; this.childNodes = v === '' ? [] : [Object.assign(new ShimText(v), { parentNode: this })]; }
  get outerHTML() {
    const attrs = [...this.attributes].map(([k, v]) => ` ${k}="${v}"`).join('');
    return `<${this.localName}${attrs}>${this.innerHTML}</${this.localName}>`;
  }
  /** Every descendant element, depth first. */
  *descendants() {
    for (const c of this.childNodes) if (c.nodeType === 1) { yield c; yield* c.descendants(); }
  }
  matches(selector) { return matchesCompound(this, selector.trim()); }
  querySelectorAll(selector) {
    const parts = selector.trim().split(/\s+/);   // descendant combinators only
    return [...this.descendants()].filter(el => {
      if (!matchesCompound(el, parts[parts.length - 1])) return false;
      let node = el, i = parts.length - 2;
      while (i >= 0) {
        node = node.parentNode;
        if (!node || node === this.parentNode) return false;
        if (node.nodeType === 1 && matchesCompound(node, parts[i])) i--;
      }
      return true;
    });
  }
  querySelector(selector) { return this.querySelectorAll(selector)[0] ?? null; }
  getElementById(id) { return [...this.descendants()].find(el => el.id === id) ?? null; }
}

/** tag, #id, .class, [attr], [attr="value"] and :not(...) of those, compounded. */
function matchesCompound(el, compound) {
  let m, rest = compound, ok = true;
  const tag = /^[a-z][a-z0-9-]*/i.exec(compound)?.[0];
  if (tag) { if (el.localName !== tag.toLowerCase()) return false; rest = compound.slice(tag.length); }
  const sub = /#([\w-]+)|\.([\w-]+)|\[([\w-]+)(?:="([^"]*)")?\]|:not\(([^)]*)\)|:disabled/g;
  while ((m = sub.exec(rest))) {
    if (m[1] !== undefined) ok &&= el.id === m[1];
    else if (m[2] !== undefined) ok &&= el.classList.contains(m[2]);
    else if (m[3] !== undefined) ok &&= m[4] === undefined ? el.hasAttribute(m[3]) : el.getAttribute(m[3]) === m[4];
    else if (m[5] !== undefined) ok &&= !matchesCompound(el, m[5]);
    else ok &&= !!el.disabled;
    if (!ok) return false;
  }
  return ok;
}

class ShimDocument {
  constructor() {
    this.documentElement = new ShimElement('html');
    this.body = new ShimElement('body');
    this.documentElement.appendChild(this.body);
  }
  createElement(tag) { return new ShimElement(tag); }
  createElementNS(ns, tag) { return new ShimElement(tag, ns); }
  createTextNode(data) { return new ShimText(data); }
  getElementById(id) { return this.documentElement.getElementById(id); }
  querySelector(s) { return this.documentElement.querySelector(s); }
  querySelectorAll(s) { return this.documentElement.querySelectorAll(s); }
  execCommand() { return true; }
  addEventListener() {}
  removeEventListener() {}
  dispatchEvent() { return true; }
}

/** The Web Worker stand-in: records posted messages, never replies. */
export class ShimWorker {
  static instances = [];
  constructor(url, options) { this.url = String(url); this.options = options; this.messages = []; this.terminated = false; ShimWorker.instances.push(this); }
  postMessage(m) { this.messages.push(m); }
  terminate() { this.terminated = true; }
}

/** Install the shim as the page's globals for one render; returns the #app container. */
export function installDom({ compact = false, hash = '' } = {}) {
  const document = new ShimDocument();
  const app = new ShimElement('div');
  app.id = 'app';
  document.body.appendChild(app);
  const mql = { matches: compact, media: '(max-width: 640px)', listeners: [],
    addEventListener(_, fn) { this.listeners.push(fn); }, removeEventListener(_, fn) { this.listeners = this.listeners.filter(f => f !== fn); } };
  const dark = { matches: false, media: '(prefers-color-scheme: dark)', addEventListener() {}, removeEventListener() {} };
  Object.assign(globalThis, {
    document, window: globalThis, location: { hash, href: `http://localhost/${hash}` },
    matchMedia: q => (q.includes('max-width') ? mql : dark), Worker: ShimWorker, innerHeight: 800,
    fetch: () => Promise.reject(new Error('offline in the test shim')),
    // preact flushes effects on the next frame; without rAF it waits 100 ms
    requestAnimationFrame: cb => setTimeout(cb, 0), cancelAnimationFrame: id => clearTimeout(id),
  });
  if (typeof globalThis.navigator === 'undefined') globalThis.navigator = {};
  ShimWorker.instances.length = 0;
  return { app, document, mql };
}

/** Let preact's deferred effects and the page's timers run. */
export const settle = (ms = 30) => new Promise(r => setTimeout(r, ms));
