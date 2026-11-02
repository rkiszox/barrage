'use strict';

const BRAND = 'BARRAGESTUDIOS';
const DISCORD = 'discord.gg/KgdnjMBThc';

const Utils = (() => {
  function extract(val, pos, width) {
    return Math.floor(val / Math.pow(2, pos)) % Math.pow(2, width);
  }

  function splitFrexp(x) {
    if (x === 0) return [0, 0];
    const ax = Math.abs(x);
    let e = Math.floor(Math.log(ax) / Math.log(2)) + 1;
    let m = ax / Math.pow(2, e);
    if (m >= 1) { m /= 2; e += 1; }
    else if (m < 0.5) { m *= 2; e -= 1; }
    return [m, e];
  }

  function packU32(val) {
    const v = Math.floor(val) % 4294967296;
    return [v % 256, Math.floor(v / 256) % 256, Math.floor(v / 65536) % 256, Math.floor(v / 16777216) % 256];
  }

  function packU16(val) {
    const v = Math.floor(val) % 65536;
    return [v % 256, Math.floor(v / 256) % 256];
  }

  function packDbl(val) {
    if (val === 0) return new Array(8).fill(0);
    let sign = 0;
    if (val < 0) { sign = 1; val = -val; }
    const [mant, exp] = splitFrexp(val);
    const bexp = exp + 1022;
    const frac = (mant * 2 - 1) * Math.pow(2, 52);
    const lo = Math.floor(frac % 4294967296);
    const hi20 = Math.floor(frac / 4294967296) % 1048576;
    const hi = sign * 2147483648 + bexp * 1048576 + hi20;
    const b1 = packU32(lo);
    const b2 = packU32(hi);
    return [...b1, ...b2];
  }

  function shuf(arr, rng) {
    for (let i = arr.length - 1; i > 0; i--) {
      const j = Math.floor(rng() * (i + 1));
      [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
  }

  function pickNums(count, lo, hi, rng) {
    const used = new Set();
    const res = [];
    while (res.length < count) {
      const v = lo + Math.floor(rng() * (hi - lo + 1));
      if (!used.has(v)) { used.add(v); res.push(v); }
    }
    return res;
  }

  function makeAlpha(rng) {
    const chars = ['b','B','f','F','l','L','k','K','o','O','p','P','h','H','m','M'];
    shuf(chars, rng);
    return chars.join('');
  }

  function seededRng(seed) {
    let s = seed >>> 0;
    return function() {
      s ^= s << 13; s ^= s >>> 17; s ^= s << 5;
      return ((s >>> 0) / 4294967296);
    };
  }

  function u32hex(n) { return '0x' + (n >>> 0).toString(16); }

  function msexpr(n, rng) {
    n = Math.floor(n);
    const style = Math.floor(rng() * 5) + 1;
    const phrases = [
      'protected by BARRAGESTUDIOS', 'virtual machine bytecode',
      'runtime environment check', 'bytecode stream decoder',
      'constant pool table', 'register state frame',
      'BARRAGESTUDIOS protection', 'dynamic constant loader',
      'arithmetic expression'
    ];
    if (style === 1) {
      const d = 15 + Math.floor(rng() * 166);
      if (rng() < 0.5) return `(${n - d}+${u32hex(d)})`;
      return `(${u32hex(n + d)}-${d})`;
    } else if (style === 2) {
      const ph = phrases[Math.floor(rng() * phrases.length)];
      const plen = ph.length;
      const rem = n + plen;
      const d = 10 + Math.floor(rng() * 81);
      if (rng() < 0.5) return `(-#${JSON.stringify(ph)}+(${u32hex(rem + d)}-${d}))`;
      return `((${rem - d}+${u32hex(d)})+-#[[${ph}]])`;
    } else if (style === 3) {
      const cnt = 2 + Math.floor(rng() * 5);
      const rem = n + cnt;
      return `(-#${'{'+(new Array(cnt).fill('nil').join(','))+'}'}+${rem})`;
    } else if (style === 4 && n > 0 && n < 5000) {
      const k = 12 + Math.floor(rng() * 179);
      const prod = n * k;
      if (rng() < 0.5) return `(${u32hex(prod)}/${k})`;
      return `(${prod}/${u32hex(k)})`;
    } else {
      const ph = phrases[Math.floor(rng() * phrases.length)];
      const plen = ph.length;
      const k = 10 + Math.floor(rng() * 51);
      const target = n + plen;
      const prod = target * k;
      return `((${u32hex(prod)}/${k})+-#${JSON.stringify(ph)})`;
    }
  }

  function msstr(s, rng) {
    const esc = part => "'" + Array.from(part).map(c => '\\' + c.charCodeAt(0)).join('') + "'";
    if (s.length < 4) return esc(s);
    const p1 = s.slice(0, 2);
    const p2 = s.slice(2, 4);
    const p3 = s.slice(4);
    const n1 = 5 + Math.floor(rng() * 76);
    const n2 = n1 + 3 + Math.floor(rng() * 38);
    const fake1 = `(${u32hex(100 + Math.floor(rng() * 301))}-${10 + Math.floor(rng() * 90)})`;
    const fake2 = `\\${40 + Math.floor(rng() * 81)}\\${40 + Math.floor(rng() * 81)}`;
    const mid = `(function(o)return(o and'${fake1}')or${esc(p2)}or'${fake2}'end)((${msexpr(n1, rng)})==(${msexpr(n2, rng)}))`;
    return p3.length > 0 ? `${esc(p1)}..${mid}..${esc(p3)}` : `${esc(p1)}..${mid}`;
  }

  return { extract, packU32, packU16, packDbl, shuf, pickNums, makeAlpha, seededRng, msexpr, msstr };
})();

const StreamCipher = (() => {
  function encryptString(input, key) {
    let stateJ = key % 35184372088832;
    let stateP = key % 255 + 2;
    const length = input.length;
    const lookupTable = {};
    let v2 = 203;
    let streamBuffer = [];

    const shufflePool = [];
    for (let i = 1; i <= 256; i++) shufflePool.push(i);
    let tempJ = stateJ;
    let tempP = stateP;

    const getStreamValue = () => {
      if (streamBuffer.length === 0) {
        tempJ = (tempJ * 85 + 6789898822691) % 35184372088832;
        do { tempP = (tempP * 76) % 257; } while (tempP === 1);
        const xorVal = tempP % 32;
        const floatVal = (Math.floor(tempJ / Math.pow(2, 13 - (tempP - xorVal) / 32)) % 4294967296) / Math.pow(2, xorVal);
        const byteVal = Math.floor((floatVal % 1) * 4294967296) + Math.floor(floatVal);
        const e = byteVal % 65536;
        const k = Math.floor((byteVal - e) / 65536);
        const v1 = e % 256;
        const h1 = Math.floor((e - v1) / 256);
        const y = k % 256;
        const w = Math.floor((k - y) / 256);
        streamBuffer = [v1, h1, y, w];
      }
      return streamBuffer.shift();
    };

    let result = '';
    for (let i = 0; i < length; i++) {
      v2 = ((input.charCodeAt(i) + getStreamValue()) + v2) % 256;
      result += String.fromCharCode(v2);
    }
    return result;
  }

  function buildStreamHeader(discord, brand) {
    return `--[[ Protected by ${brand} | ${discord} ]]\n\nlocal decryptString, obfuscatorData do\n    local mathFloor = math.floor\n    local mathRandom = math.random\n    local tableRemove = table.remove\n    local stringChar = string.char\n    local stateJ = 0\n    local stateP = 2\n    local charTable = {}\n    local lookupTable = {}\n    local v = 0\n    local shufflePool = {}\n\n    for i = 1, 256, 1 do\n        shufflePool[i] = i\n    end\n\n    repeat\n        local randomIndex = mathRandom(1, #shufflePool)\n        local value = tableRemove(shufflePool, randomIndex)\n        lookupTable[value] = stringChar(value - 1)\n    until #shufflePool == 0\n\n    local streamBuffer = {}\n    local function getStreamValue()\n        if #streamBuffer == 0 then\n            stateJ = (stateJ * 85 + 6789898822691) % 35184372088832\n            repeat\n                stateP = (stateP * 76) % 257\n            until stateP ~= 1\n            local xorVal = stateP % 32\n            local floatVal = (mathFloor(stateJ / 2 ^ (13 - (stateP - xorVal) / 32)) % 4294967296.0) / 2 ^ xorVal\n            local byteVal = mathFloor((floatVal % 1) * 4294967296.0) + mathFloor(floatVal)\n            local e = byteVal % 65536\n            local k = (byteVal - e) / 65536\n            local v1 = e % 256\n            local h1 = (e - v1) / 256\n            local y = k % 256\n            local w = (k - y) / 256\n            streamBuffer = { v1; h1, y; w }\n        end\n        return tableRemove(streamBuffer)\n    end\n\n    local cache = {}\n    obfuscatorData = setmetatable({}, { __index = cache, __metatable = nil })\n\n    function decryptString(input, key)\n        local cachedResult = cache\n        if (cachedResult)[key] then\n        else\n            streamBuffer = {}\n            local mapping = lookupTable\n            stateJ = key % 35184372088832\n            stateP = key % 255 + 2\n            local length = string.len(input)\n            (cachedResult)[key] = ""\n            local v2 = 203\n            for i = 1, length, 1 do\n                v2 = ((string.byte(input, i) + getStreamValue()) + v2) % 256\n                (cachedResult)[key] = (cachedResult)[key] .. (mapping)[v2 + 1]\n            end\n        end\n        return key\n    end\nend\n`;
  }

  function obfuscateWithStream(src, rng) {
    const lines = src.split('\n');
    let output = buildStreamHeader(DISCORD, BRAND);
    const keyBase = Math.floor(rng() * 1e10) + 1000000;
    let keyCounter = keyBase;

    const encodeStr = (s) => {
      const key = keyCounter++;
      const encrypted = encryptString(s, key);
      const escaped = Array.from(encrypted).map(c => {
        const code = c.charCodeAt(0);
        return '\\' + code;
      }).join('');
      return `(obfuscatorData)[decryptString("${escaped}", ${key})]`;
    };

    output += `\n-- Protected source (${BRAND})\n`;
    output += `local _brand = ${encodeStr(BRAND)}\n`;
    output += `local _discord = ${encodeStr(DISCORD)}\n\n`;

    for (const line of lines) {
      if (line.trim() === '' || line.trim().startsWith('--')) {
        output += line + '\n';
        continue;
      }
      const transformed = line.replace(/"([^"\\]*(\\.[^"\\]*)*)"|'([^'\\]*(\\.[^'\\]*)*)'/g, (match, dq, _, sq) => {
        const inner = dq !== undefined ? dq : sq;
        if (inner && inner.length > 1) return encodeStr(inner);
        return match;
      });
      output += transformed + '\n';
    }
    return output;
  }

  return { obfuscateWithStream };
})();

const VMObfuscator = (() => {
  const RK4OPS = new Set([9,12,13,14,15,16,17,23,24,25,38,39,40,41,42,43]);
  const RK2COPS = new Set([6,7,11]);

  function buildVopMap() {
    const list = [];
    for (let op = 0; op <= 44; op++) {
      if (RK4OPS.has(op)) {
        list.push({op, bc:false, cc:false, id:`${op}_RR`});
        list.push({op, bc:false, cc:true,  id:`${op}_RK`});
        list.push({op, bc:true,  cc:false, id:`${op}_KR`});
        list.push({op, bc:true,  cc:true,  id:`${op}_KK`});
      } else if (RK2COPS.has(op)) {
        list.push({op, bc:(op===7), cc:false, id:`${op}_R`});
        list.push({op, bc:(op===7), cc:true,  id:`${op}_K`});
      } else {
        list.push({op, bc:(op===1), cc:(op===5), id:`${op}`});
      }
    }
    return list;
  }

  function encodeMoonSec(bytes, alphabet) {
    let out = `..:::${BRAND}::..` + alphabet;
    for (const b of bytes) {
      const hi = Math.floor(b / 16);
      const lo = b % 16;
      out += alphabet[hi] + alphabet[lo];
    }
    return out;
  }

  function makeCfg(rng) {
    const vopList = buildVopMap();
    const count = vopList.length;
    const pool = Array.from({length: count}, (_, i) => i);
    Utils.shuf(pool, rng);
    const opEncode = {};
    for (let i = 0; i < count; i++) opEncode[vopList[i].id] = pool[i];
    const tagMod = 28 + Math.floor(rng() * 21);
    const tkeys = Utils.pickNums(4, 1, tagMod - 1, rng);
    return {
      vopList, opEncode,
      initKey: 15 + Math.floor(rng() * 226),
      stepKey: (10 + Math.floor(rng() * 111)) * 2 + 1,
      strStep: 25 + Math.floor(rng() * 196),
      tagMod,
      tagNil: tkeys[0], tagBool: tkeys[1], tagNum: tkeys[2], tagStr: tkeys[3],
      alphabet: Utils.makeAlpha(rng)
    };
  }

  function generateVMOutput(src, rng) {
    const ex = (n) => Utils.msexpr(n, rng);
    const mss = (s) => Utils.msstr(s, rng);
    const cfg = makeCfg(rng);

    const dkeys = Utils.pickNums(14, 120, 1450, rng);
    const [k_str,k_ldexp,k_byte,k_char,k_tbl,k_sub,k_concat,k_math,k_catfn,k_insert,k_unpack,k_select,k_tonum,k_env] = dkeys;
    const rkeys = Utils.pickNums(6, 1, 28, rng);
    const [r_u32,r_byte,r_u16,r_bits,r_dbl,r_str] = rkeys;

    const fakeBytecode = Array.from({length: 64 + Math.floor(rng()*128)}, () => Math.floor(rng()*256));
    const encoded = encodeMoonSec(fakeBytecode, cfg.alphabet);

    const headerdecls = [
      `local G=h[${ex(k_env)}];`,
      `local E=l[o[${ex(k_math)}]][o[${ex(k_ldexp)}]]or function(o,l)return o*(2^l)end;`,
      `local _=${ex(2)};`,
      `local e=${ex(1)};`,
      `local g=l[o[${ex(k_str)}]][o[${ex(k_byte)}]];`,
      `local D=${ex(3)};`,
      `local r=l[o[${ex(k_tbl)}]][o[${ex(k_concat)}]];`,
      `local b=${ex(1)};`,
      `local K=${ex(256)};local y=${ex(2048)};local q=${ex(52)};local c=${ex(4)};`,
      `local i=l[o[${ex(k_unpack)}]]or l[o[${ex(k_tbl)}]][o[${ex(k_unpack)}]];`,
      `local v=l[o[${ex(k_str)}]][o[${ex(k_char)}]];`,
      `local j=l[o[${ex(k_str)}]][o[${ex(k_sub)}]];`,
      `local A=l[o[${ex(k_select)}]];`,
      `local z=l[o[${ex(k_tbl)}]][o[${ex(k_insert)}]];`,
      `local I=o[${ex(k_catfn)}];`,
      `local o=l[o[${ex(k_tonum)}]];`
    ].join('');

    const zdecoder = `local payload=${JSON.stringify(encoded)};`;

    const vmrunner = `local function S(proto,upvals,env)return(function(...)local regs={};local pc=1;while true do pc=pc+1;end;end);end;return S({},{},{})`;

    const dictentries = [
      `[${ex(k_str)}]=${mss('string')}`,
      `[${ex(k_ldexp)}]=${mss('ldexp')}`,
      `[${ex(k_byte)}]=${mss('byte')}`,
      `[${ex(k_char)}]=${mss('char')}`,
      `[${ex(k_tbl)}]=${mss('table')}`,
      `[${ex(k_sub)}]=${mss('sub')}`,
      `[${ex(k_concat)}]=${mss('concat')}`,
      `[${ex(k_math)}]=${mss('math')}`,
      `[${ex(k_catfn)}]=(function(l,o)return l..o end)`,
      `[${ex(k_insert)}]=${mss('insert')}`,
      `[${ex(k_unpack)}]=${mss('unpack')}`,
      `[${ex(k_select)}]=${mss('select')}`,
      `[${ex(k_tonum)}]=${mss('tonumber')}`
    ];
    Utils.shuf(dictentries, rng);

    const srcEncoded = Array.from(src).map(c => {
      const code = c.charCodeAt(0);
      return ((code + cfg.initKey + 17) % 256);
    });
    const srcPayload = srcEncoded.map(b => String.fromCharCode(b)).join('');

    return `_, Protected_by_${BRAND}, Discord = '${DISCORD}'\n\n\n,nil,nil;return(function(...) _msec=(function(o,h,l)${headerdecls}${zdecoder}${vmrunner}return _msec({${dictentries.join(',')}},{[${ex(k_env)}]=(getfenv or function()return _ENV end)},((getfenv and getfenv()or _ENV)))(...)end)(...)\n`;
  }

  return { generateVMOutput };
})();

const HybridObfuscator = (() => {
  function obfuscate(src, options, rng) {
    const mode = options.mode || 'hybrid';
    const useStrings = options.strings !== false;
    const useCFF = options.cff !== false;
    const useConst = options.constants !== false;

    let result = '';

    const header = `_, Protected_by_${BRAND}, Discord = '${DISCORD}'\n`;

    if (mode === 'stream') {
      result = StreamCipher.obfuscateWithStream(src, rng);
    } else if (mode === 'vm') {
      result = VMObfuscator.generateVMOutput(src, rng);
    } else {
      const streamPass = StreamCipher.obfuscateWithStream(src, rng);
      const vmLayer = VMObfuscator.generateVMOutput(streamPass, rng);
      result = vmLayer;
    }

    if (useStrings && !result.startsWith('_, Protected')) {
      result = header + result;
    }

    if (useCFF) {
      const extraJunk = generateJunkDispatch(rng);
      result = result + '\n' + extraJunk;
    }

    if (useConst) {
      result = injectConstantFog(result, rng);
    }

    return result;
  }

  function generateJunkDispatch(rng) {
    const keys = [];
    for (let i = 0; i < 4; i++) keys.push(Math.floor(rng() * 9999) + 1000);
    const lines = [
      `local __bs=${keys[0]};local __bk=${keys[1]};`,
      `while __bs>__bk do __bs=__bs-__bk break end`,
      `while (__bs/__bk)==${Math.floor(keys[0]/keys[1])} do __bs=${keys[2]} break end`
    ];
    return lines.join('\n');
  }

  function injectConstantFog(src, rng) {
    return src.replace(/\b(\d{3,})\b/g, (match, n) => {
      const num = parseInt(n);
      if (isNaN(num) || num > 9999999) return match;
      const d = 10 + Math.floor(rng() * 90);
      if (rng() < 0.5) return `(${num - d}+${d})`;
      const hex = '0x' + (num + d).toString(16);
      return `(${hex}-${d})`;
    });
  }

  return { obfuscate };
})();

(function initUI() {
  const sourceInput = document.getElementById('sourceInput');
  const outputArea = document.getElementById('outputArea');
  const obfBtn = document.getElementById('obfBtn');
  const clearInput = document.getElementById('clearInput');
  const copyOutput = document.getElementById('copyOutput');
  const rerollSeed = document.getElementById('rerollSeed');
  const seedInput = document.getElementById('seedInput');
  const errorBar = document.getElementById('errorBar');
  const errorMsg = document.getElementById('errorMsg');
  const statsRow = document.getElementById('statsRow');
  const statLayers = document.getElementById('statLayers');
  const statRatio = document.getElementById('statRatio');
  const statTime = document.getElementById('statTime');

  function getCurrentSeed() {
    const val = seedInput.value.trim();
    if (!val || val === 'Auto') return Math.floor(Math.random() * 0xFFFFFFFF);
    return parseInt(val, 10) || Math.floor(Math.random() * 0xFFFFFFFF);
  }

  function getMode() {
    return document.querySelector('input[name="mode"]:checked')?.value || 'hybrid';
  }

  function getOptions() {
    return {
      mode: getMode(),
      strings: document.getElementById('toggleStrings').checked,
      cff: document.getElementById('toggleCFF').checked,
      constants: document.getElementById('toggleConst').checked
    };
  }

  function showError(msg) {
    errorBar.style.display = 'flex';
    errorMsg.textContent = msg;
  }

  function hideError() {
    errorBar.style.display = 'none';
  }

  function modeToLayers(mode) {
    if (mode === 'stream') return '1';
    if (mode === 'vm') return '2';
    return '3';
  }

  rerollSeed.addEventListener('click', () => {
    const newSeed = Math.floor(Math.random() * 0xFFFFFFFF);
    seedInput.value = newSeed.toString();
  });

  clearInput.addEventListener('click', () => {
    sourceInput.value = '';
    outputArea.value = '';
    hideError();
    statsRow.style.display = 'none';
  });

  copyOutput.addEventListener('click', async () => {
    const text = outputArea.value;
    if (!text) return;
    try {
      await navigator.clipboard.writeText(text);
      const icon = copyOutput.querySelector('svg');
      const originalHTML = copyOutput.innerHTML;
      copyOutput.innerHTML = `<svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="#5bf578" stroke-width="2"><polyline points="20 6 9 17 4 12"/></svg>`;
      setTimeout(() => { copyOutput.innerHTML = originalHTML; }, 1500);
    } catch (e) {
      showError('Clipboard access denied.');
    }
  });

  obfBtn.addEventListener('click', () => {
    const src = sourceInput.value.trim();
    if (!src) {
      showError('No source code provided.');
      return;
    }

    hideError();
    obfBtn.classList.add('loading');
    obfBtn.textContent = 'Processing...';

    const t0 = performance.now();

    requestAnimationFrame(() => {
      setTimeout(() => {
        try {
          const seed = getCurrentSeed();
          const rng = Utils.seededRng(seed);
          const options = getOptions();

          const result = HybridObfuscator.obfuscate(src, options, rng);

          outputArea.value = result;

          const elapsed = (performance.now() - t0).toFixed(0);
          const ratio = (result.length / Math.max(src.length, 1)).toFixed(1);
          const layers = modeToLayers(options.mode);

          statLayers.textContent = layers;
          statRatio.textContent = ratio + 'x';
          statTime.textContent = elapsed + 'ms';
          statsRow.style.display = 'grid';

          seedInput.value = seed.toString();
        } catch (err) {
          showError('Obfuscation failed: ' + err.message);
        } finally {
          obfBtn.classList.remove('loading');
          obfBtn.innerHTML = `<svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M12 22s8-4 8-10V5l-8-3-8 3v7c0 6 8 10 8 10z"/></svg> Obfuscate`;
        }
      }, 20);
    });
  });

  document.querySelectorAll('input[name="mode"]').forEach(radio => {
    radio.addEventListener('change', () => {
      outputArea.value = '';
      statsRow.style.display = 'none';
      hideError();
    });
  });

  const sample = `-- Sample script (BARRAGESTUDIOS)\nlocal players = game:GetService("Players")\nlocal localPlayer = players.LocalPlayer\n\nlocal function greet(player)\n    print("Welcome, " .. player.Name)\nend\n\ngreet(localPlayer)`;
  sourceInput.placeholder = sample;
})();
