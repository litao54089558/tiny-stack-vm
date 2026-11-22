import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode -> immediate length + 1 (0 = not an opcode). Valid opcodes are
// 0x00-0x07, 0x10-0x1E, 0x20-0x22, 0x30-0x34, 0x40-0x41, 0x50-0x53;
// note 0x1F is NOT an opcode. PUSH8=1, PUSH32=4, JMP/JZ/JNZ/CALL=2.
const IMM = new Uint8Array(256);
for (let i = 0; i <= 7; i++) IMM[i] = 1;
for (let i = 0x10; i <= 0x1e; i++) IMM[i] = 1;
for (let i = 0x20; i <= 0x22; i++) IMM[i] = 1;
for (let i = 0x30; i <= 0x34; i++) IMM[i] = 1;
IMM[0x40] = 1;
IMM[0x41] = 1;
for (let i = 0x50; i <= 0x53; i++) IMM[i] = 1;
IMM[1] = 2;
IMM[2] = 5;
for (let i = 0x30; i <= 0x33; i++) IMM[i] = 3;

function run(p: Uint8Array, inp: Uint8Array): { o: Uint8Array; c: number } {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0;
  let cp = 0;
  let pc = 0;
  let steps = 0;
  let ol = 0;
  let ip = 0;
  const end = (c: number): { o: Uint8Array; c: number } => ({ o: out.subarray(0, ol), c });

  for (;;) {
    if (steps === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    const e = IMM[op];
    if (e === 0) return end(5);
    const imm = e - 1;
    if (pc + imm >= n) return end(9);
    steps++;
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0x00:
        return end(0);
      case 0x01:
        if (sp === 256) return end(3);
        D[sp++] = (p[nx - 1] << 24) >> 24;
        break;
      case 0x02:
        if (sp === 256) return end(3);
        D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
        break;
      case 0x03:
        if (sp < 1) return end(2);
        sp--;
        break;
      case 0x04:
        if (sp < 1) return end(2);
        if (sp === 256) return end(3);
        D[sp] = D[sp - 1];
        sp++;
        break;
      case 0x05:
        if (sp < 2) return end(2);
        {
          const t = D[sp - 1];
          D[sp - 1] = D[sp - 2];
          D[sp - 2] = t;
        }
        break;
      case 0x06:
        if (sp < 2) return end(2);
        if (sp === 256) return end(3);
        D[sp] = D[sp - 2];
        sp++;
        break;
      case 0x07:
        if (sp < 3) return end(2);
        {
          const a = D[sp - 3];
          D[sp - 3] = D[sp - 2];
          D[sp - 2] = D[sp - 1];
          D[sp - 1] = a;
        }
        break;
      case 0x17:
        if (sp < 1) return end(2);
        D[sp - 1] = -D[sp - 1] | 0;
        break;
      case 0x1b:
        if (sp < 1) return end(2);
        D[sp - 1] = ~D[sp - 1];
        break;
      case 0x10:
      case 0x11:
      case 0x12:
      case 0x13:
      case 0x14:
      case 0x15:
      case 0x16:
      case 0x18:
      case 0x19:
      case 0x1a:
      case 0x1c:
      case 0x1d:
      case 0x1e:
      case 0x20:
      case 0x21:
      case 0x22:
      {
        if (sp < 2) return end(2);
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return end(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        } else if (op === 0x14) {
          if (b === 0) return end(4);
          r = b === -1 ? 0 : (a % b) | 0;
        } else if (op === 0x15) {
          if (b === 0) return end(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return end(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = a >>> 0 < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30:
      case 0x31:
      case 0x32:
      {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          if (sp < 1) return end(2);
          const v = D[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 0x40:
        if (sp < 1) return end(2);
        {
          const addr = D[sp - 1];
          if (addr < 0 || addr >= 256) return end(6);
          D[sp - 1] = M[addr];
        }
        break;
      case 0x41:
        if (sp < 2) return end(2);
        {
          const addr = D[sp - 1];
          const v = D[sp - 2];
          if (addr < 0 || addr >= 256) return end(6);
          sp -= 2;
          M[addr] = v;
        }
        break;
      case 0x50:
        if (sp < 1) return end(2);
        {
          const s = String(D[sp - 1]);
          if (ol + s.length > 65536) return end(11);
          sp--;
          for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        }
        break;
      case 0x51:
        if (sp < 1) return end(2);
        if (ol + 1 > 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52:
        if (sp === 256) return end(3);
        D[sp++] = ip < inp.length ? inp[ip++] : -1;
        break;
      case 0x53:
        if (sp < 1) return end(2);
        return end(D[--sp] & 255);
      default:
        return end(5);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), `${r.c}\n`);
}

