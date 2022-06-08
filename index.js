let KRK = [
  [0x517cc1b7, 0x27220a94, 0xfe13abe8, 0xfa9a6ee0],
  [0x6db14acc, 0x9e21c820, 0xff28b1d5, 0xef5de2b0],
  [0xdb92371d, 0x2126e970, 0x03249775, 0x04e8c90e]
];

let S1 = new Array(256);
let S2 = new Array(256);
let X1 = new Array(256);
let X2 = new Array(256);

let TS1 = new Array(256);
let TS2 = new Array(256);
let TX1 = new Array(256);
let TX2 = new Array(256);

let exp = new Array(256);
let log = new Array(256);
log[0] = 0; log[1] = 0;
exp[0] = 1;
for (let i = 1; i < 256; i++) {
  let j = (exp[i - 1] << 1) ^ exp[i - 1];
  if ((j & 0x100) != 0) j ^= 0x11b;
  exp[i] = j;
}
for (let i = 1; i < 255; i++)
  log[exp[i]] = i;

let A = [
  [1, 0, 0, 0, 1, 1, 1, 1],
  [1, 1, 0, 0, 0, 1, 1, 1],
  [1, 1, 1, 0, 0, 0, 1, 1],
  [1, 1, 1, 1, 0, 0, 0, 1],
  [1, 1, 1, 1, 1, 0, 0, 0],
  [0, 1, 1, 1, 1, 1, 0, 0],
  [0, 0, 1, 1, 1, 1, 1, 0],
  [0, 0, 0, 1, 1, 1, 1, 1]];
let B = [
  [0, 1, 0, 1, 1, 1, 1, 0],
  [0, 0, 1, 1, 1, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 1, 1],
  [1, 0, 0, 1, 1, 1, 0, 1],
  [0, 0, 1, 0, 1, 1, 0, 0],
  [1, 0, 0, 0, 0, 0, 0, 1],
  [0, 1, 0, 1, 1, 1, 0, 1],
  [1, 1, 0, 1, 0, 0, 1, 1]];

for (let i = 0; i < 256; i++) {
  let t = 0, p;
  if (i == 0)
    p = 0;
  else
    p = exp[255 - log[i]];
  for (let j = 0; j < 8; j++) {
    let s = 0;
    for (let k = 0; k < 8; k++) {
      if (((p >>> (7 - k)) & 0x01) != 0)
        s ^= A[k][j];
    }
    t = (t << 1) ^ s;
  }
  t ^= 0x63;
  S1[i] = t;
  X1[t] = i;
}
for (let i = 0; i < 256; i++) {
  let t = 0, p;
  if (i == 0)
    p = 0;
  else
    p = exp[(247 * log[i]) % 255];
  for (let j = 0; j < 8; j++) {
    let s = 0;
    for (let k = 0; k < 8; k++) {
      if (((p >>> k) & 0x01) != 0)
        s ^= B[7 - j][k];
    }
    t = (t << 1) ^ s;
  }
  t ^= 0xe2;
  S2[i] = t;
  X2[t] = i;
}

for (let i = 0; i < 256; i++) {
  TS1[i] = 0x00010101 * (S1[i] & 0xff);
  TS2[i] = 0x01000101 * (S2[i] & 0xff);
  TX1[i] = 0x01010001 * (X1[i] & 0xff);
  TX2[i] = 0x01010100 * (X2[i] & 0xff);
}

let keySize = 0;
let numberOfRounds = 0;
let masterKey = null;
let encRoundKeys = null
let decRoundKeys = null;

function reset() {
  keySize = 0;
  numberOfRounds = 0;
  masterKey = null;
  encRoundKeys = null;
  decRoundKeys = null;
}

function getKeySize() {
  return keySize;
}

function setKeySize(new_keySize) {
  reset();
  if (new_keySize != 128 && new_keySize != 192 && new_keySize != 256)
    throw new InvalidKeyException("keySize=" + keySize);
  keySize = new_keySize;
  switch (keySize) {
    case 128:
      numberOfRounds = 12;
      break;
    case 192:
      numberOfRounds = 14;
      break;
    case 256:
      numberOfRounds = 16;
  }
}

function setKey(new_masterKey) {
  if (new_masterKey.length * 8 < keySize)
    throw new InvalidKeyException("masterKey size=" + new_masterKey.length);
  decRoundKeys = null;
  encRoundKeys = null;
  masterKey = new_masterKey;
}

function doCrypt(i, ioffset, rk, nr, o, ooffset) {
  let t0, t1, t2, t3, j = 0;

  t0 = toInt(i[0 + ioffset], i[1 + ioffset], i[2 + ioffset], i[3 + ioffset]);
  t1 = toInt(i[4 + ioffset], i[5 + ioffset], i[6 + ioffset], i[7 + ioffset]);
  t2 = toInt(i[8 + ioffset], i[9 + ioffset], i[10 + ioffset], i[11 + ioffset]);
  t3 = toInt(i[12 + ioffset], i[13 + ioffset], i[14 + ioffset], i[15 + ioffset]);

  for (let r = 1; r < nr / 2; r++) {
    t0 ^= rk[j++]; t1 ^= rk[j++]; t2 ^= rk[j++]; t3 ^= rk[j++];
    t0 = TS1[(t0 >>> 24) & 0xff] ^ TS2[(t0 >>> 16) & 0xff] ^ TX1[(t0 >>> 8) & 0xff] ^ TX2[t0 & 0xff];
    t1 = TS1[(t1 >>> 24) & 0xff] ^ TS2[(t1 >>> 16) & 0xff] ^ TX1[(t1 >>> 8) & 0xff] ^ TX2[t1 & 0xff];
    t2 = TS1[(t2 >>> 24) & 0xff] ^ TS2[(t2 >>> 16) & 0xff] ^ TX1[(t2 >>> 8) & 0xff] ^ TX2[t2 & 0xff];
    t3 = TS1[(t3 >>> 24) & 0xff] ^ TS2[(t3 >>> 16) & 0xff] ^ TX1[(t3 >>> 8) & 0xff] ^ TX2[t3 & 0xff];
    t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;
    t1 = badc(t1); t2 = cdab(t2); t3 = dcba(t3);
    t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;

    t0 ^= rk[j++]; t1 ^= rk[j++]; t2 ^= rk[j++]; t3 ^= rk[j++];
    t0 = TX1[(t0 >>> 24) & 0xff] ^ TX2[(t0 >>> 16) & 0xff] ^ TS1[(t0 >>> 8) & 0xff] ^ TS2[t0 & 0xff];
    t1 = TX1[(t1 >>> 24) & 0xff] ^ TX2[(t1 >>> 16) & 0xff] ^ TS1[(t1 >>> 8) & 0xff] ^ TS2[t1 & 0xff];
    t2 = TX1[(t2 >>> 24) & 0xff] ^ TX2[(t2 >>> 16) & 0xff] ^ TS1[(t2 >>> 8) & 0xff] ^ TS2[t2 & 0xff];
    t3 = TX1[(t3 >>> 24) & 0xff] ^ TX2[(t3 >>> 16) & 0xff] ^ TS1[(t3 >>> 8) & 0xff] ^ TS2[t3 & 0xff];
    t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;
    t3 = badc(t3); t0 = cdab(t0); t1 = dcba(t1);
    t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;
  }
  t0 ^= rk[j++]; t1 ^= rk[j++]; t2 ^= rk[j++]; t3 ^= rk[j++];
  t0 = TS1[(t0 >>> 24) & 0xff] ^ TS2[(t0 >>> 16) & 0xff] ^ TX1[(t0 >>> 8) & 0xff] ^ TX2[t0 & 0xff];
  t1 = TS1[(t1 >>> 24) & 0xff] ^ TS2[(t1 >>> 16) & 0xff] ^ TX1[(t1 >>> 8) & 0xff] ^ TX2[t1 & 0xff];
  t2 = TS1[(t2 >>> 24) & 0xff] ^ TS2[(t2 >>> 16) & 0xff] ^ TX1[(t2 >>> 8) & 0xff] ^ TX2[t2 & 0xff];
  t3 = TS1[(t3 >>> 24) & 0xff] ^ TS2[(t3 >>> 16) & 0xff] ^ TX1[(t3 >>> 8) & 0xff] ^ TX2[t3 & 0xff];
  t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;
  t1 = badc(t1); t2 = cdab(t2); t3 = dcba(t3);
  t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;

  t0 ^= rk[j++]; t1 ^= rk[j++]; t2 ^= rk[j++]; t3 ^= rk[j++];
  o[0 + ooffset] = (X1[0xff & (t0 >>> 24)] ^ (rk[j] >>> 24));
  o[1 + ooffset] = (X2[0xff & (t0 >>> 16)] ^ (rk[j] >>> 16));
  o[2 + ooffset] = (S1[0xff & (t0 >>> 8)] ^ (rk[j] >>> 8));
  o[3 + ooffset] = (S2[0xff & (t0)] ^ (rk[j]));
  o[4 + ooffset] = (X1[0xff & (t1 >>> 24)] ^ (rk[j + 1] >>> 24));
  o[5 + ooffset] = (X2[0xff & (t1 >>> 16)] ^ (rk[j + 1] >>> 16));
  o[6 + ooffset] = (S1[0xff & (t1 >>> 8)] ^ (rk[j + 1] >>> 8));
  o[7 + ooffset] = (S2[0xff & (t1)] ^ (rk[j + 1]));
  o[8 + ooffset] = (X1[0xff & (t2 >>> 24)] ^ (rk[j + 2] >>> 24));
  o[9 + ooffset] = (X2[0xff & (t2 >>> 16)] ^ (rk[j + 2] >>> 16));
  o[10 + ooffset] = (S1[0xff & (t2 >>> 8)] ^ (rk[j + 2] >>> 8));
  o[11 + ooffset] = (S2[0xff & (t2)] ^ (rk[j + 2]));
  o[12 + ooffset] = (X1[0xff & (t3 >>> 24)] ^ (rk[j + 3] >>> 24));
  o[13 + ooffset] = (X2[0xff & (t3 >>> 16)] ^ (rk[j + 3] >>> 16));
  o[14 + ooffset] = (S1[0xff & (t3 >>> 8)] ^ (rk[j + 3] >>> 8));
  o[15 + ooffset] = (S2[0xff & (t3)] ^ (rk[j + 3]));
}

function decrypt2(i, ioffset, o, ooffset) {
  if (keySize == 0)
    throw new InvalidKeyException("keySize");
  if (decRoundKeys == null)
    if (masterKey == null)
      throw new InvalidKeyException("masterKey");
    else
      setupDecRoundKeys();
  doCrypt(i, ioffset, decRoundKeys, numberOfRounds, o, ooffset);
}

function encrypt2(i, ioffset, o, ooffset) {
  if (keySize == 0)
    throw new InvalidKeyException("keySize");
  if (encRoundKeys == null)
    if (masterKey == null)
      throw new InvalidKeyException("masterKey");
    else
      setupEncRoundKeys();
  doCrypt(i, ioffset, encRoundKeys, numberOfRounds, o, ooffset);
}

function setupEncRoundKeys() {
  if (keySize == 0)
    throw new InvalidKeyException("keySize");
  if (masterKey == null)
    throw new InvalidKeyException("masterKey");
  if (encRoundKeys == null)
    encRoundKeys = new Array(4 * (numberOfRounds + 1));
  decRoundKeys = null;
  doEncKeySetup(masterKey, encRoundKeys, keySize);
}

function setupDecRoundKeys() {
  if (keySize == 0)
    throw new InvalidKeyException("keySize");
  if (encRoundKeys == null)
    if (masterKey == null)
      throw new InvalidKeyException("masterKey");
    else
      setupEncRoundKeys();
  decRoundKeys = cloneObject(encRoundKeys);
  doDecKeySetup(masterKey, decRoundKeys, keySize);
}

function cloneObject(obj) {
  var clone = {};
  for (var key in obj) {
    if (typeof obj[key] == "object" && obj[key] != null) {
      clone[key] = cloneObject(obj[key]);
    } else {
      clone[key] = obj[key];
    }
  }

  return clone;
}

function setupRoundKeys() {
  setupDecRoundKeys();
}

function m(t) {
  return 0x00010101 * ((t >>> 24) & 0xff) ^ 0x01000101 * ((t >>> 16) & 0xff) ^
    0x01010001 * ((t >>> 8) & 0xff) ^ 0x01010100 * (t & 0xff);
}

function badc(t) {
  return ((t << 8) & 0xff00ff00) ^ ((t >>> 8) & 0x00ff00ff);
}

function cdab(t) {
  return ((t << 16) & 0xffff0000) ^ ((t >>> 16) & 0x0000ffff);
}

function dcba(t) {
  return (t & 0x000000ff) << 24 ^ (t & 0x0000ff00) << 8 ^ (t & 0x00ff0000) >>> 8 ^ (t & 0xff000000) >>> 24;
}

function encrypt(i, ioffset) {
  let o = Buffer.alloc(16);
  encrypt2(i, ioffset, o, 0);
  return o;
}

function decrypt(i, ioffset) {
  let o = Buffer.alloc(16);
  decrypt2(i, ioffset, o, 0);
  return o;
}

function gsrk(x, y, rot, rk, offset) {
  let q = 4 - (Math.floor(rot / 32)), r = rot % 32, s = 32 - r;

  rk[offset] = x[0] ^ y[(q) % 4] >>> r ^ y[(q + 3) % 4] << s;
  rk[offset + 1] = x[1] ^ y[(q + 1) % 4] >>> r ^ y[(q) % 4] << s;
  rk[offset + 2] = x[2] ^ y[(q + 2) % 4] >>> r ^ y[(q + 1) % 4] << s;
  rk[offset + 3] = x[3] ^ y[(q + 3) % 4] >>> r ^ y[(q + 2) % 4] << s;
}

function toInt(b0, b1, b2, b3) {
  return (b0 & 0xff) << 24 ^ (b1 & 0xff) << 16 ^ (b2 & 0xff) << 8 ^ b3 & 0xff;
}

function doEncKeySetup(mk, rk, keyBits) {
  let t0, t1, t2, t3, q, j = 0;
  let w0 = new Array(4);
  let w1 = new Array(4);
  let w2 = new Array(4);
  let w3 = new Array(4);

  w0[0] = toInt(mk[0], mk[1], mk[2], mk[3]);
  w0[1] = toInt(mk[4], mk[5], mk[6], mk[7]);
  w0[2] = toInt(mk[8], mk[9], mk[10], mk[11]);
  w0[3] = toInt(mk[12], mk[13], mk[14], mk[15]);

  q = (keyBits - 128) / 64;
  t0 = w0[0] ^ KRK[q][0]; t1 = w0[1] ^ KRK[q][1];
  t2 = w0[2] ^ KRK[q][2]; t3 = w0[3] ^ KRK[q][3];
  t0 = TS1[(t0 >>> 24) & 0xff] ^ TS2[(t0 >>> 16) & 0xff] ^ TX1[(t0 >>> 8) & 0xff] ^ TX2[t0 & 0xff];
  t1 = TS1[(t1 >>> 24) & 0xff] ^ TS2[(t1 >>> 16) & 0xff] ^ TX1[(t1 >>> 8) & 0xff] ^ TX2[t1 & 0xff];
  t2 = TS1[(t2 >>> 24) & 0xff] ^ TS2[(t2 >>> 16) & 0xff] ^ TX1[(t2 >>> 8) & 0xff] ^ TX2[t2 & 0xff];
  t3 = TS1[(t3 >>> 24) & 0xff] ^ TS2[(t3 >>> 16) & 0xff] ^ TX1[(t3 >>> 8) & 0xff] ^ TX2[t3 & 0xff];
  t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;
  t1 = badc(t1); t2 = cdab(t2); t3 = dcba(t3);
  t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;

  if (keyBits > 128) {
    w1[0] = toInt(mk[16], mk[17], mk[18], mk[19]);
    w1[1] = toInt(mk[20], mk[21], mk[22], mk[23]);
    if (keyBits > 192) {
      w1[2] = toInt(mk[24], mk[25], mk[26], mk[27]);
      w1[3] = toInt(mk[28], mk[29], mk[30], mk[31]);
    } else {
      w1[2] = w1[3] = 0;
    }
  } else {
    w1[0] = w1[1] = w1[2] = w1[3] = 0;
  }
  w1[0] ^= t0; w1[1] ^= t1; w1[2] ^= t2; w1[3] ^= t3;
  t0 = w1[0]; t1 = w1[1]; t2 = w1[2]; t3 = w1[3];

  q = (q == 2) ? 0 : (q + 1);
  t0 ^= KRK[q][0]; t1 ^= KRK[q][1]; t2 ^= KRK[q][2]; t3 ^= KRK[q][3];
  t0 = TX1[(t0 >>> 24) & 0xff] ^ TX2[(t0 >>> 16) & 0xff] ^ TS1[(t0 >>> 8) & 0xff] ^ TS2[t0 & 0xff];
  t1 = TX1[(t1 >>> 24) & 0xff] ^ TX2[(t1 >>> 16) & 0xff] ^ TS1[(t1 >>> 8) & 0xff] ^ TS2[t1 & 0xff];
  t2 = TX1[(t2 >>> 24) & 0xff] ^ TX2[(t2 >>> 16) & 0xff] ^ TS1[(t2 >>> 8) & 0xff] ^ TS2[t2 & 0xff];
  t3 = TX1[(t3 >>> 24) & 0xff] ^ TX2[(t3 >>> 16) & 0xff] ^ TS1[(t3 >>> 8) & 0xff] ^ TS2[t3 & 0xff];
  t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;
  t3 = badc(t3); t0 = cdab(t0); t1 = dcba(t1);
  t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;
  t0 ^= w0[0]; t1 ^= w0[1]; t2 ^= w0[2]; t3 ^= w0[3];
  w2[0] = t0; w2[1] = t1; w2[2] = t2; w2[3] = t3;

  q = (q == 2) ? 0 : (q + 1);
  t0 ^= KRK[q][0]; t1 ^= KRK[q][1]; t2 ^= KRK[q][2]; t3 ^= KRK[q][3];
  t0 = TS1[(t0 >>> 24) & 0xff] ^ TS2[(t0 >>> 16) & 0xff] ^ TX1[(t0 >>> 8) & 0xff] ^ TX2[t0 & 0xff];
  t1 = TS1[(t1 >>> 24) & 0xff] ^ TS2[(t1 >>> 16) & 0xff] ^ TX1[(t1 >>> 8) & 0xff] ^ TX2[t1 & 0xff];
  t2 = TS1[(t2 >>> 24) & 0xff] ^ TS2[(t2 >>> 16) & 0xff] ^ TX1[(t2 >>> 8) & 0xff] ^ TX2[t2 & 0xff];
  t3 = TS1[(t3 >>> 24) & 0xff] ^ TS2[(t3 >>> 16) & 0xff] ^ TX1[(t3 >>> 8) & 0xff] ^ TX2[t3 & 0xff];
  t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;
  t1 = badc(t1); t2 = cdab(t2); t3 = dcba(t3);
  t1 ^= t2; t2 ^= t3; t0 ^= t1; t3 ^= t1; t2 ^= t0; t1 ^= t2;
  w3[0] = t0 ^ w1[0]; w3[1] = t1 ^ w1[1]; w3[2] = t2 ^ w1[2]; w3[3] = t3 ^ w1[3];

  gsrk(w0, w1, 19, rk, j); j += 4;
  gsrk(w1, w2, 19, rk, j); j += 4;
  gsrk(w2, w3, 19, rk, j); j += 4;
  gsrk(w3, w0, 19, rk, j); j += 4;
  gsrk(w0, w1, 31, rk, j); j += 4;
  gsrk(w1, w2, 31, rk, j); j += 4;
  gsrk(w2, w3, 31, rk, j); j += 4;
  gsrk(w3, w0, 31, rk, j); j += 4;
  gsrk(w0, w1, 67, rk, j); j += 4;
  gsrk(w1, w2, 67, rk, j); j += 4;
  gsrk(w2, w3, 67, rk, j); j += 4;
  gsrk(w3, w0, 67, rk, j); j += 4;
  gsrk(w0, w1, 97, rk, j); j += 4;
  if (keyBits > 128) {
    gsrk(w1, w2, 97, rk, j); j += 4;
    gsrk(w2, w3, 97, rk, j); j += 4;
  }
  if (keyBits > 192) {
    gsrk(w3, w0, 97, rk, j); j += 4;
    gsrk(w0, w1, 109, rk, j);
  }
}

function doDecKeySetup(mk, rk, keyBits) {
  let a = 0, z;
  let t = new Array(4);

  z = 32 + keyBits / 8;
  swapBlocks(rk, 0, z);
  a += 4;
  z -= 4;

  for (; a < z; a += 4, z -= 4)
    swapAndDiffuse(rk, a, z, t);
  diff(rk, a, t, 0);
  rk[a] = t[0];
  rk[a + 1] = t[1];
  rk[a + 2] = t[2];
  rk[a + 3] = t[3];
}

function diff(i, offset1, o, offset2) {
  let t0, t1, t2, t3;

  t0 = m(i[offset1]);
  t1 = m(i[offset1 + 1]);
  t2 = m(i[offset1 + 2]);
  t3 = m(i[offset1 + 3]);
  t1 ^= t2;
  t2 ^= t3;
  t0 ^= t1;
  t3 ^= t1;
  t2 ^= t0;
  t1 ^= t2;
  t1 = badc(t1);
  t2 = cdab(t2);
  t3 = dcba(t3);
  t1 ^= t2;
  t2 ^= t3;
  t0 ^= t1;
  t3 ^= t1;
  t2 ^= t0;
  t1 ^= t2;
  o[offset2] = t0;
  o[offset2 + 1] = t1;
  o[offset2 + 2] = t2;
  o[offset2 + 3] = t3;
}

function swapBlocks(arr, offset1, offset2) {
  let t;

  for (let i = 0; i < 4; i++) {
    t = arr[offset1 + i];
    arr[offset1 + i] = arr[offset2 + i];
    arr[offset2 + i] = t;
  }
}

function swapAndDiffuse(arr, offset1, offset2, tmp) {
  diff(arr, offset1, tmp, 0);
  diff(arr, offset2, arr, offset1);
  arr[offset2] = tmp[0];
  arr[offset2 + 1] = tmp[1];
  arr[offset2 + 2] = tmp[2];
  arr[offset2 + 3] = tmp[3];
}

export {setKeySize,setKey,encrypt,decrypt}