/* Decode arbitrary bytes as simdcomp packed blocks. Every bit pattern is a valid packed block, so the
 * payload is zero-padded to the exact size the decoder reads (heap-exact, so ASan sees any overread). */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "simdcomp.h"

#define HDR 12

static uint32_t rd32(const uint8_t *p) {
  uint32_t v;
  memcpy(&v, p, 4);
  return v;
}

static __m128i *payload(const uint8_t *data, size_t size, size_t need) {
  size_t have = size > HDR ? size - HDR : 0;
  __m128i *buf = (__m128i *)malloc(need ? need : 16);
  memset(buf, 0, need ? need : 16);
  memcpy(buf, data + HDR, have < need ? have : need);
  return buf;
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  uint32_t out[1024 + 128];
  uint32_t op, bit, init, arg;
  size_t need;
  __m128i *buf;
  if (size < HDR)
    return -1;
  op = data[0] % 10;
  bit = data[1] % 33;
  arg = (uint32_t)data[2] | ((uint32_t)data[3] << 8);
  init = rd32(data + 4);
  need = (size_t)bit * sizeof(__m128i);

  switch (op) {
  case 0: {
    buf = payload(data, size, need);
    simdunpack(buf, out, bit);
    break;
  }
  case 1: {
    buf = payload(data, size, need);
    simdunpackFOR(init, buf, out, bit);
    break;
  }
  case 2: {
    buf = payload(data, size, need);
    simdunpackd1(init, buf, out, bit);
    break;
  }
  case 3: {
    size_t length = arg % 1025;
    need = (size_t)simdpack_compressedbytes((int)length, bit);
    buf = payload(data, size, need);
    simdunpack_length(buf, length, out, bit);
    break;
  }
  case 4: {
    int length = (int)(arg % 128);
    need = (size_t)simdpack_compressedbytes(length, bit);
    buf = payload(data, size, need);
    simdunpack_shortlength(buf, length, out, bit);
    break;
  }
  case 5: {
    int length = (int)(arg % 1025);
    /* simdunpackFOR_length handles at most 128 values per call */
    length %= 129;
    need = (size_t)simdpackFOR_compressedbytes(length, bit);
    buf = payload(data, size, need);
    simdunpackFOR_length(init, buf, length, out, bit);
    break;
  }
  case 6: {
    uint32_t slot = rd32(data + 8) % 128;
    volatile uint32_t sink;
    buf = payload(data, size, need);
    sink = simdselectFOR(init, buf, bit, (int)slot);
    sink += simdselectd1(init, buf, bit, (int)slot);
    (void)sink;
    break;
  }
  case 7: {
    uint32_t key = rd32(data + 8), res = 0;
    int length = 1 + (int)(arg % 128);
    __m128i off = _mm_set1_epi32((int)init);
    buf = payload(data, size, need);
    simdsearchd1(&off, buf, bit, key, &res);
    simdsearchwithlengthd1(init, buf, bit, length, key, &res);
    simdsearchwithlengthFOR(init, buf, bit, length, key, &res);
    break;
  }
  case 8: {
    __m128i off = _mm_set1_epi32((int)init);
    buf = payload(data, size, need);
    simdscand1(&off, buf, bit);
    break;
  }
  default: {
    uint32_t value = rd32(data + 8), idx = arg % 128;
    uint32_t mask;
    /* simdfastset requires value < 2^bit, and evaluates 1U << 32 for bit == 32 (upstream UB, benign) */
    if (bit == 0 || bit == 32)
      return -1;
    mask = (1u << bit) - 1;
    value &= mask;
    uint32_t before[128], after[128];
    uint32_t i;
    buf = payload(data, size, need);
    simdunpack(buf, before, bit);
    simdfastset(buf, bit, value, idx);
    simdunpack(buf, after, bit);
    for (i = 0; i < 128; i++) {
      uint32_t want = i == idx ? value : before[i];
      if (after[i] != want)
        abort();
    }
    break;
  }
  }
  free(buf);
  return 0;
}
