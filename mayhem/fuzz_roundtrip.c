/* Pack arbitrary integers with simdcomp, unpack them again and require the original values back,
 * plus agreement of select/search/maxbits with straightforward reference computations. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "simdcomp.h"

#define HDR 8
#define MAXN 1024

static uint32_t rd32(const uint8_t *p) {
  uint32_t v;
  memcpy(&v, p, 4);
  return v;
}

static uint32_t refbits(uint32_t v) {
  uint32_t b = 0;
  while (v) {
    b++;
    v >>= 1;
  }
  return b;
}

static int cmpu32(const void *a, const void *b) {
  uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b;
  return x < y ? -1 : x > y;
}

static void require(int ok) {
  if (!ok)
    abort();
}

static void check_equal(const uint32_t *a, const uint32_t *b, size_t n) {
  require(memcmp(a, b, n * sizeof(uint32_t)) == 0);
}

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  static uint32_t in[MAXN], back[MAXN + 128];
  uint32_t op, selector, i, b, init, mn, mx;
  size_t n, avail;
  __m128i *buf, *end;
  if (size < HDR)
    return -1;
  op = data[0] % 5;
  selector = (uint32_t)data[1] | ((uint32_t)data[2] << 8);
  init = rd32(data + 4);
  avail = (size - HDR) / 4;
  n = avail > MAXN ? MAXN : avail;
  for (i = 0; i < n; i++)
    in[i] = rd32(data + HDR + 4 * i);

  switch (op) {
  case 0: { /* one 128-integer block, plain */
    uint32_t mask;
    if (n < 128)
      return -1;
    mx = 0;
    for (i = 0; i < 128; i++)
      mx |= in[i];
    b = maxbits(in);
    require(b == refbits(mx));
    buf = (__m128i *)malloc(b * sizeof(__m128i) + 16);
    simdpackwithoutmask(in, buf, b);
    simdunpack(buf, back, b);
    check_equal(in, back, 128);
    for (i = 0; i < 128; i += 17)
      require(simdselectFOR(0, buf, b, (int)i) == in[i]);
    b = selector % 33;
    mask = b == 32 ? 0xFFFFFFFFu : ((1u << b) - 1);
    free(buf);
    buf = (__m128i *)malloc(b * sizeof(__m128i) + 16);
    simdpack(in, buf, b);
    simdunpack(buf, back, b);
    for (i = 0; i < 128; i++)
      require(back[i] == (in[i] & mask));
    if (b >= 1 && b <= 31) { /* simdfastset requires value < 2^b and has 1U << 32 UB at b == 32 */
      simdfastset(buf, b, init & mask, selector % 128);
      simdunpack(buf, back, b);
      require(back[selector % 128] == (init & mask));
    }
    free(buf);
    break;
  }
  case 1: { /* arbitrary length, length-aware and short variants */
    size_t len = n;
    int bytes;
    b = maxbits_length(in, (uint32_t)len);
    bytes = simdpack_compressedbytes((int)len, b);
    buf = (__m128i *)malloc(bytes ? bytes : 16);
    end = simdpack_length(in, len, buf, b);
    require((size_t)((char *)end - (char *)buf) <= (size_t)bytes);
    require(simdunpack_length(buf, len, back, b) == end);
    check_equal(in, back, len);
    free(buf);
    if (len > 128)
      len = selector % 129;
    b = maxbits_length(in, (uint32_t)len);
    bytes = simdpack_compressedbytes((int)len, b);
    buf = (__m128i *)malloc(bytes ? bytes : 16);
    end = simdpack_shortlength(in, (int)len, buf, b);
    require((size_t)((char *)end - (char *)buf) <= (size_t)bytes);
    require(simdunpack_shortlength(buf, (int)len, back, b) == end);
    check_equal(in, back, len);
    free(buf);
    break;
  }
  case 2: { /* frame of reference */
    int len;
    if (n < 128)
      return -1;
    mn = mx = in[0];
    for (i = 1; i < 128; i++) {
      if (in[i] < mn)
        mn = in[i];
      if (in[i] > mx)
        mx = in[i];
    }
    require(simdmin(in) == mn);
    b = refbits(mx - mn);
    buf = (__m128i *)malloc(b * sizeof(__m128i) + 16);
    simdpackFOR(mn, in, buf, b);
    simdunpackFOR(mn, buf, back, b);
    check_equal(in, back, 128);
    for (i = 0; i < 128; i += 13)
      require(simdselectFOR(mn, buf, b, (int)i) == in[i]);
    free(buf);
    len = (int)(selector % 129);
    b = refbits(mx - mn);
    buf = (__m128i *)malloc(simdpackFOR_compressedbytes(len, b) + 16);
    end = simdpackFOR_length(mn, in, len, buf, b);
    require(simdunpackFOR_length(mn, buf, len, back, b) == end);
    check_equal(in, back, (size_t)len);
    free(buf);
    break;
  }
  case 3: { /* differential coding on sorted data */
    uint32_t prev, maxdelta = 0, key, res = 0, want;
    int len;
    if (n < 128)
      return -1;
    qsort(in, 128, sizeof(uint32_t), cmpu32);
    if (init > in[0])
      init = in[0];
    prev = init;
    for (i = 0; i < 128; i++) {
      if (in[i] - prev > maxdelta)
        maxdelta = in[i] - prev;
      prev = in[i];
    }
    b = simdmaxbitsd1(init, in);
    require(b == refbits(maxdelta));
    buf = (__m128i *)malloc(b * sizeof(__m128i) + 16);
    simdpackwithoutmaskd1(init, in, buf, b);
    simdunpackd1(init, buf, back, b);
    check_equal(in, back, 128);
    for (i = 0; i < 128; i += 11)
      require(simdselectd1(init, buf, b, (int)i) == in[i]);
    key = in[selector % 128] + (uint32_t)(selector >> 7 & 1);
    len = (int)(selector % 129);
    for (want = 0; want < (uint32_t)len && in[want] < key; want++)
      ;
    if (len > 0 && key > in[0] && key >= init) {
      int pos = simdsearchwithlengthd1(init, buf, b, len, key, &res);
      require((uint32_t)pos == want);
      if (want < (uint32_t)len)
        require(res == in[want]);
    }
    if (b >= 1 && b <= 31) { /* simdfastset has 1U << 32 UB at b == 32 */
      simdfastsetd1(init, buf, b, in[selector % 128], selector % 128);
      simdunpackd1(init, buf, back, b);
      check_equal(in, back, 128);
    }
    free(buf);
    break;
  }
  default: { /* integrated d1 search over a whole block */
    uint32_t prev, maxdelta = 0, key, res = 0, want;
    __m128i off;
    int pos;
    if (n < 128)
      return -1;
    qsort(in, 128, sizeof(uint32_t), cmpu32);
    if (init > in[0])
      init = in[0];
    prev = init;
    for (i = 0; i < 128; i++) {
      if (in[i] - prev > maxdelta)
        maxdelta = in[i] - prev;
      prev = in[i];
    }
    b = refbits(maxdelta);
    buf = (__m128i *)malloc(b * sizeof(__m128i) + 16);
    simdpackwithoutmaskd1(init, in, buf, b);
    key = in[selector % 128];
    for (want = 0; want < 128 && in[want] < key; want++)
      ;
    off = _mm_set1_epi32((int)init);
    pos = simdsearchd1(&off, buf, b, key, &res);
    require((uint32_t)pos == want && res == in[want]);
    free(buf);
    break;
  }
  }
  return 0;
}
