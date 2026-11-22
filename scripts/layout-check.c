/* C side of the layout test (scripts/layout-check.sh, Tests/Layout.lean).
   Each line: name sizeof _Alignof offsetof(field)... ; sums are struct { tag; union } and
   print the tag and union offsets. Keep in the order of `Tests.Layout.table`.
   PACKED is defined only by the self-test (a seeded layout bug). */
#include <stdio.h>
#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#ifdef PACKED
#define ATTR __attribute__((packed))
#else
#define ATTR
#endif

struct S1 { uint8_t a; uint64_t b; } ATTR;
struct S2 { uint8_t a; uint16_t b; uint8_t c; } ATTR;
struct S3 { uint32_t a; uint8_t b; } ATTR;
struct S4 { uint64_t a; uint8_t b[3]; uint16_t c; } ATTR;
struct S5 { uint8_t a; struct S1 inner; uint8_t c; } ATTR;
struct S6 { bool flag; int32_t x; int16_t y; } ATTR;
struct S7 { } ATTR;
struct S8 { uint16_t a[5]; uint8_t b; } ATTR;
struct S9 { int8_t a; int64_t b; int8_t c; } ATTR;
struct S10 { uint8_t a; char inv[0]; uint32_t b; } ATTR;
struct S11 { uint8_t n; uint64_t cells[4]; } ATTR;
struct S12 { struct { uint8_t x; uint16_t y; } p; uint8_t c; } ATTR;
struct S13 { uint32_t a[3]; uint64_t b; } ATTR;
struct E1 { uint8_t tag; union { uint8_t a; uint64_t b; struct { uint16_t x; uint32_t y; } c; } u; } ATTR;
struct ExceptU8U64 { uint8_t tag; union { uint8_t e; uint64_t a; } u; } ATTR;
struct OptionU32 { uint8_t tag; union { struct { } n; uint32_t s; } u; } ATTR;

#define L(T) printf("%s %zu %zu", #T, sizeof(struct T), _Alignof(struct T))
#define O(T, f) printf(" %zu", offsetof(struct T, f))
#define E() printf("\n")

int main(void) {
  L(S1); O(S1, a); O(S1, b); E();
  L(S2); O(S2, a); O(S2, b); O(S2, c); E();
  L(S3); O(S3, a); O(S3, b); E();
  L(S4); O(S4, a); O(S4, b); O(S4, c); E();
  L(S5); O(S5, a); O(S5, inner); O(S5, c); E();
  L(S6); O(S6, flag); O(S6, x); O(S6, y); E();
  L(S7); E();
  L(S8); O(S8, a); O(S8, b); E();
  L(S9); O(S9, a); O(S9, b); O(S9, c); E();
  L(S10); O(S10, a); O(S10, inv); O(S10, b); E();
  L(S11); O(S11, n); O(S11, cells); E();
  L(S12); O(S12, p); O(S12, c); E();
  L(S13); O(S13, a); O(S13, b); E();
  L(E1); O(E1, tag); O(E1, u); E();
  L(ExceptU8U64); O(ExceptU8U64, tag); O(ExceptU8U64, u); E();
  L(OptionU32); O(OptionU32, tag); O(OptionU32, u); E();
  return 0;
}
