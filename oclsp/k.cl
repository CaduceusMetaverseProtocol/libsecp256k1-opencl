/*
 * OpenCL Implement Secp256k1 verify and recover.
 */
typedef ulong uint64_t;
typedef uint uint32_t;

#ifdef DETERMINISTIC
#define CHECK(cond) do { \
    if (EXPECT(!(cond), 0)) { \
        TEST_FAILURE("test condition failed"); \
    } \
} while(0)
#else
#define CHECK(cond) do { \
    if (EXPECT(!(cond), 0)) { \
        TEST_FAILURE("test condition failed: " #cond); \
    } \
} while(0)
#endif

/* Like assert(), but when VERIFY is defined, and side-effect safe. */
#ifdef VERIFY
#define VERIFY_CHECK CHECK
#define VERIFY_SETUP(stmt) do { stmt; } while(0)
#else
#define VERIFY_CHECK(cond) do { (void)(cond); } while(0)
#define VERIFY_SETUP(stmt)
#endif

#undef VERIFY_CHECK
#undef VERIFY_CHECK(cond)
#define VERIFY_CHECK(cond) do { (void)(cond); } while(0)


#define SECP256K1_RESTRICT
#define WINDOW_A 5 
#define WINDOW_G 16
#define ECMULT_TABLE_SIZE(w) (1 << ((w)-2))

/* Unpacks a constant into a overlapping multi-limbed FE element. */
#define SECP256K1_FE_CONST_INNER(d7, d6, d5, d4, d3, d2, d1, d0) { \
    (d0) & 0x3FFFFFFUL, \
    (((uint32_t)d0) >> 26) | (((uint32_t)(d1) & 0xFFFFFUL) << 6), \
    (((uint32_t)d1) >> 20) | (((uint32_t)(d2) & 0x3FFFUL) << 12), \
    (((uint32_t)d2) >> 14) | (((uint32_t)(d3) & 0xFFUL) << 18), \
    (((uint32_t)d3) >> 8) | (((uint32_t)(d4) & 0x3UL) << 24), \
    (((uint32_t)d4) >> 2) & 0x3FFFFFFUL, \
    (((uint32_t)d4) >> 28) | (((uint32_t)(d5) & 0x3FFFFFUL) << 4), \
    (((uint32_t)d5) >> 22) | (((uint32_t)(d6) & 0xFFFFUL) << 10), \
    (((uint32_t)d6) >> 16) | (((uint32_t)(d7) & 0x3FFUL) << 16), \
    (((uint32_t)d7) >> 10) \
}

#define SECP256K1_FE_CONST(d7, d6, d5, d4, d3, d2, d1, d0) {SECP256K1_FE_CONST_INNER((d7), (d6), (d5), (d4), (d3), (d2), (d1), (d0)), 1, 1}

/* Limbs of the secp256k1 order. */
#define SECP256K1_N_0 ((uint32_t)0xD0364141UL)
#define SECP256K1_N_1 ((uint32_t)0xBFD25E8CUL)
#define SECP256K1_N_2 ((uint32_t)0xAF48A03BUL)
#define SECP256K1_N_3 ((uint32_t)0xBAAEDCE6UL)
#define SECP256K1_N_4 ((uint32_t)0xFFFFFFFEUL)
#define SECP256K1_N_5 ((uint32_t)0xFFFFFFFFUL)
#define SECP256K1_N_6 ((uint32_t)0xFFFFFFFFUL)
#define SECP256K1_N_7 ((uint32_t)0xFFFFFFFFUL)

/* Limbs of 2^256 minus the secp256k1 order. */
#define SECP256K1_N_C_0 (~SECP256K1_N_0 + 1)
#define SECP256K1_N_C_1 (~SECP256K1_N_1)
#define SECP256K1_N_C_2 (~SECP256K1_N_2)
#define SECP256K1_N_C_3 (~SECP256K1_N_3)
#define SECP256K1_N_C_4 (1)

/* Limbs of half the secp256k1 order. */
#define SECP256K1_N_H_0 ((uint32_t)0x681B20A0UL)
#define SECP256K1_N_H_1 ((uint32_t)0xDFE92F46UL)
#define SECP256K1_N_H_2 ((uint32_t)0x57A4501DUL)
#define SECP256K1_N_H_3 ((uint32_t)0x5D576E73UL)
#define SECP256K1_N_H_4 ((uint32_t)0xFFFFFFFFUL)
#define SECP256K1_N_H_5 ((uint32_t)0xFFFFFFFFUL)
#define SECP256K1_N_H_6 ((uint32_t)0xFFFFFFFFUL)
#define SECP256K1_N_H_7 ((uint32_t)0x7FFFFFFFUL)

#define muladd(a,b) { \
	uint32_t tl, th; \
	{ \
		uint64_t t = (uint64_t)a * b; \
		th = t >> 32;		  /* at most 0xFFFFFFFE */ \
		tl = t; \
	} \
	c0 += tl;				  /* overflow is handled on the next line */ \
	th += (c0 < tl) ? 1 : 0;  /* at most 0xFFFFFFFF */ \
	c1 += th;				  /* overflow is handled on the next line */ \
	c2 += (c1 < th) ? 1 : 0;  /* never overflows by contract (verified in the next line) */ \
}

/** Add a*b to the number defined by (c0,c1). c1 must never overflow. */
#define muladd_fast(a,b) { \
	uint32_t tl, th; \
	{ \
		uint64_t t = (uint64_t)a * b; \
		th = t >> 32;		  /* at most 0xFFFFFFFE */ \
		tl = t; \
	} \
	c0 += tl;				  /* overflow is handled on the next line */ \
	th += (c0 < tl) ? 1 : 0;  /* at most 0xFFFFFFFF */ \
	c1 += th;				  /* never overflows by contract (verified in the next line) */ \
}

/** Add 2*a*b to the number defined by (c0,c1,c2). c2 must never overflow. */
#define muladd2(a,b) { \
	uint32_t tl, th, th2, tl2; \
	{ \
		uint64_t t = (uint64_t)a * b; \
		th = t >> 32;				/* at most 0xFFFFFFFE */ \
		tl = t; \
	} \
	th2 = th + th;					/* at most 0xFFFFFFFE (in case th was 0x7FFFFFFF) */ \
	c2 += (th2 < th) ? 1 : 0;		/* never overflows by contract (verified the next line) */ \
	VERIFY_CHECK((th2 >= th) || (c2 != 0)); \
	tl2 = tl + tl;					/* at most 0xFFFFFFFE (in case the lowest 63 bits of tl were 0x7FFFFFFF) */ \
	th2 += (tl2 < tl) ? 1 : 0;		/* at most 0xFFFFFFFF */ \
	c0 += tl2;						/* overflow is handled on the next line */ \
	th2 += (c0 < tl2) ? 1 : 0;		/* second overflow is handled on the next line */ \
	c2 += (c0 < tl2) & (th2 == 0);	/* never overflows by contract (verified the next line) */ \
	VERIFY_CHECK((c0 >= tl2) || (th2 != 0) || (c2 != 0)); \
	c1 += th2;						/* overflow is handled on the next line */ \
	c2 += (c1 < th2) ? 1 : 0;		/* never overflows by contract (verified the next line) */ \
}

/** Add a to the number defined by (c0,c1,c2). c2 must never overflow. */
#define sumadd(a) { \
	unsigned int over; \
	c0 += (a);					/* overflow is handled on the next line */ \
	over = (c0 < (a)) ? 1 : 0; \
	c1 += over; 				/* overflow is handled on the next line */ \
	c2 += (c1 < over) ? 1 : 0;	/* never overflows by contract */ \
}

/** Add a to the number defined by (c0,c1). c1 must never overflow, c2 must be zero. */
#define sumadd_fast(a) { \
	c0 += (a);				   /* overflow is handled on the next line */ \
	c1 += (c0 < (a)) ? 1 : 0;  /* never overflows by contract (verified the next line) */ \
	VERIFY_CHECK((c1 != 0) | (c0 >= (a))); \
	VERIFY_CHECK(c2 == 0); \
}

/** Extract the lowest 32 bits of (c0,c1,c2) into n, and left shift the number 32 bits. */
#define extract(n) { \
	(n) = c0; \
	c0 = c1; \
	c1 = c2; \
	c2 = 0; \
}

/** Extract the lowest 32 bits of (c0,c1,c2) into n, and left shift the number 32 bits. c2 is required to be zero. */
#define extract_fast(n) { \
	(n) = c0; \
	c0 = c1; \
	c1 = 0; \
	VERIFY_CHECK(c2 == 0); \
}

typedef struct {
    uint32_t d[8];
} secp256k1_scalarX;

typedef struct {
    uint32_t n[10];
    int magnitude;
    int normalized;
} secp256k1_feX;

typedef struct {
    secp256k1_feX x;
    secp256k1_feX y;
    int infinity; /* whether this represents the point at infinity */
} secp256k1_geX;

typedef struct {
    secp256k1_feX x; /* actual X: x/z^2 */
    secp256k1_feX y; /* actual Y: y/z^3 */
    secp256k1_feX z;
    int infinity; /* whether this represents the point at infinity */
} secp256k1_gejX;

typedef struct {
    uint32_t n[8];
} secp256k1_fe_storageX;

typedef struct {
    secp256k1_fe_storageX x;
    secp256k1_fe_storageX y;
} secp256k1_ge_storageX;

typedef struct {
    unsigned char data[64];
} secp256k1_ecdsa_signatureX;

typedef struct {
    unsigned char data[64];
} secp256k1_pubkeyX;

__constant secp256k1_feX secp256k1_ecdsa_const_p_minus_orderX = SECP256K1_FE_CONST(
    0, 0, 0, 1, 0x45512319UL, 0x50B75FC4UL, 0x402DA172UL, 0x2FC9BAEEUL
);

__constant secp256k1_feX secp256k1_ecdsa_const_order_as_feX = SECP256K1_FE_CONST(
    0xFFFFFFFFUL, 0xFFFFFFFFUL, 0xFFFFFFFFUL, 0xFFFFFFFEUL,
    0xBAAEDCE6UL, 0xAF48A03BUL, 0xBFD25E8CUL, 0xD0364141UL
);

int secp256k1_scalar_check_overflowX(secp256k1_scalarX *a) {
    int yes = 0;
	int no = 0;
	no |= (a->d[7] < SECP256K1_N_7); /* No need for a > check. */
	no |= (a->d[6] < SECP256K1_N_6); /* No need for a > check. */
	no |= (a->d[5] < SECP256K1_N_5); /* No need for a > check. */
	no |= (a->d[4] < SECP256K1_N_4);
	yes |= (a->d[4] > SECP256K1_N_4) & ~no;
	no |= (a->d[3] < SECP256K1_N_3) & ~yes;
	yes |= (a->d[3] > SECP256K1_N_3) & ~no;
	no |= (a->d[2] < SECP256K1_N_2) & ~yes;
	yes |= (a->d[2] > SECP256K1_N_2) & ~no;
	no |= (a->d[1] < SECP256K1_N_1) & ~yes;
	yes |= (a->d[1] > SECP256K1_N_1) & ~no;
	yes |= (a->d[0] >= SECP256K1_N_0) & ~no;
	return yes;
}

int secp256k1_scalar_reduceX(secp256k1_scalarX *r, unsigned int overflow) {
    uint64_t t;
	VERIFY_CHECK(overflow <= 1);
	t = (uint64_t)r->d[0] + overflow * SECP256K1_N_C_0;
	r->d[0] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)r->d[1] + overflow * SECP256K1_N_C_1;
	r->d[1] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)r->d[2] + overflow * SECP256K1_N_C_2;
	r->d[2] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)r->d[3] + overflow * SECP256K1_N_C_3;
	r->d[3] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)r->d[4] + overflow * SECP256K1_N_C_4;
	r->d[4] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)r->d[5];
	r->d[5] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)r->d[6];
	r->d[6] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)r->d[7];
	r->d[7] = t & 0xFFFFFFFFUL;
	return overflow;
}

static void secp256k1_scalar_set_b32X(secp256k1_scalarX *r, __global const unsigned char *b32, int *overflow) {
    int over;
	r->d[0] = (uint32_t)b32[31] | (uint32_t)b32[30] << 8 | (uint32_t)b32[29] << 16 | (uint32_t)b32[28] << 24;
	r->d[1] = (uint32_t)b32[27] | (uint32_t)b32[26] << 8 | (uint32_t)b32[25] << 16 | (uint32_t)b32[24] << 24;
	r->d[2] = (uint32_t)b32[23] | (uint32_t)b32[22] << 8 | (uint32_t)b32[21] << 16 | (uint32_t)b32[20] << 24;
	r->d[3] = (uint32_t)b32[19] | (uint32_t)b32[18] << 8 | (uint32_t)b32[17] << 16 | (uint32_t)b32[16] << 24;
	r->d[4] = (uint32_t)b32[15] | (uint32_t)b32[14] << 8 | (uint32_t)b32[13] << 16 | (uint32_t)b32[12] << 24;
	r->d[5] = (uint32_t)b32[11] | (uint32_t)b32[10] << 8 | (uint32_t)b32[9] << 16 | (uint32_t)b32[8] << 24;
	r->d[6] = (uint32_t)b32[7] | (uint32_t)b32[6] << 8 | (uint32_t)b32[5] << 16 | (uint32_t)b32[4] << 24;
	r->d[7] = (uint32_t)b32[3] | (uint32_t)b32[2] << 8 | (uint32_t)b32[1] << 16 | (uint32_t)b32[0] << 24;
	over = secp256k1_scalar_reduceX(r, secp256k1_scalar_check_overflowX(r));
	if (overflow) {
		*overflow = over;
	}
}

int memcmpX(unsigned char *s1, unsigned char *s2, int len)
{
	int i = 0;
	for(i=0; i < len; i++)
	{
		if(s1[i] == s2[i]) {
			continue;
		}
		if(s1[i] > s2[i])
			return 1;
		if(s1[i] < s2[i])
			return -1;
	}
	return 0;
}

void memcpyX(void *dest, __global const void *src, size_t len)
{
  char *d = dest;
  __global const char *s = src;
  while (len--)
    *d++ = *s++;
}

void memcpy_to_global(__global void *dest, const void *src, size_t len)
{
  __global char *d = dest;
  const char *s = src;
  while (len--)
    *d++ = *s++;
}

void private_memcpy(void *dest, const void *src, size_t len)
{
	char *d = dest;
  	const char *s = src;
  	while (len--)
    	*d++ = *s++;
}

static void secp256k1_fe_verifyX(const secp256k1_feX *a) {
    const uint32_t *d = a->n;
    int m = a->normalized ? 1 : 2 * a->magnitude, r = 1;
    r &= (d[0] <= 0x3FFFFFFUL * m);
    r &= (d[1] <= 0x3FFFFFFUL * m);
    r &= (d[2] <= 0x3FFFFFFUL * m);
    r &= (d[3] <= 0x3FFFFFFUL * m);
    r &= (d[4] <= 0x3FFFFFFUL * m);
    r &= (d[5] <= 0x3FFFFFFUL * m);
    r &= (d[6] <= 0x3FFFFFFUL * m);
    r &= (d[7] <= 0x3FFFFFFUL * m);
    r &= (d[8] <= 0x3FFFFFFUL * m);
    r &= (d[9] <= 0x03FFFFFUL * m);
    r &= (a->magnitude >= 0);
    r &= (a->magnitude <= 32);
    if (a->normalized) {
        r &= (a->magnitude <= 1);
        if (r && (d[9] == 0x03FFFFFUL)) {
            uint32_t mid = d[8] & d[7] & d[6] & d[5] & d[4] & d[3] & d[2];
            if (mid == 0x3FFFFFFUL) {
                r &= ((d[1] + 0x40UL + ((d[0] + 0x3D1UL) >> 26)) <= 0x3FFFFFFUL);
            }
        }
    }
    VERIFY_CHECK(r == 1);
}

int secp256k1_scalar_is_zeroX(const secp256k1_scalarX *a) {
    return (a->d[0] | a->d[1] | a->d[2] | a->d[3] | a->d[4] | a->d[5] | a->d[6] | a->d[7]) == 0;
}

void secp256k1_scalar_sqr_512X(uint32_t *l, const secp256k1_scalarX *a) {
    /* 96 bit accumulator. */
	uint32_t c0 = 0, c1 = 0, c2 = 0;

	/* l[0..15] = a[0..7]^2. */
	muladd_fast(a->d[0], a->d[0]);
	extract_fast(l[0]);
	muladd2(a->d[0], a->d[1]);
	extract(l[1]);
	muladd2(a->d[0], a->d[2]);
	muladd(a->d[1], a->d[1]);
	extract(l[2]);
	muladd2(a->d[0], a->d[3]);
	muladd2(a->d[1], a->d[2]);
	extract(l[3]);
	muladd2(a->d[0], a->d[4]);
	muladd2(a->d[1], a->d[3]);
	muladd(a->d[2], a->d[2]);
	extract(l[4]);
	muladd2(a->d[0], a->d[5]);
	muladd2(a->d[1], a->d[4]);
	muladd2(a->d[2], a->d[3]);
	extract(l[5]);
	muladd2(a->d[0], a->d[6]);
	muladd2(a->d[1], a->d[5]);
	muladd2(a->d[2], a->d[4]);
	muladd(a->d[3], a->d[3]);
	extract(l[6]);
	muladd2(a->d[0], a->d[7]);
	muladd2(a->d[1], a->d[6]);
	muladd2(a->d[2], a->d[5]);
	muladd2(a->d[3], a->d[4]);
	extract(l[7]);
	muladd2(a->d[1], a->d[7]);
	muladd2(a->d[2], a->d[6]);
	muladd2(a->d[3], a->d[5]);
	muladd(a->d[4], a->d[4]);
	extract(l[8]);
	muladd2(a->d[2], a->d[7]);
	muladd2(a->d[3], a->d[6]);
	muladd2(a->d[4], a->d[5]);
	extract(l[9]);
	muladd2(a->d[3], a->d[7]);
	muladd2(a->d[4], a->d[6]);
	muladd(a->d[5], a->d[5]);
	extract(l[10]);
	muladd2(a->d[4], a->d[7]);
	muladd2(a->d[5], a->d[6]);
	extract(l[11]);
	muladd2(a->d[5], a->d[7]);
	muladd(a->d[6], a->d[6]);
	extract(l[12]);
	muladd2(a->d[6], a->d[7]);
	extract(l[13]);
	muladd_fast(a->d[7], a->d[7]);
	extract_fast(l[14]);
	VERIFY_CHECK(c1 == 0);
	l[15] = c0;
}

static void secp256k1_scalar_reduce_512X(secp256k1_scalarX *r, const uint32_t *l) {
    uint64_t c;
	uint32_t n0 = l[8], n1 = l[9], n2 = l[10], n3 = l[11], n4 = l[12], n5 = l[13], n6 = l[14], n7 = l[15];
	uint32_t m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12;
	uint32_t p0, p1, p2, p3, p4, p5, p6, p7, p8;

	/* 96 bit accumulator. */
	uint32_t c0, c1, c2;

	/* Reduce 512 bits into 385. */
	/* m[0..12] = l[0..7] + n[0..7] * SECP256K1_N_C. */
	c0 = l[0]; c1 = 0; c2 = 0;
	muladd_fast(n0, SECP256K1_N_C_0);
	extract_fast(m0);
	sumadd_fast(l[1]);
	muladd(n1, SECP256K1_N_C_0);
	muladd(n0, SECP256K1_N_C_1);
	extract(m1);
	sumadd(l[2]);
	muladd(n2, SECP256K1_N_C_0);
	muladd(n1, SECP256K1_N_C_1);
	muladd(n0, SECP256K1_N_C_2);
	extract(m2);
	sumadd(l[3]);
	muladd(n3, SECP256K1_N_C_0);
	muladd(n2, SECP256K1_N_C_1);
	muladd(n1, SECP256K1_N_C_2);
	muladd(n0, SECP256K1_N_C_3);
	extract(m3);
	sumadd(l[4]);
	muladd(n4, SECP256K1_N_C_0);
	muladd(n3, SECP256K1_N_C_1);
	muladd(n2, SECP256K1_N_C_2);
	muladd(n1, SECP256K1_N_C_3);
	sumadd(n0);
	extract(m4);
	sumadd(l[5]);
	muladd(n5, SECP256K1_N_C_0);
	muladd(n4, SECP256K1_N_C_1);
	muladd(n3, SECP256K1_N_C_2);
	muladd(n2, SECP256K1_N_C_3);
	sumadd(n1);
	extract(m5);
	sumadd(l[6]);
	muladd(n6, SECP256K1_N_C_0);
	muladd(n5, SECP256K1_N_C_1);
	muladd(n4, SECP256K1_N_C_2);
	muladd(n3, SECP256K1_N_C_3);
	sumadd(n2);
	extract(m6);
	sumadd(l[7]);
	muladd(n7, SECP256K1_N_C_0);
	muladd(n6, SECP256K1_N_C_1);
	muladd(n5, SECP256K1_N_C_2);
	muladd(n4, SECP256K1_N_C_3);
	sumadd(n3);
	extract(m7);
	muladd(n7, SECP256K1_N_C_1);
	muladd(n6, SECP256K1_N_C_2);
	muladd(n5, SECP256K1_N_C_3);
	sumadd(n4);
	extract(m8);
	muladd(n7, SECP256K1_N_C_2);
	muladd(n6, SECP256K1_N_C_3);
	sumadd(n5);
	extract(m9);
	muladd(n7, SECP256K1_N_C_3);
	sumadd(n6);
	extract(m10);
	sumadd_fast(n7);
	extract_fast(m11);
	VERIFY_CHECK(c0 <= 1);
	m12 = c0;

	/* Reduce 385 bits into 258. */
	/* p[0..8] = m[0..7] + m[8..12] * SECP256K1_N_C. */
	c0 = m0; c1 = 0; c2 = 0;
	muladd_fast(m8, SECP256K1_N_C_0);
	extract_fast(p0);
	sumadd_fast(m1);
	muladd(m9, SECP256K1_N_C_0);
	muladd(m8, SECP256K1_N_C_1);
	extract(p1);
	sumadd(m2);
	muladd(m10, SECP256K1_N_C_0);
	muladd(m9, SECP256K1_N_C_1);
	muladd(m8, SECP256K1_N_C_2);
	extract(p2);
	sumadd(m3);
	muladd(m11, SECP256K1_N_C_0);
	muladd(m10, SECP256K1_N_C_1);
	muladd(m9, SECP256K1_N_C_2);
	muladd(m8, SECP256K1_N_C_3);
	extract(p3);
	sumadd(m4);
	muladd(m12, SECP256K1_N_C_0);
	muladd(m11, SECP256K1_N_C_1);
	muladd(m10, SECP256K1_N_C_2);
	muladd(m9, SECP256K1_N_C_3);
	sumadd(m8);
	extract(p4);
	sumadd(m5);
	muladd(m12, SECP256K1_N_C_1);
	muladd(m11, SECP256K1_N_C_2);
	muladd(m10, SECP256K1_N_C_3);
	sumadd(m9);
	extract(p5);
	sumadd(m6);
	muladd(m12, SECP256K1_N_C_2);
	muladd(m11, SECP256K1_N_C_3);
	sumadd(m10);
	extract(p6);
	sumadd_fast(m7);
	muladd_fast(m12, SECP256K1_N_C_3);
	sumadd_fast(m11);
	extract_fast(p7);
	p8 = c0 + m12;
	VERIFY_CHECK(p8 <= 2);

	/* Reduce 258 bits into 256. */
	/* r[0..7] = p[0..7] + p[8] * SECP256K1_N_C. */
	c = p0 + (uint64_t)SECP256K1_N_C_0 * p8;
	r->d[0] = c & 0xFFFFFFFFUL; c >>= 32;
	c += p1 + (uint64_t)SECP256K1_N_C_1 * p8;
	r->d[1] = c & 0xFFFFFFFFUL; c >>= 32;
	c += p2 + (uint64_t)SECP256K1_N_C_2 * p8;
	r->d[2] = c & 0xFFFFFFFFUL; c >>= 32;
	c += p3 + (uint64_t)SECP256K1_N_C_3 * p8;
	r->d[3] = c & 0xFFFFFFFFUL; c >>= 32;
	c += p4 + (uint64_t)p8;
	r->d[4] = c & 0xFFFFFFFFUL; c >>= 32;
	c += p5;
	r->d[5] = c & 0xFFFFFFFFUL; c >>= 32;
	c += p6;
	r->d[6] = c & 0xFFFFFFFFUL; c >>= 32;
	c += p7;
	r->d[7] = c & 0xFFFFFFFFUL; c >>= 32;

	/* Final reduction of r. */
	secp256k1_scalar_reduceX(r, c + secp256k1_scalar_check_overflowX(r));
}

void secp256k1_scalar_sqrX(secp256k1_scalarX *r, const secp256k1_scalarX *a) {
    uint32_t l[16];
	secp256k1_scalar_sqr_512X(l, a);
	secp256k1_scalar_reduce_512X(r, l);
}

static void secp256k1_scalar_mul_512X(uint32_t *l, const secp256k1_scalarX *a, const secp256k1_scalarX *b) {
    /* 96 bit accumulator. */
	uint32_t c0 = 0, c1 = 0, c2 = 0;

	/* l[0..15] = a[0..7] * b[0..7]. */
	muladd_fast(a->d[0], b->d[0]);
	extract_fast(l[0]);
	muladd(a->d[0], b->d[1]);
	muladd(a->d[1], b->d[0]);
	extract(l[1]);
	muladd(a->d[0], b->d[2]);
	muladd(a->d[1], b->d[1]);
	muladd(a->d[2], b->d[0]);
	extract(l[2]);
	muladd(a->d[0], b->d[3]);
	muladd(a->d[1], b->d[2]);
	muladd(a->d[2], b->d[1]);
	muladd(a->d[3], b->d[0]);
	extract(l[3]);
	muladd(a->d[0], b->d[4]);
	muladd(a->d[1], b->d[3]);
	muladd(a->d[2], b->d[2]);
	muladd(a->d[3], b->d[1]);
	muladd(a->d[4], b->d[0]);
	extract(l[4]);
	muladd(a->d[0], b->d[5]);
	muladd(a->d[1], b->d[4]);
	muladd(a->d[2], b->d[3]);
	muladd(a->d[3], b->d[2]);
	muladd(a->d[4], b->d[1]);
	muladd(a->d[5], b->d[0]);
	extract(l[5]);
	muladd(a->d[0], b->d[6]);
	muladd(a->d[1], b->d[5]);
	muladd(a->d[2], b->d[4]);
	muladd(a->d[3], b->d[3]);
	muladd(a->d[4], b->d[2]);
	muladd(a->d[5], b->d[1]);
	muladd(a->d[6], b->d[0]);
	extract(l[6]);
	muladd(a->d[0], b->d[7]);
	muladd(a->d[1], b->d[6]);
	muladd(a->d[2], b->d[5]);
	muladd(a->d[3], b->d[4]);
	muladd(a->d[4], b->d[3]);
	muladd(a->d[5], b->d[2]);
	muladd(a->d[6], b->d[1]);
	muladd(a->d[7], b->d[0]);
	extract(l[7]);
	muladd(a->d[1], b->d[7]);
	muladd(a->d[2], b->d[6]);
	muladd(a->d[3], b->d[5]);
	muladd(a->d[4], b->d[4]);
	muladd(a->d[5], b->d[3]);
	muladd(a->d[6], b->d[2]);
	muladd(a->d[7], b->d[1]);
	extract(l[8]);
	muladd(a->d[2], b->d[7]);
	muladd(a->d[3], b->d[6]);
	muladd(a->d[4], b->d[5]);
	muladd(a->d[5], b->d[4]);
	muladd(a->d[6], b->d[3]);
	muladd(a->d[7], b->d[2]);
	extract(l[9]);
	muladd(a->d[3], b->d[7]);
	muladd(a->d[4], b->d[6]);
	muladd(a->d[5], b->d[5]);
	muladd(a->d[6], b->d[4]);
	muladd(a->d[7], b->d[3]);
	extract(l[10]);
	muladd(a->d[4], b->d[7]);
	muladd(a->d[5], b->d[6]);
	muladd(a->d[6], b->d[5]);
	muladd(a->d[7], b->d[4]);
	extract(l[11]);
	muladd(a->d[5], b->d[7]);
	muladd(a->d[6], b->d[6]);
	muladd(a->d[7], b->d[5]);
	extract(l[12]);
	muladd(a->d[6], b->d[7]);
	muladd(a->d[7], b->d[6]);
	extract(l[13]);
	muladd_fast(a->d[7], b->d[7]);
	extract_fast(l[14]);
	VERIFY_CHECK(c1 == 0);
	l[15] = c0;
}

void secp256k1_scalar_mulX(secp256k1_scalarX *r, const secp256k1_scalarX *a, const secp256k1_scalarX *b) {
    uint32_t l[16];
	secp256k1_scalar_mul_512X(l, a, b);
	secp256k1_scalar_reduce_512X(r, l);
}

void secp256k1_scalar_inverseX(secp256k1_scalarX *r, const secp256k1_scalarX *x) {
    secp256k1_scalarX *t;
    int i;
    /* First compute x ^ (2^N - 1) for some values of N. */
    secp256k1_scalarX x2, x3, x4, x6, x7, x8, x15, x30, x60, x120, x127;

    secp256k1_scalar_sqrX(&x2,  x);
    secp256k1_scalar_mulX(&x2, &x2,  x);

    secp256k1_scalar_sqrX(&x3, &x2);
    secp256k1_scalar_mulX(&x3, &x3,  x);

    secp256k1_scalar_sqrX(&x4, &x3);
    secp256k1_scalar_mulX(&x4, &x4,  x);

    secp256k1_scalar_sqrX(&x6, &x4);
    secp256k1_scalar_sqrX(&x6, &x6);
    secp256k1_scalar_mulX(&x6, &x6, &x2);

    secp256k1_scalar_sqrX(&x7, &x6);
    secp256k1_scalar_mulX(&x7, &x7,  x);

    secp256k1_scalar_sqrX(&x8, &x7);
    secp256k1_scalar_mulX(&x8, &x8,  x);

    secp256k1_scalar_sqrX(&x15, &x8);
    for (i = 0; i < 6; i++) {
        secp256k1_scalar_sqrX(&x15, &x15);
    }
    secp256k1_scalar_mulX(&x15, &x15, &x7);

    secp256k1_scalar_sqrX(&x30, &x15);
    for (i = 0; i < 14; i++) {
        secp256k1_scalar_sqrX(&x30, &x30);
    }
    secp256k1_scalar_mulX(&x30, &x30, &x15);

    secp256k1_scalar_sqrX(&x60, &x30);
    for (i = 0; i < 29; i++) {
        secp256k1_scalar_sqrX(&x60, &x60);
    }
    secp256k1_scalar_mulX(&x60, &x60, &x30);

    secp256k1_scalar_sqrX(&x120, &x60);
    for (i = 0; i < 59; i++) {
        secp256k1_scalar_sqrX(&x120, &x120);
    }
    secp256k1_scalar_mulX(&x120, &x120, &x60);

    secp256k1_scalar_sqrX(&x127, &x120);
    for (i = 0; i < 6; i++) {
        secp256k1_scalar_sqrX(&x127, &x127);
    }
    secp256k1_scalar_mulX(&x127, &x127, &x7);

    /* Then accumulate the final result (t starts at x127). */
    t = &x127;
    for (i = 0; i < 2; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 4; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x3); /* 111 */
    for (i = 0; i < 2; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 2; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 2; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 4; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x3); /* 111 */
    for (i = 0; i < 3; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x2); /* 11 */
    for (i = 0; i < 4; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x3); /* 111 */
    for (i = 0; i < 5; i++) { /* 00 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x3); /* 111 */
    for (i = 0; i < 4; i++) { /* 00 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x2); /* 11 */
    for (i = 0; i < 2; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 2; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 5; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x4); /* 1111 */
    for (i = 0; i < 2; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 3; i++) { /* 00 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 4; i++) { /* 000 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 2; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 10; i++) { /* 0000000 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x3); /* 111 */
    for (i = 0; i < 4; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x3); /* 111 */
    for (i = 0; i < 9; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x8); /* 11111111 */
    for (i = 0; i < 2; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 3; i++) { /* 00 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 3; i++) { /* 00 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 5; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x4); /* 1111 */
    for (i = 0; i < 2; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 5; i++) { /* 000 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x2); /* 11 */
    for (i = 0; i < 4; i++) { /* 00 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x2); /* 11 */
    for (i = 0; i < 2; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 8; i++) { /* 000000 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x2); /* 11 */
    for (i = 0; i < 3; i++) { /* 0 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, &x2); /* 11 */
    for (i = 0; i < 3; i++) { /* 00 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 6; i++) { /* 00000 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(t, t, x); /* 1 */
    for (i = 0; i < 8; i++) { /* 00 */
        secp256k1_scalar_sqrX(t, t);
    }
    secp256k1_scalar_mulX(r, t, &x6); /* 111111 */
}

static void secp256k1_scalar_inverse_varX(secp256k1_scalarX *r, const secp256k1_scalarX *x) {
    secp256k1_scalar_inverseX(r, x);
}

static void secp256k1_scalar_clearX(secp256k1_scalarX *r) {
    r->d[0] = 0;
	r->d[1] = 0;
	r->d[2] = 0;
	r->d[3] = 0;
	r->d[4] = 0;
	r->d[5] = 0;
	r->d[6] = 0;
	r->d[7] = 0;
}

unsigned int secp256k1_scalar_get_bitsX(const secp256k1_scalarX *a, unsigned int offset, unsigned int count) {
    VERIFY_CHECK((offset + count - 1) >> 5 == offset >> 5);
	return (a->d[offset >> 5] >> (offset & 0x1F)) & ((1 << count) - 1);
}

static void secp256k1_scalar_negateX(secp256k1_scalarX *r, const secp256k1_scalarX *a) {
    uint32_t nonzero = 0xFFFFFFFFUL * (secp256k1_scalar_is_zeroX(a) == 0);
	uint64_t t = (uint64_t)(~a->d[0]) + SECP256K1_N_0 + 1;
	r->d[0] = t & nonzero; t >>= 32;
	t += (uint64_t)(~a->d[1]) + SECP256K1_N_1;
	r->d[1] = t & nonzero; t >>= 32;
	t += (uint64_t)(~a->d[2]) + SECP256K1_N_2;
	r->d[2] = t & nonzero; t >>= 32;
	t += (uint64_t)(~a->d[3]) + SECP256K1_N_3;
	r->d[3] = t & nonzero; t >>= 32;
	t += (uint64_t)(~a->d[4]) + SECP256K1_N_4;
	r->d[4] = t & nonzero; t >>= 32;
	t += (uint64_t)(~a->d[5]) + SECP256K1_N_5;
	r->d[5] = t & nonzero; t >>= 32;
	t += (uint64_t)(~a->d[6]) + SECP256K1_N_6;
	r->d[6] = t & nonzero; t >>= 32;
	t += (uint64_t)(~a->d[7]) + SECP256K1_N_7;
	r->d[7] = t & nonzero;
}

unsigned int secp256k1_scalar_get_bits_varX(const secp256k1_scalarX *a, unsigned int offset, unsigned int count) {
    VERIFY_CHECK(count < 32);
	VERIFY_CHECK(offset + count <= 256);
	if ((offset + count - 1) >> 5 == offset >> 5) {
		return secp256k1_scalar_get_bitsX(a, offset, count);
	} else {
		VERIFY_CHECK((offset >> 5) + 1 < 8);
		return ((a->d[offset >> 5] >> (offset & 0x1F)) | (a->d[(offset >> 5) + 1] << (32 - (offset & 0x1F)))) & ((((uint32_t)1) << count) - 1);
	}
}

static void secp256k1_scalar_get_b32X(unsigned char *bin, const secp256k1_scalarX* a) {
    bin[0] = a->d[7] >> 24; bin[1] = a->d[7] >> 16; bin[2] = a->d[7] >> 8; bin[3] = a->d[7];
	bin[4] = a->d[6] >> 24; bin[5] = a->d[6] >> 16; bin[6] = a->d[6] >> 8; bin[7] = a->d[6];
	bin[8] = a->d[5] >> 24; bin[9] = a->d[5] >> 16; bin[10] = a->d[5] >> 8; bin[11] = a->d[5];
	bin[12] = a->d[4] >> 24; bin[13] = a->d[4] >> 16; bin[14] = a->d[4] >> 8; bin[15] = a->d[4];
	bin[16] = a->d[3] >> 24; bin[17] = a->d[3] >> 16; bin[18] = a->d[3] >> 8; bin[19] = a->d[3];
	bin[20] = a->d[2] >> 24; bin[21] = a->d[2] >> 16; bin[22] = a->d[2] >> 8; bin[23] = a->d[2];
	bin[24] = a->d[1] >> 24; bin[25] = a->d[1] >> 16; bin[26] = a->d[1] >> 8; bin[27] = a->d[1];
	bin[28] = a->d[0] >> 24; bin[29] = a->d[0] >> 16; bin[30] = a->d[0] >> 8; bin[31] = a->d[0];
}
static int secp256k1_scalar_addX(secp256k1_scalarX *r, const secp256k1_scalarX *a, const secp256k1_scalarX *b) {
    int overflow;
	uint64_t t = (uint64_t)a->d[0] + b->d[0];
	r->d[0] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)a->d[1] + b->d[1];
	r->d[1] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)a->d[2] + b->d[2];
	r->d[2] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)a->d[3] + b->d[3];
	r->d[3] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)a->d[4] + b->d[4];
	r->d[4] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)a->d[5] + b->d[5];
	r->d[5] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)a->d[6] + b->d[6];
	r->d[6] = t & 0xFFFFFFFFUL; t >>= 32;
	t += (uint64_t)a->d[7] + b->d[7];
	r->d[7] = t & 0xFFFFFFFFUL; t >>= 32;
	overflow = t + secp256k1_scalar_check_overflowX(r);
	VERIFY_CHECK(overflow == 0 || overflow == 1);
	secp256k1_scalar_reduceX(r, overflow);
	return overflow;
}

void secp256k1_fe_from_storageX_s(secp256k1_feX *r, const secp256k1_fe_storageX *a) 
{
    r->n[0] = a->n[0] & 0x3FFFFFFUL;
    r->n[1] = a->n[0] >> 26 | ((a->n[1] << 6) & 0x3FFFFFFUL);
    r->n[2] = a->n[1] >> 20 | ((a->n[2] << 12) & 0x3FFFFFFUL);
    r->n[3] = a->n[2] >> 14 | ((a->n[3] << 18) & 0x3FFFFFFUL);
    r->n[4] = a->n[3] >> 8 | ((a->n[4] << 24) & 0x3FFFFFFUL);
    r->n[5] = (a->n[4] >> 2) & 0x3FFFFFFUL;
    r->n[6] = a->n[4] >> 28 | ((a->n[5] << 4) & 0x3FFFFFFUL);
    r->n[7] = a->n[5] >> 22 | ((a->n[6] << 10) & 0x3FFFFFFUL);
    r->n[8] = a->n[6] >> 16 | ((a->n[7] << 16) & 0x3FFFFFFUL);
    r->n[9] = a->n[7] >> 10;

    r->magnitude = 1;
    r->normalized = 1;
}

static int secp256k1_fe_set_b32X(secp256k1_feX *r, __global const unsigned char *a) {
	int i;
    r->n[0] = r->n[1] = r->n[2] = r->n[3] = r->n[4] = 0;
    r->n[5] = r->n[6] = r->n[7] = r->n[8] = r->n[9] = 0;
    for (i=0; i<32; i++) {
        int j;
        for (j=0; j<4; j++) {
            int limb = (8*i+2*j)/26;
            int shift = (8*i+2*j)%26;
            r->n[limb] |= (uint32_t)((a[31-i] >> (2*j)) & 0x3) << shift;
        }
    }
    if (r->n[9] == 0x3FFFFFUL && (r->n[8] & r->n[7] & r->n[6] & r->n[5] & r->n[4] & r->n[3] & r->n[2]) == 0x3FFFFFFUL && (r->n[1] + 0x40UL + ((r->n[0] + 0x3D1UL) >> 26)) > 0x3FFFFFFUL) {
        return 0;
    }

    r->magnitude = 1;
    r->normalized = 1;
    secp256k1_fe_verifyX(r);
    return 1;
}

static int secp256k1_fe_set_b32XX(secp256k1_feX *r, const unsigned char *a) {
	int i;
    r->n[0] = r->n[1] = r->n[2] = r->n[3] = r->n[4] = 0;
    r->n[5] = r->n[6] = r->n[7] = r->n[8] = r->n[9] = 0;
    for (i=0; i<32; i++) {
        int j;
        for (j=0; j<4; j++) {
            int limb = (8*i+2*j)/26;
            int shift = (8*i+2*j)%26;
            r->n[limb] |= (uint32_t)((a[31-i] >> (2*j)) & 0x3) << shift;
        }
    }
    if (r->n[9] == 0x3FFFFFUL && (r->n[8] & r->n[7] & r->n[6] & r->n[5] & r->n[4] & r->n[3] & r->n[2]) == 0x3FFFFFFUL && (r->n[1] + 0x40UL + ((r->n[0] + 0x3D1UL) >> 26)) > 0x3FFFFFFUL) {
        return 0;
    }

    r->magnitude = 1;
    r->normalized = 1;
    secp256k1_fe_verifyX(r);
    return 1;
}

void secp256k1_fe_set_intX(secp256k1_feX *r, int a) {
    r->n[0] = a;
    r->n[1] = r->n[2] = r->n[3] = r->n[4] = r->n[5] = r->n[6] = r->n[7] = r->n[8] = r->n[9] = 0;
    r->magnitude = 1;
    r->normalized = 1;
    secp256k1_fe_verifyX(r);
}

#define VERIFY_BITS(x, n) VERIFY_CHECK(((x) >> (n)) == 0)

void secp256k1_fe_mul_innerX(uint32_t *r, const uint32_t *a, const uint32_t * SECP256K1_RESTRICT b) {
    uint64_t c, d;
    uint64_t u0, u1, u2, u3, u4, u5, u6, u7, u8;
    uint32_t t9, t1, t0, t2, t3, t4, t5, t6, t7;
    const uint32_t M = 0x3FFFFFFUL, R0 = 0x3D10UL, R1 = 0x400UL;

    VERIFY_BITS(a[0], 30);
    VERIFY_BITS(a[1], 30);
    VERIFY_BITS(a[2], 30);
    VERIFY_BITS(a[3], 30);
    VERIFY_BITS(a[4], 30);
    VERIFY_BITS(a[5], 30);
    VERIFY_BITS(a[6], 30);
    VERIFY_BITS(a[7], 30);
    VERIFY_BITS(a[8], 30);
    VERIFY_BITS(a[9], 26);
    VERIFY_BITS(b[0], 30);
    VERIFY_BITS(b[1], 30);
    VERIFY_BITS(b[2], 30);
    VERIFY_BITS(b[3], 30);
    VERIFY_BITS(b[4], 30);
    VERIFY_BITS(b[5], 30);
    VERIFY_BITS(b[6], 30);
    VERIFY_BITS(b[7], 30);
    VERIFY_BITS(b[8], 30);
    VERIFY_BITS(b[9], 26);

    /** [... a b c] is a shorthand for ... + a<<52 + b<<26 + c<<0 mod n.
     *  px is a shorthand for sum(a[i]*b[x-i], i=0..x).
     *  Note that [x 0 0 0 0 0 0 0 0 0 0] = [x*R1 x*R0].
     */

    d  = (uint64_t)a[0] * b[9]
       + (uint64_t)a[1] * b[8]
       + (uint64_t)a[2] * b[7]
       + (uint64_t)a[3] * b[6]
       + (uint64_t)a[4] * b[5]
       + (uint64_t)a[5] * b[4]
       + (uint64_t)a[6] * b[3]
       + (uint64_t)a[7] * b[2]
       + (uint64_t)a[8] * b[1]
       + (uint64_t)a[9] * b[0];
    /* VERIFY_BITS(d, 64); */
    /* [d 0 0 0 0 0 0 0 0 0] = [p9 0 0 0 0 0 0 0 0 0] */
    t9 = d & M; d >>= 26;
    VERIFY_BITS(t9, 26);
    VERIFY_BITS(d, 38);
    /* [d t9 0 0 0 0 0 0 0 0 0] = [p9 0 0 0 0 0 0 0 0 0] */

    c  = (uint64_t)a[0] * b[0];
    VERIFY_BITS(c, 60);
    /* [d t9 0 0 0 0 0 0 0 0 c] = [p9 0 0 0 0 0 0 0 0 p0] */
    d += (uint64_t)a[1] * b[9]
       + (uint64_t)a[2] * b[8]
       + (uint64_t)a[3] * b[7]
       + (uint64_t)a[4] * b[6]
       + (uint64_t)a[5] * b[5]
       + (uint64_t)a[6] * b[4]
       + (uint64_t)a[7] * b[3]
       + (uint64_t)a[8] * b[2]
       + (uint64_t)a[9] * b[1];
    VERIFY_BITS(d, 63);
    /* [d t9 0 0 0 0 0 0 0 0 c] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
    u0 = d & M; d >>= 26; c += u0 * R0;
    VERIFY_BITS(u0, 26);
    VERIFY_BITS(d, 37);
    VERIFY_BITS(c, 61);
    /* [d u0 t9 0 0 0 0 0 0 0 0 c-u0*R0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
    t0 = c & M; c >>= 26; c += u0 * R1;
    VERIFY_BITS(t0, 26);
    VERIFY_BITS(c, 37);
    /* [d u0 t9 0 0 0 0 0 0 0 c-u0*R1 t0-u0*R0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
    /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */

    c += (uint64_t)a[0] * b[1]
       + (uint64_t)a[1] * b[0];
    VERIFY_BITS(c, 62);
    /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p10 p9 0 0 0 0 0 0 0 p1 p0] */
    d += (uint64_t)a[2] * b[9]
       + (uint64_t)a[3] * b[8]
       + (uint64_t)a[4] * b[7]
       + (uint64_t)a[5] * b[6]
       + (uint64_t)a[6] * b[5]
       + (uint64_t)a[7] * b[4]
       + (uint64_t)a[8] * b[3]
       + (uint64_t)a[9] * b[2];
    VERIFY_BITS(d, 63);
    /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
    u1 = d & M; d >>= 26; c += u1 * R0;
    VERIFY_BITS(u1, 26);
    VERIFY_BITS(d, 37);
    VERIFY_BITS(c, 63);
    /* [d u1 0 t9 0 0 0 0 0 0 0 c-u1*R0 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
    t1 = c & M; c >>= 26; c += u1 * R1;
    VERIFY_BITS(t1, 26);
    VERIFY_BITS(c, 38);
    /* [d u1 0 t9 0 0 0 0 0 0 c-u1*R1 t1-u1*R0 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
    /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */

    c += (uint64_t)a[0] * b[2]
       + (uint64_t)a[1] * b[1]
       + (uint64_t)a[2] * b[0];
    VERIFY_BITS(c, 62);
    /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    d += (uint64_t)a[3] * b[9]
       + (uint64_t)a[4] * b[8]
       + (uint64_t)a[5] * b[7]
       + (uint64_t)a[6] * b[6]
       + (uint64_t)a[7] * b[5]
       + (uint64_t)a[8] * b[4]
       + (uint64_t)a[9] * b[3];
    VERIFY_BITS(d, 63);
    /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    u2 = d & M; d >>= 26; c += u2 * R0;
    VERIFY_BITS(u2, 26);
    VERIFY_BITS(d, 37);
    VERIFY_BITS(c, 63);
    /* [d u2 0 0 t9 0 0 0 0 0 0 c-u2*R0 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    t2 = c & M; c >>= 26; c += u2 * R1;
    VERIFY_BITS(t2, 26);
    VERIFY_BITS(c, 38);
    /* [d u2 0 0 t9 0 0 0 0 0 c-u2*R1 t2-u2*R0 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */

    c += (uint64_t)a[0] * b[3]
       + (uint64_t)a[1] * b[2]
       + (uint64_t)a[2] * b[1]
       + (uint64_t)a[3] * b[0];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    d += (uint64_t)a[4] * b[9]
       + (uint64_t)a[5] * b[8]
       + (uint64_t)a[6] * b[7]
       + (uint64_t)a[7] * b[6]
       + (uint64_t)a[8] * b[5]
       + (uint64_t)a[9] * b[4];
    VERIFY_BITS(d, 63);
    /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    u3 = d & M; d >>= 26; c += u3 * R0;
    VERIFY_BITS(u3, 26);
    VERIFY_BITS(d, 37);
    /* VERIFY_BITS(c, 64); */
    /* [d u3 0 0 0 t9 0 0 0 0 0 c-u3*R0 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    t3 = c & M; c >>= 26; c += u3 * R1;
    VERIFY_BITS(t3, 26);
    VERIFY_BITS(c, 39);
    /* [d u3 0 0 0 t9 0 0 0 0 c-u3*R1 t3-u3*R0 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */

    c += (uint64_t)a[0] * b[4]
       + (uint64_t)a[1] * b[3]
       + (uint64_t)a[2] * b[2]
       + (uint64_t)a[3] * b[1]
       + (uint64_t)a[4] * b[0];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    d += (uint64_t)a[5] * b[9]
       + (uint64_t)a[6] * b[8]
       + (uint64_t)a[7] * b[7]
       + (uint64_t)a[8] * b[6]
       + (uint64_t)a[9] * b[5];
    VERIFY_BITS(d, 62);
    /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    u4 = d & M; d >>= 26; c += u4 * R0;
    VERIFY_BITS(u4, 26);
    VERIFY_BITS(d, 36);
    /* VERIFY_BITS(c, 64); */
    /* [d u4 0 0 0 0 t9 0 0 0 0 c-u4*R0 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    t4 = c & M; c >>= 26; c += u4 * R1;
    VERIFY_BITS(t4, 26);
    VERIFY_BITS(c, 39);
    /* [d u4 0 0 0 0 t9 0 0 0 c-u4*R1 t4-u4*R0 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */

    c += (uint64_t)a[0] * b[5]
       + (uint64_t)a[1] * b[4]
       + (uint64_t)a[2] * b[3]
       + (uint64_t)a[3] * b[2]
       + (uint64_t)a[4] * b[1]
       + (uint64_t)a[5] * b[0];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)a[6] * b[9]
       + (uint64_t)a[7] * b[8]
       + (uint64_t)a[8] * b[7]
       + (uint64_t)a[9] * b[6];
    VERIFY_BITS(d, 62);
    /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    u5 = d & M; d >>= 26; c += u5 * R0;
    VERIFY_BITS(u5, 26);
    VERIFY_BITS(d, 36);
    /* VERIFY_BITS(c, 64); */
    /* [d u5 0 0 0 0 0 t9 0 0 0 c-u5*R0 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    t5 = c & M; c >>= 26; c += u5 * R1;
    VERIFY_BITS(t5, 26);
    VERIFY_BITS(c, 39);
    /* [d u5 0 0 0 0 0 t9 0 0 c-u5*R1 t5-u5*R0 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */

    c += (uint64_t)a[0] * b[6]
       + (uint64_t)a[1] * b[5]
       + (uint64_t)a[2] * b[4]
       + (uint64_t)a[3] * b[3]
       + (uint64_t)a[4] * b[2]
       + (uint64_t)a[5] * b[1]
       + (uint64_t)a[6] * b[0];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)a[7] * b[9]
       + (uint64_t)a[8] * b[8]
       + (uint64_t)a[9] * b[7];
    VERIFY_BITS(d, 61);
    /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    u6 = d & M; d >>= 26; c += u6 * R0;
    VERIFY_BITS(u6, 26);
    VERIFY_BITS(d, 35);
    /* VERIFY_BITS(c, 64); */
    /* [d u6 0 0 0 0 0 0 t9 0 0 c-u6*R0 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    t6 = c & M; c >>= 26; c += u6 * R1;
    VERIFY_BITS(t6, 26);
    VERIFY_BITS(c, 39);
    /* [d u6 0 0 0 0 0 0 t9 0 c-u6*R1 t6-u6*R0 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */

    c += (uint64_t)a[0] * b[7]
       + (uint64_t)a[1] * b[6]
       + (uint64_t)a[2] * b[5]
       + (uint64_t)a[3] * b[4]
       + (uint64_t)a[4] * b[3]
       + (uint64_t)a[5] * b[2]
       + (uint64_t)a[6] * b[1]
       + (uint64_t)a[7] * b[0];
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x8000007C00000007UL);
    /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)a[8] * b[9]
       + (uint64_t)a[9] * b[8];
    VERIFY_BITS(d, 58);
    /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    u7 = d & M; d >>= 26; c += u7 * R0;
    VERIFY_BITS(u7, 26);
    VERIFY_BITS(d, 32);
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x800001703FFFC2F7UL);
    /* [d u7 0 0 0 0 0 0 0 t9 0 c-u7*R0 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    t7 = c & M; c >>= 26; c += u7 * R1;
    VERIFY_BITS(t7, 26);
    VERIFY_BITS(c, 38);
    /* [d u7 0 0 0 0 0 0 0 t9 c-u7*R1 t7-u7*R0 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */

    c += (uint64_t)a[0] * b[8]
       + (uint64_t)a[1] * b[7]
       + (uint64_t)a[2] * b[6]
       + (uint64_t)a[3] * b[5]
       + (uint64_t)a[4] * b[4]
       + (uint64_t)a[5] * b[3]
       + (uint64_t)a[6] * b[2]
       + (uint64_t)a[7] * b[1]
       + (uint64_t)a[8] * b[0];
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x9000007B80000008UL);
    /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)a[9] * b[9];
    VERIFY_BITS(d, 57);
    /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    u8 = d & M; d >>= 26; c += u8 * R0;
    VERIFY_BITS(u8, 26);
    VERIFY_BITS(d, 31);
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x9000016FBFFFC2F8UL);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 t4 t3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    r[3] = t3;
    VERIFY_BITS(r[3], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 t4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[4] = t4;
    VERIFY_BITS(r[4], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[5] = t5;
    VERIFY_BITS(r[5], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[6] = t6;
    VERIFY_BITS(r[6], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[7] = t7;
    VERIFY_BITS(r[7], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    r[8] = c & M; c >>= 26; c += u8 * R1;
    VERIFY_BITS(r[8], 26);
    VERIFY_BITS(c, 39);
    /* [d u8 0 0 0 0 0 0 0 0 t9+c-u8*R1 r8-u8*R0 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 0 0 t9+c r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    c   += d * R0 + t9;
    VERIFY_BITS(c, 45);
    /* [d 0 0 0 0 0 0 0 0 0 c-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[9] = c & (M >> 4); c >>= 22; c += d * (R1 << 4);
    VERIFY_BITS(r[9], 22);
    VERIFY_BITS(c, 46);
    /* [d 0 0 0 0 0 0 0 0 r9+((c-d*R1<<4)<<22)-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 -d*R1 r9+(c<<22)-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    d    = c * (R0 >> 4) + t0;
    VERIFY_BITS(d, 56);
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1 d-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[0] = d & M; d >>= 26;
    VERIFY_BITS(r[0], 26);
    VERIFY_BITS(d, 30);
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1+d r0-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    d   += c * (R1 >> 4) + t1;
    VERIFY_BITS(d, 53);
    VERIFY_CHECK(d <= 0x10000003FFFFBFUL);
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 d-c*R1>>4 r0-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [r9 r8 r7 r6 r5 r4 r3 t2 d r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[1] = d & M; d >>= 26;
    VERIFY_BITS(r[1], 26);
    VERIFY_BITS(d, 27);
    VERIFY_CHECK(d <= 0x4000000UL);
    /* [r9 r8 r7 r6 r5 r4 r3 t2+d r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    d   += t2;
    VERIFY_BITS(d, 27);
    /* [r9 r8 r7 r6 r5 r4 r3 d r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[2] = d;
    VERIFY_BITS(r[2], 27);
    /* [r9 r8 r7 r6 r5 r4 r3 r2 r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
}

void secp256k1_fe_mul_innerXXX(uint32_t *r, const uint32_t *a, const uint32_t * SECP256K1_RESTRICT b) {
    uint64_t c, d;
    uint64_t u0, u1, u2, u3, u4, u5, u6, u7, u8;
    uint32_t t9, t1, t0, t2, t3, t4, t5, t6, t7;
    const uint32_t M = 0x3FFFFFFUL, R0 = 0x3D10UL, R1 = 0x400UL;

    VERIFY_BITS(a[0], 30);
    VERIFY_BITS(a[1], 30);
    VERIFY_BITS(a[2], 30);
    VERIFY_BITS(a[3], 30);
    VERIFY_BITS(a[4], 30);
    VERIFY_BITS(a[5], 30);
    VERIFY_BITS(a[6], 30);
    VERIFY_BITS(a[7], 30);
    VERIFY_BITS(a[8], 30);
    VERIFY_BITS(a[9], 26);
    VERIFY_BITS(b[0], 30);
    VERIFY_BITS(b[1], 30);
    VERIFY_BITS(b[2], 30);
    VERIFY_BITS(b[3], 30);
    VERIFY_BITS(b[4], 30);
    VERIFY_BITS(b[5], 30);
    VERIFY_BITS(b[6], 30);
    VERIFY_BITS(b[7], 30);
    VERIFY_BITS(b[8], 30);
    VERIFY_BITS(b[9], 26);

    /** [... a b c] is a shorthand for ... + a<<52 + b<<26 + c<<0 mod n.
     *  px is a shorthand for sum(a[i]*b[x-i], i=0..x).
     *  Note that [x 0 0 0 0 0 0 0 0 0 0] = [x*R1 x*R0].
     */

    d  = (uint64_t)a[0] * b[9]
       + (uint64_t)a[1] * b[8]
       + (uint64_t)a[2] * b[7]
       + (uint64_t)a[3] * b[6]
       + (uint64_t)a[4] * b[5]
       + (uint64_t)a[5] * b[4]
       + (uint64_t)a[6] * b[3]
       + (uint64_t)a[7] * b[2]
       + (uint64_t)a[8] * b[1]
       + (uint64_t)a[9] * b[0];
    /* VERIFY_BITS(d, 64); */
    /* [d 0 0 0 0 0 0 0 0 0] = [p9 0 0 0 0 0 0 0 0 0] */
    t9 = d & M; d >>= 26;
    VERIFY_BITS(t9, 26);
    VERIFY_BITS(d, 38);
    /* [d t9 0 0 0 0 0 0 0 0 0] = [p9 0 0 0 0 0 0 0 0 0] */

    c  = (uint64_t)a[0] * b[0];
    VERIFY_BITS(c, 60);
    /* [d t9 0 0 0 0 0 0 0 0 c] = [p9 0 0 0 0 0 0 0 0 p0] */
    d += (uint64_t)a[1] * b[9]
       + (uint64_t)a[2] * b[8]
       + (uint64_t)a[3] * b[7]
       + (uint64_t)a[4] * b[6]
       + (uint64_t)a[5] * b[5]
       + (uint64_t)a[6] * b[4]
       + (uint64_t)a[7] * b[3]
       + (uint64_t)a[8] * b[2]
       + (uint64_t)a[9] * b[1];
    VERIFY_BITS(d, 63);
    /* [d t9 0 0 0 0 0 0 0 0 c] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
    u0 = d & M; d >>= 26; c += u0 * R0;
    VERIFY_BITS(u0, 26);
    VERIFY_BITS(d, 37);
    VERIFY_BITS(c, 61);
    /* [d u0 t9 0 0 0 0 0 0 0 0 c-u0*R0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
    t0 = c & M; c >>= 26; c += u0 * R1;
    VERIFY_BITS(t0, 26);
    VERIFY_BITS(c, 37);
    /* [d u0 t9 0 0 0 0 0 0 0 c-u0*R1 t0-u0*R0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
    /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */

    c += (uint64_t)a[0] * b[1]
       + (uint64_t)a[1] * b[0];
    VERIFY_BITS(c, 62);
    /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p10 p9 0 0 0 0 0 0 0 p1 p0] */
    d += (uint64_t)a[2] * b[9]
       + (uint64_t)a[3] * b[8]
       + (uint64_t)a[4] * b[7]
       + (uint64_t)a[5] * b[6]
       + (uint64_t)a[6] * b[5]
       + (uint64_t)a[7] * b[4]
       + (uint64_t)a[8] * b[3]
       + (uint64_t)a[9] * b[2];
    VERIFY_BITS(d, 63);
    /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
    u1 = d & M; d >>= 26; c += u1 * R0;
    VERIFY_BITS(u1, 26);
    VERIFY_BITS(d, 37);
    VERIFY_BITS(c, 63);
    /* [d u1 0 t9 0 0 0 0 0 0 0 c-u1*R0 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
    t1 = c & M; c >>= 26; c += u1 * R1;
    VERIFY_BITS(t1, 26);
    VERIFY_BITS(c, 38);
    /* [d u1 0 t9 0 0 0 0 0 0 c-u1*R1 t1-u1*R0 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
    /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */

    c += (uint64_t)a[0] * b[2]
       + (uint64_t)a[1] * b[1]
       + (uint64_t)a[2] * b[0];
    VERIFY_BITS(c, 62);
    /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    d += (uint64_t)a[3] * b[9]
       + (uint64_t)a[4] * b[8]
       + (uint64_t)a[5] * b[7]
       + (uint64_t)a[6] * b[6]
       + (uint64_t)a[7] * b[5]
       + (uint64_t)a[8] * b[4]
       + (uint64_t)a[9] * b[3];
    VERIFY_BITS(d, 63);
    /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    u2 = d & M; d >>= 26; c += u2 * R0;
    VERIFY_BITS(u2, 26);
    VERIFY_BITS(d, 37);
    VERIFY_BITS(c, 63);
    /* [d u2 0 0 t9 0 0 0 0 0 0 c-u2*R0 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    t2 = c & M; c >>= 26; c += u2 * R1;
    VERIFY_BITS(t2, 26);
    VERIFY_BITS(c, 38);
    /* [d u2 0 0 t9 0 0 0 0 0 c-u2*R1 t2-u2*R0 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */

    c += (uint64_t)a[0] * b[3]
       + (uint64_t)a[1] * b[2]
       + (uint64_t)a[2] * b[1]
       + (uint64_t)a[3] * b[0];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    d += (uint64_t)a[4] * b[9]
       + (uint64_t)a[5] * b[8]
       + (uint64_t)a[6] * b[7]
       + (uint64_t)a[7] * b[6]
       + (uint64_t)a[8] * b[5]
       + (uint64_t)a[9] * b[4];
    VERIFY_BITS(d, 63);
    /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    u3 = d & M; d >>= 26; c += u3 * R0;
    VERIFY_BITS(u3, 26);
    VERIFY_BITS(d, 37);
    /* VERIFY_BITS(c, 64); */
    /* [d u3 0 0 0 t9 0 0 0 0 0 c-u3*R0 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    t3 = c & M; c >>= 26; c += u3 * R1;
    VERIFY_BITS(t3, 26);
    VERIFY_BITS(c, 39);
    /* [d u3 0 0 0 t9 0 0 0 0 c-u3*R1 t3-u3*R0 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */

    c += (uint64_t)a[0] * b[4]
       + (uint64_t)a[1] * b[3]
       + (uint64_t)a[2] * b[2]
       + (uint64_t)a[3] * b[1]
       + (uint64_t)a[4] * b[0];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    d += (uint64_t)a[5] * b[9]
       + (uint64_t)a[6] * b[8]
       + (uint64_t)a[7] * b[7]
       + (uint64_t)a[8] * b[6]
       + (uint64_t)a[9] * b[5];
    VERIFY_BITS(d, 62);
    /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    u4 = d & M; d >>= 26; c += u4 * R0;
    VERIFY_BITS(u4, 26);
    VERIFY_BITS(d, 36);
    /* VERIFY_BITS(c, 64); */
    /* [d u4 0 0 0 0 t9 0 0 0 0 c-u4*R0 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    t4 = c & M; c >>= 26; c += u4 * R1;
    VERIFY_BITS(t4, 26);
    VERIFY_BITS(c, 39);
    /* [d u4 0 0 0 0 t9 0 0 0 c-u4*R1 t4-u4*R0 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */

    c += (uint64_t)a[0] * b[5]
       + (uint64_t)a[1] * b[4]
       + (uint64_t)a[2] * b[3]
       + (uint64_t)a[3] * b[2]
       + (uint64_t)a[4] * b[1]
       + (uint64_t)a[5] * b[0];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)a[6] * b[9]
       + (uint64_t)a[7] * b[8]
       + (uint64_t)a[8] * b[7]
       + (uint64_t)a[9] * b[6];
    VERIFY_BITS(d, 62);
    /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    u5 = d & M; d >>= 26; c += u5 * R0;
    VERIFY_BITS(u5, 26);
    VERIFY_BITS(d, 36);
    /* VERIFY_BITS(c, 64); */
    /* [d u5 0 0 0 0 0 t9 0 0 0 c-u5*R0 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    t5 = c & M; c >>= 26; c += u5 * R1;
    VERIFY_BITS(t5, 26);
    VERIFY_BITS(c, 39);
    /* [d u5 0 0 0 0 0 t9 0 0 c-u5*R1 t5-u5*R0 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */

    c += (uint64_t)a[0] * b[6]
       + (uint64_t)a[1] * b[5]
       + (uint64_t)a[2] * b[4]
       + (uint64_t)a[3] * b[3]
       + (uint64_t)a[4] * b[2]
       + (uint64_t)a[5] * b[1]
       + (uint64_t)a[6] * b[0];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)a[7] * b[9]
       + (uint64_t)a[8] * b[8]
       + (uint64_t)a[9] * b[7];
    VERIFY_BITS(d, 61);
    /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    u6 = d & M; d >>= 26; c += u6 * R0;
    VERIFY_BITS(u6, 26);
    VERIFY_BITS(d, 35);
    /* VERIFY_BITS(c, 64); */
    /* [d u6 0 0 0 0 0 0 t9 0 0 c-u6*R0 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    t6 = c & M; c >>= 26; c += u6 * R1;
    VERIFY_BITS(t6, 26);
    VERIFY_BITS(c, 39);
    /* [d u6 0 0 0 0 0 0 t9 0 c-u6*R1 t6-u6*R0 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */

    c += (uint64_t)a[0] * b[7]
       + (uint64_t)a[1] * b[6]
       + (uint64_t)a[2] * b[5]
       + (uint64_t)a[3] * b[4]
       + (uint64_t)a[4] * b[3]
       + (uint64_t)a[5] * b[2]
       + (uint64_t)a[6] * b[1]
       + (uint64_t)a[7] * b[0];
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x8000007C00000007UL);
    /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)a[8] * b[9]
       + (uint64_t)a[9] * b[8];
    VERIFY_BITS(d, 58);
    /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    u7 = d & M; d >>= 26; c += u7 * R0;
    VERIFY_BITS(u7, 26);
    VERIFY_BITS(d, 32);
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x800001703FFFC2F7UL);
    /* [d u7 0 0 0 0 0 0 0 t9 0 c-u7*R0 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    t7 = c & M; c >>= 26; c += u7 * R1;
    VERIFY_BITS(t7, 26);
    VERIFY_BITS(c, 38);
    /* [d u7 0 0 0 0 0 0 0 t9 c-u7*R1 t7-u7*R0 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */

    c += (uint64_t)a[0] * b[8]
       + (uint64_t)a[1] * b[7]
       + (uint64_t)a[2] * b[6]
       + (uint64_t)a[3] * b[5]
       + (uint64_t)a[4] * b[4]
       + (uint64_t)a[5] * b[3]
       + (uint64_t)a[6] * b[2]
       + (uint64_t)a[7] * b[1]
       + (uint64_t)a[8] * b[0];
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x9000007B80000008UL);
    /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)a[9] * b[9];
    VERIFY_BITS(d, 57);
    /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    u8 = d & M; d >>= 26; c += u8 * R0;
    VERIFY_BITS(u8, 26);
    VERIFY_BITS(d, 31);
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x9000016FBFFFC2F8UL);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 t4 t3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    r[3] = t3;
    VERIFY_BITS(r[3], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 t4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[4] = t4;
    VERIFY_BITS(r[4], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[5] = t5;
    VERIFY_BITS(r[5], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[6] = t6;
    VERIFY_BITS(r[6], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[7] = t7;
    VERIFY_BITS(r[7], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    r[8] = c & M; c >>= 26; c += u8 * R1;
    VERIFY_BITS(r[8], 26);
    VERIFY_BITS(c, 39);
    /* [d u8 0 0 0 0 0 0 0 0 t9+c-u8*R1 r8-u8*R0 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 0 0 t9+c r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    c   += d * R0 + t9;
    VERIFY_BITS(c, 45);
    /* [d 0 0 0 0 0 0 0 0 0 c-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[9] = c & (M >> 4); c >>= 22; c += d * (R1 << 4);
    VERIFY_BITS(r[9], 22);
    VERIFY_BITS(c, 46);
    /* [d 0 0 0 0 0 0 0 0 r9+((c-d*R1<<4)<<22)-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 -d*R1 r9+(c<<22)-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    d    = c * (R0 >> 4) + t0;
    VERIFY_BITS(d, 56);
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1 d-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[0] = d & M; d >>= 26;
    VERIFY_BITS(r[0], 26);
    VERIFY_BITS(d, 30);
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1+d r0-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    d   += c * (R1 >> 4) + t1;
    VERIFY_BITS(d, 53);
    VERIFY_CHECK(d <= 0x10000003FFFFBFUL);
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 d-c*R1>>4 r0-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [r9 r8 r7 r6 r5 r4 r3 t2 d r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[1] = d & M; d >>= 26;
    VERIFY_BITS(r[1], 26);
    VERIFY_BITS(d, 27);
    VERIFY_CHECK(d <= 0x4000000UL);
    /* [r9 r8 r7 r6 r5 r4 r3 t2+d r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    d   += t2;
    VERIFY_BITS(d, 27);
    /* [r9 r8 r7 r6 r5 r4 r3 d r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[2] = d;
    VERIFY_BITS(r[2], 27);
    /* [r9 r8 r7 r6 r5 r4 r3 r2 r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
}

void memsetX(void *dest, int val, size_t len)
{
  unsigned char *ptr = dest;
  while (len-- > 0)
    *ptr++ = (unsigned char)val;
}

static void secp256k1_fe_mulX(secp256k1_feX *r, const secp256k1_feX *a, const secp256k1_feX * SECP256K1_RESTRICT b) {
	VERIFY_CHECK(a->magnitude <= 8);
	VERIFY_CHECK(b->magnitude <= 8);
	secp256k1_fe_verifyX(a);
	secp256k1_fe_verifyX(b);
	VERIFY_CHECK(r != b);
	secp256k1_fe_mul_innerX(r->n, a->n, b->n);
	r->magnitude = 1;
	r->normalized = 0;
	secp256k1_fe_verifyX(r);
}

void secp256k1_fe_mul_intX(secp256k1_feX *r, int a) {
	r->n[0] *= a;
	r->n[1] *= a;
	r->n[2] *= a;
	r->n[3] *= a;
	r->n[4] *= a;
	r->n[5] *= a;
	r->n[6] *= a;
	r->n[7] *= a;
	r->n[8] *= a;
	r->n[9] *= a;

	r->magnitude *= a;
	r->normalized = 0;
	secp256k1_fe_verifyX(r);
}

static void secp256k1_fe_normalize_weakX(secp256k1_feX *r) {
    uint32_t t0 = r->n[0], t1 = r->n[1], t2 = r->n[2], t3 = r->n[3], t4 = r->n[4],
             t5 = r->n[5], t6 = r->n[6], t7 = r->n[7], t8 = r->n[8], t9 = r->n[9];

    /* Reduce t9 at the start so there will be at most a single carry from the first pass */
    uint32_t x = t9 >> 22; t9 &= 0x03FFFFFUL;

    /* The first pass ensures the magnitude is 1, ... */
    t0 += x * 0x3D1UL; t1 += (x << 6);
    t1 += (t0 >> 26); t0 &= 0x3FFFFFFUL;
    t2 += (t1 >> 26); t1 &= 0x3FFFFFFUL;
    t3 += (t2 >> 26); t2 &= 0x3FFFFFFUL;
    t4 += (t3 >> 26); t3 &= 0x3FFFFFFUL;
    t5 += (t4 >> 26); t4 &= 0x3FFFFFFUL;
    t6 += (t5 >> 26); t5 &= 0x3FFFFFFUL;
    t7 += (t6 >> 26); t6 &= 0x3FFFFFFUL;
    t8 += (t7 >> 26); t7 &= 0x3FFFFFFUL;
    t9 += (t8 >> 26); t8 &= 0x3FFFFFFUL;

    /* ... except for a possible carry at bit 22 of t9 (i.e. bit 256 of the field element) */
    VERIFY_CHECK(t9 >> 23 == 0);

    r->n[0] = t0; r->n[1] = t1; r->n[2] = t2; r->n[3] = t3; r->n[4] = t4;
    r->n[5] = t5; r->n[6] = t6; r->n[7] = t7; r->n[8] = t8; r->n[9] = t9;

    r->magnitude = 1;
    secp256k1_fe_verifyX(r);
}

void secp256k1_fe_sqr_innerX(uint32_t *r, const uint32_t *a) {
    uint64_t c, d;
    uint64_t u0, u1, u2, u3, u4, u5, u6, u7, u8;
    uint32_t t9, t0, t1, t2, t3, t4, t5, t6, t7;
    const uint32_t M = 0x3FFFFFFUL, R0 = 0x3D10UL, R1 = 0x400UL;

    VERIFY_BITS(a[0], 30);
    VERIFY_BITS(a[1], 30);
    VERIFY_BITS(a[2], 30);
    VERIFY_BITS(a[3], 30);
    VERIFY_BITS(a[4], 30);
    VERIFY_BITS(a[5], 30);
    VERIFY_BITS(a[6], 30);
    VERIFY_BITS(a[7], 30);
    VERIFY_BITS(a[8], 30);
    VERIFY_BITS(a[9], 26);

    /** [... a b c] is a shorthand for ... + a<<52 + b<<26 + c<<0 mod n.
     *  px is a shorthand for sum(a[i]*a[x-i], i=0..x).
     *  Note that [x 0 0 0 0 0 0 0 0 0 0] = [x*R1 x*R0].
     */

    d  = (uint64_t)(a[0]*2) * a[9]
       + (uint64_t)(a[1]*2) * a[8]
       + (uint64_t)(a[2]*2) * a[7]
       + (uint64_t)(a[3]*2) * a[6]
       + (uint64_t)(a[4]*2) * a[5];
    /* VERIFY_BITS(d, 64); */
    /* [d 0 0 0 0 0 0 0 0 0] = [p9 0 0 0 0 0 0 0 0 0] */
    t9 = d & M; d >>= 26;
    VERIFY_BITS(t9, 26);
    VERIFY_BITS(d, 38);
    /* [d t9 0 0 0 0 0 0 0 0 0] = [p9 0 0 0 0 0 0 0 0 0] */

    c  = (uint64_t)a[0] * a[0];
    VERIFY_BITS(c, 60);
    /* [d t9 0 0 0 0 0 0 0 0 c] = [p9 0 0 0 0 0 0 0 0 p0] */
    d += (uint64_t)(a[1]*2) * a[9]
       + (uint64_t)(a[2]*2) * a[8]
       + (uint64_t)(a[3]*2) * a[7]
       + (uint64_t)(a[4]*2) * a[6]
       + (uint64_t)a[5] * a[5];
    VERIFY_BITS(d, 63);
    /* [d t9 0 0 0 0 0 0 0 0 c] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
    u0 = d & M; d >>= 26; c += u0 * R0;
    VERIFY_BITS(u0, 26);
    VERIFY_BITS(d, 37);
    VERIFY_BITS(c, 61);
    /* [d u0 t9 0 0 0 0 0 0 0 0 c-u0*R0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
    t0 = c & M; c >>= 26; c += u0 * R1;
    VERIFY_BITS(t0, 26);
    VERIFY_BITS(c, 37);
    /* [d u0 t9 0 0 0 0 0 0 0 c-u0*R1 t0-u0*R0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */
    /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p10 p9 0 0 0 0 0 0 0 0 p0] */

    c += (uint64_t)(a[0]*2) * a[1];
    VERIFY_BITS(c, 62);
    /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p10 p9 0 0 0 0 0 0 0 p1 p0] */
    d += (uint64_t)(a[2]*2) * a[9]
       + (uint64_t)(a[3]*2) * a[8]
       + (uint64_t)(a[4]*2) * a[7]
       + (uint64_t)(a[5]*2) * a[6];
    VERIFY_BITS(d, 63);
    /* [d 0 t9 0 0 0 0 0 0 0 c t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
    u1 = d & M; d >>= 26; c += u1 * R0;
    VERIFY_BITS(u1, 26);
    VERIFY_BITS(d, 37);
    VERIFY_BITS(c, 63);
    /* [d u1 0 t9 0 0 0 0 0 0 0 c-u1*R0 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
    t1 = c & M; c >>= 26; c += u1 * R1;
    VERIFY_BITS(t1, 26);
    VERIFY_BITS(c, 38);
    /* [d u1 0 t9 0 0 0 0 0 0 c-u1*R1 t1-u1*R0 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */
    /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p11 p10 p9 0 0 0 0 0 0 0 p1 p0] */

    c += (uint64_t)(a[0]*2) * a[2]
       + (uint64_t)a[1] * a[1];
    VERIFY_BITS(c, 62);
    /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    d += (uint64_t)(a[3]*2) * a[9]
       + (uint64_t)(a[4]*2) * a[8]
       + (uint64_t)(a[5]*2) * a[7]
       + (uint64_t)a[6] * a[6];
    VERIFY_BITS(d, 63);
    /* [d 0 0 t9 0 0 0 0 0 0 c t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    u2 = d & M; d >>= 26; c += u2 * R0;
    VERIFY_BITS(u2, 26);
    VERIFY_BITS(d, 37);
    VERIFY_BITS(c, 63);
    /* [d u2 0 0 t9 0 0 0 0 0 0 c-u2*R0 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    t2 = c & M; c >>= 26; c += u2 * R1;
    VERIFY_BITS(t2, 26);
    VERIFY_BITS(c, 38);
    /* [d u2 0 0 t9 0 0 0 0 0 c-u2*R1 t2-u2*R0 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */
    /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 0 p2 p1 p0] */

    c += (uint64_t)(a[0]*2) * a[3]
       + (uint64_t)(a[1]*2) * a[2];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    d += (uint64_t)(a[4]*2) * a[9]
       + (uint64_t)(a[5]*2) * a[8]
       + (uint64_t)(a[6]*2) * a[7];
    VERIFY_BITS(d, 63);
    /* [d 0 0 0 t9 0 0 0 0 0 c t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    u3 = d & M; d >>= 26; c += u3 * R0;
    VERIFY_BITS(u3, 26);
    VERIFY_BITS(d, 37);
    /* VERIFY_BITS(c, 64); */
    /* [d u3 0 0 0 t9 0 0 0 0 0 c-u3*R0 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    t3 = c & M; c >>= 26; c += u3 * R1;
    VERIFY_BITS(t3, 26);
    VERIFY_BITS(c, 39);
    /* [d u3 0 0 0 t9 0 0 0 0 c-u3*R1 t3-u3*R0 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */
    /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 0 p3 p2 p1 p0] */

    c += (uint64_t)(a[0]*2) * a[4]
       + (uint64_t)(a[1]*2) * a[3]
       + (uint64_t)a[2] * a[2];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    d += (uint64_t)(a[5]*2) * a[9]
       + (uint64_t)(a[6]*2) * a[8]
       + (uint64_t)a[7] * a[7];
    VERIFY_BITS(d, 62);
    /* [d 0 0 0 0 t9 0 0 0 0 c t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    u4 = d & M; d >>= 26; c += u4 * R0;
    VERIFY_BITS(u4, 26);
    VERIFY_BITS(d, 36);
    /* VERIFY_BITS(c, 64); */
    /* [d u4 0 0 0 0 t9 0 0 0 0 c-u4*R0 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    t4 = c & M; c >>= 26; c += u4 * R1;
    VERIFY_BITS(t4, 26);
    VERIFY_BITS(c, 39);
    /* [d u4 0 0 0 0 t9 0 0 0 c-u4*R1 t4-u4*R0 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 0 p4 p3 p2 p1 p0] */

    c += (uint64_t)(a[0]*2) * a[5]
       + (uint64_t)(a[1]*2) * a[4]
       + (uint64_t)(a[2]*2) * a[3];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)(a[6]*2) * a[9]
       + (uint64_t)(a[7]*2) * a[8];
    VERIFY_BITS(d, 62);
    /* [d 0 0 0 0 0 t9 0 0 0 c t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    u5 = d & M; d >>= 26; c += u5 * R0;
    VERIFY_BITS(u5, 26);
    VERIFY_BITS(d, 36);
    /* VERIFY_BITS(c, 64); */
    /* [d u5 0 0 0 0 0 t9 0 0 0 c-u5*R0 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    t5 = c & M; c >>= 26; c += u5 * R1;
    VERIFY_BITS(t5, 26);
    VERIFY_BITS(c, 39);
    /* [d u5 0 0 0 0 0 t9 0 0 c-u5*R1 t5-u5*R0 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 0 p5 p4 p3 p2 p1 p0] */

    c += (uint64_t)(a[0]*2) * a[6]
       + (uint64_t)(a[1]*2) * a[5]
       + (uint64_t)(a[2]*2) * a[4]
       + (uint64_t)a[3] * a[3];
    VERIFY_BITS(c, 63);
    /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)(a[7]*2) * a[9]
       + (uint64_t)a[8] * a[8];
    VERIFY_BITS(d, 61);
    /* [d 0 0 0 0 0 0 t9 0 0 c t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    u6 = d & M; d >>= 26; c += u6 * R0;
    VERIFY_BITS(u6, 26);
    VERIFY_BITS(d, 35);
    /* VERIFY_BITS(c, 64); */
    /* [d u6 0 0 0 0 0 0 t9 0 0 c-u6*R0 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    t6 = c & M; c >>= 26; c += u6 * R1;
    VERIFY_BITS(t6, 26);
    VERIFY_BITS(c, 39);
    /* [d u6 0 0 0 0 0 0 t9 0 c-u6*R1 t6-u6*R0 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 0 p6 p5 p4 p3 p2 p1 p0] */

    c += (uint64_t)(a[0]*2) * a[7]
       + (uint64_t)(a[1]*2) * a[6]
       + (uint64_t)(a[2]*2) * a[5]
       + (uint64_t)(a[3]*2) * a[4];
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x8000007C00000007UL);
    /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)(a[8]*2) * a[9];
    VERIFY_BITS(d, 58);
    /* [d 0 0 0 0 0 0 0 t9 0 c t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    u7 = d & M; d >>= 26; c += u7 * R0;
    VERIFY_BITS(u7, 26);
    VERIFY_BITS(d, 32);
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x800001703FFFC2F7UL);
    /* [d u7 0 0 0 0 0 0 0 t9 0 c-u7*R0 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    t7 = c & M; c >>= 26; c += u7 * R1;
    VERIFY_BITS(t7, 26);
    VERIFY_BITS(c, 38);
    /* [d u7 0 0 0 0 0 0 0 t9 c-u7*R1 t7-u7*R0 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 0 p7 p6 p5 p4 p3 p2 p1 p0] */

    c += (uint64_t)(a[0]*2) * a[8]
       + (uint64_t)(a[1]*2) * a[7]
       + (uint64_t)(a[2]*2) * a[6]
       + (uint64_t)(a[3]*2) * a[5]
       + (uint64_t)a[4] * a[4];
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x9000007B80000008UL);
    /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    d += (uint64_t)a[9] * a[9];
    VERIFY_BITS(d, 57);
    /* [d 0 0 0 0 0 0 0 0 t9 c t7 t6 t5 t4 t3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    u8 = d & M; d >>= 26; c += u8 * R0;
    VERIFY_BITS(u8, 26);
    VERIFY_BITS(d, 31);
    /* VERIFY_BITS(c, 64); */
    VERIFY_CHECK(c <= 0x9000016FBFFFC2F8UL);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 t4 t3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    r[3] = t3;
    VERIFY_BITS(r[3], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 t4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[4] = t4;
    VERIFY_BITS(r[4], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 t5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[5] = t5;
    VERIFY_BITS(r[5], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 t6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[6] = t6;
    VERIFY_BITS(r[6], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 t7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[7] = t7;
    VERIFY_BITS(r[7], 26);
    /* [d u8 0 0 0 0 0 0 0 0 t9 c-u8*R0 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    r[8] = c & M; c >>= 26; c += u8 * R1;
    VERIFY_BITS(r[8], 26);
    VERIFY_BITS(c, 39);
    /* [d u8 0 0 0 0 0 0 0 0 t9+c-u8*R1 r8-u8*R0 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 0 0 t9+c r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    c   += d * R0 + t9;
    VERIFY_BITS(c, 45);
    /* [d 0 0 0 0 0 0 0 0 0 c-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[9] = c & (M >> 4); c >>= 22; c += d * (R1 << 4);
    VERIFY_BITS(r[9], 22);
    VERIFY_BITS(c, 46);
    /* [d 0 0 0 0 0 0 0 0 r9+((c-d*R1<<4)<<22)-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [d 0 0 0 0 0 0 0 -d*R1 r9+(c<<22)-d*R0 r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1 t0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */

    d    = c * (R0 >> 4) + t0;
    VERIFY_BITS(d, 56);
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1 d-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[0] = d & M; d >>= 26;
    VERIFY_BITS(r[0], 26);
    VERIFY_BITS(d, 30);
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 t1+d r0-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    d   += c * (R1 >> 4) + t1;
    VERIFY_BITS(d, 53);
    VERIFY_CHECK(d <= 0x10000003FFFFBFUL);
    /* [r9+(c<<22) r8 r7 r6 r5 r4 r3 t2 d-c*R1>>4 r0-c*R0>>4] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    /* [r9 r8 r7 r6 r5 r4 r3 t2 d r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[1] = d & M; d >>= 26;
    VERIFY_BITS(r[1], 26);
    VERIFY_BITS(d, 27);
    VERIFY_CHECK(d <= 0x4000000UL);
    /* [r9 r8 r7 r6 r5 r4 r3 t2+d r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    d   += t2;
    VERIFY_BITS(d, 27);
    /* [r9 r8 r7 r6 r5 r4 r3 d r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
    r[2] = d;
    VERIFY_BITS(r[2], 27);
    /* [r9 r8 r7 r6 r5 r4 r3 r2 r1 r0] = [p18 p17 p16 p15 p14 p13 p12 p11 p10 p9 p8 p7 p6 p5 p4 p3 p2 p1 p0] */
}

void secp256k1_fe_negateX(secp256k1_feX *r, const secp256k1_feX *a, int m) {

    VERIFY_CHECK(a->magnitude <= m);
    secp256k1_fe_verifyX(a);
    r->n[0] = 0x3FFFC2FUL * 2 * (m + 1) - a->n[0];
    r->n[1] = 0x3FFFFBFUL * 2 * (m + 1) - a->n[1];
    r->n[2] = 0x3FFFFFFUL * 2 * (m + 1) - a->n[2];
    r->n[3] = 0x3FFFFFFUL * 2 * (m + 1) - a->n[3];
    r->n[4] = 0x3FFFFFFUL * 2 * (m + 1) - a->n[4];
    r->n[5] = 0x3FFFFFFUL * 2 * (m + 1) - a->n[5];
    r->n[6] = 0x3FFFFFFUL * 2 * (m + 1) - a->n[6];
    r->n[7] = 0x3FFFFFFUL * 2 * (m + 1) - a->n[7];
    r->n[8] = 0x3FFFFFFUL * 2 * (m + 1) - a->n[8];
    r->n[9] = 0x03FFFFFUL * 2 * (m + 1) - a->n[9];
    r->magnitude = m + 1;
    r->normalized = 0;
    secp256k1_fe_verifyX(r);
}

static void secp256k1_fe_normalizeX(secp256k1_feX *r) {
    uint32_t t0 = r->n[0], t1 = r->n[1], t2 = r->n[2], t3 = r->n[3], t4 = r->n[4],
             t5 = r->n[5], t6 = r->n[6], t7 = r->n[7], t8 = r->n[8], t9 = r->n[9];

    /* Reduce t9 at the start so there will be at most a single carry from the first pass */
    uint32_t m;
    uint32_t x = t9 >> 22; t9 &= 0x03FFFFFUL;

    /* The first pass ensures the magnitude is 1, ... */
    t0 += x * 0x3D1UL; t1 += (x << 6);
    t1 += (t0 >> 26); t0 &= 0x3FFFFFFUL;
    t2 += (t1 >> 26); t1 &= 0x3FFFFFFUL;
    t3 += (t2 >> 26); t2 &= 0x3FFFFFFUL; m = t2;
    t4 += (t3 >> 26); t3 &= 0x3FFFFFFUL; m &= t3;
    t5 += (t4 >> 26); t4 &= 0x3FFFFFFUL; m &= t4;
    t6 += (t5 >> 26); t5 &= 0x3FFFFFFUL; m &= t5;
    t7 += (t6 >> 26); t6 &= 0x3FFFFFFUL; m &= t6;
    t8 += (t7 >> 26); t7 &= 0x3FFFFFFUL; m &= t7;
    t9 += (t8 >> 26); t8 &= 0x3FFFFFFUL; m &= t8;

    /* ... except for a possible carry at bit 22 of t9 (i.e. bit 256 of the field element) */
    VERIFY_CHECK(t9 >> 23 == 0);

    /* At most a single final reduction is needed; check if the value is >= the field characteristic */
    x = (t9 >> 22) | ((t9 == 0x03FFFFFUL) & (m == 0x3FFFFFFUL)
        & ((t1 + 0x40UL + ((t0 + 0x3D1UL) >> 26)) > 0x3FFFFFFUL));

    /* Apply the final reduction (for constant-time behaviour, we do it always) */
    t0 += x * 0x3D1UL; t1 += (x << 6);
    t1 += (t0 >> 26); t0 &= 0x3FFFFFFUL;
    t2 += (t1 >> 26); t1 &= 0x3FFFFFFUL;
    t3 += (t2 >> 26); t2 &= 0x3FFFFFFUL;
    t4 += (t3 >> 26); t3 &= 0x3FFFFFFUL;
    t5 += (t4 >> 26); t4 &= 0x3FFFFFFUL;
    t6 += (t5 >> 26); t5 &= 0x3FFFFFFUL;
    t7 += (t6 >> 26); t6 &= 0x3FFFFFFUL;
    t8 += (t7 >> 26); t7 &= 0x3FFFFFFUL;
    t9 += (t8 >> 26); t8 &= 0x3FFFFFFUL;

    /* If t9 didn't carry to bit 22 already, then it should have after any final reduction */
    VERIFY_CHECK(t9 >> 22 == x);

    /* Mask off the possible multiple of 2^256 from the final reduction */
    t9 &= 0x03FFFFFUL;

    r->n[0] = t0; r->n[1] = t1; r->n[2] = t2; r->n[3] = t3; r->n[4] = t4;
    r->n[5] = t5; r->n[6] = t6; r->n[7] = t7; r->n[8] = t8; r->n[9] = t9;

    r->magnitude = 1;
    r->normalized = 1;
    secp256k1_fe_verifyX(r);
}

/** Convert a field element to a 32-byte big endian value. Requires the input to be normalized */
static void secp256k1_fe_get_b32X(unsigned char *r, const secp256k1_feX *a) {
    int i;
    VERIFY_CHECK(a->normalized);
    secp256k1_fe_verifyX(a);

    for (i=0; i<32; i++) {
        int j;
        int c = 0;
        for (j=0; j<4; j++) {
            int limb = (8*i+2*j)/26;
            int shift = (8*i+2*j)%26;
            c |= ((a->n[limb] >> shift) & 0x3) << (2 * j);
        }
        r[31-i] = c;
    }
}

static void secp256k1_fe_sqrX(secp256k1_feX *r, const secp256k1_feX *a) {
	VERIFY_CHECK(a->magnitude <= 8);
	secp256k1_fe_verifyX(a);
	secp256k1_fe_sqr_innerX(r->n, a->n);
	r->magnitude = 1;
	r->normalized = 0;
	secp256k1_fe_verifyX(r);
}


void secp256k1_fe_addX(secp256k1_feX *r, const secp256k1_feX *a) {
    secp256k1_fe_verifyX(a);
    r->n[0] += a->n[0];
    r->n[1] += a->n[1];
    r->n[2] += a->n[2];
    r->n[3] += a->n[3];
    r->n[4] += a->n[4];
    r->n[5] += a->n[5];
    r->n[6] += a->n[6];
    r->n[7] += a->n[7];
    r->n[8] += a->n[8];
    r->n[9] += a->n[9];
    r->magnitude += a->magnitude;
    r->normalized = 0;
    secp256k1_fe_verifyX(r);
}

void secp256k1_fe_addXX(secp256k1_feX *r, __constant secp256k1_feX *a) {
    /*secp256k1_fe_verifyX(a);*/
    r->n[0] += a->n[0];
    r->n[1] += a->n[1];
    r->n[2] += a->n[2];
    r->n[3] += a->n[3];
    r->n[4] += a->n[4];
    r->n[5] += a->n[5];
    r->n[6] += a->n[6];
    r->n[7] += a->n[7];
    r->n[8] += a->n[8];
    r->n[9] += a->n[9];
    r->magnitude += a->magnitude;
    r->normalized = 0;
    /*secp256k1_fe_verifyX(r);*/
}

static int secp256k1_fe_is_oddX(const secp256k1_feX *a) {
    VERIFY_CHECK(a->normalized);
    secp256k1_fe_verifyX(a);
    return a->n[0] & 1;
}

int secp256k1_fe_cmp_varX(secp256k1_feX *a, __constant secp256k1_feX *b) {
	int i;
    for (i = 9; i >= 0; i--) {
        if (a->n[i] > b->n[i]) {
            return 1;
        }
        if (a->n[i] < b->n[i]) {
            return -1;
        }
    }
    return 0;
}
static void secp256k1_fe_invX(secp256k1_feX *r, const secp256k1_feX *a) {
    secp256k1_feX x2, x3, x6, x9, x11, x22, x44, x88, x176, x220, x223, t1;
    int j;

    /** The binary representation of (p - 2) has 5 blocks of 1s, with lengths in
     *  { 1, 2, 22, 223 }. Use an addition chain to calculate 2^n - 1 for each block:
     *  [1], [2], 3, 6, 9, 11, [22], 44, 88, 176, 220, [223]
     */

    secp256k1_fe_sqrX(&x2, a);
    secp256k1_fe_mulX(&x2, &x2, a);

    secp256k1_fe_sqrX(&x3, &x2);
    secp256k1_fe_mulX(&x3, &x3, a);

    x6 = x3;
    for (j=0; j<3; j++) {
        secp256k1_fe_sqrX(&x6, &x6);
    }
    secp256k1_fe_mulX(&x6, &x6, &x3);

    x9 = x6;
    for (j=0; j<3; j++) {
        secp256k1_fe_sqrX(&x9, &x9);
    }
    secp256k1_fe_mulX(&x9, &x9, &x3);

    x11 = x9;
    for (j=0; j<2; j++) {
        secp256k1_fe_sqrX(&x11, &x11);
    }
    secp256k1_fe_mulX(&x11, &x11, &x2);

    x22 = x11;
    for (j=0; j<11; j++) {
        secp256k1_fe_sqrX(&x22, &x22);
    }
    secp256k1_fe_mulX(&x22, &x22, &x11);

    x44 = x22;
    for (j=0; j<22; j++) {
        secp256k1_fe_sqrX(&x44, &x44);
    }
    secp256k1_fe_mulX(&x44, &x44, &x22);

    x88 = x44;
    for (j=0; j<44; j++) {
        secp256k1_fe_sqrX(&x88, &x88);
    }
    secp256k1_fe_mulX(&x88, &x88, &x44);

    x176 = x88;
    for (j=0; j<88; j++) {
        secp256k1_fe_sqrX(&x176, &x176);
    }
    secp256k1_fe_mulX(&x176, &x176, &x88);

    x220 = x176;
    for (j=0; j<44; j++) {
        secp256k1_fe_sqrX(&x220, &x220);
    }
    secp256k1_fe_mulX(&x220, &x220, &x44);

    x223 = x220;
    for (j=0; j<3; j++) {
        secp256k1_fe_sqrX(&x223, &x223);
    }
    secp256k1_fe_mulX(&x223, &x223, &x3);

    /* The final result is then assembled using a sliding window over the blocks. */

    t1 = x223;
    for (j=0; j<23; j++) {
        secp256k1_fe_sqrX(&t1, &t1);
    }
    secp256k1_fe_mulX(&t1, &t1, &x22);
    for (j=0; j<5; j++) {
        secp256k1_fe_sqrX(&t1, &t1);
    }
    secp256k1_fe_mulX(&t1, &t1, a);
    for (j=0; j<3; j++) {
        secp256k1_fe_sqrX(&t1, &t1);
    }
    secp256k1_fe_mulX(&t1, &t1, &x2);
    for (j=0; j<2; j++) {
        secp256k1_fe_sqrX(&t1, &t1);
    }
    secp256k1_fe_mulX(r, a, &t1);
}

static int secp256k1_fe_normalizes_to_zero_varX(secp256k1_feX *r) {
    uint32_t t0, t1, t2, t3, t4, t5, t6, t7, t8, t9;
    uint32_t z0, z1;
    uint32_t x;

    t0 = r->n[0];
    t9 = r->n[9];

    /* Reduce t9 at the start so there will be at most a single carry from the first pass */
    x = t9 >> 22;

    /* The first pass ensures the magnitude is 1, ... */
    t0 += x * 0x3D1UL;

    /* z0 tracks a possible raw value of 0, z1 tracks a possible raw value of P */
    z0 = t0 & 0x3FFFFFFUL;
    z1 = z0 ^ 0x3D0UL;

    /* Fast return path should catch the majority of cases */
    if ((z0 != 0UL) & (z1 != 0x3FFFFFFUL)) {
        return 0;
    }

    t1 = r->n[1];
    t2 = r->n[2];
    t3 = r->n[3];
    t4 = r->n[4];
    t5 = r->n[5];
    t6 = r->n[6];
    t7 = r->n[7];
    t8 = r->n[8];

    t9 &= 0x03FFFFFUL;
    t1 += (x << 6);

    t1 += (t0 >> 26);
    t2 += (t1 >> 26); t1 &= 0x3FFFFFFUL; z0 |= t1; z1 &= t1 ^ 0x40UL;
    t3 += (t2 >> 26); t2 &= 0x3FFFFFFUL; z0 |= t2; z1 &= t2;
    t4 += (t3 >> 26); t3 &= 0x3FFFFFFUL; z0 |= t3; z1 &= t3;
    t5 += (t4 >> 26); t4 &= 0x3FFFFFFUL; z0 |= t4; z1 &= t4;
    t6 += (t5 >> 26); t5 &= 0x3FFFFFFUL; z0 |= t5; z1 &= t5;
    t7 += (t6 >> 26); t6 &= 0x3FFFFFFUL; z0 |= t6; z1 &= t6;
    t8 += (t7 >> 26); t7 &= 0x3FFFFFFUL; z0 |= t7; z1 &= t7;
    t9 += (t8 >> 26); t8 &= 0x3FFFFFFUL; z0 |= t8; z1 &= t8;
                                         z0 |= t9; z1 &= t9 ^ 0x3C00000UL;

    /* ... except for a possible carry at bit 22 of t9 (i.e. bit 256 of the field element) */
    VERIFY_CHECK(t9 >> 23 == 0);

    return (z0 == 0) | (z1 == 0x3FFFFFFUL);
}

int secp256k1_fe_equal_varX(const secp256k1_feX *a, const secp256k1_feX *b) {
    secp256k1_feX na;
    secp256k1_fe_negateX(&na, a, 1);
    secp256k1_fe_addX(&na, b);
    return secp256k1_fe_normalizes_to_zero_varX(&na);
}

static void secp256k1_fe_inv_varX(secp256k1_feX *r, const secp256k1_feX *a) {
    secp256k1_fe_invX(r, a);
}

void secp256k1_fe_clearX(secp256k1_feX *a) {
    int i;
    a->magnitude = 0;
    a->normalized = 1;
    for (i=0; i<10; i++) {
        a->n[i] = 0;
    }
}

static int secp256k1_fe_sqrt_varX(secp256k1_feX *r, const secp256k1_feX *a) {
    secp256k1_feX x2, x3, x6, x9, x11, x22, x44, x88, x176, x220, x223, t1;
    int j;

    /** The binary representation of (p + 1)/4 has 3 blocks of 1s, with lengths in
     *      *  { 2, 22, 223 }. Use an addition chain to calculate 2^n - 1 for each block:
     *           *  1, [2], 3, 6, 9, 11, [22], 44, 88, 176, 220, [223]
     *                */

    secp256k1_fe_sqrX(&x2, a);
    secp256k1_fe_mulX(&x2, &x2, a);

    secp256k1_fe_sqrX(&x3, &x2);
    secp256k1_fe_mulX(&x3, &x3, a);

    x6 = x3;
    for (j=0; j<3; j++) {
        secp256k1_fe_sqrX(&x6, &x6);
    }
    secp256k1_fe_mulX(&x6, &x6, &x3);

    x9 = x6;
    for (j=0; j<3; j++) {
        secp256k1_fe_sqrX(&x9, &x9);
    }
    secp256k1_fe_mulX(&x9, &x9, &x3);

    x11 = x9;
    for (j=0; j<2; j++) {
        secp256k1_fe_sqrX(&x11, &x11);
    }
    secp256k1_fe_mulX(&x11, &x11, &x2);

    x22 = x11;
    for (j=0; j<11; j++) {
        secp256k1_fe_sqrX(&x22, &x22);
    }
    secp256k1_fe_mulX(&x22, &x22, &x11);

    x44 = x22;
    for (j=0; j<22; j++) {
        secp256k1_fe_sqrX(&x44, &x44);
    }
    secp256k1_fe_mulX(&x44, &x44, &x22);

    x88 = x44;
    for (j=0; j<44; j++) {
        secp256k1_fe_sqrX(&x88, &x88);
    }
    secp256k1_fe_mulX(&x88, &x88, &x44);

    x176 = x88;
    for (j=0; j<88; j++) {
        secp256k1_fe_sqrX(&x176, &x176);
    }
    secp256k1_fe_mulX(&x176, &x176, &x88);

    x220 = x176;
    for (j=0; j<44; j++) {
        secp256k1_fe_sqrX(&x220, &x220);
    }
    secp256k1_fe_mulX(&x220, &x220, &x44);

    x223 = x220;
    for (j=0; j<3; j++) {
        secp256k1_fe_sqrX(&x223, &x223);
    }
    secp256k1_fe_mulX(&x223, &x223, &x3);

    /* The final result is then assembled using a sliding window over the blocks. */

    t1 = x223;
    for (j=0; j<23; j++) {
        secp256k1_fe_sqrX(&t1, &t1);
    }
    secp256k1_fe_mulX(&t1, &t1, &x22);
    for (j=0; j<6; j++) {
        secp256k1_fe_sqrX(&t1, &t1);
    }
    secp256k1_fe_mulX(&t1, &t1, &x2);
    secp256k1_fe_sqrX(&t1, &t1);
    secp256k1_fe_sqrX(r, &t1);

    /* Check that a square root was actually calculated */

    secp256k1_fe_sqrX(&t1, r);
    return secp256k1_fe_equal_varX(&t1, a);
}

static void secp256k1_fe_to_storageX(secp256k1_fe_storageX *r, const secp256k1_feX *a) {
    VERIFY_CHECK(a->normalized);
    r->n[0] = a->n[0] | a->n[1] << 26;
    r->n[1] = a->n[1] >> 6 | a->n[2] << 20;
    r->n[2] = a->n[2] >> 12 | a->n[3] << 14;
    r->n[3] = a->n[3] >> 18 | a->n[4] << 8;
    r->n[4] = a->n[4] >> 24 | a->n[5] << 2 | a->n[6] << 28;
    r->n[5] = a->n[6] >> 4 | a->n[7] << 22;
    r->n[6] = a->n[7] >> 10 | a->n[8] << 16;
    r->n[7] = a->n[8] >> 16 | a->n[9] << 10;
}

static void secp256k1_fe_from_storageX(secp256k1_feX *r, __global const secp256k1_fe_storageX *a) {
    r->n[0] = a->n[0] & 0x3FFFFFFUL;
    r->n[1] = a->n[0] >> 26 | ((a->n[1] << 6) & 0x3FFFFFFUL);
    r->n[2] = a->n[1] >> 20 | ((a->n[2] << 12) & 0x3FFFFFFUL);
    r->n[3] = a->n[2] >> 14 | ((a->n[3] << 18) & 0x3FFFFFFUL);
    r->n[4] = a->n[3] >> 8 | ((a->n[4] << 24) & 0x3FFFFFFUL);
    r->n[5] = (a->n[4] >> 2) & 0x3FFFFFFUL;
    r->n[6] = a->n[4] >> 28 | ((a->n[5] << 4) & 0x3FFFFFFUL);
    r->n[7] = a->n[5] >> 22 | ((a->n[6] << 10) & 0x3FFFFFFUL);
    r->n[8] = a->n[6] >> 16 | ((a->n[7] << 16) & 0x3FFFFFFUL);
    r->n[9] = a->n[7] >> 10;

    r->magnitude = 1;
    r->normalized = 1;
}

static void secp256k1_fe_normalize_varX(secp256k1_feX *r) {
    uint32_t t0 = r->n[0], t1 = r->n[1], t2 = r->n[2], t3 = r->n[3], t4 = r->n[4],
             t5 = r->n[5], t6 = r->n[6], t7 = r->n[7], t8 = r->n[8], t9 = r->n[9];

    /* Reduce t9 at the start so there will be at most a single carry from the first pass */
    uint32_t m;
    uint32_t x = t9 >> 22; t9 &= 0x03FFFFFUL;

    /* The first pass ensures the magnitude is 1, ... */
    t0 += x * 0x3D1UL; t1 += (x << 6);
    t1 += (t0 >> 26); t0 &= 0x3FFFFFFUL;
    t2 += (t1 >> 26); t1 &= 0x3FFFFFFUL;
    t3 += (t2 >> 26); t2 &= 0x3FFFFFFUL; m = t2;
    t4 += (t3 >> 26); t3 &= 0x3FFFFFFUL; m &= t3;
    t5 += (t4 >> 26); t4 &= 0x3FFFFFFUL; m &= t4;
    t6 += (t5 >> 26); t5 &= 0x3FFFFFFUL; m &= t5;
    t7 += (t6 >> 26); t6 &= 0x3FFFFFFUL; m &= t6;
    t8 += (t7 >> 26); t7 &= 0x3FFFFFFUL; m &= t7;
    t9 += (t8 >> 26); t8 &= 0x3FFFFFFUL; m &= t8;

    /* ... except for a possible carry at bit 22 of t9 (i.e. bit 256 of the field element) */
    VERIFY_CHECK(t9 >> 23 == 0);

    /* At most a single final reduction is needed; check if the value is >= the field characteristic */
    x = (t9 >> 22) | ((t9 == 0x03FFFFFUL) & (m == 0x3FFFFFFUL)
        & ((t1 + 0x40UL + ((t0 + 0x3D1UL) >> 26)) > 0x3FFFFFFUL));

    if (x) {
        t0 += 0x3D1UL; t1 += (x << 6);
        t1 += (t0 >> 26); t0 &= 0x3FFFFFFUL;
        t2 += (t1 >> 26); t1 &= 0x3FFFFFFUL;
        t3 += (t2 >> 26); t2 &= 0x3FFFFFFUL;
        t4 += (t3 >> 26); t3 &= 0x3FFFFFFUL;
        t5 += (t4 >> 26); t4 &= 0x3FFFFFFUL;
        t6 += (t5 >> 26); t5 &= 0x3FFFFFFUL;
        t7 += (t6 >> 26); t6 &= 0x3FFFFFFUL;
        t8 += (t7 >> 26); t7 &= 0x3FFFFFFUL;
        t9 += (t8 >> 26); t8 &= 0x3FFFFFFUL;

        /* If t9 didn't carry to bit 22 already, then it should have after any final reduction */
        VERIFY_CHECK(t9 >> 22 == x);

        /* Mask off the possible multiple of 2^256 from the final reduction */
        t9 &= 0x03FFFFFUL;
    }

    r->n[0] = t0; r->n[1] = t1; r->n[2] = t2; r->n[3] = t3; r->n[4] = t4;
    r->n[5] = t5; r->n[6] = t6; r->n[7] = t7; r->n[8] = t8; r->n[9] = t9;

    r->magnitude = 1;
    r->normalized = 1;
    secp256k1_fe_verifyX(r);
}

static int secp256k1_ge_is_infinityX(const secp256k1_geX *a) {
        return a->infinity;
}

static int secp256k1_ge_is_valid_varX(const secp256k1_geX *a) {
    secp256k1_feX y2, x3, c;
    if (a->infinity) {
        return 0;
    }
    /* y^2 = x^3 + 7 */
    secp256k1_fe_sqrX(&y2, &a->y);
    secp256k1_fe_sqrX(&x3, &a->x); 
    secp256k1_fe_mulX(&x3, &x3, &a->x);
    secp256k1_fe_set_intX(&c, 7);
    secp256k1_fe_addX(&x3, &c);
    secp256k1_fe_normalize_weakX(&x3);
    return secp256k1_fe_equal_varX(&y2, &x3);
}

static void secp256k1_ge_negX(secp256k1_geX *r, const secp256k1_geX *a) {
    *r = *a;
    secp256k1_fe_normalize_weakX(&r->y);
    secp256k1_fe_negateX(&r->y, &r->y, 1);
}

static void secp256k1_ge_from_storageX(secp256k1_geX *r, __global const secp256k1_ge_storageX *a) {
	/*printf("ge C %ul %ul \n", a->x.n[0], a->y.n[0]);*/
	secp256k1_fe_from_storageX(&r->x, &a->x);
	secp256k1_fe_from_storageX(&r->y, &a->y);
	/*printf("C %ul %ul %ul %ul \n", r->x.n[0], r->y.n[0], a->x.n[0], a->y.n[0]);*/
	r->infinity = 0;
}

static void secp256k1_ge_from_storageX_s(secp256k1_geX *r, const secp256k1_ge_storageX *a) {
    secp256k1_fe_from_storageX_s(&r->x, &a->x);
    secp256k1_fe_from_storageX_s(&r->y, &a->y);
    r->infinity = 0;
}

static void secp256k1_ge_set_xyX(secp256k1_geX *r, const secp256k1_feX *x, const secp256k1_feX *y) {
    r->infinity = 0;
    r->x = *x;
    r->y = *y;
}

static void secp256k1_gej_set_geX(secp256k1_gejX *r, const secp256k1_geX *a) {
	r->x = a->x;
	r->y = a->y;
	r->infinity = a->infinity;
	secp256k1_fe_set_intX(&r->z, 1);
}

static int secp256k1_gej_is_infinityX(const secp256k1_gejX *a) {
    return a->infinity;
}

static int secp256k1_ge_set_xo_varX(secp256k1_geX *r, const secp256k1_feX *x, int odd) {
    secp256k1_feX x2, x3, c;
    r->x = *x;
    secp256k1_fe_sqrX(&x2, x);
    secp256k1_fe_mulX(&x3, x, &x2);
    r->infinity = 0;
    secp256k1_fe_set_intX(&c, 7);
    secp256k1_fe_addX(&c, &x3);
    if (!secp256k1_fe_sqrt_varX(&r->y, &c)) {
        return 0;
    }
    secp256k1_fe_normalize_varX(&r->y);
    if (secp256k1_fe_is_oddX(&r->y) != odd) {
        secp256k1_fe_negateX(&r->y, &r->y, 1);
    }
    return 1;
}


static void secp256k1_gej_double_varX(secp256k1_gejX *r, const secp256k1_gejX *a, secp256k1_feX *rzr) {

    /* Operations: 3 mul, 4 sqr, 0 normalize, 12 mul_int/add/negate */
    secp256k1_feX t1,t2,t3,t4;
    /** For secp256k1, 2Q is infinity if and only if Q is infinity. This is because if 2Q = infinity,
     *  Q must equal -Q, or that Q.y == -(Q.y), or Q.y is 0. For a point on y^2 = x^3 + 7 to have
     *  y=0, x^3 must be -7 mod p. However, -7 has no cube root mod p.
     */
    r->infinity = a->infinity;
    if (r->infinity) {
        if (rzr != 0) {
            secp256k1_fe_set_intX(rzr, 1);
        }
        return;
    }

    if (rzr != 0) {
        *rzr = a->y;
        secp256k1_fe_normalize_weakX(rzr);
        secp256k1_fe_mul_intX(rzr, 2);
    }

    secp256k1_fe_mulX(&r->z, &a->z, &a->y);
    secp256k1_fe_mul_intX(&r->z, 2);       /* Z' = 2*Y*Z (2) */
    secp256k1_fe_sqrX(&t1, &a->x);
    secp256k1_fe_mul_intX(&t1, 3);         /* T1 = 3*X^2 (3) */
    secp256k1_fe_sqrX(&t2, &t1);           /* T2 = 9*X^4 (1) */
    secp256k1_fe_sqrX(&t3, &a->y);
    secp256k1_fe_mul_intX(&t3, 2);         /* T3 = 2*Y^2 (2) */
    secp256k1_fe_sqrX(&t4, &t3);
    secp256k1_fe_mul_intX(&t4, 2);         /* T4 = 8*Y^4 (2) */
    secp256k1_fe_mulX(&t3, &t3, &a->x);    /* T3 = 2*X*Y^2 (1) */
    r->x = t3;
    secp256k1_fe_mul_intX(&r->x, 4);       /* X' = 8*X*Y^2 (4) */
    secp256k1_fe_negateX(&r->x, &r->x, 4); /* X' = -8*X*Y^2 (5) */
    secp256k1_fe_addX(&r->x, &t2);         /* X' = 9*X^4 - 8*X*Y^2 (6) */
    secp256k1_fe_negateX(&t2, &t2, 1);     /* T2 = -9*X^4 (2) */
    secp256k1_fe_mul_intX(&t3, 6);         /* T3 = 12*X*Y^2 (6) */
    secp256k1_fe_addX(&t3, &t2);           /* T3 = 12*X*Y^2 - 9*X^4 (8) */
    secp256k1_fe_mulX(&r->y, &t1, &t3);    /* Y' = 36*X^3*Y^2 - 27*X^6 (1) */
    secp256k1_fe_negateX(&t2, &t4, 2);     /* T2 = -8*Y^4 (3) */
    secp256k1_fe_addX(&r->y, &t2);         /* Y' = 36*X^3*Y^2 - 27*X^6 - 8*Y^4 (4) */
}

static void secp256k1_ge_set_gej_zinvX(secp256k1_geX *r, const secp256k1_gejX *a, const secp256k1_feX *zi) {
    secp256k1_feX zi2;
    secp256k1_feX zi3;
    secp256k1_fe_sqrX(&zi2, zi);
    secp256k1_fe_mulX(&zi3, &zi2, zi);
    secp256k1_fe_mulX(&r->x, &a->x, &zi2);
    secp256k1_fe_mulX(&r->y, &a->y, &zi3);
    r->infinity = a->infinity;
}
static void secp256k1_ge_to_storageX(secp256k1_ge_storageX *r, const secp256k1_geX *a) {
    secp256k1_feX x, y;
    VERIFY_CHECK(!a->infinity);
    x = a->x;
    secp256k1_fe_normalizeX(&x);
    y = a->y;
    secp256k1_fe_normalizeX(&y);
    secp256k1_fe_to_storageX(&r->x, &x);
    secp256k1_fe_to_storageX(&r->y, &y);
}

static void secp256k1_gej_add_ge_varX(secp256k1_gejX *r, const secp256k1_gejX *a, const secp256k1_geX *b, secp256k1_feX *rzr) {
    /* 8 mul, 3 sqr, 4 normalize, 12 mul_int/add/negate */
    secp256k1_feX z12, u1, u2, s1, s2, h, i, i2, h2, h3, t;
    if (a->infinity) {
        secp256k1_gej_set_geX(r, b);
        return;
    }
    if (b->infinity) {
        if (rzr != 0) {
            secp256k1_fe_set_intX(rzr, 1);
        }
        *r = *a;
        return;
    }
    r->infinity = 0;

    secp256k1_fe_sqrX(&z12, &a->z);
    u1 = a->x; secp256k1_fe_normalize_weakX(&u1);
    secp256k1_fe_mulX(&u2, &b->x, &z12);
    s1 = a->y; secp256k1_fe_normalize_weakX(&s1);
    secp256k1_fe_mulX(&s2, &b->y, &z12); secp256k1_fe_mulX(&s2, &s2, &a->z);
    secp256k1_fe_negateX(&h, &u1, 1); secp256k1_fe_addX(&h, &u2);
    secp256k1_fe_negateX(&i, &s1, 1); secp256k1_fe_addX(&i, &s2);
    if (secp256k1_fe_normalizes_to_zero_varX(&h)) {
        if (secp256k1_fe_normalizes_to_zero_varX(&i)) {
            secp256k1_gej_double_varX(r, a, rzr);
        } else {
            if (rzr != 0) {
                secp256k1_fe_set_intX(rzr, 0);
            }
            r->infinity = 1;
        }
        return;
    }
    secp256k1_fe_sqrX(&i2, &i);
    secp256k1_fe_sqrX(&h2, &h);
    secp256k1_fe_mulX(&h3, &h, &h2);
    if (rzr != 0) {
        *rzr = h;
    }
    secp256k1_fe_mulX(&r->z, &a->z, &h);
    secp256k1_fe_mulX(&t, &u1, &h2);
    r->x = t; secp256k1_fe_mul_intX(&r->x, 2); secp256k1_fe_addX(&r->x, &h3); secp256k1_fe_negateX(&r->x, &r->x, 3); secp256k1_fe_addX(&r->x, &i2);
    secp256k1_fe_negateX(&r->y, &r->x, 5); secp256k1_fe_addX(&r->y, &t); secp256k1_fe_mulX(&r->y, &r->y, &i);
    secp256k1_fe_mulX(&h3, &h3, &s1); secp256k1_fe_negateX(&h3, &h3, 1);
    secp256k1_fe_addX(&r->y, &h3);
}

static void secp256k1_gej_rescaleX(secp256k1_gejX *r, const secp256k1_feX *s) {
    /* Operations: 4 mul, 1 sqr */
    secp256k1_feX zz;
    secp256k1_fe_sqrX(&zz, s);
    secp256k1_fe_mulX(&r->x, &r->x, &zz);                /* r->x *= s^2 */
    secp256k1_fe_mulX(&r->y, &r->y, &zz);
    secp256k1_fe_mulX(&r->y, &r->y, s);                  /* r->y *= s^3 */
    secp256k1_fe_mulX(&r->z, &r->z, s);                  /* r->z *= s   */
}

static void secp256k1_ge_globalz_set_table_gejX(size_t len, secp256k1_geX *r, secp256k1_feX *globalz, const secp256k1_gejX *a, const secp256k1_feX *zr) {
    size_t i = len - 1;
    secp256k1_feX zs;

    if (len > 0) {
        /* The z of the final point gives us the "global Z" for the table. */
        r[i].x = a[i].x;
        r[i].y = a[i].y;
        /* Ensure all y values are in weak normal form for fast negation of points */
        secp256k1_fe_normalize_weakX(&r[i].y);
        *globalz = a[i].z;
        r[i].infinity = 0;
        zs = zr[i];

        /* Work our way backwards, using the z-ratios to scale the x/y values. */
        while (i > 0) {
            if (i != len - 1) {
                secp256k1_fe_mulX(&zs, &zs, &zr[i]);
            }
            i--;
            secp256k1_ge_set_gej_zinvX(&r[i], &a[i], &zs);
        }
    }
}

static void secp256k1_gej_set_infinityX(secp256k1_gejX *r) {
    r->infinity = 1;
	secp256k1_fe_set_intX(&r->x, 0);
    secp256k1_fe_set_intX(&r->y, 0);
    secp256k1_fe_set_intX(&r->z, 0);
}

#define ECMULT_TABLE_GET_GE(r,pre,n,w) do { \
    VERIFY_CHECK(((n) & 1) == 1); \
    VERIFY_CHECK((n) >= -((1 << ((w)-1)) - 1)); \
    VERIFY_CHECK((n) <=  ((1 << ((w)-1)) - 1)); \
    if ((n) > 0) { \
        *(r) = (pre)[((n)-1)/2]; \
    } else { \
        secp256k1_ge_negX((r), &(pre)[(-(n)-1)/2]); \
    } \
} while(0)


#define ECMULT_TABLE_GET_GE_STORAGE(r,pre,n,w) do { \
		VERIFY_CHECK(((n) & 1) == 1); \
		VERIFY_CHECK((n) >= -((1 << ((w)-1)) - 1)); \
		VERIFY_CHECK((n) <=  ((1 << ((w)-1)) - 1)); \
		if ((n) > 0) { \
			secp256k1_ge_from_storageX((r), &(pre)[((n)-1)/2]); \
		} else { \
			secp256k1_ge_from_storageX((r), &(pre)[(-(n)-1)/2]); \
			secp256k1_ge_negX((r), (r)); \
		} \
	} while(0)


static void secp256k1_gej_add_zinv_varX(secp256k1_gejX *r, const secp256k1_gejX *a, const secp256k1_geX *b, const secp256k1_feX *bzinv) {
    /* 9 mul, 3 sqr, 4 normalize, 12 mul_int/add/negate */
    secp256k1_feX az, z12, u1, u2, s1, s2, h, i, i2, h2, h3, t;
    if (b->infinity) {
        *r = *a;
        return;
    }
	
    if (a->infinity) {
        secp256k1_feX bzinv2, bzinv3;
        r->infinity = b->infinity;
        secp256k1_fe_sqrX(&bzinv2, bzinv);
        secp256k1_fe_mulX(&bzinv3, &bzinv2, bzinv);
        secp256k1_fe_mulX(&r->x, &b->x, &bzinv2);
        secp256k1_fe_mulX(&r->y, &b->y, &bzinv3);
        secp256k1_fe_set_intX(&r->z, 1);
		
        return;
    }
    r->infinity = 0;

    secp256k1_fe_mulX(&az, &a->z, bzinv);

    secp256k1_fe_sqrX(&z12, &az);
    u1 = a->x; secp256k1_fe_normalize_weakX(&u1);
    secp256k1_fe_mulX(&u2, &b->x, &z12);
    s1 = a->y; secp256k1_fe_normalize_weakX(&s1);
    secp256k1_fe_mulX(&s2, &b->y, &z12); secp256k1_fe_mulX(&s2, &s2, &az);
    secp256k1_fe_negateX(&h, &u1, 1); secp256k1_fe_addX(&h, &u2);
    secp256k1_fe_negateX(&i, &s1, 1); secp256k1_fe_addX(&i, &s2);
    if (secp256k1_fe_normalizes_to_zero_varX(&h)) {
        if (secp256k1_fe_normalizes_to_zero_varX(&i)) {
            secp256k1_gej_double_varX(r, a, 0);
        } else {
            r->infinity = 1;
        }
        return;
    }
    secp256k1_fe_sqrX(&i2, &i);
    secp256k1_fe_sqrX(&h2, &h);
    secp256k1_fe_mulX(&h3, &h, &h2);
    r->z = a->z; secp256k1_fe_mulX(&r->z, &r->z, &h);
    secp256k1_fe_mulX(&t, &u1, &h2);
    r->x = t; secp256k1_fe_mul_intX(&r->x, 2); secp256k1_fe_addX(&r->x, &h3); secp256k1_fe_negateX(&r->x, &r->x, 3); secp256k1_fe_addX(&r->x, &i2);
    secp256k1_fe_negateX(&r->y, &r->x, 5); secp256k1_fe_addX(&r->y, &t); secp256k1_fe_mulX(&r->y, &r->y, &i);
    secp256k1_fe_mulX(&h3, &h3, &s1); secp256k1_fe_negateX(&h3, &h3, 1);
    secp256k1_fe_addX(&r->y, &h3);
}

static int secp256k1_gej_eq_x_varX(const secp256k1_feX *x, const secp256k1_gejX *a) {
    secp256k1_feX r, r2;
    secp256k1_fe_sqrX(&r, &a->z); secp256k1_fe_mulX(&r, &r, x);
    r2 = a->x; secp256k1_fe_normalize_weakX(&r2);
    return secp256k1_fe_equal_varX(&r, &r2);
}

static void secp256k1_ge_set_gej_var(secp256k1_geX *r, secp256k1_gejX *a) {
    secp256k1_feX z2, z3; 
    r->infinity = a->infinity;
    if (a->infinity) {
        return;
    }   
    secp256k1_fe_inv_varX(&a->z, &a->z);
    secp256k1_fe_sqrX(&z2, &a->z);
    secp256k1_fe_mulX(&z3, &a->z, &z2);
    secp256k1_fe_mulX(&a->x, &a->x, &z2);
    secp256k1_fe_mulX(&a->y, &a->y, &z3);
    secp256k1_fe_set_intX(&a->z, 1); 
    r->x = a->x;
    r->y = a->y;
}

static int secp256k1_ecmult_wnafX(int *wnaf, int len, const secp256k1_scalarX *a, int w) {
    secp256k1_scalarX s;
    int last_set_bit = -1;
    int bit = 0;
    int sign = 1;
    int carry = 0;

    memsetX(wnaf, 0, len * sizeof(wnaf[0]));

    s = *a;
    if (secp256k1_scalar_get_bitsX(&s, 255, 1)) {
        secp256k1_scalar_negateX(&s, &s);
        sign = -1;
    }

    while (bit < len) {
        int now;
        int word;
        if (secp256k1_scalar_get_bitsX(&s, bit, 1) == (unsigned int)carry) {
            bit++;
            continue;
        }

        now = w;
        if (now > len - bit) {
            now = len - bit;
        }

        word = secp256k1_scalar_get_bits_varX(&s, bit, now) + carry;

        carry = (word >> (w-1)) & 1;
        word -= carry << w;

        wnaf[bit] = sign * word;
        last_set_bit = bit;

        bit += now;
    }
	/* 
    while (bit < 256) {
        CHECK(secp256k1_scalar_get_bitsX(&s, bit++, 1) == 0);
    } */

    return last_set_bit + 1;
}

static void secp256k1_ecmult_odd_multiples_tableX(int n, secp256k1_gejX *prej, secp256k1_feX *zr, const secp256k1_gejX *a) {
    secp256k1_gejX d;
    secp256k1_geX a_ge, d_ge;
    int i;

    secp256k1_gej_double_varX(&d, a, 0);

    d_ge.x = d.x;
    d_ge.y = d.y;
    d_ge.infinity = 0;

    secp256k1_ge_set_gej_zinvX(&a_ge, a, &d.z);
    prej[0].x = a_ge.x;
    prej[0].y = a_ge.y;
    prej[0].z = a->z;
    prej[0].infinity = 0;

    zr[0] = d.z;
    for (i = 1; i < n; i++) {
        secp256k1_gej_add_ge_varX(&prej[i], &prej[i-1], &d_ge, &zr[i]);
    }

    /*
     * Each point in 'prej' has a z coordinate too small by a factor of 'd.z'. Only
     * the final point's z coordinate is actually used though, so just update that.
     */
    secp256k1_fe_mulX(&prej[n-1].z, &prej[n-1].z, &d.z);
}

static void secp256k1_ecmult_odd_multiples_table_globalz_windowaX(secp256k1_geX *pre, secp256k1_feX *globalz, const secp256k1_gejX *a) {
    secp256k1_gejX prej[ECMULT_TABLE_SIZE(WINDOW_A)];
    secp256k1_feX zr[ECMULT_TABLE_SIZE(WINDOW_A)];

    /* Compute the odd multiples in Jacobian form. */
    secp256k1_ecmult_odd_multiples_tableX(ECMULT_TABLE_SIZE(WINDOW_A), prej, zr, a);
    /* Bring them to the same Z denominator. */
    secp256k1_ge_globalz_set_table_gejX(ECMULT_TABLE_SIZE(WINDOW_A), pre, globalz, prej, zr);
}


static void secp256k1_ecmultX(__global const secp256k1_ge_storageX *ctx, secp256k1_gejX *r, const secp256k1_gejX *a, const secp256k1_scalarX *na, const secp256k1_scalarX *ng) {
    secp256k1_geX pre_a[ECMULT_TABLE_SIZE(WINDOW_A)];
    secp256k1_geX tmpa;
    secp256k1_feX Z;
    int wnaf_na[256];
    int bits_na;
    int wnaf_ng[256];
    int bits_ng;
    int i;
    int bits;


    /* build wnaf representation for na. */
    bits_na     = secp256k1_ecmult_wnafX(wnaf_na,     256, na,      WINDOW_A);
    bits = bits_na;

    /* Calculate odd multiples of a.
     * All multiples are brought to the same Z 'denominator', which is stored
     * in Z. Due to secp256k1' isomorphism we can do all operations pretending
     * that the Z coordinate was 1, use affine addition formulae, and correct
     * the Z coordinate of the result once at the end.
     * The exception is the precomputed G table points, which are actually
     * affine. Compared to the base used for other points, they have a Z ratio
     * of 1/Z, so we can use secp256k1_gej_add_zinv_var, which uses the same
     * isomorphism to efficiently add with a known Z inverse.
     */
    secp256k1_ecmult_odd_multiples_table_globalz_windowaX(pre_a, &Z, a);

    bits_ng     = secp256k1_ecmult_wnafX(wnaf_ng,     256, ng,      WINDOW_G);
    if (bits_ng > bits) {
        bits = bits_ng;
    }

    secp256k1_gej_set_infinityX(r);
    for (i = bits - 1; i >= 0; i--) {
        int n;
        secp256k1_gej_double_varX(r, r, 0);

        if (i < bits_na && (n = wnaf_na[i])) {
            ECMULT_TABLE_GET_GE(&tmpa, pre_a, n, WINDOW_A);
            secp256k1_gej_add_ge_varX(r, r, &tmpa, 0);
        }
        if (i < bits_ng && (n = wnaf_ng[i])) {
            ECMULT_TABLE_GET_GE_STORAGE(&tmpa, ctx, n, WINDOW_G);
            secp256k1_gej_add_zinv_varX(r, r, &tmpa, &Z);
        }
    }

    if (!r->infinity) {
        secp256k1_fe_mulX(&r->z, &r->z, &Z);
    }
}

static void secp256k1_ecdsa_signature_loadX(secp256k1_scalarX* r, secp256k1_scalarX* s, secp256k1_ecdsa_signatureX* sig) {
    if (sizeof(secp256k1_scalarX) == 32) {
        private_memcpy(r, &sig->data[0], 32);
        private_memcpy(s, &sig->data[32], 32);
    } 
#if 0
	else {
        secp256k1_scalar_set_b32X(r, &sig->data[0], (int*)0);
        secp256k1_scalar_set_b32X(s, &sig->data[32], (int*)0);
    }
#endif
}

static void secp256k1_ecdsa_signature_saveX(secp256k1_ecdsa_signatureX* sig, const secp256k1_scalarX* r, const secp256k1_scalarX* s) {
    if (sizeof(secp256k1_scalarX) == 32) {
        private_memcpy(&sig->data[0], r, 32);
        private_memcpy(&sig->data[32], s, 32);
    } else {
        secp256k1_scalar_get_b32X(&sig->data[0], r);
        secp256k1_scalar_get_b32X(&sig->data[32], s);
    }
}

int secp256k1_ecdsa_signature_parse_compactX(secp256k1_ecdsa_signatureX* sig, __global const unsigned char *input64) {
    secp256k1_scalarX r, s;
    int ret = 1;
    int overflow = 0;

    secp256k1_scalar_set_b32X(&r, &input64[0], &overflow);
    ret &= !overflow;
    secp256k1_scalar_set_b32X(&s, &input64[32], &overflow);
    ret &= !overflow;
    if (ret) {
        secp256k1_ecdsa_signature_saveX(sig, &r, &s);
    } else {
        memsetX(sig, 0, sizeof(*sig));
    }
    return ret;
}

static int secp256k1_pubkey_loadX(secp256k1_geX* ge, const secp256k1_pubkeyX* pubkey) {
    if (sizeof(secp256k1_ge_storageX) == 64) {
        /* When the secp256k1_ge_storageX type is exactly 64 byte, use its
         * representation inside secp256k1_pubkeyX, as conversion is very fast.
         * Note that secp256k1_pubkey_save must use the same representation. */
        secp256k1_ge_storageX s;
        private_memcpy(&s, &pubkey->data[0], 64);
        secp256k1_ge_from_storageX_s(ge, &s);
    }
#if 0
	else {
        /* Otherwise, fall back to 32-byte big endian for X and Y. */
        secp256k1_feX x, y;
        secp256k1_fe_set_b32X(&x, pubkey->data);
        secp256k1_fe_set_b32X(&y, pubkey->data + 32);
        secp256k1_ge_set_xyX(ge, &x, &y);
    }
#endif
    return 1;
}

# define SECP256K1_EC_COMPRESSED  (1 << 0)
static int secp256k1_eckey_pubkey_parseX(secp256k1_geX *elem, const unsigned char *pub, size_t size) {
    if (size == 33 && (pub[0] == 0x02 || pub[0] == 0x03)) {
        secp256k1_feX x;
        return secp256k1_fe_set_b32XX(&x, pub+1) && secp256k1_ge_set_xo_varX(elem, &x, pub[0] == 0x03);
    } else if (size == 65 && (pub[0] == 0x04 || pub[0] == 0x06 || pub[0] == 0x07)) {
        secp256k1_feX x, y;
        if (!secp256k1_fe_set_b32XX(&x, pub+1) || !secp256k1_fe_set_b32XX(&y, pub+33)) {
            return 0;
        }
        secp256k1_ge_set_xyX(elem, &x, &y);
        if ((pub[0] == 0x06 || pub[0] == 0x07) && secp256k1_fe_is_oddX(&y) != (pub[0] == 0x07)) {
            return 0;
        }
        return secp256k1_ge_is_valid_varX(elem);
    } else {
        return 0;
    }
}

static int secp256k1_eckey_pubkey_serializeX(secp256k1_geX *elem, unsigned char *pub, size_t *size, unsigned int flags) {
    if (secp256k1_ge_is_infinityX(elem)) {
        return 0;
    }
    secp256k1_fe_normalize_varX(&elem->x);
    secp256k1_fe_normalize_varX(&elem->y);
    secp256k1_fe_get_b32X(&pub[1], &elem->x);
    if (flags & SECP256K1_EC_COMPRESSED) {
        *size = 33;
        pub[0] = 0x02 | (secp256k1_fe_is_oddX(&elem->y) ? 0x01 : 0x00);
    } else {
        *size = 65;
        pub[0] = 0x04;
        secp256k1_fe_get_b32X(&pub[33], &elem->y);
    }
    return 1;
}
static void secp256k1_pubkey_saveX(secp256k1_pubkeyX* pubkey, secp256k1_geX* ge) {
    if (sizeof(secp256k1_ge_storageX) == 64) {
        secp256k1_ge_storageX s;
        secp256k1_ge_to_storageX(&s, ge);
        private_memcpy(&pubkey->data[0], &s, 64);
    } else {
        VERIFY_CHECK(!secp256k1_ge_is_infinityX(ge));
        secp256k1_fe_normalize_varX(&ge->x);
        secp256k1_fe_normalize_varX(&ge->y);
        secp256k1_fe_get_b32X(pubkey->data, &ge->x);
        secp256k1_fe_get_b32X(pubkey->data + 32, &ge->y);
    }
}

static void secp256k1_ge_clearX(secp256k1_geX *r) {
    r->infinity = 0;
    secp256k1_fe_clearX(&r->x);
    secp256k1_fe_clearX(&r->y);
}

int secp256k1_ec_pubkey_parseX(secp256k1_pubkeyX* pubkey, const unsigned char *input, size_t inputlen) {
    secp256k1_geX Q;

    memsetX(pubkey, 0, sizeof(*pubkey));
    if (!secp256k1_eckey_pubkey_parseX(&Q, input, inputlen)) {
        return 0;
    }
    secp256k1_pubkey_saveX(pubkey, &Q);
	secp256k1_ge_clearX(&Q);
    return 1;
}

typedef struct {
    unsigned char data[65];
} secp256k1_ecdsa_recoverable_signatureX;

static int secp256k1_ecdsa_sig_recoverX(__global const secp256k1_ge_storageX *ctx, const secp256k1_scalarX *sigr, const secp256k1_scalarX* sigs, secp256k1_geX *pubkey, const secp256k1_scalarX *message, int recid) {
    unsigned char brx[32];
    secp256k1_feX fx; 
    secp256k1_geX x;
    secp256k1_gejX xj; 
    secp256k1_scalarX rn, u1, u2; 
    secp256k1_gejX qj; 

    if (secp256k1_scalar_is_zeroX(sigr) || secp256k1_scalar_is_zeroX(sigs)) {
        return 0;
    }   

    secp256k1_scalar_get_b32X(brx, sigr);
    VERIFY_CHECK(secp256k1_fe_set_b32XX(&fx, brx)); /* brx comes from a scalar, so is less than the order; certainly less than p */
    if (recid & 2) {
        if (secp256k1_fe_cmp_varX(&fx, &secp256k1_ecdsa_const_p_minus_orderX) >= 0) {
            return 0;
        }
        secp256k1_fe_addXX(&fx, &secp256k1_ecdsa_const_order_as_feX);
    }
    if (!secp256k1_ge_set_xo_varX(&x, &fx, recid & 1)) {
        return 0;
    }   
    secp256k1_gej_set_geX(&xj, &x);
    secp256k1_scalar_inverse_varX(&rn, sigr);
    secp256k1_scalar_mulX(&u1, &rn, message);
    secp256k1_scalar_negateX(&u1, &u1);
    secp256k1_scalar_mulX(&u2, &rn, sigs);
    secp256k1_ecmultX(ctx, &qj, &xj, &u2, &u1);
    secp256k1_ge_set_gej_var(pubkey, &qj);
    return !secp256k1_gej_is_infinityX(&qj);
}

static void secp256k1_ecdsa_recoverable_signature_saveX(secp256k1_ecdsa_recoverable_signatureX* sig, const secp256k1_scalarX* r, const secp256k1_scalarX* s, int recid) {
    if (sizeof(secp256k1_scalarX) == 32) {
        private_memcpy(&sig->data[0], r, 32);
        private_memcpy(&sig->data[32], s, 32);
    } else {
        secp256k1_scalar_get_b32X(&sig->data[0], r);
        secp256k1_scalar_get_b32X(&sig->data[32], s);
    }
    sig->data[64] = recid;
}

static int secp256k1_ecdsa_recoverable_signature_parse_compactX(secp256k1_ecdsa_recoverable_signatureX* sig, __global const unsigned char *input64, int recid) {
    secp256k1_scalarX r, s;
    int ret = 1;
    int overflow = 0;

    secp256k1_scalar_set_b32X(&r, &input64[0], &overflow);
    ret &= !overflow;
    secp256k1_scalar_set_b32X(&s, &input64[32], &overflow);
    ret &= !overflow;
    if (ret) {
        secp256k1_ecdsa_recoverable_signature_saveX(sig, &r, &s, recid);
    } else {
        memsetX(sig, 0, sizeof(*sig));
    }
    return ret;
}

static int secp256k1_ecdsa_sig_verifyX(__global const secp256k1_ge_storageX *ctx, const secp256k1_scalarX *sigr, const secp256k1_scalarX *sigs,
										const secp256k1_geX *pubkey, const secp256k1_scalarX *message) 
{
    unsigned char c[32];
    secp256k1_scalarX u1, u2, sn;
    secp256k1_feX xr;
    secp256k1_gejX pubkeyj;
    secp256k1_gejX pr;

    if (secp256k1_scalar_is_zeroX(sigr) || secp256k1_scalar_is_zeroX(sigs)) {
        return 0;
    }
	
    secp256k1_scalar_inverse_varX(&sn, sigs);
    secp256k1_scalar_mulX(&u1, &sn, message);
    secp256k1_scalar_mulX(&u2, &sn, sigr);
    secp256k1_gej_set_geX(&pubkeyj, pubkey);
    secp256k1_ecmultX(ctx, &pr, &pubkeyj, &u2, &u1);
    if (secp256k1_gej_is_infinityX(&pr)) {
        return 0;
    }
    secp256k1_scalar_get_b32X(c, sigr);
    secp256k1_fe_set_b32XX(&xr, c);
    if (secp256k1_gej_eq_x_varX(&xr, &pr)) {
        return 1;
    }
	if (secp256k1_fe_cmp_varX(&xr, &secp256k1_ecdsa_const_p_minus_orderX) >= 0) {
		return 0;
    }
    secp256k1_fe_addXX(&xr, &secp256k1_ecdsa_const_order_as_feX);
    if (secp256k1_gej_eq_x_varX(&xr, &pr)) {
        return 1;
    }
    return 0;
}

static void secp256k1_ecdsa_recoverable_signature_loadX(secp256k1_scalarX* r, secp256k1_scalarX* s, int* recid, const secp256k1_ecdsa_recoverable_signatureX* sig) {
    if (sizeof(secp256k1_scalarX) == 32) {
        /* When the secp256k1_scalar type is exactly 32 byte, use its
         * representation inside secp256k1_ecdsa_signature, as conversion is very fast.
         * Note that secp256k1_ecdsa_signature_save must use the same representation. */
        private_memcpy(r, &sig->data[0], 32);
        private_memcpy(s, &sig->data[32], 32);
    } 
	/*else {
        secp256k1_scalar_set_b32X(r, &sig->data[0], (int*)0);
        secp256k1_scalar_set_b32X(s, &sig->data[32], (int*)0);
    }
    */
    *recid = sig->data[64];
}

static void secp256k1_ge_set_table_gej_varX(size_t len, secp256k1_geX *r, const secp256k1_gejX *a, const secp256k1_feX *zr) {
    size_t i = len - 1;
    secp256k1_feX zi;

    if (len > 0) {
        /* Compute the inverse of the last z coordinate, and use it to compute the last affine output. */
        secp256k1_fe_invX(&zi, &a[i].z);
        secp256k1_ge_set_gej_zinvX(&r[i], &a[i], &zi);

        /* Work out way backwards, using the z-ratios to scale the x/y values. */
        while (i > 0) {
            secp256k1_fe_mulX(&zi, &zi, &zr[i]);
            i--;
            secp256k1_ge_set_gej_zinvX(&r[i], &a[i], &zi);
        }
    }
}

int secp256k1_ec_pubkey_serializeX(unsigned char *output, size_t *outputlen, const secp256k1_pubkeyX* pubkey, unsigned int flags) {
    secp256k1_geX Q;

    return (secp256k1_pubkey_loadX(&Q, pubkey) &&
            secp256k1_eckey_pubkey_serializeX(&Q, output, outputlen, flags));
}

int secp256k1_ecdsa_recoverX(__global const secp256k1_ge_storageX *ctx,  const secp256k1_ecdsa_recoverable_signatureX *signature,
								__global const unsigned char *msg32, secp256k1_pubkeyX *pubkey) {
    secp256k1_geX q;
    secp256k1_scalarX r, s;
    secp256k1_scalarX m;
    int recid;

    secp256k1_ecdsa_recoverable_signature_loadX(&r, &s, &recid, signature);
    if(recid < 0 || recid > 3) {
		memsetX(pubkey,0x0, sizeof(pubkey));
		return 0;
    } else {
		secp256k1_scalar_set_b32X(&m, msg32, (int*)0);
		if (secp256k1_ecdsa_sig_recoverX(ctx, &r, &s, &q, &m, recid)) {
			secp256k1_pubkey_saveX(pubkey, &q);
		} else {
			memsetX(pubkey,0x0, sizeof(pubkey));
			return 0;
		}
	}
	return 1;
}

int secp256k1_ecdsa_verifyX(__global const secp256k1_ge_storageX* ctx, const secp256k1_ecdsa_signatureX *sig, 
										__global const unsigned char *msg32, const secp256k1_pubkeyX *pubkey) { 
	secp256k1_geX q;
    secp256k1_scalarX r, s;
    secp256k1_scalarX m;
    secp256k1_scalar_set_b32X(&m, msg32, (int*)0);
	
    secp256k1_ecdsa_signature_loadX(&r, &s, sig);
	int tmp = (secp256k1_pubkey_loadX(&q, pubkey) && secp256k1_ecdsa_sig_verifyX(ctx, &r, &s, &q, &m));
	return tmp;
}

/*
 * Kernel 
 */
typedef struct Msg32 {
    unsigned char data[32];
}Msg32;

typedef struct EthPubkey {
	unsigned char data[65];
}EthPubkey;

__kernel void secp256k1_ocl_ecdsa_recoverX(__global const secp256k1_ge_storageX* ctx, __global const secp256k1_ecdsa_recoverable_signatureX *rsigdata,
										__global const Msg32 *msgdata, __global EthPubkey *pubkey_out)
{
	secp256k1_ecdsa_recoverable_signatureX sig;
	secp256k1_pubkeyX pubkey;
	unsigned char serial_pubkey[65];
	size_t outputlen = 65;
	int recid = 0;

	int idx = get_global_id(0);
	recid = rsigdata[idx].data[64];
	
	secp256k1_ecdsa_recoverable_signature_parse_compactX(&sig, rsigdata[idx].data, recid);
	secp256k1_ecdsa_recoverX(ctx, &sig, msgdata[idx].data, &pubkey);

	secp256k1_ec_pubkey_serializeX(serial_pubkey, &outputlen, &pubkey, 0);
	memcpy_to_global(pubkey_out[idx].data, serial_pubkey, sizeof(serial_pubkey));
}

// secp256k1_ext_ecdsa_verify verifies an encoded compact signature.
//
// Returns: 1: signature is valid
//			0: signature is invalid
// Args:	ctx:		pointer to a context object (cannot be NULL)
//	In: 	sigdata:	pointer to a 64-byte signature (cannot be NULL)
//			msgdata:	pointer to a 32-byte message (cannot be NULL)
//			pubkeydata: pointer to public key data, 65 bytes length (cannot be NULL)
__kernel void secp256k1_ocl_ecdsa_verifyX(__global const secp256k1_ge_storageX* ctx, __global const secp256k1_ecdsa_signatureX *sigdata,
	__global const Msg32 *msgdata, __global const EthPubkey *ethpubkey, __global int *res) 
{
	secp256k1_ecdsa_signatureX sig;
	secp256k1_pubkeyX pubkey;
	int ret = 0;
	unsigned char pub[65];
	size_t pubkeylen = 65;
	
	int idx = get_global_id(0);

	memcpyX(pub,ethpubkey[idx].data, sizeof(pub));
	
	if (!secp256k1_ecdsa_signature_parse_compactX(&sig, sigdata[idx].data)) {
		ret = 0;
	}else if (!secp256k1_ec_pubkey_parseX(&pubkey, pub, pubkeylen)) {
		ret = 0;
	} else {
		ret = secp256k1_ecdsa_verifyX(ctx, &sig, msgdata[idx].data, &pubkey);
	}
	
	res[idx] = ret;
}
