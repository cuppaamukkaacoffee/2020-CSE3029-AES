/*
 * Copyright 2020. Heekuck Oh, all rights reserved
 * 이 프로그램은 한양대학교 ERICA 소프트웨어학부 재학생을 위한 교육용으로 제작되었습니다.
 */
#include <stdlib.h>
#if !defined(__FreeBSD__) || !defined(__NetBSD__) || !defined(__OpenBSD__) || !defined(__bsdi__) || !defined(__DragonFly__)
#include <bsd/stdlib.h>
#endif
#include <string.h>
#include <gmp.h>
#include "rsa_pss.h"

#if defined(SHA224)
void (*sha)(const unsigned char *, unsigned int, unsigned char *) = sha224;
#elif defined(SHA256)
void (*sha)(const unsigned char *, unsigned int, unsigned char *) = sha256;
#elif defined(SHA384)
void (*sha)(const unsigned char *, unsigned int, unsigned char *) = sha384;
#else
void (*sha)(const unsigned char *, unsigned int, unsigned char *) = sha512;
#endif

/*
 * Copyright 2020. Heekuck Oh, all rights reserved
 * rsa_generate_key() - generates RSA keys e, d and n in octet strings.
 * If mode = 0, then e = 65537 is used. Otherwise e will be randomly selected.
 * Carmichael's totient function Lambda(n) is used.
 */
void rsa_generate_key(void *_e, void *_d, void *_n, int mode)
{
    mpz_t p, q, lambda, e, d, n, gcd;
    gmp_randstate_t state;
    
    /*
     * Initialize mpz variables
     */
    mpz_inits(p, q, lambda, e, d, n, gcd, NULL);
    gmp_randinit_default(state);
    gmp_randseed_ui(state, arc4random());
    /*
     * Generate prime p and q such that 2^(RSAKEYSIZE-1) <= p*q < 2^RSAKEYSIZE
     */
    do {
        do {
            mpz_urandomb(p, state, RSAKEYSIZE/2);
        } while (mpz_probab_prime_p(p, 50) == 0);
        do {
            mpz_urandomb(q, state, RSAKEYSIZE/2);
        } while (mpz_probab_prime_p(q, 50) == 0);
        mpz_mul(n, p, q);
    } while (!mpz_tstbit(n, RSAKEYSIZE-1));
    /*
     * Generate e and d using Lambda(n)
     */
    mpz_sub_ui(p, p, 1);
    mpz_sub_ui(q, q, 1);
    mpz_lcm(lambda, p, q);
    if (mode == 0)
        mpz_set_ui(e, 65537);
    else do {
        mpz_urandomb(e, state, RSAKEYSIZE);
        mpz_gcd(gcd, e, lambda);
    } while (mpz_cmp(e, lambda) >= 0 || mpz_cmp_ui(gcd, 1) != 0);
    mpz_invert(d, e, lambda);
    /*
     * Convert mpz_t values into octet strings
     */
    mpz_export(_e, NULL, 1, RSAKEYSIZE/8, 1, 0, e);
    mpz_export(_d, NULL, 1, RSAKEYSIZE/8, 1, 0, d);
    mpz_export(_n, NULL, 1, RSAKEYSIZE/8, 1, 0, n);
    /*
     * Free the space occupied by mpz variables
     */
    mpz_clears(p, q, lambda, e, d, n, gcd, NULL);
}

/*
 * Copyright 2020. Heekuck Oh, all rights reserved
 * rsa_cipher() - compute m^k mod n
 * If m >= n then returns EM_MSG_OUT_OF_RANGE, otherwise returns 0 for success.
 */
int rsa_cipher(void *_m, const void *_k, const void *_n)
{
    mpz_t m, k, n;
    
    /*
     * Initialize mpz variables
     */
    mpz_inits(m, k, n, NULL);
    /*
     * Convert big-endian octets into mpz_t values
     */
    mpz_import(m, RSAKEYSIZE/8, 1, 1, 1, 0, _m);
    mpz_import(k, RSAKEYSIZE/8, 1, 1, 1, 0, _k);
    mpz_import(n, RSAKEYSIZE/8, 1, 1, 1, 0, _n);
    /*
     * Compute m^k mod n
     */
    if (mpz_cmp(m, n) >= 0) {
        mpz_clears(m, k, n, NULL);
        return EM_MSG_OUT_OF_RANGE;
    }
    mpz_powm(m, m, k, n);
    /*
     * Convert mpz_t m into the octet string _m
     */
    mpz_export(_m, NULL, 1, RSAKEYSIZE/8, 1, 0, m);
    /*
     * Free the space occupied by mpz variables
     */
    mpz_clears(m, k, n, NULL);
    return 0;
}

/*
 * Copyright 2020. Heekuck Oh, all rights reserved
 * mgf() - A mask generating function for signature verification.
 */
static unsigned char *mgf(const unsigned char *mgfSeed, size_t seedLen, unsigned char *mask, size_t maskLen)
{
    uint32_t i, count, c;
    size_t hLen;
    unsigned char *mgfIn, *m;

    hLen = SHASIZE / 8;
    if (maskLen > 0x0100000000 * hLen)
        return NULL;
    
    if ((mgfIn = (unsigned char *)malloc(seedLen + 4)) == NULL)
        return NULL;

    memcpy(mgfIn, mgfSeed, seedLen);
    count = maskLen / hLen + (maskLen % hLen ? 1 : 0);

    if ((m = (unsigned char *)malloc(count * hLen)) == NULL)
        return NULL;
    
    for (i = 0; i < count; i++){
        c = i;
        mgfIn[seedLen + 3] = c & 0x000000ff; c >>= 8;
        mgfIn[seedLen + 2] = c & 0x000000ff; c >>= 8;
        mgfIn[seedLen + 1] = c & 0x000000ff; c >>= 8;
        mgfIn[seedLen] = c & 0x000000ff; c >>= 8;
        (*sha)(mgfIn, seedLen + 4, m + i * hLen);
    }

    memcpy(mask, m, maskLen);
    free(mgfIn); free(m);
    return mask;
}

/*
 * rsassa_pss_sign - RSA Signature Scheme with Appendix
 * 작성자 주석: 해당 함수는 메세지 m에 대한 RSASSA-PSS 서명을 생성한다.
 *              편의를 위해 M'의 크기 (MPRSIZE = 64 + 2 * SHASIZE 비트) 와
 *              DB, maskedDB의 크기 (DBSIZE = RSAKEYSIZE - SHASIZE - 8 비트) 매크로를
 *              rsa_pss.h 에 따로 선언하였다.
 */
int rsassa_pss_sign(const void *m, size_t mLen, const void *d, const void *n, void *s)
{   
    size_t hSize;
    void *salt, *maskedDB;
    mpz_t rop, _mask, _dB, _maskedDB;
    gmp_randstate_t state;
    unsigned char mPrime[MPRSIZE / 8];
    unsigned char mPrimeHash[SHASIZE / 8];
    unsigned char mask[DBSIZE / 8];
    unsigned char dB[DBSIZE / 8];
    unsigned char mHash[SHASIZE/8];
    unsigned char em[RSAKEYSIZE / 8];

    /*
        입력된 메시지가 SHA2 함수의 지정 입력한도 바이트를 초과할 경우 EM_MSG_TOO_LONG을 리턴한다.
        mLen 데이터 타입 특성상(= 64비트) SHA224와 SHA256인 경우(한도 2^61 바이트)에만 한도를 초과한 mLen이
        입력될 수 있다.
    */
    if (SHASIZE < 384 && mLen > 0x1fffffffffffffff) return EM_MSG_TOO_LONG;

    // 입력된 m에 대한 해시 mHash를 생성한다.
    (*sha)((unsigned char *)m, (unsigned int)mLen, mHash);

    /*
        salt 값으로 사용할 무작위 정수를 생성한다. 시드는 arc4random() 합수를 통해 생성하며,
        rrandomb을 사용해 SHASIZE 길이( 2^(SHASIZE - 1) =< rop < 2^SHASIZE )를
        가진 무작위수 rop를 생성하고 해당 데이터를 바이트 단위로 void* salt 에 저장한다.
    */
    mpz_init(rop);
    gmp_randinit_default(state);
    gmp_randseed_ui(state, arc4random());
    mpz_rrandomb(rop, state, SHASIZE);
    salt = mpz_export(NULL, NULL, 1, SHASIZE / 8, 1, 0, rop);
    mpz_clear(rop);

    // unsigned char 배열 mPrime에 8바이트의 0x0와 mHash, salt를 차례대로 붙여 M'을 생성한다.
    memset(mPrime, 0x0, 8);
    memcpy(mPrime + 8, mHash, SHASIZE / 8);
    memcpy(mPrime + 8 + SHASIZE / 8, (unsigned char *)salt, SHASIZE / 8);

    /*
        M'에 대한 해시 mPrimeHash를 생성한다. 생성된 mPrimeHash는 em생성에 사용되기에
        해당 데이터의 길이가 em에 들어가기에 너무 클 경우 EM_HASH_TOO_LING을 리턴한다.        
    */
    (*sha)(mPrime, (unsigned int)(MPRSIZE / 8), mPrimeHash);
    if ((hSize = sizeof(mPrimeHash) / sizeof(mPrimeHash[0])) > RSAKEYSIZE / 2)
        return EM_HASH_TOO_LONG;

    // mgf 함수를 통해 mPrimeHash에 대한 해시 mask를 생성한다.
    mgf(mPrimeHash, (size_t)(SHASIZE / 8), mask, (size_t)(DBSIZE / 8));

    /*
        maskedDB를 생성에 사용될 dB를 생성한다. dB의 길이는 mPrimeHash와 0xbc 바이트를
        합쳤을 때 RSAKEYSIZE 만큼의 길이가 나오도록 정한다. dB 내부에 salt와 0x01 바이트가
        들어올 위치까지 0x0으로 채우고 이후 0x01과 salt를 차례대로 붙여 dB를 완성한다.
    */
    memset(dB, 0, (DBSIZE / 8) - (SHASIZE / 8) - 1);
    dB[(DBSIZE / 8) - (SHASIZE / 8) - 1] = 0x01;
    memcpy(dB + (DBSIZE / 8) - (SHASIZE / 8), (unsigned char*)salt, SHASIZE / 8);

    /*
        mask와 dB를 xor 하여 maskedDB를 생성한다. 이 때 비트 너비가 큰 두 배열을
        각각 mpz_t _mask, _dB 에 옮겨 xor을 한다. 결과는 mpz_t _maskedDB를 통해
        void *maskedDB에 저장된다.
    */
    mpz_inits(_mask, _dB, _maskedDB, NULL);
    mpz_import(_mask, DBSIZE / 8, 1, 1, 1, 0, (void *)mask);
    mpz_import(_dB, DBSIZE / 8, 1, 1, 1, 0, (void *)dB);
    mpz_xor(_maskedDB, _mask, _dB);
    maskedDB = mpz_export(NULL, NULL, 1, DBSIZE / 8, 1, 0, _maskedDB);
    mpz_clears(_mask, _dB, _maskedDB, NULL);

    /*
        maskedDB, mPrimeHash, 0xbc를 합쳐 unsigned char *em을 생성한다.
        이 때 em의 첫 비트가 1일 경우 RSAKEYSIZE를 초과하지 않도록 해당 비트를
        0으로 수정한다. 
    */
    memcpy(em, maskedDB, DBSIZE / 8);
    memcpy(em + DBSIZE / 8, mPrimeHash, SHASIZE / 8);
    em[RSAKEYSIZE / 8 - 1] = 0xbc;
    if (em[0] >> 7) em[0] &= 0x7f;

    /*
        생성된 em을 rsa_cipher를 통해 암호화하여 서명 s를 생성한다. 이 때
        em의 크기가 n 보다 커서 rsa_cipher가 EM_MSG_OUT_OF_RANGE를 리턴할 경우
        그대로 전달한다.
    */
    if (rsa_cipher((void *)em, d, n) == EM_MSG_OUT_OF_RANGE)
        return EM_MSG_OUT_OF_RANGE;
    memcpy(s, em, RSAKEYSIZE / 8);

    return 0;
}

/*
 * rsassa_pss_verify - RSA Signature Scheme with Appendix
 * 작성자 주석: 해당 함수는 메세지 m에 대한 RSA-PSS 서명 s를 입력받아 해당 서명의 무결성을 인증한다.
 *              편의를 위해 M'의 크기 (MPRSIZE = 64 + 2 * SHASIZE 비트) 와
 *              DB, maskedDB의 크기 (DBSIZE = RSAKEYSIZE - SHASIZE - 8 비트) 매크로를
 *              rsa_pss.h 에 따로 선언하였다.
 */
int rsassa_pss_verify(const void *m, size_t mLen, const void *e, const void *n, const void *s)
{
    void *dB;
    mpz_t _mask, _dB, _maskedDB;
    unsigned char em[RSAKEYSIZE];
    unsigned char mHash[SHASIZE / 8];
    unsigned char maskedDB[DBSIZE / 8];
    unsigned char mPrimeHash[SHASIZE / 8];
    unsigned char mask[DBSIZE / 8];
    unsigned char salt[SHASIZE / 8];
    unsigned char pad[(DBSIZE / 8) - (SHASIZE / 8)];
    unsigned char mPrime[MPRSIZE / 8];
    unsigned char hashPrime[SHASIZE / 8];

    /*
        입력된 메시지가 SHA2 함수의 지정 입력한도 바이트를 초과할 경우 EM_MSG_TOO_LONG을 리턴한다.
        mLen 데이터 타입 특성상(= 64비트) SHA224와 SHA256인 경우(한도 2^61 바이트)에만 한도를 초과한 mLen이
        입력될 수 있다. 
    */
    if (SHASIZE < 384 && mLen > 0x1fffffffffffffff) return EM_MSG_TOO_LONG;

    /*
        입력 받은 s를 unsigned char *em에 저장하고 복호화한다. 이 때
        em의 크기가 n 보다 커서 rsa_cipher가 EM_MSG_OUT_OF_RANGE를 리턴할 경우
        그대로 전달한다.
    */
    memcpy(em, s, RSAKEYSIZE);
    if (rsa_cipher((void *)em, e, n) == EM_MSG_OUT_OF_RANGE)
        return EM_MSG_OUT_OF_RANGE;

    /*
        복호화 된 em의 마지막 바이트가 0xbc가 아니거나 em의 첫 번째 비트가 0이 아닐경우
        각 경우에 맞는 에러를 리턴한다.
    */
    if (em[RSAKEYSIZE / 8 - 1] != 0xbc) return EM_INVALID_LAST;
    if ((em[0] >> 7) != 0) return EM_INVALID_INIT;
    
    // em에서 maskedDB를 추출한다.
    memcpy(maskedDB, em, DBSIZE / 8);
    
    // em에서 mPrimeHash를 추출한다.
    memcpy(mPrimeHash, em + DBSIZE / 8, SHASIZE / 8);
    
    // mgf 함수를 통해 mPrimeHash에 대한 해시 mask를 생성한다.
    mgf(mPrimeHash, (size_t)(SHASIZE / 8), mask, (size_t)(DBSIZE / 8));
    
    /*
        maskedDB와 mask를 xor 하여 dB를 생성한다. 이 때 비트 너비가 큰 두 배열을
        각각 mpz_t _maskedDB, _mask 에 옮겨 xor을 한다. 결과는 mpz_t _dB를 통해
        void *dB에 저장된다.
    */
    mpz_inits(_mask, _dB, _maskedDB, NULL);
    mpz_import(_maskedDB, DBSIZE / 8, 1, 1, 1, 0, (void *)maskedDB);
    mpz_import(_mask, DBSIZE / 8, 1, 1, 1, 0, (void *)mask);
    mpz_xor(_dB, _maskedDB, _mask);
    dB = mpz_export(NULL, NULL, 1, DBSIZE / 8, 1, 0, _dB);
    mpz_clears(_mask, _dB, _maskedDB, NULL);
    
    /*
        dB에서 pad를 추출한다. 추출한 pad의 마지막 바이트가 0x01인지 확인하고,
        나머지 바이트가 0x00인지 확인한다. 첫 바이트의 경우 서명 과정에서
        0x80으로 변하는 경우가 있으므로 0x00 혹은 0x80인지 확인한다.
    */
    memcpy(pad, dB, (DBSIZE / 8) - (SHASIZE / 8));
    if (pad[0] != 0x80 && pad[0] != 0x0) return EM_INVALID_PD2;
    for (int i = 1; i < (DBSIZE / 8) - (SHASIZE / 8) - 1; ++i)
        if (pad[i]) return EM_INVALID_PD2;
    if (pad[(DBSIZE / 8) - (SHASIZE / 8) - 1] != 0x01) return EM_INVALID_PD2;
    
    // dB에서 salt를 추출한다.
    memcpy(salt, dB + (DBSIZE / 8) - (SHASIZE / 8), SHASIZE / 8);

    // 입력된 m에 대한 해시 mHash를 생성한다.
    (*sha)((unsigned char *)m, (unsigned int)mLen, mHash);
    
    // unsigned char 배열 mPrime에 8바이트의 0x0와 mHash, salt를 차례대로 붙여 M'을 생성한다.
    memset(mPrime, 0x0, 8);
    memcpy(mPrime + 8, mHash, SHASIZE / 8);
    memcpy(mPrime + 8 + SHASIZE / 8, (unsigned char *)salt, SHASIZE / 8);

    // M'에 대한 해시 hashPrime을 생성한다.
    (*sha)((unsigned char *)mPrime, (unsigned int)(MPRSIZE / 8), hashPrime);
    
    // 전달된 mPrimeHash와 생성된 hashPrime의 내용이 다를 경우 EM_HASH_MISMATCH를 리턴한다.
    if (memcmp(hashPrime, mPrimeHash, SHASIZE / 8) != 0) return EM_HASH_MISMATCH;

    return 0;
}