/*
 * Copyright 2020. Heekuck Oh, all rights reserved
 * 이 프로그램은 한양대학교 ERICA 소프트웨어학부 재학생을 위한 교육용으로 제작되었습니다.
 */
#include <stdio.h>
#if !defined(__FreeBSD__) || !defined(__NetBSD__) || !defined(__OpenBSD__) || !defined(__bsdi__) || !defined(__DragonFly__)
#include <bsd/stdlib.h>
#endif
#include <stdlib.h>
#include <gmp.h>
#include "rsa_pss.h"

int main(void)
{
    char e[RSAKEYSIZE/8], d[RSAKEYSIZE/8], n[RSAKEYSIZE/8];
    char s[RSAKEYSIZE/8];
    long x;
    int i, val, count = 0;

    /*
     * RSA keys
     */
    rsa_generate_key(e, d, n, 1);
    printf("e = ");
    for (i = 0; i < RSAKEYSIZE/8; ++i)
        printf("%02hhx", e[i]);
    printf("\nd = ");
    for (i = 0; i < RSAKEYSIZE/8; ++i)
        printf("%02hhx", d[i]);
    printf("\nn = ");
    for (i = 0; i < RSAKEYSIZE/8; ++i)
        printf("%02hhx", n[i]);
    printf("\n---\n");
    // unsigned char message[6] = "sample";
    // uint64_t *message;
    // *message = 0x1000000001;
    // rsa_cipher((void *)message, e, n);
    // printf("\nmessage = ");
    // for (i = 0; i < RSAKEYSIZE/8; ++i)
    //     printf("%02hhx", n[i]);
    // printf("\n---\n");
    // rsa_cipher((void *)message, d, n);
    // printf("\nmessage = ");
    // for (i = 0; i < RSAKEYSIZE/8; ++i)
    //     printf("%02hhx", n[i]);
    // printf("\n---\n");
    /*
     * Valid signature test
     */
    if ((val = rsassa_pss_sign("sample", 6, d, n, s)) != 0) {
        printf("Signature Error: %d -- FAILED\n", val);
        return 1;
    }
    printf("s = ");
    for (i = 0; i < RSAKEYSIZE/8; ++i)
        printf("%02hhx", s[i]);
    printf("\n");
    if ((val = rsassa_pss_verify("sample", 6, e, n, s)) != 0) {
        printf("Verification Error: %d -- FAILED\n", val);
        return 1;
    }
    printf("Valid Signature! -- PASSED\n---\n");
    /*
     * Invalid signature test
     */
    if ((val = rsassa_pss_sign("invalid sample", 14, d, n, s)) != 0) {
        printf("Signature Error: %d -- FAILED\n", val);
        return 1;
    }
    printf("s = ");
    for (i = 0; i < RSAKEYSIZE/8; ++i)
        printf("%02hhx", s[i]);
    printf("\n");
    if ((val = rsassa_pss_verify("invalid_sample", 14, e, n, s)) != 0)
        printf("Verification Error: %d, invalid signature -- PASSED\n---\n", val);
    else {
        printf("Verification Error -- FAILED\n");
        return 1;
    }
    /*
     * Wrong key test
     */
    if ((val = rsassa_pss_sign("sample", 6, e, n, s)) != 0) {
        printf("Signature Error: %d -- FAILED\n", val);
        return 1;
    }
    printf("s = ");
    for (i = 0; i < RSAKEYSIZE/8; ++i)
        printf("%02hhx", s[i]);
    printf("\n");
    if ((val = rsassa_pss_verify("sample", 6, e, n, s)) != 0)
        printf("Verification Error: %d -- PASSED\n", val);
    else {
        printf("Logic Error! -- FAILED\n---\n");
        return 1;
    }
    /*
     * Signature data error
     */
    if ((val = rsassa_pss_sign("It always seems impossible until it is done.", 44, d, n, s)) != 0) {
        printf("Signature Error: %d -- FAILED\n", val);
        return 1;
    }
    s[0] = s[1] = 0;
    printf("s = ");
    for (i = 0; i < RSAKEYSIZE/8; ++i)
        printf("%02hhx", s[i]);
    printf("\n");
    if ((val = rsassa_pss_verify("It always seems impossible until it is done.", 44, e, n, s)) != 0)
        printf("Verification Error: %d -- PASSED\n", val);
    else {
        printf("Logic Error! -- FAILED\n---\n");
        return 1;
    }
    /*
     * Random test
     */
    printf("Random Testing"); fflush(stdout);
    rsa_generate_key(e, d, n, 0);
    do {
        arc4random_buf(&x, sizeof(long));
        if ((val = rsassa_pss_sign(&x, sizeof(long), d, n, s)) != 0) {
            printf("Signature Error: %d -- terminated\n", val);
            return 1;
        }
        if ((val = rsassa_pss_verify(&x, sizeof(long), e, n, s)) != 0) {
            printf("Verification Error: %d -- terminated\n", val);
            return 1;
        }
        if (++count % 0xff == 0) {
            printf(".");
            fflush(stdout);
        }
    } while (count < 0xfff);
    printf("No error found! -- PASSED\n");
    return 0;
}
