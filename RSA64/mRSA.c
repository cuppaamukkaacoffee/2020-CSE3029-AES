/*
 * Copyright 2020. Heekuck Oh, all rights reserved
 * 이 프로그램은 한양대학교 ERICA 소프트웨어학부 재학생을 위한 교육용으로 제작되었습니다.
 */
#include <stdlib.h>
#if !defined(__FreeBSD__) || !defined(__NetBSD__) || !defined(__OpenBSD__) || !defined(__bsdi__) || !defined(__DragonFly__)
#include <bsd/stdlib.h>
#endif
#include "mRSA.h"

/*
 * mod_add() - computes a+b mod m
 * 만일 a+b에서 오버플로가 발생하면 값이 틀리게 된다.
 * 이런 경우에는 m을 빼서 오버플로가 생기지 않게 한다. 즉, a+(b-m)을 계산하면 된다.
 * 오버플로는 a+b >= b가 성립하지 않을 때 발생한다.
 * 제작자 주석: 위의 설명대로 오버플로가 생기기 않게 a + b 대신 a + (b - m)을 계산한다.
 *              해당 작업은 a - (m - b)와 동치이다. 만약  a < m - b 일 경우 해당 결과에
 *              m을 더해준다(a - b + m). 해당 작업은 m - b + a와 동치이다. 따라서
 *              순차적으로 계산할 시에 결과값이 음수가 나오는 것을 방지한다.
 *              위의 관계는 a, b < m 일 경우에만 성립하므로 함수 초입에
 *              각각의 a, b에 modular 연산을 해준다. 
 */
static uint64_t mod_add(uint64_t a, uint64_t b, uint64_t m)
{   
    a %= m;
    b %= m;
    b = m - b;
    if (b > a)
        return m - b + a;
    return a - b;
}

/*
 * mod_mul() - computes a * b mod m
 * 모듈러 값이 2^64(≡ 0)인 경우 64비트 데이터 단월르 감안하여
 * 모듈러 연산을 진행하지 않는다.
 */
static uint64_t mod_mul(uint64_t a, uint64_t b, uint64_t m)
{   
    uint64_t r = 0x0;
    while (b > 0) {
        if (b & 1)
            r = (m == 0 ? r + a : mod_add(r, a, m));
        b = b >> 1;
        a = (m == 0 ? a + a : mod_add(a, a, m));
    }
    return r;
}

/*
 * mod_pow() - computes a^b mod m
 * 모듈러 값이 2^64(≡ 0)인 경우 64비트 데이터 단위임을 감안하여
 * 모듈러 연산을 진행하지 않는다.
 */
static uint64_t mod_pow(uint64_t a, uint64_t b, uint64_t m)
{
    uint64_t r = 0x1;
    while (b > 0) {
        if (b & 1)
            r = (m == 0 ? r * a : mod_mul(r, a, m));
        b = b >> 1;
        a = (m == 0 ? a * a : mod_mul(a, a, m));
    }
    return r;
}

/*
 * gcd() - Euclidean algorithm
 *
 * 유클리드 알고리즘 gcd(a,b) = gcd(b,a mod b)를 사용하여 최대공약수를 계산한다.
 * 만일 a가 0이면 b가 최대공약수가 된다. 그 반대도 마찬가지이다.
 * a, b가 모두 음이 아닌 정수라고 가정한다.
 * 재귀함수 호출을 사용하지 말고 while 루프를 사용하여 구현하는 것이 빠르고 좋다.
 */
static uint64_t gcd(uint64_t a, uint64_t b)
{   
    uint64_t t;
    while(a && b) {
        t = a;
        a = b;
        b = t % b;
    }
    return a + b;
}

/*
 * xgcd() - Extended Euclidean algorithm
 *
 * 확장유클리드 알고리즘은 두 수의 최대공약수와 gcd(a,b) = ax + by 식을 만족하는
 * x와 y를 계산하는 알고리즘이다. 강의노트를 참조하여 구현한다.
 * a, b가 모두 음이 아닌 정수라고 가정한다.
 */
static int64_t xgcd(uint64_t a, uint64_t b, uint64_t *x, uint64_t *y)
{
    uint64_t d0 = a, d1 = b, x1 = 0, y1 = 1, q, t;
    *x = 1, *y = 0;
    int flag;
    while(d1){
        q = d0/d1;
        t = d1;
        d1 = d0 - q * d1;
        d0 = t;

        t = x1;
        if (*x < q * x1) flag = 1;
        else flag = 0;
        x1 = *x - q * x1;
        
        *x = t;
        t = y1;
        y1 = *y - q * y1;
        *y = t;
    }
    return d0;
}

/*
 * mul_inv() - computes multiplicative inverse a^-1 mod m
 * 모듈러 값이 2^64(≡ 0)인 uint64_t를 처리하므로
 * xgcd() 함수의 결과값 x에 underflow가 일어날 경우 x + m을 리턴한다.
 */
static uint64_t mul_inv(uint64_t a, uint64_t m)
{
    uint64_t x, y, d;
    d = xgcd(a, m, &x, &y);
    if (d == 1) {
        if (x >> 63)
            return x + m;
        return x % m;
    }
    return 0;
}

/*
    결정적 밀러라빈 함수에 사용할 확률론적 밀러라빈 함수 구현체이다. 이미 a와 k, q가 결정되었다고 가정한다.
    a^q == 1 mod n 일 경우 1(probable/inconclusive)을 반환하며,
    k > i >= 0 인 i와 관련하여 (a^q)^(2*i) = n - 1 mod n 에 해당하는 i가 존재할 경우
    역시 1(probable/inconclusive)을 반환한다. 위의 두가지 경우에 해당하지 않을 경우 0(composite)을 반환한다.
*/
static int prob_miller_rabin(uint64_t n, uint64_t a, uint64_t k, uint64_t q)
{
    int i;
    if (mod_pow(a, q, n) == 1)
        return 1;
    for (i = 0; k > i ; i++) {
        if (mod_pow(mod_pow(a, q, n), mod_pow(2, i, n), n) == (n - 1))
            return 1;
    }
    return 0;
}

/*
 * miller_rabin() - Miller-Rabin Primality Test (deterministic version)
 * 결정적 밀러라빈 알고리즘을 사용하여 n이 소수이면 PRIME을, 합성수이면 COMPOSITE를 넘겨준다.
 * 결정적 밀러라빈 알고리즘은 n < 2^64일 때, 검증할 베이스 a의 값을 무작위로 선택하지 않고
 * 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37만 검증해도 알 수 있다는 것에 기반한다.
 * 작성자 주석: 위에 제시된 소수들을 a로 입력받는 12번의 확률론적 밀러라빈 함수를 호출해 모든 경우에
 *              1이 반환될 경우 PRIME을 반환하며, 아닐 경우 COMPOSITE를 반환한다.
 *              이미 처음 12개의 소수가 a의 값으로 제공되므로 37 >= n 인 경우에 한해서,
 *              n이 제공된 a들중 하나일 경우 PRIME을 반환한다. 나아가 n이 짝수일 경우에 추가 계산 없이
 *              COMPOSITE를 반환한다.
 *              함수 초입에 d = n - 1에 대하여 반복적으로 mod 2 작업을 하여 k값을 확보하며, 
 *              n - 1 / 2^k 작업을 통애 q 값을 구한다. 우선적으로 짝수를 제외하였기 때문에 k는
 *              모든 경우에 0보다 크며 q는 홀수라고 가정해도 무방하다.
 *              k와 q가 확보되면 앞서 제시한 대로 12번의 확률론적 밀러라빈 함수를 호출해
 *              소수 여부를 결정한다.
 */
static int miller_rabin(uint64_t n)
{   
    uint64_t q, k = 0;
    uint64_t d = n - 1;
    if (n == 2 || n == 3 || n == 5 || n == 7 || n == 11 || n == 13 ||
        n == 17 || n == 19 || n == 23 || n == 29 || n == 31 || n == 37)
        return PRIME;
    if (n % 2 == 0)
        return COMPOSITE;
    while (d % 2 == 0) {
        k++;
        d = d >> 1;
    }
    q = (n - 1) / mod_pow(2, k, n);

    if ((prob_miller_rabin(n, 2, k, q)) && (prob_miller_rabin(n, 3, k, q)) &&
        (prob_miller_rabin(n, 5, k, q)) && (prob_miller_rabin(n, 7, k, q)) &&
        (prob_miller_rabin(n, 11, k, q)) && (prob_miller_rabin(n, 13, k, q)) &&
        (prob_miller_rabin(n, 17, k, q)) && (prob_miller_rabin(n, 19, k, q)) &&
        (prob_miller_rabin(n, 23, k, q)) && (prob_miller_rabin(n, 29, k, q)) &&
        (prob_miller_rabin(n, 31, k, q)) && (prob_miller_rabin(n, 37, k, q)))
        return PRIME;
    return COMPOSITE;
}

/*
 * mRSA_generate_key() - generates mini RSA keys e, d and n
 * Carmichael's totient function Lambda(n) is used.
 * 작성자 주석: 해당 함수는 RSA 키페어 {e, n}: 공개키, {d, n}: 비밀키 를 생성한다.
 *              libbsd의 arc4random()을 사용해 64비트 정수 p와 q를 생성하고
 *              n = p * q를 생성한다. 생성된 p, q가 소수이며, n의 길이가 64비트일때까지 루프를 돌며
 *              p, q, n을 생성한다. p, q, n이 생성되면 
 *               i = gcd(p - 1, q - 1),
 *              carmike = lambda(n) = lcm(p - 1, q - 1) = (p - 1)(q - 1) / gcd(p - 1, q - 1)를 생성한다.
 *              n과 carmike(= lambda(n))를 생성한 후 e와 d를 생성한다.
 *              e는 arc4random을 통해 무작위 32비트 unsigned 정수로 초기화 되며,
 *              e가 소수이며, carmike에 대한 multiplicative inverse d가 존재할 시에만
 *              생성된 e, d를 받아들이고 최종적인 키 생성 과정을 마친다.
 */
void mRSA_generate_key(uint64_t *e, uint64_t *d, uint64_t *n)
{
    uint64_t p, q, carmike, i;
    do {
        p = arc4random();
        q = arc4random();
        *n = p * q;
    }
    while (miller_rabin(p) == 0 || miller_rabin(q) == 0
            || *n < 0x8000000000000000);

    i = gcd(p - 1, q - 1);
    carmike = mod_mul(p - 1, q - 1, 0) / i;

    do {
        arc4random_buf(e, sizeof(uint64_t));
        *e %= carmike;
    }
    while(gcd(*e, carmike) != 1 || (*d = mul_inv(*e, carmike)) == 0);
}

/*
 * mRSA_cipher() - compute m^k mod n
 * If data >= n then returns 1 (error), otherwise 0 (success).
 */
int mRSA_cipher(uint64_t *m, uint64_t k, uint64_t n)
{
    if (*m > n) return 1;
    *m = mod_pow(*m, k, n);
    return 0;
}
