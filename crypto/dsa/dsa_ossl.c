/*
 * Copyright 1995-2016 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the OpenSSL license (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

#include <stdio.h>
#include "internal/cryptlib.h"
#include <openssl/bn.h>
#include <openssl/sha.h>
#include "dsa_locl.h"
#include <openssl/asn1.h>

static DSA_SIG *dsa_do_sign(const unsigned char *dgst, int dlen, DSA *dsa);
static int dsa_sign_setup_no_digest(DSA *dsa, BN_CTX *ctx_in, BIGNUM **kinvp,
                                    BIGNUM **rp);
static int dsa_sign_setup(DSA *dsa, BN_CTX *ctx_in, BIGNUM **kinvp,
                          BIGNUM **rp, const unsigned char *dgst, int dlen);
static int dsa_do_verify(const unsigned char *dgst, int dgst_len,
                         DSA_SIG *sig, DSA *dsa);
static int dsa_init(DSA *dsa);
static int dsa_finish(DSA *dsa);

static DSA_METHOD openssl_dsa_meth = {
    "OpenSSL DSA method",
    dsa_do_sign,
    dsa_sign_setup_no_digest,
    dsa_do_verify,
    NULL,                       /* dsa_mod_exp, */
    NULL,                       /* dsa_bn_mod_exp, */
    dsa_init,
    dsa_finish,
    DSA_FLAG_FIPS_METHOD,
    NULL,
    NULL,
    NULL
};

static const DSA_METHOD *default_DSA_method = &openssl_dsa_meth;

void DSA_set_default_method(const DSA_METHOD *meth)
{
    default_DSA_method = meth;
}

const DSA_METHOD *DSA_get_default_method(void)
{
    return default_DSA_method;
}

const DSA_METHOD *DSA_OpenSSL(void)
{
    return &openssl_dsa_meth;
}

static DSA_SIG *dsa_do_sign(const unsigned char *dgst, int dlen, DSA *dsa)
{
    BIGNUM *kinv = NULL;
    BIGNUM *k = NULL;
    BIGNUM *r = NULL;
    BIGNUM *m;
    BIGNUM *xr;
    BIGNUM *xe;
    BN_CTX *ctx = NULL;
    int reason = ERR_R_BN_LIB;
    DSA_SIG *ret = NULL;
    int rv = 0;

    m = BN_new();
    xr = BN_new();
    xe = BN_new();
    if (m == NULL || xr == NULL || xe == NULL)
        goto err;

    if (!dsa->p || !dsa->q || !dsa->g) {
        reason = DSA_R_MISSING_PARAMETERS;
        goto err;
    }

    ret = DSA_SIG_new();
    if (ret == NULL)
        goto err;
    r = BN_new();
    ret->r = BN_new();
    ret->s = BN_new();
    if (r == NULL || ret->r == NULL || ret->s == NULL)
        goto err;

    ctx = BN_CTX_new();
    if (ctx == NULL)
        goto err;
 redo:
    if (dsa->type == kDSA)
    {
        if (!dsa_sign_setup(dsa, ctx, &kinv, &ret->r, dgst, dlen))
            goto err;

        if (dlen > BN_num_bytes(dsa->q))
            /*
             * if the digest length is greater than the size of q use the
             * BN_num_bits(dsa->q) leftmost bits of the digest, see fips 186-3,
             * 4.2
             */
            dlen = BN_num_bytes(dsa->q);

        if (BN_bin2bn(dgst, dlen, m) == NULL)
            goto err;

        /* Compute  s = inv(k) (m + xr) mod q */
        if (!BN_mod_mul(xr, dsa->priv_key, ret->r, dsa->q, ctx))
            goto err;               /* s = xr */
        if (!BN_add(ret->s, xr, m))
            goto err;               /* s = m + xr */
        if (BN_cmp(ret->s, dsa->q) > 0)
            if (!BN_sub(ret->s, ret->s, dsa->q))
                goto err;
        if (!BN_mod_mul(ret->s, ret->s, kinv, dsa->q, ctx))
            goto err;

        /*
         * Redo if r or s is zero as required by FIPS 186-3: this is very
         * unlikely.
         */
        if (BN_is_zero(ret->r) || BN_is_zero(ret->s))
            goto redo;
    }
    else if (dsa->type == kSCHNORR)
    {
        SCHNORR_SIG* sig = (SCHNORR_SIG*)ret;
        if (!dsa_sign_setup(dsa, ctx, &k, &r, dgst, dlen))
            goto err;

        //if (dlen > BN_num_bytes(dsa->q))
            /*
             * if the digest length is greater than the size of q use the
             * BN_num_bits(dsa->q) leftmost bits of the digest, see fips 186-3,
             * 4.2
             */
        //    dlen = BN_num_bytes(dsa->q);

        unsigned char hash[SHA256_DIGEST_LENGTH];
        unsigned char rmsg[1024];
        int rlen = 0;

        /* Compute e = h(m || r) */
        rlen = BN_bn2bin(r, rmsg);
        if (rlen == 0)
            goto err;

        SHA256_CTX sha256;
        SHA256_Init(&sha256);
        SHA256_Update(&sha256, dgst, dlen);
        SHA256_Update(&sha256, rmsg, rlen);
        SHA256_Final(hash, &sha256);
        BN_bin2bn(hash, 64, sig->e);

        /* Compute  s = ((xe) + k) mod q */
        if (!BN_mod_mul(xe, dsa->priv_key, sig->e, dsa->q, ctx)) /* s = xe */
            goto err;
        if (!BN_add(sig->s, xe, k)) /* s = xe + k */
            goto err;
        while (BN_cmp(sig->s, dsa->q) > 0) /* s = s mod q */
            if (!BN_sub(sig->s, sig->s, dsa->q))
                goto err;
        /*
         * Redo if r or s is zero as required by FIPS 186-3: this is very
         * unlikely.
         */
        /* (s, e) */
        if (BN_is_zero(sig->s) || BN_is_zero(sig->e))
            goto redo;
    }

    rv = 1;

 err:
    if (rv == 0) {
        DSAerr(DSA_F_DSA_DO_SIGN, reason);
        DSA_SIG_free(ret);
        ret = NULL;
    }
    BN_CTX_free(ctx);
    BN_clear_free(m);
    BN_clear_free(r);
    BN_clear_free(xr);
    BN_clear_free(xe);
    BN_clear_free(kinv);
    BN_clear_free(k);
    return ret;
}

static int dsa_sign_setup_no_digest(DSA *dsa, BN_CTX *ctx_in,
                                    BIGNUM **kinvp, BIGNUM **rp)
{
    return dsa_sign_setup(dsa, ctx_in, kinvp, rp, NULL, 0);
}

static int dsa_sign_setup(DSA *dsa, BN_CTX *ctx_in,
                          BIGNUM **kinvp, BIGNUM **rp,
                          const unsigned char *dgst, int dlen)
{
    BN_CTX *ctx = NULL;
    BIGNUM *k, *kinv = NULL, *r = *rp;
    BIGNUM *l, *m;
    int ret = 0;
    int q_bits;

    if (!dsa->p || !dsa->q || !dsa->g) {
        DSAerr(DSA_F_DSA_SIGN_SETUP, DSA_R_MISSING_PARAMETERS);
        return 0;
    }

    k = BN_new();
    l = BN_new();
    m = BN_new();
    if (k == NULL || l == NULL || m == NULL)
        goto err;

    if (ctx_in == NULL) {
        if ((ctx = BN_CTX_new()) == NULL)
            goto err;
    } else
        ctx = ctx_in;

    /* Preallocate space */
    q_bits = BN_num_bits(dsa->q);
    if (!BN_set_bit(k, q_bits)
        || !BN_set_bit(l, q_bits)
        || !BN_set_bit(m, q_bits))
        goto err;

    /* Get random k */
    do {
        if (dgst != NULL) {
            /*
             * We calculate k from SHA512(private_key + H(message) + random).
             * This protects the private key from a weak PRNG.
             */
            if (!BN_generate_dsa_nonce(k, dsa->q, dsa->priv_key, dgst,
                                       dlen, ctx))
                goto err;
        } else if (!BN_priv_rand_range(k, dsa->q))
            goto err;
    } while (BN_is_zero(k));

    BN_set_flags(k, BN_FLG_CONSTTIME);

    if (dsa->flags & DSA_FLAG_CACHE_MONT_P) {
        if (!BN_MONT_CTX_set_locked(&dsa->method_mont_p,
                                    dsa->lock, dsa->p, ctx))
            goto err;
    }

    /* Compute r = (g^k mod p) mod q */

    /*
     * We do not want timing information to leak the length of k, so we
     * compute G^k using an equivalent scalar of fixed bit-length.
     *
     * We unconditionally perform both of these additions to prevent a
     * small timing information leakage.  We then choose the sum that is
     * one bit longer than the modulus.
     *
     * TODO: revisit the BN_copy aiming for a memory access agnostic
     * conditional copy.
     */
    if (!BN_add(l, k, dsa->q)
        || !BN_add(m, l, dsa->q)
        || !BN_copy(k, BN_num_bits(l) > q_bits ? l : m))
        goto err;

    if ((dsa)->meth->bn_mod_exp != NULL) {
            if (!dsa->meth->bn_mod_exp(dsa, r, dsa->g, k, dsa->p, ctx,
                                       dsa->method_mont_p))
                goto err;
    } else {
            if (!BN_mod_exp_mont(r, dsa->g, k, dsa->p, ctx, dsa->method_mont_p))
                goto err;
    }

    if (dsa->type == kDSA)
    {
        if (!BN_mod(r, r, dsa->q, ctx))
            goto err;

        /* Compute  part of 's = inv(k) (m + xr) mod q' */
        if ((kinv = BN_mod_inverse(NULL, k, dsa->q, ctx)) == NULL)
            goto err;
    }
    else if (dsa->type == kSCHNORR)
    {
        kinv = k;
    }

    BN_clear_free(*kinvp);
    *kinvp = kinv;
    kinv = NULL;
    ret = 1;
 err:
    if (!ret)
        DSAerr(DSA_F_DSA_SIGN_SETUP, ERR_R_BN_LIB);
    if (ctx != ctx_in)
        BN_CTX_free(ctx);
    if (dsa->type == kDSA)
        BN_clear_free(k);
    BN_clear_free(l);
    BN_clear_free(m);
    return ret;
}

static int dsa_do_verify(const unsigned char *dgst, int dgst_len,
                         DSA_SIG *sig, DSA *dsa)
{
    BN_CTX *ctx;
    BIGNUM *u1, *u2, *t1;
    BN_MONT_CTX *mont = NULL;
    const BIGNUM *r, *s, *e;
    int ret = -1, i;

    if (!dsa->p || !dsa->q || !dsa->g) {
        DSAerr(DSA_F_DSA_DO_VERIFY, DSA_R_MISSING_PARAMETERS);
        return -1;
    }

    i = BN_num_bits(dsa->q);
    /* fips 186-3 allows only different sizes for q */
    if (i != 160 && i != 224 && i != 256) {
        DSAerr(DSA_F_DSA_DO_VERIFY, DSA_R_BAD_Q_VALUE);
        return -1;
    }

    if (BN_num_bits(dsa->p) > OPENSSL_DSA_MAX_MODULUS_BITS) {
        DSAerr(DSA_F_DSA_DO_VERIFY, DSA_R_MODULUS_TOO_LARGE);
        return -1;
    }

    u1 = BN_new();
    u2 = BN_new();
    t1 = BN_new();
    ctx = BN_CTX_new();
    if (u1 == NULL || u2 == NULL || t1 == NULL || ctx == NULL)
        goto err;

    if (dsa->type == kDSA)
    {
        DSA_SIG_get0(sig, &r, &s);
        if (BN_is_zero(r) || BN_is_negative(r) ||
            BN_ucmp(r, dsa->q) >= 0) {
            ret = 0;
            goto err;
        }
    }
    else if (dsa->type == kSCHNORR)
    {
        DSA_SIG_get0(sig, &s, &e);
        if (BN_is_zero(e)) {
            ret = 0;
            goto err;
        }
    }

    if (BN_is_zero(s) || BN_is_negative(s) ||
        BN_ucmp(s, dsa->q) >= 0) {
        ret = 0;
        goto err;
    }

    if (dsa->type == kDSA)
    {
        /*
         * Calculate W = inv(S) mod Q save W in u2
         */
        if ((BN_mod_inverse(u2, s, dsa->q, ctx)) == NULL)
            goto err;

        /* save M in u1 */
        if (dgst_len > (i >> 3))
            /*
             * if the digest length is greater than the size of q use the
             * BN_num_bits(dsa->q) leftmost bits of the digest, see fips 186-3,
             * 4.2
             */
            dgst_len = (i >> 3);
        if (BN_bin2bn(dgst, dgst_len, u1) == NULL)
            goto err;

        /* u1 = M * w mod q */
        if (!BN_mod_mul(u1, u1, u2, dsa->q, ctx))
            goto err;

        /* u2 = r * w mod q */
        if (!BN_mod_mul(u2, r, u2, dsa->q, ctx))
            goto err;

        if (dsa->flags & DSA_FLAG_CACHE_MONT_P) {
            mont = BN_MONT_CTX_set_locked(&dsa->method_mont_p,
                                          dsa->lock, dsa->p, ctx);
            if (!mont)
                goto err;
        }

        if (dsa->meth->dsa_mod_exp != NULL) {
            if (!dsa->meth->dsa_mod_exp(dsa, t1, dsa->g, u1, dsa->pub_key, u2,
                                        dsa->p, ctx, mont))
                goto err;
        } else {
            if (!BN_mod_exp2_mont(t1, dsa->g, u1, dsa->pub_key, u2, dsa->p, ctx,
                                  mont))
                goto err;
        }

        /* let u1 = u1 mod q */
        if (!BN_mod(u1, t1, dsa->q, ctx))
            goto err;

        /*
         * V is now in u1.  If the signature is correct, it will be equal to R.
         */
        ret = (BN_ucmp(u1, r) == 0);
    }
    else if (dsa->type == kSCHNORR)
    {
        unsigned char hash[SHA256_DIGEST_LENGTH];
        unsigned char vmsg[1024];
        int vlen = 0;

        /* t1 = v = a^s * y^(-e) mod p) */
        if ((BN_mod_inverse(u1, dsa->pub_key, dsa->p, ctx)) == NULL)
            goto err;

        if (dsa->flags & DSA_FLAG_CACHE_MONT_P) {
            mont = BN_MONT_CTX_set_locked(&dsa->method_mont_p,
                                          dsa->lock, dsa->p, ctx);
            if (!mont)
                goto err;
        }

        if (dsa->meth->dsa_mod_exp != NULL) {
            if (!dsa->meth->dsa_mod_exp(dsa, t1, dsa->g, s, u1, e, dsa->p, ctx,
                                        mont))
                goto err;
        } else {
            if (!BN_mod_exp2_mont(t1, dsa->g, s, u1, e, dsa->p, ctx, mont))
                goto err;
        }

        /* e' = h(m||v) */
        vlen = BN_bn2bin(t1, vmsg);
        if (vlen == 0)
            goto err;

        SHA256_CTX sha256;
        SHA256_Init(&sha256);
        SHA256_Update(&sha256, dgst, dgst_len);
        SHA256_Update(&sha256, vmsg, vlen);
        SHA256_Final(hash, &sha256);
        BN_bin2bn(hash, 64, u2);

        /* e' == e */
        ret = (BN_ucmp(u2, e) == 0);
    }

 err:
    if (ret < 0)
        DSAerr(DSA_F_DSA_DO_VERIFY, ERR_R_BN_LIB);
    BN_CTX_free(ctx);
    BN_free(u1);
    BN_free(u2);
    BN_free(t1);
    return ret;
}

static int dsa_init(DSA *dsa)
{
    dsa->flags |= DSA_FLAG_CACHE_MONT_P;
    return 1;
}

static int dsa_finish(DSA *dsa)
{
    BN_MONT_CTX_free(dsa->method_mont_p);
    return 1;
}
