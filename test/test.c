#include <stdio.h>
#include <string.h>
#include "bench.h"
#include "secp256k1.h"
#include "secp256k1_recovery.h"

#define check(cond) do { \
	if (!(cond)) {\
		printf("test condition failed:"#cond);\
	}\
} while(0)

#if !defined(SECP256K1_EC_UNCOMPRESSED)
#define SECP256K1_EC_UNCOMPRESSED 0
#endif

// secp256k1_ext_ecdsa_recover recovers the public key of an encoded compact signature.
//
// Returns: 1: recovery was successful
//			0: recovery was not successful
// Args:	ctx:		pointer to a context object (cannot be NULL)
//	Out:	pubkey_out: the serialized 65-byte public key of the signer (cannot be NULL)
//	In: 	sigdata:	pointer to a 65-byte signature with the recovery id at the end (cannot be NULL)
//			msgdata:	pointer to a 32-byte message (cannot be NULL)
static int secp256k1_ext_ecdsa_recover(
	const secp256k1_context* ctx,
	unsigned char *pubkey_out,
	const unsigned char *sigdata,
	const unsigned char *msgdata
) {
	secp256k1_ecdsa_recoverable_signature sig;
	secp256k1_pubkey pubkey;

	if (!secp256k1_ecdsa_recoverable_signature_parse_compact(ctx, &sig, sigdata, (int)sigdata[64])) {
		return 0;
	}
	if (!secp256k1_ecdsa_recover(ctx, &pubkey, &sig, msgdata)) {
		return 0;
	}
	size_t outputlen = 65;
	return secp256k1_ec_pubkey_serialize(ctx, pubkey_out, &outputlen, &pubkey, SECP256K1_EC_UNCOMPRESSED);
}

// secp256k1_ext_ecdsa_verify verifies an encoded compact signature.
//
// Returns: 1: signature is valid
//			0: signature is invalid
// Args:	ctx:		pointer to a context object (cannot be NULL)
//	In: 	sigdata:	pointer to a 64-byte signature (cannot be NULL)
//			msgdata:	pointer to a 32-byte message (cannot be NULL)
//			pubkeydata: pointer to public key data (cannot be NULL)
//			pubkeylen:	length of pubkeydata
static int secp256k1_ext_ecdsa_verify(
	const secp256k1_context* ctx,
	const unsigned char *sigdata,
	const unsigned char *msgdata,
	const unsigned char *pubkeydata,
	size_t pubkeylen
) {
	secp256k1_ecdsa_signature sig;
	secp256k1_pubkey pubkey;

	if (!secp256k1_ecdsa_signature_parse_compact(ctx, &sig, sigdata)) {
		return 0;
	}
	if (!secp256k1_ec_pubkey_parse(ctx, &pubkey, pubkeydata, pubkeylen)) {
		return 0;
	}
	return secp256k1_ecdsa_verify(ctx, &sig, msgdata, &pubkey);
}

static int secp256k1_ext_recovery_sign(
	const secp256k1_context* ctx,
	const unsigned char *msgdata,
	const unsigned char *seckey,
	unsigned char *rsigdata)
{
	secp256k1_ecdsa_recoverable_signature rsig;
	int recid = 0;
	if( secp256k1_ec_seckey_verify(ctx, seckey) != 1 ) {
		return 0;
	}
	if(secp256k1_ecdsa_sign_recoverable(ctx, &rsig, msgdata, seckey, NULL, NULL) == 0) {
		return 0;
	}
	secp256k1_ecdsa_recoverable_signature_serialize_compact(ctx, rsigdata, &recid, &rsig);
	rsigdata[64] = recid;
	return 1;
}

static void hex_dumpln(char *msg, unsigned char *buf, int len) {
	int i = 0;
	if (msg) {
		printf("%s",msg);
	}
	for(i=0; i < len; i++) {
		printf("%02x",buf[i]);
	}
	printf("\n");
}
static void hex_dump(char *msg, unsigned char *buf, int len) {
	int i = 0;
	if (msg) {
		printf("%s",msg);
	}
	for(i=0; i < len; i++) {
		printf("%02x",buf[i]);
	}
}


typedef struct {
    secp256k1_context *ctx;
	secp256k1_pubkey pubkey;
	secp256k1_pubkey recpubkey;
    secp256k1_ecdsa_signature sig;
	secp256k1_ecdsa_recoverable_signature rsig;
    unsigned char msg[32];
    unsigned char key[32];
	unsigned char ethrecpubkey[65];
	int idx;
} benchmark_verify_t;

const int count = 200;

static void benchmark_sign_and_verify(void* arg) {
    int i;
    benchmark_verify_t* data = (benchmark_verify_t*)arg;

    for (i = 0; i < count; i++) {
		
        check(secp256k1_ecdsa_verify(data->ctx, &data->sig, data->msg, &data->pubkey));
    }
}

static void benchmark_sign_and_verify_setup(void* arg) {
    int i;
	unsigned char pubkey[65];
    size_t pubkeylen = 65;
    benchmark_verify_t* data = (benchmark_verify_t*)arg;

	data->idx++;
	for (i = 0; i < 32; i++) {
        data->msg[i] = 1 + i + data->idx;
    }
    for (i = 0; i < 32; i++) {
        data->key[i] = 33 + i + data->idx;
    }

	check(secp256k1_ext_recovery_sign(data->ctx,data->msg, data->key, data->rsig.data));
	check(secp256k1_ext_ecdsa_recover(data->ctx,data->ethrecpubkey, data->rsig.data, data->msg));
    // used to run recover pubkey test.
    hex_dump("./testk 1 ", data->msg, 32);
    hex_dump(" ", data->rsig.data, 65);
    hex_dumpln(" ", data->ethrecpubkey+1, 64);
    // used to run verify signature test.
    hex_dump("./testk ", data->msg, 32);
    hex_dump(" ", data->rsig.data, 64);
    hex_dumpln(" ", data->ethrecpubkey, 65);
#if 0
	hex_dumpln("private ", data->key,32);
	hex_dumpln("message ", data->msg,32);
	hex_dumpln("rsig ", data->rsig.data, 65);
	hex_dumpln("pubkey ", data->ethrecpubkey, 65);
#endif


	check(secp256k1_ec_pubkey_create(data->ctx, &data->pubkey, data->key));
	check(secp256k1_ecdsa_sign(data->ctx, &data->sig, data->msg, data->key, NULL, NULL));
	secp256k1_ecdsa_sign_recoverable(data->ctx, &data->rsig, data->msg, data->key, NULL, NULL);
	secp256k1_ecdsa_recover(data->ctx, &data->recpubkey, &data->rsig, data->msg);
#if 0
	hex_dump("private", data->key,32);
	hex_dump("message", data->msg,32);
	hex_dump("signat",data->sig.data,64);
	hex_dump("rsig", data->rsig.data, 65);
	hex_dump("pubkey",data->pubkey.data,64);
	hex_dump("recpub", data->recpubkey.data, 64);
    printf("============================\n");
#endif
}


int main(void) {
    benchmark_verify_t data;
	memset(&data,0x0, sizeof(benchmark_verify_t));

    data.ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
    
    run_benchmark("ecdsa_verify", benchmark_sign_and_verify, benchmark_sign_and_verify_setup, NULL, &data, 100, count);

    secp256k1_context_destroy(data.ctx);
    return 0;
}

