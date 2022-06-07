#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <sys/time.h>
#include "oclsp.h"
#include "secp256k1.h"
#include "secp256k1_recovery.h"

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

int hexcharToIntX(char c)
{ 
	if (c >= '0' && c <= '9') return (c - '0');
	if (c >= 'A' && c <= 'F') return (c - 'A' + 10);
	if (c >= 'a' && c <= 'f') return (c - 'a' + 10);
	return 0;
}

int hexstringToBytesX(char* hexstring,unsigned char* bytes,int hexlength)
{
	int i = 0;
	if(hexlength%2 != 0)
	{
		return 0;
	}
	for (i=0 ; i <hexlength ; i+=2) {
	    bytes[i/2] = (unsigned char) ((hexcharToIntX(hexstring[i]) << 4) | hexcharToIntX(hexstring[i+1]));
	}
	return 1;
}

static struct timeval gTs, gTe;
static struct timezone gTz;

#define PROFILE_start() {\
   gettimeofday(&gTs, &gTz);\
}\

#define PROFILE_end(msg) {\
   gettimeofday(&gTe, &gTz);\
   double time_taken = (double)(gTe.tv_sec*1000000 + gTe.tv_usec - gTs.tv_sec*1000000 - gTs.tv_usec); \
   printf("%s took %f seconds.\n", msg, time_taken/1000000);\
}\


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

static FILE *frand = NULL;
void get_test_random32(unsigned char *data)
{

	if(frand == NULL)
	{
		frand = fopen("/dev/urandom", "r");
	}
	if(feof(frand))
	{
		fseek(frand, 0, SEEK_SET);
	}

	if ((frand == NULL) || !fread(data, 32, 1, frand)) {
		printf("open/read from /dev/urandom failed.\n");
		exit(-1);
	}
	
	/*fclose(frand);*/
}

void bench_ocl_verify_test(secp256k1_context *ctx, int testcount, int argc, char ** argv)
{
	unsigned char seckey[32];
	unsigned char msg[32];
	unsigned char rsig[65];
	unsigned char recpubkey[65];
	int i = 0, result = 1, ret = 0;

	int *resall = (int*)malloc(testcount * sizeof(int));
	ocl_msg *msgall = (ocl_msg*)malloc(testcount * sizeof(ocl_msg));
	ocl_pubkey *pubkeyall = (ocl_pubkey*)malloc(testcount * sizeof(ocl_pubkey));
	secp256k1_ecdsa_signatureX *sigall = (secp256k1_ecdsa_signatureX*)malloc(testcount * sizeof(secp256k1_ecdsa_signatureX));

	get_test_random32(seckey);
	for(i = 0; i < testcount; i++)
	{
		get_test_random32(msg);
		ret = secp256k1_ext_recovery_sign(ctx, msg, seckey, rsig);
		if(ret != 1)
		{
			printf("secp256k1_ext_recovery_sign failed\n");
			exit(1);
		}
		memcpy(msgall[i].data, msg, sizeof(msg));
		memcpy(sigall[i].data, rsig, sizeof(secp256k1_ecdsa_signatureX));
	}
	
	ret = secp256k1_ext_ecdsa_recover(ctx, recpubkey, rsig, msg);
	if(ret != 1)
	{
		printf("secp256k1_ext_ecdsa_recover failed\n");
		exit(1);
	}

	for(i=0; i < testcount; i++)
	{
		memcpy(pubkeyall[i].data, recpubkey, sizeof(recpubkey));
	}

	ret = secp256k1_ecdsa_verify_ocl(testcount, sigall, msgall, pubkeyall, resall);
	for(i = 0; i < testcount; i++)
	{
		if (1 != resall[i])
		{
			result = 0;
			break;
		}
	}
	
	if(ret != 1 || result != 1)
	{
		printf("bench_verify_test result: failed\n\n");
	}
	else
	{
		printf("bench_verify_test result: ok\n\n");
	}

	free(msgall);
	free(sigall);
	free(resall);
	free(pubkeyall);
	
}

void bench_ocl_recover_test(secp256k1_context *ctx, int testcount, int argc, char ** argv)
{
	unsigned char seckey[32];
	unsigned char msg[32];
	unsigned char rsig[65];
	unsigned char recpubkey[65];
	int i = 0, result = 1, ret = 0;

	ocl_msg *msgall = (ocl_msg*)malloc(testcount * sizeof(ocl_msg));
	secp256k1_ecdsa_recoverable_signatureX *rsigall = (secp256k1_ecdsa_recoverable_signatureX*)malloc(testcount * sizeof(secp256k1_ecdsa_recoverable_signatureX));
	ocl_pubkey *pubkeyall = (ocl_pubkey*)malloc(testcount * sizeof(ocl_pubkey));

	get_test_random32(seckey);
	for(i = 0; i < testcount; i++)
	{
		get_test_random32(msg);
		ret = secp256k1_ext_recovery_sign(ctx, msg, seckey, rsig);
		if(ret != 1)
		{
			printf("secp256k1_ext_recovery_sign failed\n");
			exit(1);
		}
		memcpy(msgall[i].data, msg, sizeof(msg));
		memcpy(rsigall[i].data, rsig, sizeof(rsig));
	}
	
	ret = secp256k1_ext_ecdsa_recover(ctx, recpubkey, rsig, msg);
	if(ret != 1)
	{
		printf("secp256k1_ext_ecdsa_recover failed\n");
		exit(1);
	}

	ret = secp256k1_ecdsa_recover_ocl(testcount, rsigall, msgall, pubkey);
	for(i = 0; i < testcount; i++)
	{
		if(0 != memcmp(pubkey[i].data, recpubkey))
		{
			result = 0;
			break;
		}
	}
	
	if(ret != 1 || result != 1)
	{
		printf("bench_recover_test result: failed\n\n");
	}
	else
	{
		printf("bench_recover_test result: ok\n\n");
	}
	
	free(rsigall);
	free(msgall);
	free(pubkeyall);

	return;
}
#if 1
void base_check(secp256k1_context *ctx, int argc, char ** argv) {
	secp256k1_ecdsa_signature sig;
	secp256k1_ecdsa_recoverable_signature rsig;
	int ret = 0;
    if( 3 == argc){
        /* genenrate recoverable signature use command :./tests msg seckey */
		size_t pub_out = 65;
        unsigned char msg[32];
        unsigned char seckey[32];
        unsigned char rsig[65];
		unsigned char recpub[65];
		secp256k1_pubkey pubkey;
        if (strlen(argv[1]) != 64) {
            printf("invalid param: given msg(%s) length %d\n", argv[1], strlen(argv[1]));
            return ;
        }

        hexstringToBytesX(argv[1], msg, strlen(argv[1]));
        if (strlen(argv[2]) != 64) {
            printf("invalid param: given seckey(%s) length %d\n", argv[2], strlen(argv[2]));
            return ;
        }

        hexstringToBytesX(argv[2], seckey, strlen(argv[2]));
        hex_dumpln("msg:",msg,sizeof(msg));
        hex_dumpln("sec:",seckey,sizeof(seckey));

		ret = secp256k1_ecdsa_sign(ctx,&sig,msg,seckey,NULL,NULL);
		if(ret != 1)
		{
			printf("ecdsa sign failed.\n");
		}

		ret = secp256k1_ec_pubkey_create(ctx,&pubkey,seckey);
		if(ret != 1)
		{
			printf("ecdsa create pubkey failed.\n");
		}
		secp256k1_ec_pubkey_serialize(ctx,recpub, &pub_out, &pubkey,0);
		
		ret = secp256k1_ecdsa_verify(ctx,&sig,msg,&pubkey);
		if(ret != 1)
		{
			printf("ecdsa verify failed.\n");
		}
		

		hex_dumpln("sig:",sig.data,sizeof(sig));
		hex_dumpln("genpub:",pubkey.data,sizeof(pubkey));
		hex_dumpln("serpub:",recpub,sizeof(recpub));

        secp256k1_ext_recovery_sign(ctx,msg,seckey,rsig);
		secp256k1_ext_ecdsa_recover(ctx,recpub,rsig,msg);
        hex_dumpln("rsig:",rsig,sizeof(rsig));
		hex_dumpln("recpub:",recpub,sizeof(recpub));
    }else if (5 == argc) {
		/*
		* verify signature use command: ./tests 0 count private msg
		* recover pubkey   use command: ./tests 1 msg signature pubkey
		*/
		int choice = atoi(argv[1]);
		if (0 == choice%10) {
			/*
			* 
			* verify signature use command: ./tests 0 msg signature pubkey
			*/
			ocl_pubkey spubkey;
			ocl_msg ocl_msg;

			if (strlen(argv[2]) != 64) {
				printf("invalid param: given msg(%s) length %d\n", argv[2], strlen(argv[2]));
				return ;
			}
			hexstringToBytesX(argv[2], ocl_msg.data, strlen(argv[2]));

			if (strlen(argv[3]) != 128) {
				printf("invalid param: given signature(%s) length %d\n", argv[3], strlen(argv[3]));
				return ;
			}
			hexstringToBytesX(argv[3], sig.data, strlen(argv[3]));

			if (strlen(argv[4]) != 130) {
				printf("invalid param: given pubkey(%s) length %d\n", argv[4], strlen(argv[4]));
				return ;
			}
			hexstringToBytesX(argv[4], spubkey.data, strlen(argv[4]));

			secp256k1_ocl_ecdsa_verifyX(*ctx->ecmult_ctx.pre_g, &sig, &ocl_msg, &spubkey,&ret);

			hex_dumpln("signature:", sig.data,sizeof(sig));
			hex_dumpln("msg:",ocl_msg.data,sizeof(ocl_msg.data));
			hex_dumpln("pubkey:", spubkey.data,sizeof(spubkey.data));

			printf("verify result: %s\n", ret == 1 ? "ok" : "failed");
			if (ret != 1)
			{
				exit(1);
			}

			return;
		} else if (1 == choice%10) {
			/*
			* recover pubkey   use command: ./tests 1 msg signature pubkey
			*/
			ocl_pubkey recpub;
			ocl_pubkey pubkey;
			ocl_msg ocl_msg;

			if (strlen(argv[2]) != 64) {
				printf("invalid param: given msg(%s) length %d\n", argv[2], strlen(argv[2]));
				return ;
			}
			hexstringToBytesX(argv[2], ocl_msg.data, strlen(argv[2]));

			if (strlen(argv[3]) != 130) {
				printf("invalid param: given recoverable sig(%s) length %d\n", argv[3], strlen(argv[3]));
				return ;
			}
			hexstringToBytesX(argv[3], rsig.data, strlen(argv[3]));

			if (strlen(argv[4]) != 130) {
				printf("invalid param: given pubkey(%s) length %d\n", argv[4], strlen(argv[4]));
				return ;
			}
			hexstringToBytesX(argv[4], pubkey.data, strlen(argv[4]));

			secp256k1_ocl_ecdsa_recoverX(*ctx->ecmult_ctx.pre_g, &rsig, &ocl_msg, &recpub);
			ret = memcmpX(pubkey.data, recpub.data, sizeof(pubkey));
			
			hex_dumpln("rsig:", rsig.data,sizeof(rsig));
			hex_dumpln("msg:", ocl_msg.data,sizeof(ocl_msg.data));
			hex_dumpln("recpubkey:", recpub.data,sizeof(recpub));
			hex_dump("pubkey:", pubkey.data,sizeof(pubkey));
			printf("recover result: %s\n", ret == 0 ? "ok" :"failed");
			if (ret != 0)
			{
				exit(1);
			}
		}
		
		return;
	}

}
#endif

void bench_loaddata_test(secp256k1_context *ctx, int testcount, int argc, char ** argv)
{
	int i = 0, total = 0, ret = 0, res = 0;
	char *data_path1 = "data/eth_rsh.txt";
	char *data_path2 = "data/eth_v.txt";
	char *data_path3 = "data/eth_xy.txt";
	FILE *fd1;
	FILE *fd2;
	FILE *fd3;
	unsigned char  r[32],s[32],h[32],v, x[32], y[32];
	
	ocl_msg msg;
	ocl_pubkey pubkey,recpubkey;
	ocl_signature sig;
	ocl_recoverable_signature rsig;

	if (((fd1 = fopen(data_path1, "r")) == NULL)||((fd2 = fopen(data_path2, "r")) == NULL)||((fd3 = fopen(data_path3, "r")) == NULL))
	{
			printf("open data file error!!\n");
			exit(1);
	}

	while((total < testcount))
	{
		if(feof(fd1) || feof(fd2) || feof(fd3))
		{
			fseek(fd1, 0, SEEK_SET);
			fseek(fd2, 0, SEEK_SET);
			fseek(fd3, 0, SEEK_SET);
		}
		
		for(int i=0;i<32;i++)
		{
				fscanf(fd1,"%hhu,%hhu,%hhu\n",&r[i],&s[i],&h[i]);
		}
		fscanf(fd2,"%hhu\n",&v);
		for(int i=0;i<32;i++)
		{
				fscanf(fd3,"%hhu,%hhu\n",&x[i],&y[i]);
		}
		memcpy(msg.data,h,sizeof(h));
		memcpy(rsig.data,r,sizeof(r));
		memcpy(rsig.data+32,s,sizeof(s));
		rsig.data[64] = v;
		memcpy(sig.data,r,sizeof(r));
		memcpy(sig.data+32,s,sizeof(s));
		pubkey.data[0] = 0x04;
		memcpy(pubkey.data+1, x,sizeof(x));
		memcpy(pubkey.data+1+32, y,sizeof(y));

		ret = secp256k1_ecdsa_recover_ocl(1, &rsig, &msg, &recpubkey);
		if(ret != 1 || 0 != memcmp(recpubkey.data, pubkey.data, sizeof(ocl_pubkey)))
		{
			printf("loaddata test recover failed.\n");
			exit(1);
		}
		
		ret = secp256k1_ecdsa_verify_ocl(1, &sig, &msg, &pubkey, &res);
		if(ret != 1 || res != 1)
		{
			printf("loaddata test verify failed.\n");
			exit(1);
		}
		
		total++;
	}
	fclose(fd1);
	fclose(fd2);
	fclose(fd3);

	
	printf("loaddata test %d items result ok.\n", testcount);
}

int main(int argc, char ** argv)
{
	FILE *fp = NULL;
	int MAX_SOURCE_SIZE=512 * 1024;
	unsigned char *source_str = NULL;
	int source_size = 0;
	secp256k1_context *ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
	fp = fopen("src/k.cl", "r");
	if (!fp) {
		fprintf(stderr, "Failed to load kernel.\n");
		exit(1);
	}
	source_str = (char*)malloc(MAX_SOURCE_SIZE);
	source_size = fread( source_str, 1, MAX_SOURCE_SIZE, fp);
	fclose(fp);

	secp256_ocl_init(source_str,source_size, 0);
	
	if(argc > 1)
	{
		base_check(ctx, argc, argv);
	}
	else
	{
		bench_ocl_recover_test(ctx, 10000, argc, argv);
		bench_ocl_verify_test(ctx, 10000, argc, argv);
		
		bench_loaddata_test(ctx, 10000, argc, argv);
	}

	secp256_ocl_destory();
	secp256k1_context_destroy(ctx);
	
    return 0;
}
