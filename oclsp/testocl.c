// Last Update:2020-08-27 14:15:30
/**
 * @file testocl.c
 * @brief 
 * @author luxueqian
 * @version 0.1.00
 * @date 2020-08-27
 */

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <sys/time.h>
#include "oclsp.h"

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

void load_data(int testcount, ocl_msg *allmsg, ocl_recoverable_signature *allrsig, ocl_pubkey *allpubkey) 
{
	int i = 0, total = 0, ret = 0, res = 0;
	char *data_path1 = "data/eth_rsh.txt";
	char *data_path2 = "data/eth_v.txt";
	char *data_path3 = "data/eth_xy.txt";
	FILE *fd1;
	FILE *fd2;
	FILE *fd3;
	int failed = 0;
	unsigned char  r[32],s[32],h[32],v, x[32], y[32];

	if (((fd1 = fopen(data_path1, "r")) == NULL)||((fd2 = fopen(data_path2, "r")) == NULL)||((fd3 = fopen(data_path3, "r")) == NULL))
	{
			printf("open data file error!!\n");
			exit(1);
	}

	while((total < testcount))
	{
		ocl_msg *msg = allmsg + total;
		ocl_pubkey *pubkey = allpubkey + total;
		ocl_recoverable_signature *rsig = allrsig + total;
		
		if(feof(fd1) || feof(fd2) || feof(fd3))
		{
			break;
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
		memcpy(msg->data,h,sizeof(h));
		memcpy(rsig->data,r,sizeof(r));
		memcpy(rsig->data+32,s,sizeof(s));
		rsig->data[64] = v;
		pubkey->data[0] = 0x04;
		memcpy(pubkey->data+1, x,sizeof(x));
		memcpy(pubkey->data+1+32, y,sizeof(y));

		total++;
	}
	if (total < testcount) 
	{
		for (int i = 0; total < testcount; i++) 
		{
			ocl_msg *msg = allmsg + total;
			ocl_pubkey *pubkey = allpubkey + total;
			ocl_recoverable_signature *rsig = allrsig + total;
			memcpy(msg->data, allmsg[i].data, sizeof(ocl_msg));
			memcpy(rsig->data, allrsig[i].data, sizeof(ocl_recoverable_signature));
			memcpy(pubkey->data, allpubkey[i].data, sizeof(ocl_pubkey));

			total++;
		}
	}
	fclose(fd1);
	fclose(fd2);
	fclose(fd3);
	printf("load %d data ok.\n", total);

}

void bench_recover_test(int testcount, int argc, char ** argv)
{
	int ret = 0, failed = 0;

	ocl_msg *allmsg = (ocl_msg*)malloc(testcount * sizeof(ocl_msg));
	ocl_recoverable_signature *allrsig = (ocl_recoverable_signature*)malloc(testcount * sizeof(ocl_recoverable_signature));
	ocl_pubkey *allpubkey = (ocl_pubkey*)malloc(testcount * sizeof(ocl_pubkey));
	ocl_pubkey *all_recpubkey = (ocl_pubkey*)malloc(testcount * sizeof(ocl_pubkey));

	load_data(testcount, allmsg, allrsig, allpubkey);

	PROFILE_start();
	ret = secp256k1_ecdsa_recover_ocl(testcount, allrsig, allmsg, all_recpubkey);
	if (ret != 1)
	{
		printf("test recover failed.\n");
		exit(1);
	}
	PROFILE_end("ocl recover ")
	
	for (int i = 0; i < testcount; i++) 
	{
		if (0 != memcmp(all_recpubkey[i].data, allpubkey[i].data, sizeof(ocl_pubkey)))
		{
			//printf("recover failed, got ");
			//hex_dumpln("",all_recpubkey[i].data, sizeof(ocl_pubkey));
			failed ++;
		}
		else 
		{
			//printf("got recoverd ");
			//hex_dumpln("",all_recpubkey[i].data, sizeof(ocl_pubkey));
		}
	}
	free(allmsg);
	free(allpubkey);
	free(allrsig);
	free(all_recpubkey);
	if (failed > 0)
	{
		printf("loaddata test %d items %d failed.\n", testcount, failed);
	}
}


void bench_loaddata_test(int testcount, int argc, char ** argv)
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
			break;
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

	printf("loaddata test %d items result ok.\n", total);
}

void bench_quickly_test(int testcount, int argc, char ** argv)
{
	int randomcount = 100000;
	for(int i = 0; i < testcount; i++) 
	{
		printf("--> %d\n",i);
		bench_recover_test(randomcount, argc, argv);
	}
}



int main(int argc, char ** argv)
{
	FILE *fp = NULL;
	int MAX_SOURCE_SIZE=512 * 1024;
	unsigned char *source_str = NULL;
	int source_size = 0;

	fp = fopen("k.cl", "r");
	if (!fp) {
		fprintf(stderr, "Failed to open kernel file.\n");
		exit(1);
	}
	source_str = (char*)malloc(MAX_SOURCE_SIZE);
	source_size = fread( source_str, 1, MAX_SOURCE_SIZE, fp);
	fclose(fp);

	secp256_ocl_init(source_str,source_size, 0);
	
	bench_loaddata_test(10000, argc, argv);
	bench_recover_test(10000, argc, argv);
	bench_quickly_test(10, argc, argv);

	secp256_ocl_destory();
    return 0;
}
