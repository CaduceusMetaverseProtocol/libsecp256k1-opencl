// Last Update:2020-08-27 13:52:07
/**
 * @file oclsp.h
 * @brief 
 * @author luxueqian
 * @version 0.1.00
 * @date 2020-08-26
 */

#ifndef OCLSP_H
#define OCLSP_H

typedef struct {
    unsigned char data[65];
} ocl_recoverable_signature;

typedef struct {
    unsigned char data[64];
} ocl_signature;


typedef struct {
    unsigned char data[32];
} ocl_msg;

typedef struct {
	unsigned char data[65];
} ocl_pubkey;

int secp256_ocl_init(unsigned char *code, int codelen, int mode);
int secp256_ocl_destory();
int secp256k1_ecdsa_recover_ocl(int count, ocl_recoverable_signature *rsigall, 
	ocl_msg *msgall, ocl_pubkey *pubkeyall);
int secp256k1_ecdsa_verify_ocl(int count, ocl_signature *sigall, 
	ocl_msg *msg32all, ocl_pubkey *pubkeyall, int *resall);

#endif  /*OCLSP_H*/
