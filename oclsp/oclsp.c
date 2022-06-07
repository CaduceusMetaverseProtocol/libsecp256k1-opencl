// Last Update:2020-08-27 13:57:22
/**
 * @file oclsp.c
 * @brief 
 * @author luxueqian
 * @version 0.1.00
 * @date 2020-08-26
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <sys/time.h>
#include "oclsp.h"
#include "secp256k1.h"
#include "secp256k1_recovery.h"

#include "util.h"
#include "hash_impl.h"
#include "testrand_impl.h"

#ifdef __APPLE__
#include <OpenCL/opencl.h>
#else
#include <CL/cl.h>
#endif

#define __global 
#define __constant
#define __kernel
#define get_global_id(a) (a)

typedef uint64_t ulong;
typedef unsigned char uchar;

#include "k.cl"
typedef struct {
    secp256k1_ge_storageX (*pre_g)[];
} secp256k1_ecmult_contextX;

typedef struct {
    secp256k1_ecmult_contextX ecmult_ctx;
}secp256k1_context_inner;

typedef struct secp256k1_ocl {
    cl_device_id device_id;
    cl_context context;
    cl_program program;
    cl_kernel recover_kernel;
    cl_kernel verify_kernel;
    secp256k1_context *ctx;
	secp256k1_ge_storageX* arr;
}secp256k1_ocl;

const int PRE_G_LENGTH = 16384; // can't change to any other value.
const int N_LENGTH = 8;		 // can't change to any other value.

static int init_opencl(secp256k1_ocl *ocl, unsigned char * code, int code_len, int mode)
{
    cl_platform_id platform_id = NULL;
    cl_device_id device_id = NULL;   
    cl_uint ret_num_devices;
    cl_uint ret_num_platforms;
    cl_device_type type = CL_DEVICE_TYPE_GPU; 
    cl_int clret;
    char *source_str;
    size_t source_size;
	int i,j;
	secp256k1_context_inner* ictx;

    ocl->ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
	
    {
        source_str = (char*)malloc(code_len);
        memcpy(source_str, code, code_len);
        source_size = code_len;
    }

    if(mode == 1)
    {
        type = CL_DEVICE_TYPE_CPU;
    }

    clret = clGetPlatformIDs(1, &platform_id, &ret_num_platforms);
    clret = clGetDeviceIDs( platform_id, type, 1, 
            &device_id, &ret_num_devices);

    ocl->device_id = device_id;
    ocl->context = clCreateContext( NULL, 1, &device_id, NULL, NULL, &clret);
    if(CL_SUCCESS != clret)
    {
        printf("clCreateContext failed\n");
        return 1;
    }
    ocl->program = clCreateProgramWithSource(ocl->context, 1, 
            (const char **)&source_str, (const size_t *)&source_size, &clret);
    if(CL_SUCCESS != clret)
    {
        printf("clCreateProgramWithSource failed\n");
        return 1;
    }

    clret = clBuildProgram(ocl->program, 1, &device_id, NULL, NULL, NULL);
    if(CL_SUCCESS != clret)
    {	 
        size_t log_size;
        char *log;

        clGetProgramBuildInfo(ocl->program, device_id, CL_PROGRAM_BUILD_LOG, 0, NULL, &log_size);
        log = (char *) malloc(log_size);
        clGetProgramBuildInfo(ocl->program, device_id, CL_PROGRAM_BUILD_LOG, log_size, log, NULL);
        printf("program build failed, log:\n\%s\n", log);
        return 1;
    }

    ocl->recover_kernel = clCreateKernel(ocl->program, "secp256k1_ocl_ecdsa_recoverX", &clret);
    if(CL_SUCCESS != clret)
    {
        printf("create recover kernel failed\n");
        return 1;
    }
    ocl->verify_kernel  = clCreateKernel(ocl->program, "secp256k1_ocl_ecdsa_verifyX", &clret);
    if(CL_SUCCESS != clret)
    {
        printf("create verify kernel failed\n");
        return 1;
    }

	ictx = (secp256k1_context_inner*)ocl->ctx;
    ocl->arr = (secp256k1_ge_storageX*)malloc(PRE_G_LENGTH*sizeof(secp256k1_ge_storageX));
    for(i = 0; i < PRE_G_LENGTH; i++ )
    {
        for(j = 0; j < N_LENGTH; j++ )
        {
            ocl->arr[i].x.n[j] = (*ictx->ecmult_ctx.pre_g)[i].x.n[j];
            ocl->arr[i].y.n[j] = (*ictx->ecmult_ctx.pre_g)[i].y.n[j];
        }
    }

	
    return 0;
}

static void release_ocl(secp256k1_ocl *ocl)
{
    if(ocl->verify_kernel != NULL)
    {
        clReleaseKernel(ocl->verify_kernel);
        ocl->verify_kernel = NULL;
    }
    if(ocl->recover_kernel != NULL)
    {
        clReleaseKernel(ocl->recover_kernel);
        ocl->recover_kernel = NULL;
    }
    if(ocl->program != NULL)
    {
        clReleaseProgram(ocl->program);
        ocl->program = NULL;
    }
    if(ocl->context != NULL)
    {
        clReleaseContext(ocl->context);
        ocl->context = NULL;
    }
	if(ocl->arr != NULL)
	{
		free(ocl->arr);
		ocl->arr = NULL;
	}
    if(ocl->ctx != NULL)
    {
        secp256k1_context_destroy(ocl->ctx);
        ocl->ctx = NULL;
    }
}
/*
* return: 	1	success
*			0	failed
* param:	resall	
*/
static int verify_ocl(secp256k1_ocl *ocl, int taskcount, secp256k1_ecdsa_signature *sigall, 
	const Msg32 *msg32all, const EthPubkey *pubkeyall, int *resall) 
{
    const int LIST_SIZE = taskcount;
    int result = 1;
    size_t global_item_size;
    secp256k1_ge_storageX* arr = ocl->arr;

    cl_int clret = CL_SUCCESS;
    cl_command_queue command_queue = clCreateCommandQueue(ocl->context, ocl->device_id, 0, &clret);
    cl_mem a_mem_obj = clCreateBuffer(ocl->context, CL_MEM_READ_ONLY, 
            PRE_G_LENGTH*sizeof(secp256k1_ge_storageX), NULL, &clret);

    cl_mem b_mem_obj = clCreateBuffer(ocl->context, CL_MEM_READ_ONLY, 
            LIST_SIZE*sizeof(secp256k1_ecdsa_signatureX), NULL, &clret);

    cl_mem c_mem_obj = clCreateBuffer(ocl->context, CL_MEM_READ_ONLY, 
            LIST_SIZE * sizeof(Msg32), NULL, &clret);

    cl_mem d_mem_obj = clCreateBuffer(ocl->context, CL_MEM_READ_ONLY, 
            LIST_SIZE*sizeof(EthPubkey), NULL, &clret);
    cl_mem e_mem_obj = clCreateBuffer(ocl->context, CL_MEM_WRITE_ONLY, 
            LIST_SIZE*sizeof(int), NULL, &clret);

    clret |= clEnqueueWriteBuffer(command_queue, a_mem_obj, CL_TRUE, 0,
            PRE_G_LENGTH*sizeof(secp256k1_ge_storageX), arr, 0, NULL, NULL);
    clret |= clEnqueueWriteBuffer(command_queue, b_mem_obj, CL_TRUE, 0,
            LIST_SIZE*sizeof(secp256k1_ecdsa_signatureX), sigall, 0, NULL, NULL); 
    clret |= clEnqueueWriteBuffer(command_queue, c_mem_obj, CL_TRUE, 0,
            LIST_SIZE*sizeof(Msg32), msg32all, 0, NULL, NULL);
    clret |= clEnqueueWriteBuffer(command_queue, d_mem_obj, CL_TRUE, 0,
            LIST_SIZE*sizeof(EthPubkey), pubkeyall, 0, NULL, NULL);
	
	if(CL_SUCCESS == clret)
	{
	    clret |= clSetKernelArg(ocl->verify_kernel, 0, sizeof(cl_mem), (void *)&a_mem_obj);
	    clret |= clSetKernelArg(ocl->verify_kernel, 1, sizeof(cl_mem), (void *)&b_mem_obj);
	    clret |= clSetKernelArg(ocl->verify_kernel, 2, sizeof(cl_mem), (void *)&c_mem_obj);
	    clret |= clSetKernelArg(ocl->verify_kernel, 3, sizeof(cl_mem), (void *)&d_mem_obj);
	    clret |= clSetKernelArg(ocl->verify_kernel, 4, sizeof(cl_mem), (void *)&e_mem_obj);
		
		if(CL_SUCCESS == clret)
		{
			global_item_size = LIST_SIZE; 
			clret |= clEnqueueNDRangeKernel(command_queue, ocl->verify_kernel, 1, NULL,
					&global_item_size, NULL, 0, NULL, NULL);
			
			clret |= clEnqueueReadBuffer(command_queue, e_mem_obj, CL_TRUE, 0, 
					LIST_SIZE*sizeof(int), resall, 0, NULL, NULL);
		}

	}

    clFlush(command_queue);
    clReleaseMemObject(a_mem_obj);
    clReleaseMemObject(b_mem_obj);
    clReleaseMemObject(c_mem_obj);
    clReleaseMemObject(d_mem_obj);
    clReleaseMemObject(e_mem_obj);
    clReleaseCommandQueue(command_queue);

	if(CL_SUCCESS != clret)
	{
		result = 0;
	}

    return result;
}

static int recover_ocl(secp256k1_ocl *ocl, int taskcount, secp256k1_ecdsa_recoverable_signature *rsigall, 
	Msg32 *msgall, EthPubkey *pubkeyall) 
{
    const int LIST_SIZE = taskcount;
    size_t global_item_size; 
    int result = 1;
    cl_int clret = CL_SUCCESS;
    secp256k1_ge_storageX* arr = ocl->arr;

    cl_command_queue command_queue = clCreateCommandQueue(ocl->context, ocl->device_id, 0, &clret);
    cl_mem a_mem_obj = clCreateBuffer(ocl->context, CL_MEM_READ_ONLY, 
            PRE_G_LENGTH*sizeof(secp256k1_ge_storageX), NULL, &clret);

    cl_mem b_mem_obj = clCreateBuffer(ocl->context, CL_MEM_READ_ONLY, 
            LIST_SIZE*sizeof(secp256k1_ecdsa_recoverable_signatureX), NULL, &clret);

    cl_mem c_mem_obj = clCreateBuffer(ocl->context, CL_MEM_READ_ONLY, 
            LIST_SIZE * sizeof(Msg32), NULL, &clret);

    cl_mem d_mem_obj = clCreateBuffer(ocl->context, CL_MEM_WRITE_ONLY, 
            LIST_SIZE*sizeof(EthPubkey), NULL, &clret);

    clret |= clEnqueueWriteBuffer(command_queue, a_mem_obj, CL_TRUE, 0,
            PRE_G_LENGTH*sizeof(secp256k1_ge_storageX), arr, 0, NULL, NULL);
    clret |= clEnqueueWriteBuffer(command_queue, b_mem_obj, CL_TRUE, 0,
            LIST_SIZE*sizeof(secp256k1_ecdsa_recoverable_signatureX), rsigall, 0, NULL, NULL); 
    clret |= clEnqueueWriteBuffer(command_queue, c_mem_obj, CL_TRUE, 0,
            LIST_SIZE*sizeof(Msg32), msgall, 0, NULL, NULL);

	if(CL_SUCCESS == clret)
	{
		clret |= clSetKernelArg(ocl->recover_kernel, 0, sizeof(cl_mem), (void *)&a_mem_obj);
		clret |= clSetKernelArg(ocl->recover_kernel, 1, sizeof(cl_mem), (void *)&b_mem_obj);
		clret |= clSetKernelArg(ocl->recover_kernel, 2, sizeof(cl_mem), (void *)&c_mem_obj);
		clret |= clSetKernelArg(ocl->recover_kernel, 3, sizeof(cl_mem), (void *)&d_mem_obj);

		if(CL_SUCCESS == clret)	
		{
			global_item_size = LIST_SIZE;
			clret |= clEnqueueNDRangeKernel(command_queue, ocl->recover_kernel, 1, NULL,
					&global_item_size, NULL, 0, NULL, NULL);	 
			clret |= clEnqueueReadBuffer(command_queue, d_mem_obj, CL_TRUE, 0, 
					LIST_SIZE*sizeof(EthPubkey), pubkeyall, 0, NULL, NULL);			
		}
		
	}

    clFlush(command_queue);
    clReleaseMemObject(a_mem_obj);
    clReleaseMemObject(b_mem_obj);
    clReleaseMemObject(c_mem_obj);
    clReleaseMemObject(d_mem_obj);
    clReleaseCommandQueue(command_queue);

	if(CL_SUCCESS != clret)
	{
		result = 0;
	}

    return result;
}

static secp256k1_ocl gocl;
int secp256_ocl_init(unsigned char *code, int codelen, int mode)
{
	memset(&gocl, 0, sizeof(gocl));
    if (NULL == gocl.context)
    {
        if (0 != init_opencl(&gocl,code, codelen, mode))
        {
            printf("init opencl failed\n");
            return -1;
        }
    }
    return 0;
}

int secp256_ocl_destory()
{
    release_ocl(&gocl);
	return 1;
}

int secp256k1_ecdsa_recover_ocl(int count, ocl_recoverable_signature*rsigall, 
	ocl_msg *msgall, ocl_pubkey *pubkeyall) 
{
	if(gocl.arr == NULL || gocl.context == NULL)
	{
		printf("handle not init");
		return 0;
	}
	return recover_ocl(&gocl, count, (secp256k1_ecdsa_recoverable_signature*)rsigall, 
		(Msg32*)msgall, (EthPubkey*)pubkeyall);
}

int secp256k1_ecdsa_verify_ocl(int count, ocl_signature *sigall, 
	ocl_msg *msg32all, ocl_pubkey *pubkeyall, int *resall) 
{
	if(gocl.arr == NULL || gocl.context == NULL)
	{
		printf("handle not init");
		return 0;
	}

	return verify_ocl(&gocl, count, (secp256k1_ecdsa_signature *)sigall, 
		(const Msg32*)msg32all, (const EthPubkey*)pubkeyall, resall);
}
