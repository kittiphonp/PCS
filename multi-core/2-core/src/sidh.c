/********************************************************************************************
* SIDH: an efficient supersingular isogeny cryptography library
*
* Abstract: ephemeral supersingular isogeny Diffie-Hellman key exchange (SIDH)
*********************************************************************************************/ 

#include "random/random.h"

#if defined PARALLEL

#include <omp.h>
#include<pthread.h>
#endif

static void clear_words(void* mem, digit_t nwords)
{ // Clear digits from memory. "nwords" indicates the number of digits to be zeroed.
  // This function uses the volatile type qualifier to inform the compiler not to optimize out the memory clearing.
    unsigned int i;
    volatile digit_t *v = mem; 

    for (i = 0; i < nwords; i++) {
        v[i] = 0;
    }
}


static void init_basis(digit_t *gen, f2elm_t XP, f2elm_t XQ, f2elm_t XR)
{ // Initialization of basis points

    fpcopy(gen,                  XP[0]);
    fpcopy(gen +   NWORDS_FIELD, XP[1]);
    fpcopy(gen + 2*NWORDS_FIELD, XQ[0]);
    fpzero(XQ[1]);
    fpcopy(gen + 3*NWORDS_FIELD, XR[0]);
    fpcopy(gen + 4*NWORDS_FIELD, XR[1]);
}

static void fp2_encode(const f2elm_t x, unsigned char *enc)
{ // Conversion of GF(p^2) element from Montgomery to standard representation, and encoding by removing leading 0 bytes
    unsigned int i;
    f2elm_t t;

    from_fp2mont(x, t);

    for (i = 0; i < FP2_ENCODED_BYTES / 2; i++) {
        enc[i] = ((unsigned char*)t)[i];
        enc[i + FP2_ENCODED_BYTES / 2] = ((unsigned char*)t)[i + MAXBITS_FIELD / 8];
    }
}


static void fp2_decode(const unsigned char *enc, f2elm_t x)
{ // Parse byte sequence back into GF(p^2) element, and conversion to Montgomery representation
    unsigned int i;

    for (i = 0; i < 2*(MAXBITS_FIELD / 8); i++) ((unsigned char *)x)[i] = 0;
    for (i = 0; i < FP2_ENCODED_BYTES / 2; i++) {
        ((unsigned char*)x)[i] = enc[i];
        ((unsigned char*)x)[i + MAXBITS_FIELD / 8] = enc[i + FP2_ENCODED_BYTES / 2];
    }
    to_fp2mont(x, x);
}

void random_mod_order_A(unsigned char* random_digits)
{  // Generation of Alice's secret key  
   // Outputs random value in [0, 2^eA - 1]
    unsigned long long nbytes = NBITS_TO_NBYTES(OALICE_BITS);

    clear_words((void*)random_digits, MAXWORDS_ORDER);
    randombytes(random_digits, nbytes);
    random_digits[nbytes-1] &= MASK_ALICE;    // Masking last byte 
    

}

#if ((BOB_PRIMES == 1))

void random_mod_order_B(unsigned char* random_digits)
{  // Generation of Bob's secret key  
   // Outputs random value in [0, 2^Floor(Log(2, oB)) - 1]
    unsigned long long nbytes = NBITS_TO_NBYTES(OBOB_BITS-1);

    clear_words((void*)random_digits, MAXWORDS_ORDER);
    randombytes(random_digits, nbytes);
    random_digits[nbytes-1] &= MASK_BOB;     // Masking last byte 
}

#else

void random_mod_order_B(unsigned char* random_digits)
{  // Generation of Bob's secret key  
   // Outputs random value in [0, 2^Floor(Log(2, oB)) - 1]
    unsigned long long nbytes = NBITS_TO_NBYTES(MAXWORDS_ORDER*64);

    clear_words((void*)random_digits, MAXWORDS_ORDER);
    randombytes(random_digits, nbytes);
    random_digits[(nbytes/2)-1] &= MASK_BOB;     // Masking last byte
    random_digits[nbytes-1] &= MASK_BOB1;             // Masking last byte
}

#endif





int EphemeralKeyGeneration_A(const unsigned char* PrivateKeyA, unsigned char* PublicKeyA) {
    point_proj_t phiP = {0}, phiQ = {0}, phiR = {0}, pts[1407];
    f2elm_t XPA, XQA, XRA, coeff[MAX_Alice][3], A24plus[MAX_Alice+1] = {0}, C24[MAX_Alice+1] = {0}, A = {0};
    char lock1[2], lock[184][2];

    for(int i = 0; i < 2; i++)
        lock1[i] = 1;

    for(int i = 0; i < 184; i++)
        for(int j = 0; j < 2; j++)
            lock[i][j] = 1;

    init_basis((digit_t*)A_gen, XPA, XQA, XRA);
    init_basis((digit_t*)B_gen, phiP->X, phiQ->X, phiR->X);
    fpcopy((digit_t*)&Montgomery_one, (phiP->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, (phiQ->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, (phiR->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, A24plus[0][0]);
    fp2add(A24plus[0], A24plus[0], C24[0]);

    omp_set_num_threads(2);
    #pragma omp parallel
    {
        #pragma omp sections
        {
            #pragma omp section
            {
                LADDER3PT_NS_prcmp(XPA, XRA, (digit_t*)PrivateKeyA, ALICE, pts[0], A, 2*186);
                lock1[0] = 0;
                while(lock1[1]) {
                    #pragma omp flush(lock1[1])
                }

                eval_4_isog_mod(pts[81], pts[100], coeff[0]);
                eval_4_isog_mod(pts[99], pts[103], coeff[2]);
                eval_4_isog_mod(pts[100], pts[104], coeff[1]);
                lock[0][0] = 0;
                while(lock[0][1]) {
                    #pragma omp flush(lock[0][1])
                }

                eval_4_isog_mod(pts[104], pts[107], coeff[2]);
                eval_4_isog_mod(pts[76], pts[108], coeff[0]);
                lock[1][0] = 0;
                while(lock[1][1]) {
                    #pragma omp flush(lock[1][1])
                }

                eval_4_isog_mod(pts[108], pts[111], coeff[1]);
                xDBLe(pts[109], pts[112], A24plus[5], C24[5], 2);
                get_4_isog(pts[112], A24plus[6], C24[6], coeff[5]);
                lock[2][0] = 0;
                while(lock[2][1]) {
                    #pragma omp flush(lock[2][1])
                }

                eval_4_isog_mod(pts[109], pts[115], coeff[5]);
                get_4_isog(pts[115], A24plus[7], C24[7], coeff[6]);
                eval_4_isog_mod(pts[113], pts[116], coeff[5]);
                eval_4_isog_mod(pts[116], pts[118], coeff[6]);
                xDBLe(pts[118], pts[120], A24plus[7], C24[7], 2);
                xDBLe(pts[120], pts[123], A24plus[7], C24[7], 2);
                get_4_isog(pts[123], A24plus[8], C24[8], coeff[7]);
                lock[3][0] = 0;
                while(lock[3][1]) {
                    #pragma omp flush(lock[3][1])
                }

                eval_4_isog_mod(pts[121], pts[124], coeff[6]);
                eval_4_isog_mod(pts[118], pts[127], coeff[7]);
                eval_4_isog_mod(pts[124], pts[128], coeff[7]);
                lock[4][0] = 0;
                while(lock[4][1]) {
                    #pragma omp flush(lock[4][1])
                }

                eval_4_isog_mod(pts[128], pts[131], coeff[8]);
                lock[5][0] = 0;
                while(lock[5][1]) {
                    #pragma omp flush(lock[5][1])
                }

                eval_4_isog_mod(pts[131], pts[133], coeff[9]);
                xDBLe(pts[133], pts[135], A24plus[10], C24[10], 2);
                xDBLe(pts[135], pts[137], A24plus[10], C24[10], 2);
                xDBLe(pts[137], pts[139], A24plus[10], C24[10], 2);
                xDBLe(pts[139], pts[141], A24plus[10], C24[10], 2);
                get_4_isog(pts[141], A24plus[11], C24[11], coeff[10]);
                eval_4_isog_mod(pts[139], pts[143], coeff[10]);
                get_4_isog(pts[143], A24plus[12], C24[12], coeff[11]);
                lock[6][0] = 0;
                while(lock[6][1]) {
                    #pragma omp flush(lock[6][1])
                }

                eval_4_isog_mod(pts[137], pts[144], coeff[10]);
                eval_4_isog_mod(pts[144], pts[147], coeff[11]);
                get_4_isog(pts[147], A24plus[13], C24[13], coeff[12]);
                lock[7][0] = 0;
                while(lock[7][1]) {
                    #pragma omp flush(lock[7][1])
                }

                eval_4_isog_mod(pts[146], pts[149], coeff[10]);
                eval_4_isog_mod(pts[55], pts[150], coeff[0]);
                lock[8][0] = 0;
                while(lock[8][1]) {
                    #pragma omp flush(lock[8][1])
                }

                eval_4_isog_mod(pts[149], pts[152], coeff[11]);
                eval_4_isog_mod(pts[152], pts[155], coeff[12]);
                lock[9][0] = 0;
                while(lock[9][1]) {
                    #pragma omp flush(lock[9][1])
                }

                eval_4_isog_mod(pts[153], pts[156], coeff[2]);
                eval_4_isog_mod(pts[156], pts[159], coeff[3]);
                eval_4_isog_mod(pts[159], pts[161], coeff[4]);
                eval_4_isog_mod(pts[161], pts[163], coeff[5]);
                eval_4_isog_mod(pts[163], pts[165], coeff[6]);
                eval_4_isog_mod(pts[165], pts[167], coeff[7]);
                eval_4_isog_mod(pts[167], pts[169], coeff[8]);
                eval_4_isog_mod(pts[169], pts[171], coeff[9]);
                eval_4_isog_mod(pts[171], pts[173], coeff[10]);
                eval_4_isog_mod(pts[173], pts[175], coeff[11]);
                lock[10][0] = 0;
                while(lock[10][1]) {
                    #pragma omp flush(lock[10][1])
                }

                eval_4_isog_mod(pts[170], pts[177], coeff[15]);
                eval_4_isog_mod(pts[166], pts[178], coeff[15]);
                lock[11][0] = 0;
                while(lock[11][1]) {
                    #pragma omp flush(lock[11][1])
                }

                eval_4_isog_mod(pts[178], pts[181], coeff[16]);
                eval_4_isog_mod(pts[179], pts[183], coeff[13]);
                lock[12][0] = 0;
                while(lock[12][1]) {
                    #pragma omp flush(lock[12][1])
                }

                eval_4_isog_mod(pts[182], pts[185], coeff[16]);
                eval_4_isog_mod(pts[183], pts[186], coeff[14]);
                lock[13][0] = 0;
                while(lock[13][1]) {
                    #pragma omp flush(lock[13][1])
                }

                eval_4_isog_mod(pts[186], pts[189], coeff[15]);
                eval_4_isog_mod(pts[184], pts[190], coeff[18]);
                get_4_isog(pts[190], A24plus[20], C24[20], coeff[19]);
                lock[14][0] = 0;
                while(lock[14][1]) {
                    #pragma omp flush(lock[14][1])
                }

                eval_4_isog_mod(pts[189], pts[192], coeff[16]);
                eval_4_isog_mod(pts[192], pts[194], coeff[17]);
                eval_4_isog_mod(pts[194], pts[196], coeff[18]);
                eval_4_isog_mod(pts[196], pts[198], coeff[19]);
                lock[15][0] = 0;
                while(lock[15][1]) {
                    #pragma omp flush(lock[15][1])
                }

                eval_4_isog_mod(pts[193], pts[200], coeff[20]);
                eval_4_isog_mod(pts[200], pts[203], coeff[21]);
                get_4_isog(pts[203], A24plus[23], C24[23], coeff[22]);
                lock[16][0] = 0;
                while(lock[16][1]) {
                    #pragma omp flush(lock[16][1])
                }

                eval_4_isog_mod(pts[202], pts[205], coeff[1]);
                eval_4_isog_mod(pts[205], pts[207], coeff[2]);
                eval_4_isog_mod(pts[207], pts[209], coeff[3]);
                eval_4_isog_mod(pts[209], pts[211], coeff[4]);
                eval_4_isog_mod(pts[211], pts[213], coeff[5]);
                eval_4_isog_mod(pts[213], pts[215], coeff[6]);
                eval_4_isog_mod(pts[215], pts[217], coeff[7]);
                eval_4_isog_mod(pts[217], pts[219], coeff[8]);
                eval_4_isog_mod(pts[219], pts[221], coeff[9]);
                eval_4_isog_mod(pts[221], pts[223], coeff[10]);
                eval_4_isog_mod(pts[223], pts[225], coeff[11]);
                eval_4_isog_mod(pts[225], pts[227], coeff[12]);
                eval_4_isog_mod(pts[227], pts[229], coeff[13]);
                eval_4_isog_mod(pts[229], pts[231], coeff[14]);
                lock[17][0] = 0;
                while(lock[17][1]) {
                    #pragma omp flush(lock[17][1])
                }

                eval_4_isog_mod(pts[226], pts[233], coeff[23]);
                eval_4_isog_mod(pts[231], pts[235], coeff[15]);
                lock[18][0] = 0;
                while(lock[18][1]) {
                    #pragma omp flush(lock[18][1])
                }

                eval_4_isog_mod(pts[233], pts[236], coeff[24]);
                get_4_isog(pts[236], A24plus[26], C24[26], coeff[25]);
                eval_4_isog_mod(pts[216], pts[238], coeff[23]);
                lock[19][0] = 0;
                while(lock[19][1]) {
                    #pragma omp flush(lock[19][1])
                }

                eval_4_isog_mod(pts[238], pts[241], coeff[24]);
                eval_4_isog_mod(pts[239], pts[242], coeff[17]);
                eval_4_isog_mod(pts[241], pts[244], coeff[25]);
                eval_4_isog_mod(pts[242], pts[246], coeff[18]);
                lock[20][0] = 0;
                while(lock[20][1]) {
                    #pragma omp flush(lock[20][1])
                }

                eval_4_isog_mod(pts[245], pts[249], coeff[24]);
                eval_4_isog_mod(pts[246], pts[250], coeff[19]);
                lock[21][0] = 0;
                while(lock[21][1]) {
                    #pragma omp flush(lock[21][1])
                }

                eval_4_isog_mod(pts[249], pts[252], coeff[25]);
                eval_4_isog_mod(pts[252], pts[255], coeff[26]);
                lock[22][0] = 0;
                while(lock[22][1]) {
                    #pragma omp flush(lock[22][1])
                }

                eval_4_isog_mod(pts[253], pts[256], coeff[21]);
                eval_4_isog_mod(pts[256], pts[259], coeff[22]);
                lock[23][0] = 0;
                while(lock[23][1]) {
                    #pragma omp flush(lock[23][1])
                }

                eval_4_isog_mod(pts[251], pts[261], coeff[28]);
                eval_4_isog_mod(pts[258], pts[262], coeff[28]);
                lock[24][0] = 0;
                while(lock[24][1]) {
                    #pragma omp flush(lock[24][1])
                }

                eval_4_isog_mod(pts[262], pts[265], coeff[29]);
                lock[25][0] = 0;
                while(lock[25][1]) {
                    #pragma omp flush(lock[25][1])
                }

                eval_4_isog_mod(pts[265], pts[267], coeff[30]);
                xDBLe(pts[267], pts[269], A24plus[31], C24[31], 2);
                xDBLe(pts[269], pts[271], A24plus[31], C24[31], 2);
                xDBLe(pts[271], pts[273], A24plus[31], C24[31], 2);
                xDBLe(pts[273], pts[275], A24plus[31], C24[31], 2);
                get_4_isog(pts[275], A24plus[32], C24[32], coeff[31]);
                eval_4_isog_mod(pts[273], pts[277], coeff[31]);
                get_4_isog(pts[277], A24plus[33], C24[33], coeff[32]);
                lock[26][0] = 0;
                while(lock[26][1]) {
                    #pragma omp flush(lock[26][1])
                }

                eval_4_isog_mod(pts[267], pts[279], coeff[31]);
                eval_4_isog_mod(pts[276], pts[280], coeff[30]);
                lock[27][0] = 0;
                while(lock[27][1]) {
                    #pragma omp flush(lock[27][1])
                }

                eval_4_isog_mod(pts[279], pts[282], coeff[32]);
                eval_4_isog_mod(pts[282], pts[284], coeff[33]);
                xDBLe(pts[284], pts[286], A24plus[34], C24[34], 2);
                get_4_isog(pts[286], A24plus[35], C24[35], coeff[34]);
                lock[28][0] = 0;
                while(lock[28][1]) {
                    #pragma omp flush(lock[28][1])
                }

                eval_4_isog_mod(pts[284], pts[288], coeff[34]);
                get_4_isog(pts[288], A24plus[36], C24[36], coeff[35]);
                lock[29][0] = 0;
                while(lock[29][1]) {
                    #pragma omp flush(lock[29][1])
                }

                eval_4_isog_mod(pts[1], pts[291], coeff[0]);
                eval_4_isog_mod(pts[291], pts[293], coeff[1]);
                eval_4_isog_mod(pts[293], pts[295], coeff[2]);
                eval_4_isog_mod(pts[295], pts[297], coeff[3]);
                eval_4_isog_mod(pts[297], pts[299], coeff[4]);
                eval_4_isog_mod(pts[299], pts[301], coeff[5]);
                eval_4_isog_mod(pts[301], pts[303], coeff[6]);
                eval_4_isog_mod(pts[303], pts[305], coeff[7]);
                eval_4_isog_mod(pts[305], pts[307], coeff[8]);
                eval_4_isog_mod(pts[307], pts[309], coeff[9]);
                eval_4_isog_mod(pts[309], pts[311], coeff[10]);
                eval_4_isog_mod(pts[311], pts[313], coeff[11]);
                eval_4_isog_mod(pts[313], pts[315], coeff[12]);
                eval_4_isog_mod(pts[315], pts[317], coeff[13]);
                eval_4_isog_mod(pts[317], pts[319], coeff[14]);
                eval_4_isog_mod(pts[319], pts[321], coeff[15]);
                eval_4_isog_mod(pts[321], pts[323], coeff[16]);
                eval_4_isog_mod(pts[323], pts[325], coeff[17]);
                eval_4_isog_mod(pts[325], pts[327], coeff[18]);
                eval_4_isog_mod(pts[327], pts[329], coeff[19]);
                eval_4_isog_mod(pts[329], pts[331], coeff[20]);
                lock[30][0] = 0;
                while(lock[30][1]) {
                    #pragma omp flush(lock[30][1])
                }

                eval_4_isog_mod(pts[328], pts[332], coeff[36]);
                get_4_isog(pts[332], A24plus[38], C24[38], coeff[37]);
                lock[31][0] = 0;
                while(lock[31][1]) {
                    #pragma omp flush(lock[31][1])
                }

                eval_4_isog_mod(pts[322], pts[334], coeff[36]);
                eval_4_isog_mod(pts[334], pts[336], coeff[37]);
                lock[32][0] = 0;
                while(lock[32][1]) {
                    #pragma omp flush(lock[32][1])
                }

                eval_4_isog_mod(pts[336], pts[338], coeff[38]);
                xDBLe(pts[338], pts[340], A24plus[39], C24[39], 2);
                get_4_isog(pts[340], A24plus[40], C24[40], coeff[39]);
                eval_4_isog_mod(pts[331], pts[343], coeff[21]);
                lock[33][0] = 0;
                while(lock[33][1]) {
                    #pragma omp flush(lock[33][1])
                }

                eval_4_isog_mod(pts[341], pts[345], coeff[39]);
                eval_4_isog_mod(pts[342], pts[346], coeff[37]);
                lock[34][0] = 0;
                while(lock[34][1]) {
                    #pragma omp flush(lock[34][1])
                }

                eval_4_isog_mod(pts[345], pts[348], coeff[40]);
                xDBLe(pts[348], pts[351], A24plus[41], C24[41], 2);
                lock[35][0] = 0;
                while(lock[35][1]) {
                    #pragma omp flush(lock[35][1])
                }

                eval_4_isog_mod(pts[349], pts[352], coeff[39]);
                eval_4_isog_mod(pts[352], pts[355], coeff[40]);
                lock[36][0] = 0;
                while(lock[36][1]) {
                    #pragma omp flush(lock[36][1])
                }

                eval_4_isog_mod(pts[351], pts[357], coeff[41]);
                get_4_isog(pts[357], A24plus[43], C24[43], coeff[42]);
                eval_4_isog_mod(pts[355], pts[359], coeff[41]);
                eval_4_isog_mod(pts[290], pts[360], coeff[36]);
                lock[37][0] = 0;
                while(lock[37][1]) {
                    #pragma omp flush(lock[37][1])
                }

                eval_4_isog_mod(pts[359], pts[363], coeff[42]);
                eval_4_isog_mod(pts[360], pts[364], coeff[37]);
                lock[38][0] = 0;
                while(lock[38][1]) {
                    #pragma omp flush(lock[38][1])
                }

                eval_4_isog_mod(pts[363], pts[366], coeff[43]);
                xDBLe(pts[366], pts[369], A24plus[44], C24[44], 2);
                lock[39][0] = 0;
                while(lock[39][1]) {
                    #pragma omp flush(lock[39][1])
                }

                eval_4_isog_mod(pts[368], pts[371], coeff[29]);
                xDBLe(pts[369], pts[372], A24plus[44], C24[44], 2);
                lock[40][0] = 0;
                while(lock[40][1]) {
                    #pragma omp flush(lock[40][1])
                }

                xDBLe(pts[372], pts[375], A24plus[44], C24[44], 2);
                eval_4_isog_mod(pts[373], pts[376], coeff[41]);
                lock[41][0] = 0;
                while(lock[41][1]) {
                    #pragma omp flush(lock[41][1])
                }

                eval_4_isog_mod(pts[376], pts[379], coeff[42]);
                eval_4_isog_mod(pts[377], pts[380], coeff[32]);
                lock[42][0] = 0;
                while(lock[42][1]) {
                    #pragma omp flush(lock[42][1])
                }

                eval_4_isog_mod(pts[366], pts[383], coeff[44]);
                eval_4_isog_mod(pts[379], pts[384], coeff[43]);
                eval_4_isog_mod(pts[383], pts[387], coeff[45]);
                eval_4_isog_mod(pts[384], pts[388], coeff[44]);
                lock[43][0] = 0;
                while(lock[43][1]) {
                    #pragma omp flush(lock[43][1])
                }

                eval_4_isog_mod(pts[387], pts[390], coeff[46]);
                xDBLe(pts[390], pts[393], A24plus[47], C24[47], 2);
                get_4_isog(pts[393], A24plus[48], C24[48], coeff[47]);
                lock[44][0] = 0;
                while(lock[44][1]) {
                    #pragma omp flush(lock[44][1])
                }

                eval_4_isog_mod(pts[391], pts[394], coeff[46]);
                eval_4_isog_mod(pts[394], pts[397], coeff[47]);
                lock[45][0] = 0;
                while(lock[45][1]) {
                    #pragma omp flush(lock[45][1])
                }

                eval_4_isog_mod(pts[397], pts[399], coeff[48]);
                xDBLe(pts[399], pts[401], A24plus[49], C24[49], 2);
                xDBLe(pts[401], pts[403], A24plus[49], C24[49], 2);
                xDBLe(pts[403], pts[405], A24plus[49], C24[49], 2);
                xDBLe(pts[405], pts[407], A24plus[49], C24[49], 2);
                xDBLe(pts[407], pts[409], A24plus[49], C24[49], 2);
                xDBLe(pts[409], pts[411], A24plus[49], C24[49], 2);
                xDBLe(pts[411], pts[413], A24plus[49], C24[49], 2);
                get_4_isog(pts[413], A24plus[50], C24[50], coeff[49]);
                eval_4_isog_mod(pts[411], pts[415], coeff[49]);
                get_4_isog(pts[415], A24plus[51], C24[51], coeff[50]);
                lock[46][0] = 0;
                while(lock[46][1]) {
                    #pragma omp flush(lock[46][1])
                }

                eval_4_isog_mod(pts[409], pts[416], coeff[49]);
                eval_4_isog_mod(pts[416], pts[419], coeff[50]);
                get_4_isog(pts[419], A24plus[52], C24[52], coeff[51]);
                eval_4_isog_mod(pts[399], pts[421], coeff[49]);
                lock[47][0] = 0;
                while(lock[47][1]) {
                    #pragma omp flush(lock[47][1])
                }

                eval_4_isog_mod(pts[418], pts[422], coeff[47]);
                eval_4_isog_mod(pts[422], pts[425], coeff[48]);
                lock[48][0] = 0;
                while(lock[48][1]) {
                    #pragma omp flush(lock[48][1])
                }

                xDBLe(pts[423], pts[426], A24plus[52], C24[52], 2);
                get_4_isog(pts[426], A24plus[53], C24[53], coeff[52]);
                lock[49][0] = 0;
                while(lock[49][1]) {
                    #pragma omp flush(lock[49][1])
                }

                eval_4_isog_mod(pts[425], pts[428], coeff[49]);
                eval_4_isog_mod(pts[428], pts[431], coeff[50]);
                eval_4_isog_mod(pts[431], pts[433], coeff[51]);
                eval_4_isog_mod(pts[433], pts[435], coeff[52]);
                lock[50][0] = 0;
                while(lock[50][1]) {
                    #pragma omp flush(lock[50][1])
                }

                xDBLe(pts[434], pts[436], A24plus[54], C24[54], 2);
                get_4_isog(pts[436], A24plus[55], C24[55], coeff[54]);
                lock[51][0] = 0;
                while(lock[51][1]) {
                    #pragma omp flush(lock[51][1])
                }

                eval_4_isog_mod(pts[432], pts[439], coeff[54]);
                lock[52][0] = 0;
                while(lock[52][1]) {
                    #pragma omp flush(lock[52][1])
                }

                eval_4_isog_mod(pts[437], pts[440], coeff[54]);
                eval_4_isog_mod(pts[440], pts[442], coeff[55]);
                lock[53][0] = 0;
                while(lock[53][1]) {
                    #pragma omp flush(lock[53][1])
                }

                eval_4_isog_mod(pts[442], pts[444], coeff[56]);
                xDBLe(pts[444], pts[446], A24plus[57], C24[57], 2);
                xDBLe(pts[446], pts[448], A24plus[57], C24[57], 2);
                xDBLe(pts[448], pts[450], A24plus[57], C24[57], 2);
                xDBLe(pts[450], pts[452], A24plus[57], C24[57], 2);
                xDBLe(pts[452], pts[454], A24plus[57], C24[57], 2);
                xDBLe(pts[454], pts[456], A24plus[57], C24[57], 2);
                xDBLe(pts[456], pts[458], A24plus[57], C24[57], 2);
                xDBLe(pts[458], pts[460], A24plus[57], C24[57], 2);
                xDBLe(pts[460], pts[462], A24plus[57], C24[57], 2);
                xDBLe(pts[462], pts[464], A24plus[57], C24[57], 2);
                xDBLe(pts[464], pts[466], A24plus[57], C24[57], 2);
                xDBLe(pts[466], pts[468], A24plus[57], C24[57], 2);
                xDBLe(pts[468], pts[470], A24plus[57], C24[57], 2);
                xDBLe(pts[470], pts[472], A24plus[57], C24[57], 2);
                xDBLe(pts[472], pts[474], A24plus[57], C24[57], 2);
                xDBLe(pts[474], pts[476], A24plus[57], C24[57], 2);
                xDBLe(pts[476], pts[478], A24plus[57], C24[57], 2);
                xDBLe(pts[478], pts[480], A24plus[57], C24[57], 2);
                xDBLe(pts[480], pts[482], A24plus[57], C24[57], 2);
                xDBLe(pts[482], pts[484], A24plus[57], C24[57], 2);
                xDBLe(pts[484], pts[486], A24plus[57], C24[57], 2);
                xDBLe(pts[486], pts[488], A24plus[57], C24[57], 2);
                xDBLe(pts[488], pts[490], A24plus[57], C24[57], 2);
                xDBLe(pts[490], pts[492], A24plus[57], C24[57], 2);
                xDBLe(pts[492], pts[494], A24plus[57], C24[57], 2);
                xDBLe(pts[494], pts[496], A24plus[57], C24[57], 2);
                xDBLe(pts[496], pts[498], A24plus[57], C24[57], 2);
                xDBLe(pts[498], pts[500], A24plus[57], C24[57], 2);
                xDBLe(pts[500], pts[502], A24plus[57], C24[57], 2);
                xDBLe(pts[502], pts[504], A24plus[57], C24[57], 2);
                xDBLe(pts[504], pts[506], A24plus[57], C24[57], 2);
                xDBLe(pts[506], pts[508], A24plus[57], C24[57], 2);
                get_4_isog(pts[508], A24plus[58], C24[58], coeff[57]);
                lock[54][0] = 0;
                while(lock[54][1]) {
                    #pragma omp flush(lock[54][1])
                }

                eval_4_isog_mod(pts[506], pts[510], coeff[57]);
                get_4_isog(pts[510], A24plus[59], C24[59], coeff[58]);
                lock[55][0] = 0;
                while(lock[55][1]) {
                    #pragma omp flush(lock[55][1])
                }

                eval_4_isog_mod(pts[511], pts[513], coeff[58]);
                get_4_isog(pts[513], A24plus[60], C24[60], coeff[59]);
                eval_4_isog_mod(pts[494], pts[515], coeff[57]);
                lock[56][0] = 0;
                while(lock[56][1]) {
                    #pragma omp flush(lock[56][1])
                }

                eval_4_isog_mod(pts[515], pts[517], coeff[58]);
                eval_4_isog_mod(pts[517], pts[519], coeff[59]);
                eval_4_isog_mod(pts[484], pts[520], coeff[57]);
                lock[57][0] = 0;
                while(lock[57][1]) {
                    #pragma omp flush(lock[57][1])
                }

                eval_4_isog_mod(pts[520], pts[523], coeff[58]);
                eval_4_isog_mod(pts[523], pts[525], coeff[59]);
                eval_4_isog_mod(pts[525], pts[527], coeff[60]);
                eval_4_isog_mod(pts[527], pts[529], coeff[61]);
                lock[58][0] = 0;
                while(lock[58][1]) {
                    #pragma omp flush(lock[58][1])
                }

                eval_4_isog_mod(pts[526], pts[530], coeff[62]);
                get_4_isog(pts[530], A24plus[64], C24[64], coeff[63]);
                eval_4_isog_mod(pts[529], pts[532], coeff[62]);
                lock[59][0] = 0;
                while(lock[59][1]) {
                    #pragma omp flush(lock[59][1])
                }

                eval_4_isog_mod(pts[531], pts[534], coeff[63]);
                get_4_isog(pts[534], A24plus[65], C24[65], coeff[64]);
                lock[60][0] = 0;
                while(lock[60][1]) {
                    #pragma omp flush(lock[60][1])
                }

                eval_4_isog_mod(pts[535], pts[537], coeff[64]);
                xDBLe(pts[537], pts[539], A24plus[65], C24[65], 2);
                xDBLe(pts[539], pts[541], A24plus[65], C24[65], 2);
                eval_4_isog_mod(pts[509], pts[543], coeff[34]);
                xDBLe(pts[541], pts[544], A24plus[65], C24[65], 2);
                lock[61][0] = 0;
                while(lock[61][1]) {
                    #pragma omp flush(lock[61][1])
                }

                xDBLe(pts[544], pts[547], A24plus[65], C24[65], 2);
                get_4_isog(pts[547], A24plus[66], C24[66], coeff[65]);
                eval_4_isog_mod(pts[545], pts[548], coeff[63]);
                lock[62][0] = 0;
                while(lock[62][1]) {
                    #pragma omp flush(lock[62][1])
                }

                eval_4_isog_mod(pts[544], pts[550], coeff[65]);
                get_4_isog(pts[550], A24plus[67], C24[67], coeff[66]);
                eval_4_isog_mod(pts[548], pts[553], coeff[64]);
                lock[63][0] = 0;
                while(lock[63][1]) {
                    #pragma omp flush(lock[63][1])
                }

                eval_4_isog_mod(pts[549], pts[554], coeff[37]);
                eval_4_isog_mod(pts[552], pts[556], coeff[66]);
                lock[64][0] = 0;
                while(lock[64][1]) {
                    #pragma omp flush(lock[64][1])
                }

                eval_4_isog_mod(pts[554], pts[558], coeff[38]);
                eval_4_isog_mod(pts[558], pts[561], coeff[39]);
                lock[65][0] = 0;
                while(lock[65][1]) {
                    #pragma omp flush(lock[65][1])
                }

                xDBLe(pts[559], pts[562], A24plus[68], C24[68], 2);
                get_4_isog(pts[562], A24plus[69], C24[69], coeff[68]);
                eval_4_isog_mod(pts[561], pts[565], coeff[40]);
                lock[66][0] = 0;
                while(lock[66][1]) {
                    #pragma omp flush(lock[66][1])
                }

                eval_4_isog_mod(pts[559], pts[566], coeff[68]);
                get_4_isog(pts[566], A24plus[70], C24[70], coeff[69]);
                eval_4_isog_mod(pts[564], pts[568], coeff[58]);
                lock[67][0] = 0;
                while(lock[67][1]) {
                    #pragma omp flush(lock[67][1])
                }

                eval_4_isog_mod(pts[567], pts[570], coeff[69]);
                xDBLe(pts[570], pts[573], A24plus[70], C24[70], 2);
                lock[68][0] = 0;
                while(lock[68][1]) {
                    #pragma omp flush(lock[68][1])
                }

                eval_4_isog_mod(pts[572], pts[575], coeff[43]);
                xDBLe(pts[573], pts[576], A24plus[70], C24[70], 2);
                lock[69][0] = 0;
                while(lock[69][1]) {
                    #pragma omp flush(lock[69][1])
                }

                xDBLe(pts[576], pts[579], A24plus[70], C24[70], 2);
                eval_4_isog_mod(pts[577], pts[580], coeff[62]);
                lock[70][0] = 0;
                while(lock[70][1]) {
                    #pragma omp flush(lock[70][1])
                }

                eval_4_isog_mod(pts[580], pts[583], coeff[63]);
                eval_4_isog_mod(pts[581], pts[584], coeff[46]);
                lock[71][0] = 0;
                while(lock[71][1]) {
                    #pragma omp flush(lock[71][1])
                }

                eval_4_isog_mod(pts[583], pts[586], coeff[64]);
                eval_4_isog_mod(pts[586], pts[589], coeff[65]);
                lock[72][0] = 0;
                while(lock[72][1]) {
                    #pragma omp flush(lock[72][1])
                }

                eval_4_isog_mod(pts[587], pts[590], coeff[48]);
                eval_4_isog_mod(pts[590], pts[593], coeff[49]);
                lock[73][0] = 0;
                while(lock[73][1]) {
                    #pragma omp flush(lock[73][1])
                }

                eval_4_isog_mod(pts[588], pts[594], coeff[70]);
                get_4_isog(pts[594], A24plus[72], C24[72], coeff[71]);
                eval_4_isog_mod(pts[579], pts[596], coeff[70]);
                lock[74][0] = 0;
                while(lock[74][1]) {
                    #pragma omp flush(lock[74][1])
                }

                eval_4_isog_mod(pts[593], pts[598], coeff[50]);
                eval_4_isog_mod(pts[570], pts[601], coeff[70]);
                eval_4_isog_mod(pts[598], pts[603], coeff[51]);
                eval_4_isog_mod(pts[601], pts[605], coeff[71]);
                eval_4_isog_mod(pts[603], pts[607], coeff[52]);
                lock[75][0] = 0;
                while(lock[75][1]) {
                    #pragma omp flush(lock[75][1])
                }

                eval_4_isog_mod(pts[605], pts[609], coeff[72]);
                eval_4_isog_mod(pts[606], pts[610], coeff[70]);
                lock[76][0] = 0;
                while(lock[76][1]) {
                    #pragma omp flush(lock[76][1])
                }

                eval_4_isog_mod(pts[609], pts[613], coeff[73]);
                eval_4_isog_mod(pts[610], pts[614], coeff[71]);
                lock[77][0] = 0;
                while(lock[77][1]) {
                    #pragma omp flush(lock[77][1])
                }

                eval_4_isog_mod(pts[613], pts[616], coeff[74]);
                xDBLe(pts[616], pts[619], A24plus[75], C24[75], 2);
                lock[78][0] = 0;
                while(lock[78][1]) {
                    #pragma omp flush(lock[78][1])
                }

                eval_4_isog_mod(pts[618], pts[621], coeff[56]);
                xDBLe(pts[619], pts[622], A24plus[75], C24[75], 2);
                get_4_isog(pts[622], A24plus[76], C24[76], coeff[75]);
                lock[79][0] = 0;
                while(lock[79][1]) {
                    #pragma omp flush(lock[79][1])
                }

                eval_4_isog_mod(pts[619], pts[625], coeff[75]);
                get_4_isog(pts[625], A24plus[77], C24[77], coeff[76]);
                eval_4_isog_mod(pts[616], pts[626], coeff[75]);
                eval_4_isog_mod(pts[626], pts[629], coeff[76]);
                get_4_isog(pts[629], A24plus[78], C24[78], coeff[77]);
                lock[80][0] = 0;
                while(lock[80][1]) {
                    #pragma omp flush(lock[80][1])
                }

                eval_4_isog_mod(pts[627], pts[630], coeff[76]);
                eval_4_isog_mod(pts[630], pts[632], coeff[77]);
                xDBLe(pts[632], pts[634], A24plus[78], C24[78], 2);
                xDBLe(pts[634], pts[636], A24plus[78], C24[78], 2);
                xDBLe(pts[636], pts[638], A24plus[78], C24[78], 2);
                xDBLe(pts[638], pts[640], A24plus[78], C24[78], 2);
                xDBLe(pts[640], pts[642], A24plus[78], C24[78], 2);
                xDBLe(pts[642], pts[644], A24plus[78], C24[78], 2);
                xDBLe(pts[644], pts[646], A24plus[78], C24[78], 2);
                xDBLe(pts[646], pts[648], A24plus[78], C24[78], 2);
                xDBLe(pts[648], pts[650], A24plus[78], C24[78], 2);
                xDBLe(pts[650], pts[652], A24plus[78], C24[78], 2);
                xDBLe(pts[652], pts[654], A24plus[78], C24[78], 2);
                get_4_isog(pts[654], A24plus[79], C24[79], coeff[78]);
                lock[81][0] = 0;
                while(lock[81][1]) {
                    #pragma omp flush(lock[81][1])
                }

                eval_4_isog_mod(pts[650], pts[657], coeff[78]);
                eval_4_isog_mod(pts[655], pts[659], coeff[72]);
                lock[82][0] = 0;
                while(lock[82][1]) {
                    #pragma omp flush(lock[82][1])
                }

                eval_4_isog_mod(pts[658], pts[661], coeff[79]);
                eval_4_isog_mod(pts[640], pts[662], coeff[78]);
                lock[83][0] = 0;
                while(lock[83][1]) {
                    #pragma omp flush(lock[83][1])
                }

                eval_4_isog_mod(pts[662], pts[665], coeff[79]);
                eval_4_isog_mod(pts[663], pts[666], coeff[74]);
                eval_4_isog_mod(pts[665], pts[668], coeff[80]);
                eval_4_isog_mod(pts[666], pts[670], coeff[75]);
                lock[84][0] = 0;
                while(lock[84][1]) {
                    #pragma omp flush(lock[84][1])
                }

                eval_4_isog_mod(pts[669], pts[673], coeff[79]);
                eval_4_isog_mod(pts[670], pts[674], coeff[76]);
                lock[85][0] = 0;
                while(lock[85][1]) {
                    #pragma omp flush(lock[85][1])
                }

                eval_4_isog_mod(pts[673], pts[676], coeff[80]);
                eval_4_isog_mod(pts[676], pts[679], coeff[81]);
                lock[86][0] = 0;
                while(lock[86][1]) {
                    #pragma omp flush(lock[86][1])
                }

                eval_4_isog_mod(pts[677], pts[680], coeff[78]);
                eval_4_isog_mod(pts[680], pts[683], coeff[79]);
                lock[87][0] = 0;
                while(lock[87][1]) {
                    #pragma omp flush(lock[87][1])
                }

                eval_4_isog_mod(pts[678], pts[684], coeff[83]);
                get_4_isog(pts[684], A24plus[85], C24[85], coeff[84]);
                eval_4_isog_mod(pts[682], pts[686], coeff[83]);
                lock[88][0] = 0;
                while(lock[88][1]) {
                    #pragma omp flush(lock[88][1])
                }

                eval_4_isog_mod(pts[686], pts[689], coeff[84]);
                lock[89][0] = 0;
                while(lock[89][1]) {
                    #pragma omp flush(lock[89][1])
                }

                eval_4_isog_mod(pts[689], pts[691], coeff[85]);
                xDBLe(pts[691], pts[693], A24plus[86], C24[86], 2);
                xDBLe(pts[693], pts[695], A24plus[86], C24[86], 2);
                xDBLe(pts[695], pts[697], A24plus[86], C24[86], 2);
                get_4_isog(pts[697], A24plus[87], C24[87], coeff[86]);
                eval_4_isog_mod(pts[695], pts[699], coeff[86]);
                get_4_isog(pts[699], A24plus[88], C24[88], coeff[87]);
                lock[90][0] = 0;
                while(lock[90][1]) {
                    #pragma omp flush(lock[90][1])
                }

                eval_4_isog_mod(pts[693], pts[700], coeff[86]);
                eval_4_isog_mod(pts[700], pts[703], coeff[87]);
                get_4_isog(pts[703], A24plus[89], C24[89], coeff[88]);
                lock[91][0] = 0;
                while(lock[91][1]) {
                    #pragma omp flush(lock[91][1])
                }

                eval_4_isog_mod(pts[701], pts[704], coeff[87]);
                eval_4_isog_mod(pts[704], pts[706], coeff[88]);
                get_4_isog(pts[706], A24plus[90], C24[90], coeff[89]);
                lock[92][0] = 0;
                while(lock[92][1]) {
                    #pragma omp flush(lock[92][1])
                }

                eval_4_isog_mod(pts[707], pts[708], coeff[89]);
                xDBLe(pts[708], pts[709], A24plus[90], C24[90], 2);
                xDBLe(pts[709], pts[710], A24plus[90], C24[90], 2);
                xDBLe(pts[710], pts[711], A24plus[90], C24[90], 2);
                xDBLe(pts[711], pts[712], A24plus[90], C24[90], 2);
                xDBLe(pts[712], pts[713], A24plus[90], C24[90], 2);
                xDBLe(pts[713], pts[714], A24plus[90], C24[90], 2);
                xDBLe(pts[714], pts[715], A24plus[90], C24[90], 2);
                xDBLe(pts[715], pts[716], A24plus[90], C24[90], 2);
                xDBLe(pts[716], pts[717], A24plus[90], C24[90], 2);
                xDBLe(pts[717], pts[718], A24plus[90], C24[90], 2);
                xDBLe(pts[718], pts[719], A24plus[90], C24[90], 2);
                xDBLe(pts[719], pts[720], A24plus[90], C24[90], 2);
                xDBLe(pts[720], pts[721], A24plus[90], C24[90], 2);
                xDBLe(pts[721], pts[722], A24plus[90], C24[90], 2);
                xDBLe(pts[722], pts[723], A24plus[90], C24[90], 2);
                xDBLe(pts[723], pts[724], A24plus[90], C24[90], 2);
                xDBLe(pts[724], pts[725], A24plus[90], C24[90], 2);
                xDBLe(pts[725], pts[726], A24plus[90], C24[90], 2);
                xDBLe(pts[726], pts[727], A24plus[90], C24[90], 2);
                xDBLe(pts[727], pts[728], A24plus[90], C24[90], 2);
                xDBLe(pts[728], pts[729], A24plus[90], C24[90], 2);
                xDBLe(pts[729], pts[730], A24plus[90], C24[90], 2);
                xDBLe(pts[730], pts[731], A24plus[90], C24[90], 2);
                xDBLe(pts[731], pts[732], A24plus[90], C24[90], 2);
                xDBLe(pts[732], pts[733], A24plus[90], C24[90], 2);
                xDBLe(pts[733], pts[734], A24plus[90], C24[90], 2);
                xDBLe(pts[734], pts[735], A24plus[90], C24[90], 2);
                xDBLe(pts[735], pts[736], A24plus[90], C24[90], 2);
                xDBLe(pts[736], pts[737], A24plus[90], C24[90], 2);
                xDBLe(pts[737], pts[738], A24plus[90], C24[90], 2);
                xDBLe(pts[738], pts[739], A24plus[90], C24[90], 2);
                xDBLe(pts[739], pts[740], A24plus[90], C24[90], 2);
                xDBLe(pts[740], pts[741], A24plus[90], C24[90], 2);
                xDBLe(pts[741], pts[742], A24plus[90], C24[90], 2);
                xDBLe(pts[742], pts[743], A24plus[90], C24[90], 2);
                xDBLe(pts[743], pts[744], A24plus[90], C24[90], 2);
                xDBLe(pts[744], pts[745], A24plus[90], C24[90], 2);
                xDBLe(pts[745], pts[746], A24plus[90], C24[90], 2);
                xDBLe(pts[746], pts[747], A24plus[90], C24[90], 2);
                xDBLe(pts[747], pts[748], A24plus[90], C24[90], 2);
                xDBLe(pts[748], pts[749], A24plus[90], C24[90], 2);
                xDBLe(pts[749], pts[750], A24plus[90], C24[90], 2);
                xDBLe(pts[750], pts[751], A24plus[90], C24[90], 2);
                xDBLe(pts[751], pts[752], A24plus[90], C24[90], 2);
                xDBLe(pts[752], pts[753], A24plus[90], C24[90], 2);
                xDBLe(pts[753], pts[754], A24plus[90], C24[90], 2);
                xDBLe(pts[754], pts[755], A24plus[90], C24[90], 2);
                xDBLe(pts[755], pts[756], A24plus[90], C24[90], 2);
                xDBLe(pts[756], pts[757], A24plus[90], C24[90], 2);
                xDBLe(pts[757], pts[758], A24plus[90], C24[90], 2);
                xDBLe(pts[758], pts[759], A24plus[90], C24[90], 2);
                xDBLe(pts[759], pts[760], A24plus[90], C24[90], 2);
                xDBLe(pts[760], pts[761], A24plus[90], C24[90], 2);
                xDBLe(pts[761], pts[762], A24plus[90], C24[90], 2);
                xDBLe(pts[762], pts[763], A24plus[90], C24[90], 2);
                xDBLe(pts[763], pts[764], A24plus[90], C24[90], 2);
                xDBLe(pts[764], pts[765], A24plus[90], C24[90], 2);
                xDBLe(pts[765], pts[766], A24plus[90], C24[90], 2);
                xDBLe(pts[766], pts[767], A24plus[90], C24[90], 2);
                xDBLe(pts[767], pts[768], A24plus[90], C24[90], 2);
                xDBLe(pts[768], pts[769], A24plus[90], C24[90], 2);
                xDBLe(pts[769], pts[770], A24plus[90], C24[90], 2);
                xDBLe(pts[770], pts[771], A24plus[90], C24[90], 2);
                xDBLe(pts[771], pts[772], A24plus[90], C24[90], 2);
                xDBLe(pts[772], pts[773], A24plus[90], C24[90], 2);
                xDBLe(pts[773], pts[774], A24plus[90], C24[90], 2);
                xDBLe(pts[774], pts[775], A24plus[90], C24[90], 2);
                xDBLe(pts[775], pts[776], A24plus[90], C24[90], 2);
                xDBLe(pts[776], pts[777], A24plus[90], C24[90], 2);
                xDBLe(pts[777], pts[778], A24plus[90], C24[90], 2);
                xDBLe(pts[778], pts[779], A24plus[90], C24[90], 2);
                xDBLe(pts[779], pts[780], A24plus[90], C24[90], 2);
                xDBLe(pts[780], pts[781], A24plus[90], C24[90], 2);
                xDBLe(pts[781], pts[782], A24plus[90], C24[90], 2);
                xDBLe(pts[782], pts[783], A24plus[90], C24[90], 2);
                xDBLe(pts[783], pts[784], A24plus[90], C24[90], 2);
                xDBLe(pts[784], pts[785], A24plus[90], C24[90], 2);
                xDBLe(pts[785], pts[786], A24plus[90], C24[90], 2);
                xDBLe(pts[786], pts[787], A24plus[90], C24[90], 2);
                xDBLe(pts[787], pts[788], A24plus[90], C24[90], 2);
                xDBLe(pts[788], pts[789], A24plus[90], C24[90], 2);
                xDBLe(pts[789], pts[790], A24plus[90], C24[90], 2);
                xDBLe(pts[790], pts[791], A24plus[90], C24[90], 2);
                xDBLe(pts[791], pts[792], A24plus[90], C24[90], 2);
                xDBLe(pts[792], pts[793], A24plus[90], C24[90], 2);
                xDBLe(pts[793], pts[794], A24plus[90], C24[90], 2);
                xDBLe(pts[794], pts[795], A24plus[90], C24[90], 2);
                xDBLe(pts[795], pts[796], A24plus[90], C24[90], 2);
                xDBLe(pts[796], pts[797], A24plus[90], C24[90], 2);
                xDBLe(pts[797], pts[798], A24plus[90], C24[90], 2);
                xDBLe(pts[798], pts[799], A24plus[90], C24[90], 2);
                xDBLe(pts[799], pts[800], A24plus[90], C24[90], 2);
                xDBLe(pts[800], pts[801], A24plus[90], C24[90], 2);
                xDBLe(pts[801], pts[802], A24plus[90], C24[90], 2);
                xDBLe(pts[802], pts[803], A24plus[90], C24[90], 2);
                get_4_isog(pts[803], A24plus[91], C24[91], coeff[90]);
                lock[93][0] = 0;
                while(lock[93][1]) {
                    #pragma omp flush(lock[93][1])
                }

                eval_4_isog_mod(pts[801], pts[805], coeff[90]);
                lock[94][0] = 0;
                while(lock[94][1]) {
                    #pragma omp flush(lock[94][1])
                }

                eval_4_isog_mod(pts[799], pts[806], coeff[90]);
                eval_4_isog_mod(pts[806], pts[808], coeff[91]);
                lock[95][0] = 0;
                while(lock[95][1]) {
                    #pragma omp flush(lock[95][1])
                }

                eval_4_isog_mod(pts[808], pts[810], coeff[92]);
                xDBLe(pts[810], pts[812], A24plus[93], C24[93], 2);
                get_4_isog(pts[812], A24plus[94], C24[94], coeff[93]);
                eval_4_isog_mod(pts[810], pts[815], coeff[93]);
                get_4_isog(pts[815], A24plus[95], C24[95], coeff[94]);
                lock[96][0] = 0;
                while(lock[96][1]) {
                    #pragma omp flush(lock[96][1])
                }

                eval_4_isog_mod(pts[814], pts[817], coeff[91]);
                eval_4_isog_mod(pts[817], pts[819], coeff[92]);
                eval_4_isog_mod(pts[819], pts[821], coeff[93]);
                eval_4_isog_mod(pts[821], pts[823], coeff[94]);
                lock[97][0] = 0;
                while(lock[97][1]) {
                    #pragma omp flush(lock[97][1])
                }

                eval_4_isog_mod(pts[820], pts[824], coeff[95]);
                get_4_isog(pts[824], A24plus[97], C24[97], coeff[96]);
                eval_4_isog_mod(pts[823], pts[826], coeff[95]);
                lock[98][0] = 0;
                while(lock[98][1]) {
                    #pragma omp flush(lock[98][1])
                }

                eval_4_isog_mod(pts[826], pts[829], coeff[96]);
                lock[99][0] = 0;
                while(lock[99][1]) {
                    #pragma omp flush(lock[99][1])
                }

                eval_4_isog_mod(pts[829], pts[831], coeff[97]);
                xDBLe(pts[831], pts[833], A24plus[98], C24[98], 2);
                xDBLe(pts[833], pts[835], A24plus[98], C24[98], 2);
                xDBLe(pts[835], pts[837], A24plus[98], C24[98], 2);
                xDBLe(pts[837], pts[839], A24plus[98], C24[98], 2);
                get_4_isog(pts[839], A24plus[99], C24[99], coeff[98]);
                eval_4_isog_mod(pts[837], pts[841], coeff[98]);
                get_4_isog(pts[841], A24plus[100], C24[100], coeff[99]);
                lock[100][0] = 0;
                while(lock[100][1]) {
                    #pragma omp flush(lock[100][1])
                }

                eval_4_isog_mod(pts[835], pts[842], coeff[98]);
                eval_4_isog_mod(pts[842], pts[845], coeff[99]);
                get_4_isog(pts[845], A24plus[101], C24[101], coeff[100]);
                lock[101][0] = 0;
                while(lock[101][1]) {
                    #pragma omp flush(lock[101][1])
                }

                eval_4_isog_mod(pts[844], pts[847], coeff[98]);
                eval_4_isog_mod(pts[847], pts[849], coeff[99]);
                eval_4_isog_mod(pts[849], pts[851], coeff[100]);
                eval_4_isog_mod(pts[771], pts[852], coeff[90]);
                lock[102][0] = 0;
                while(lock[102][1]) {
                    #pragma omp flush(lock[102][1])
                }

                eval_4_isog_mod(pts[852], pts[855], coeff[91]);
                eval_4_isog_mod(pts[855], pts[857], coeff[92]);
                eval_4_isog_mod(pts[857], pts[859], coeff[93]);
                eval_4_isog_mod(pts[859], pts[861], coeff[94]);
                eval_4_isog_mod(pts[861], pts[863], coeff[95]);
                eval_4_isog_mod(pts[863], pts[865], coeff[96]);
                eval_4_isog_mod(pts[865], pts[867], coeff[97]);
                eval_4_isog_mod(pts[867], pts[869], coeff[98]);
                eval_4_isog_mod(pts[869], pts[871], coeff[99]);
                lock[103][0] = 0;
                while(lock[103][1]) {
                    #pragma omp flush(lock[103][1])
                }

                eval_4_isog_mod(pts[868], pts[872], coeff[103]);
                get_4_isog(pts[872], A24plus[105], C24[105], coeff[104]);
                eval_4_isog_mod(pts[862], pts[874], coeff[103]);
                lock[104][0] = 0;
                while(lock[104][1]) {
                    #pragma omp flush(lock[104][1])
                }

                eval_4_isog_mod(pts[873], pts[876], coeff[104]);
                get_4_isog(pts[876], A24plus[106], C24[106], coeff[105]);
                eval_4_isog_mod(pts[875], pts[879], coeff[101]);
                lock[105][0] = 0;
                while(lock[105][1]) {
                    #pragma omp flush(lock[105][1])
                }

                eval_4_isog_mod(pts[877], pts[880], coeff[105]);
                xDBLe(pts[880], pts[883], A24plus[106], C24[106], 2);
                get_4_isog(pts[883], A24plus[107], C24[107], coeff[106]);
                lock[106][0] = 0;
                while(lock[106][1]) {
                    #pragma omp flush(lock[106][1])
                }

                eval_4_isog_mod(pts[881], pts[884], coeff[105]);
                eval_4_isog_mod(pts[884], pts[887], coeff[106]);
                lock[107][0] = 0;
                while(lock[107][1]) {
                    #pragma omp flush(lock[107][1])
                }

                eval_4_isog_mod(pts[887], pts[889], coeff[107]);
                xDBLe(pts[889], pts[891], A24plus[108], C24[108], 2);
                xDBLe(pts[891], pts[893], A24plus[108], C24[108], 2);
                get_4_isog(pts[893], A24plus[109], C24[109], coeff[108]);
                eval_4_isog_mod(pts[754], pts[895], coeff[90]);
                lock[108][0] = 0;
                while(lock[108][1]) {
                    #pragma omp flush(lock[108][1])
                }

                eval_4_isog_mod(pts[889], pts[897], coeff[108]);
                eval_4_isog_mod(pts[895], pts[899], coeff[91]);
                lock[109][0] = 0;
                while(lock[109][1]) {
                    #pragma omp flush(lock[109][1])
                }

                eval_4_isog_mod(pts[898], pts[901], coeff[109]);
                lock[110][0] = 0;
                while(lock[110][1]) {
                    #pragma omp flush(lock[110][1])
                }

                eval_4_isog_mod(pts[901], pts[903], coeff[110]);
                xDBLe(pts[903], pts[905], A24plus[111], C24[111], 2);
                xDBLe(pts[905], pts[907], A24plus[111], C24[111], 2);
                xDBLe(pts[907], pts[909], A24plus[111], C24[111], 2);
                xDBLe(pts[909], pts[911], A24plus[111], C24[111], 2);
                xDBLe(pts[911], pts[913], A24plus[111], C24[111], 2);
                xDBLe(pts[913], pts[915], A24plus[111], C24[111], 2);
                xDBLe(pts[915], pts[917], A24plus[111], C24[111], 2);
                xDBLe(pts[917], pts[919], A24plus[111], C24[111], 2);
                xDBLe(pts[919], pts[921], A24plus[111], C24[111], 2);
                xDBLe(pts[921], pts[923], A24plus[111], C24[111], 2);
                xDBLe(pts[923], pts[925], A24plus[111], C24[111], 2);
                get_4_isog(pts[925], A24plus[112], C24[112], coeff[111]);
                eval_4_isog_mod(pts[923], pts[927], coeff[111]);
                get_4_isog(pts[927], A24plus[113], C24[113], coeff[112]);
                lock[111][0] = 0;
                while(lock[111][1]) {
                    #pragma omp flush(lock[111][1])
                }

                eval_4_isog_mod(pts[917], pts[929], coeff[111]);
                eval_4_isog_mod(pts[926], pts[930], coeff[105]);
                eval_4_isog_mod(pts[929], pts[932], coeff[112]);
                lock[112][0] = 0;
                while(lock[112][1]) {
                    #pragma omp flush(lock[112][1])
                }

                eval_4_isog_mod(pts[930], pts[934], coeff[106]);
                eval_4_isog_mod(pts[934], pts[937], coeff[107]);
                lock[113][0] = 0;
                while(lock[113][1]) {
                    #pragma omp flush(lock[113][1])
                }

                eval_4_isog_mod(pts[936], pts[939], coeff[113]);
                eval_4_isog_mod(pts[937], pts[941], coeff[108]);
                lock[114][0] = 0;
                while(lock[114][1]) {
                    #pragma omp flush(lock[114][1])
                }

                eval_4_isog_mod(pts[939], pts[943], coeff[114]);
                eval_4_isog_mod(pts[941], pts[945], coeff[109]);
                lock[115][0] = 0;
                while(lock[115][1]) {
                    #pragma omp flush(lock[115][1])
                }

                eval_4_isog_mod(pts[944], pts[947], coeff[113]);
                eval_4_isog_mod(pts[945], pts[948], coeff[110]);
                lock[116][0] = 0;
                while(lock[116][1]) {
                    #pragma omp flush(lock[116][1])
                }

                eval_4_isog_mod(pts[948], pts[951], coeff[111]);
                xDBLe(pts[949], pts[952], A24plus[116], C24[116], 2);
                get_4_isog(pts[952], A24plus[117], C24[117], coeff[116]);
                lock[117][0] = 0;
                while(lock[117][1]) {
                    #pragma omp flush(lock[117][1])
                }

                eval_4_isog_mod(pts[949], pts[955], coeff[116]);
                get_4_isog(pts[955], A24plus[118], C24[118], coeff[117]);
                eval_4_isog_mod(pts[946], pts[956], coeff[116]);
                eval_4_isog_mod(pts[956], pts[959], coeff[117]);
                get_4_isog(pts[959], A24plus[119], C24[119], coeff[118]);
                lock[118][0] = 0;
                while(lock[118][1]) {
                    #pragma omp flush(lock[118][1])
                }

                eval_4_isog_mod(pts[957], pts[960], coeff[117]);
                eval_4_isog_mod(pts[960], pts[962], coeff[118]);
                xDBLe(pts[962], pts[964], A24plus[119], C24[119], 2);
                xDBLe(pts[964], pts[967], A24plus[119], C24[119], 2);
                lock[119][0] = 0;
                while(lock[119][1]) {
                    #pragma omp flush(lock[119][1])
                }

                eval_4_isog_mod(pts[966], pts[969], coeff[91]);
                xDBLe(pts[967], pts[970], A24plus[119], C24[119], 2);
                get_4_isog(pts[970], A24plus[120], C24[120], coeff[119]);
                lock[120][0] = 0;
                while(lock[120][1]) {
                    #pragma omp flush(lock[120][1])
                }

                eval_4_isog_mod(pts[967], pts[973], coeff[119]);
                get_4_isog(pts[973], A24plus[121], C24[121], coeff[120]);
                eval_4_isog_mod(pts[964], pts[974], coeff[119]);
                eval_4_isog_mod(pts[971], pts[976], coeff[119]);
                lock[121][0] = 0;
                while(lock[121][1]) {
                    #pragma omp flush(lock[121][1])
                }

                eval_4_isog_mod(pts[975], pts[979], coeff[120]);
                eval_4_isog_mod(pts[977], pts[981], coeff[94]);
                lock[122][0] = 0;
                while(lock[122][1]) {
                    #pragma omp flush(lock[122][1])
                }

                eval_4_isog_mod(pts[979], pts[982], coeff[121]);
                get_4_isog(pts[982], A24plus[123], C24[123], coeff[122]);
                lock[123][0] = 0;
                while(lock[123][1]) {
                    #pragma omp flush(lock[123][1])
                }

                eval_4_isog_mod(pts[983], pts[985], coeff[122]);
                xDBLe(pts[985], pts[987], A24plus[123], C24[123], 2);
                xDBLe(pts[987], pts[989], A24plus[123], C24[123], 2);
                xDBLe(pts[989], pts[991], A24plus[123], C24[123], 2);
                xDBLe(pts[991], pts[993], A24plus[123], C24[123], 2);
                xDBLe(pts[993], pts[995], A24plus[123], C24[123], 2);
                xDBLe(pts[995], pts[997], A24plus[123], C24[123], 2);
                xDBLe(pts[997], pts[999], A24plus[123], C24[123], 2);
                xDBLe(pts[999], pts[1001], A24plus[123], C24[123], 2);
                xDBLe(pts[1001], pts[1003], A24plus[123], C24[123], 2);
                xDBLe(pts[1003], pts[1005], A24plus[123], C24[123], 2);
                xDBLe(pts[1005], pts[1007], A24plus[123], C24[123], 2);
                xDBLe(pts[1007], pts[1009], A24plus[123], C24[123], 2);
                xDBLe(pts[1009], pts[1011], A24plus[123], C24[123], 2);
                xDBLe(pts[1011], pts[1013], A24plus[123], C24[123], 2);
                xDBLe(pts[1013], pts[1015], A24plus[123], C24[123], 2);
                xDBLe(pts[1015], pts[1017], A24plus[123], C24[123], 2);
                get_4_isog(pts[1017], A24plus[124], C24[124], coeff[123]);
                eval_4_isog_mod(pts[1015], pts[1019], coeff[123]);
                get_4_isog(pts[1019], A24plus[125], C24[125], coeff[124]);
                lock[124][0] = 0;
                while(lock[124][1]) {
                    #pragma omp flush(lock[124][1])
                }

                eval_4_isog_mod(pts[1013], pts[1020], coeff[123]);
                eval_4_isog_mod(pts[1020], pts[1023], coeff[124]);
                get_4_isog(pts[1023], A24plus[126], C24[126], coeff[125]);
                eval_4_isog_mod(pts[1003], pts[1025], coeff[123]);
                lock[125][0] = 0;
                while(lock[125][1]) {
                    #pragma omp flush(lock[125][1])
                }

                eval_4_isog_mod(pts[1022], pts[1026], coeff[114]);
                eval_4_isog_mod(pts[1026], pts[1029], coeff[115]);
                lock[126][0] = 0;
                while(lock[126][1]) {
                    #pragma omp flush(lock[126][1])
                }

                xDBLe(pts[1027], pts[1030], A24plus[126], C24[126], 2);
                get_4_isog(pts[1030], A24plus[127], C24[127], coeff[126]);
                eval_4_isog_mod(pts[1029], pts[1033], coeff[116]);
                lock[127][0] = 0;
                while(lock[127][1]) {
                    #pragma omp flush(lock[127][1])
                }

                eval_4_isog_mod(pts[1027], pts[1034], coeff[126]);
                get_4_isog(pts[1034], A24plus[128], C24[128], coeff[127]);
                eval_4_isog_mod(pts[1033], pts[1037], coeff[117]);
                lock[128][0] = 0;
                while(lock[128][1]) {
                    #pragma omp flush(lock[128][1])
                }

                eval_4_isog_mod(pts[1035], pts[1038], coeff[127]);
                xDBLe(pts[1038], pts[1041], A24plus[128], C24[128], 2);
                eval_4_isog_mod(pts[985], pts[1043], coeff[123]);
                xDBLe(pts[1041], pts[1045], A24plus[128], C24[128], 2);
                get_4_isog(pts[1045], A24plus[129], C24[129], coeff[128]);
                eval_4_isog_mod(pts[1043], pts[1047], coeff[124]);
                eval_4_isog_mod(pts[1041], pts[1049], coeff[128]);
                get_4_isog(pts[1049], A24plus[130], C24[130], coeff[129]);
                lock[129][0] = 0;
                while(lock[129][1]) {
                    #pragma omp flush(lock[129][1])
                }

                eval_4_isog_mod(pts[1046], pts[1051], coeff[128]);
                eval_4_isog_mod(pts[1047], pts[1052], coeff[125]);
                eval_4_isog_mod(pts[1051], pts[1055], coeff[129]);
                eval_4_isog_mod(pts[1052], pts[1056], coeff[126]);
                lock[130][0] = 0;
                while(lock[130][1]) {
                    #pragma omp flush(lock[130][1])
                }

                eval_4_isog_mod(pts[708], pts[1058], coeff[90]);
                eval_4_isog_mod(pts[1056], pts[1060], coeff[127]);
                eval_4_isog_mod(pts[1058], pts[1062], coeff[91]);
                eval_4_isog_mod(pts[1060], pts[1064], coeff[128]);
                eval_4_isog_mod(pts[1062], pts[1066], coeff[92]);
                eval_4_isog_mod(pts[1064], pts[1068], coeff[129]);
                eval_4_isog_mod(pts[1066], pts[1070], coeff[93]);
                eval_4_isog_mod(pts[1068], pts[1072], coeff[130]);
                eval_4_isog_mod(pts[1070], pts[1074], coeff[94]);
                lock[131][0] = 0;
                while(lock[131][1]) {
                    #pragma omp flush(lock[131][1])
                }

                eval_4_isog_mod(pts[1063], pts[1076], coeff[131]);
                eval_4_isog_mod(pts[1073], pts[1079], coeff[127]);
                eval_4_isog_mod(pts[1076], pts[1081], coeff[132]);
                get_4_isog(pts[1081], A24plus[134], C24[134], coeff[133]);
                lock[132][0] = 0;
                while(lock[132][1]) {
                    #pragma omp flush(lock[132][1])
                }

                eval_4_isog_mod(pts[1077], pts[1082], coeff[132]);
                eval_4_isog_mod(pts[1080], pts[1085], coeff[96]);
                eval_4_isog_mod(pts[1082], pts[1086], coeff[133]);
                get_4_isog(pts[1086], A24plus[135], C24[135], coeff[134]);
                eval_4_isog_mod(pts[1085], pts[1089], coeff[97]);
                lock[133][0] = 0;
                while(lock[133][1]) {
                    #pragma omp flush(lock[133][1])
                }

                eval_4_isog_mod(pts[1087], pts[1090], coeff[134]);
                xDBLe(pts[1090], pts[1093], A24plus[135], C24[135], 2);
                lock[134][0] = 0;
                while(lock[134][1]) {
                    #pragma omp flush(lock[134][1])
                }

                eval_4_isog_mod(pts[1091], pts[1094], coeff[131]);
                eval_4_isog_mod(pts[1094], pts[1097], coeff[132]);
                lock[135][0] = 0;
                while(lock[135][1]) {
                    #pragma omp flush(lock[135][1])
                }

                xDBLe(pts[1096], pts[1099], A24plus[135], C24[135], 2);
                eval_4_isog_mod(pts[1097], pts[1100], coeff[133]);
                lock[136][0] = 0;
                while(lock[136][1]) {
                    #pragma omp flush(lock[136][1])
                }

                xDBLe(pts[1099], pts[1102], A24plus[135], C24[135], 2);
                get_4_isog(pts[1102], A24plus[136], C24[136], coeff[135]);
                lock[137][0] = 0;
                while(lock[137][1]) {
                    #pragma omp flush(lock[137][1])
                }

                eval_4_isog_mod(pts[1101], pts[1104], coeff[102]);
                eval_4_isog_mod(pts[1096], pts[1106], coeff[135]);
                eval_4_isog_mod(pts[1103], pts[1109], coeff[135]);
                lock[138][0] = 0;
                while(lock[138][1]) {
                    #pragma omp flush(lock[138][1])
                }

                eval_4_isog_mod(pts[1106], pts[1111], coeff[136]);
                get_4_isog(pts[1111], A24plus[138], C24[138], coeff[137]);
                eval_4_isog_mod(pts[1108], pts[1113], coeff[136]);
                eval_4_isog_mod(pts[1109], pts[1114], coeff[136]);
                lock[139][0] = 0;
                while(lock[139][1]) {
                    #pragma omp flush(lock[139][1])
                }

                eval_4_isog_mod(pts[1113], pts[1117], coeff[137]);
                eval_4_isog_mod(pts[1115], pts[1119], coeff[105]);
                lock[140][0] = 0;
                while(lock[140][1]) {
                    #pragma omp flush(lock[140][1])
                }

                eval_4_isog_mod(pts[1118], pts[1121], coeff[138]);
                lock[141][0] = 0;
                while(lock[141][1]) {
                    #pragma omp flush(lock[141][1])
                }

                eval_4_isog_mod(pts[1119], pts[1122], coeff[106]);
                eval_4_isog_mod(pts[1122], pts[1124], coeff[107]);
                eval_4_isog_mod(pts[1124], pts[1126], coeff[108]);
                eval_4_isog_mod(pts[1126], pts[1128], coeff[109]);
                eval_4_isog_mod(pts[1128], pts[1130], coeff[110]);
                eval_4_isog_mod(pts[1130], pts[1132], coeff[111]);
                eval_4_isog_mod(pts[1132], pts[1134], coeff[112]);
                eval_4_isog_mod(pts[1134], pts[1136], coeff[113]);
                eval_4_isog_mod(pts[1136], pts[1138], coeff[114]);
                eval_4_isog_mod(pts[1138], pts[1140], coeff[115]);
                eval_4_isog_mod(pts[1140], pts[1142], coeff[116]);
                eval_4_isog_mod(pts[1142], pts[1144], coeff[117]);
                eval_4_isog_mod(pts[1144], pts[1146], coeff[118]);
                eval_4_isog_mod(pts[1146], pts[1148], coeff[119]);
                eval_4_isog_mod(pts[1148], pts[1150], coeff[120]);
                eval_4_isog_mod(pts[1150], pts[1152], coeff[121]);
                eval_4_isog_mod(pts[1152], pts[1154], coeff[122]);
                eval_4_isog_mod(pts[1154], pts[1156], coeff[123]);
                eval_4_isog_mod(pts[1156], pts[1158], coeff[124]);
                eval_4_isog_mod(pts[1158], pts[1160], coeff[125]);
                eval_4_isog_mod(pts[1160], pts[1162], coeff[126]);
                lock[142][0] = 0;
                while(lock[142][1]) {
                    #pragma omp flush(lock[142][1])
                }

                eval_4_isog_mod(pts[1153], pts[1165], coeff[140]);
                eval_4_isog_mod(pts[1162], pts[1166], coeff[127]);
                eval_4_isog_mod(pts[1165], pts[1168], coeff[141]);
                lock[143][0] = 0;
                while(lock[143][1]) {
                    #pragma omp flush(lock[143][1])
                }

                eval_4_isog_mod(pts[1168], pts[1171], coeff[142]);
                eval_4_isog_mod(pts[1143], pts[1173], coeff[140]);
                xDBLe(pts[1171], pts[1175], A24plus[143], C24[143], 2);
                get_4_isog(pts[1175], A24plus[144], C24[144], coeff[143]);
                eval_4_isog_mod(pts[1173], pts[1177], coeff[141]);
                eval_4_isog_mod(pts[1171], pts[1179], coeff[143]);
                get_4_isog(pts[1179], A24plus[145], C24[145], coeff[144]);
                lock[144][0] = 0;
                while(lock[144][1]) {
                    #pragma omp flush(lock[144][1])
                }

                eval_4_isog_mod(pts[1177], pts[1181], coeff[142]);
                eval_4_isog_mod(pts[1135], pts[1182], coeff[140]);
                eval_4_isog_mod(pts[1181], pts[1185], coeff[143]);
                eval_4_isog_mod(pts[1182], pts[1186], coeff[141]);
                eval_4_isog_mod(pts[1185], pts[1189], coeff[144]);
                eval_4_isog_mod(pts[1186], pts[1190], coeff[142]);
                lock[145][0] = 0;
                while(lock[145][1]) {
                    #pragma omp flush(lock[145][1])
                }

                eval_4_isog_mod(pts[1189], pts[1193], coeff[145]);
                eval_4_isog_mod(pts[1123], pts[1195], coeff[140]);
                lock[146][0] = 0;
                while(lock[146][1]) {
                    #pragma omp flush(lock[146][1])
                }

                eval_4_isog_mod(pts[1191], pts[1196], coeff[134]);
                eval_4_isog_mod(pts[1195], pts[1199], coeff[141]);
                eval_4_isog_mod(pts[1196], pts[1200], coeff[135]);
                eval_4_isog_mod(pts[1199], pts[1203], coeff[142]);
                eval_4_isog_mod(pts[1200], pts[1204], coeff[136]);
                eval_4_isog_mod(pts[1203], pts[1207], coeff[143]);
                eval_4_isog_mod(pts[1204], pts[1208], coeff[137]);
                lock[147][0] = 0;
                while(lock[147][1]) {
                    #pragma omp flush(lock[147][1])
                }

                eval_4_isog_mod(pts[1197], pts[1210], coeff[147]);
                eval_4_isog_mod(pts[1207], pts[1212], coeff[144]);
                eval_4_isog_mod(pts[1210], pts[1214], coeff[148]);
                get_4_isog(pts[1214], A24plus[150], C24[150], coeff[149]);
                eval_4_isog_mod(pts[1212], pts[1216], coeff[145]);
                lock[148][0] = 0;
                while(lock[148][1]) {
                    #pragma omp flush(lock[148][1])
                }

                eval_4_isog_mod(pts[1215], pts[1218], coeff[149]);
                xDBLe(pts[1218], pts[1221], A24plus[150], C24[150], 2);
                lock[149][0] = 0;
                while(lock[149][1]) {
                    #pragma omp flush(lock[149][1])
                }

                eval_4_isog_mod(pts[1219], pts[1222], coeff[147]);
                eval_4_isog_mod(pts[1222], pts[1225], coeff[148]);
                lock[150][0] = 0;
                while(lock[150][1]) {
                    #pragma omp flush(lock[150][1])
                }

                eval_4_isog_mod(pts[1223], pts[1226], coeff[142]);
                eval_4_isog_mod(pts[1226], pts[1229], coeff[143]);
                lock[151][0] = 0;
                while(lock[151][1]) {
                    #pragma omp flush(lock[151][1])
                }

                eval_4_isog_mod(pts[1224], pts[1230], coeff[150]);
                get_4_isog(pts[1230], A24plus[152], C24[152], coeff[151]);
                eval_4_isog_mod(pts[1218], pts[1232], coeff[150]);
                lock[152][0] = 0;
                while(lock[152][1]) {
                    #pragma omp flush(lock[152][1])
                }

                eval_4_isog_mod(pts[1229], pts[1234], coeff[144]);
                eval_4_isog_mod(pts[1233], pts[1237], coeff[151]);
                eval_4_isog_mod(pts[1234], pts[1238], coeff[145]);
                lock[153][0] = 0;
                while(lock[153][1]) {
                    #pragma omp flush(lock[153][1])
                }

                eval_4_isog_mod(pts[1237], pts[1240], coeff[152]);
                eval_4_isog_mod(pts[1240], pts[1242], coeff[153]);
                xDBLe(pts[1242], pts[1244], A24plus[154], C24[154], 2);
                xDBLe(pts[1244], pts[1246], A24plus[154], C24[154], 2);
                xDBLe(pts[1246], pts[1248], A24plus[154], C24[154], 2);
                xDBLe(pts[1248], pts[1250], A24plus[154], C24[154], 2);
                xDBLe(pts[1250], pts[1252], A24plus[154], C24[154], 2);
                get_4_isog(pts[1252], A24plus[155], C24[155], coeff[154]);
                lock[154][0] = 0;
                while(lock[154][1]) {
                    #pragma omp flush(lock[154][1])
                }

                eval_4_isog_mod(pts[1248], pts[1255], coeff[154]);
                eval_4_isog_mod(pts[1246], pts[1256], coeff[154]);
                lock[155][0] = 0;
                while(lock[155][1]) {
                    #pragma omp flush(lock[155][1])
                }

                eval_4_isog_mod(pts[1253], pts[1258], coeff[153]);
                eval_4_isog_mod(pts[1256], pts[1260], coeff[155]);
                lock[156][0] = 0;
                while(lock[156][1]) {
                    #pragma omp flush(lock[156][1])
                }

                eval_4_isog_mod(pts[1258], pts[1262], coeff[154]);
                eval_4_isog_mod(pts[1262], pts[1265], coeff[155]);
                eval_4_isog_mod(pts[1265], pts[1267], coeff[156]);
                lock[157][0] = 0;
                while(lock[157][1]) {
                    #pragma omp flush(lock[157][1])
                }

                eval_4_isog_mod(pts[1267], pts[1269], coeff[157]);
                lock[158][0] = 0;
                while(lock[158][1]) {
                    #pragma omp flush(lock[158][1])
                }

                eval_4_isog_mod(pts[1269], pts[1271], coeff[158]);
                lock[159][0] = 0;
                while(lock[159][1]) {
                    #pragma omp flush(lock[159][1])
                }

                eval_4_isog_mod(pts[1271], pts[1272], coeff[159]);
                xDBLe(pts[1272], pts[1273], A24plus[160], C24[160], 2);
                xDBLe(pts[1273], pts[1274], A24plus[160], C24[160], 2);
                xDBLe(pts[1274], pts[1275], A24plus[160], C24[160], 2);
                xDBLe(pts[1275], pts[1276], A24plus[160], C24[160], 2);
                xDBLe(pts[1276], pts[1277], A24plus[160], C24[160], 2);
                xDBLe(pts[1277], pts[1278], A24plus[160], C24[160], 2);
                xDBLe(pts[1278], pts[1279], A24plus[160], C24[160], 2);
                xDBLe(pts[1279], pts[1280], A24plus[160], C24[160], 2);
                xDBLe(pts[1280], pts[1281], A24plus[160], C24[160], 2);
                xDBLe(pts[1281], pts[1282], A24plus[160], C24[160], 2);
                xDBLe(pts[1282], pts[1283], A24plus[160], C24[160], 2);
                xDBLe(pts[1283], pts[1284], A24plus[160], C24[160], 2);
                xDBLe(pts[1284], pts[1285], A24plus[160], C24[160], 2);
                xDBLe(pts[1285], pts[1286], A24plus[160], C24[160], 2);
                xDBLe(pts[1286], pts[1287], A24plus[160], C24[160], 2);
                xDBLe(pts[1287], pts[1288], A24plus[160], C24[160], 2);
                xDBLe(pts[1288], pts[1289], A24plus[160], C24[160], 2);
                xDBLe(pts[1289], pts[1290], A24plus[160], C24[160], 2);
                xDBLe(pts[1290], pts[1291], A24plus[160], C24[160], 2);
                xDBLe(pts[1291], pts[1292], A24plus[160], C24[160], 2);
                xDBLe(pts[1292], pts[1293], A24plus[160], C24[160], 2);
                xDBLe(pts[1293], pts[1294], A24plus[160], C24[160], 2);
                xDBLe(pts[1294], pts[1295], A24plus[160], C24[160], 2);
                xDBLe(pts[1295], pts[1296], A24plus[160], C24[160], 2);
                xDBLe(pts[1296], pts[1297], A24plus[160], C24[160], 2);
                get_4_isog(pts[1297], A24plus[161], C24[161], coeff[160]);
                lock[160][0] = 0;
                while(lock[160][1]) {
                    #pragma omp flush(lock[160][1])
                }

                eval_4_isog_mod(pts[1295], pts[1299], coeff[160]);
                lock[161][0] = 0;
                while(lock[161][1]) {
                    #pragma omp flush(lock[161][1])
                }

                eval_4_isog_mod(pts[1293], pts[1300], coeff[160]);
                eval_4_isog_mod(pts[1300], pts[1302], coeff[161]);
                lock[162][0] = 0;
                while(lock[162][1]) {
                    #pragma omp flush(lock[162][1])
                }

                eval_4_isog_mod(pts[1302], pts[1304], coeff[162]);
                xDBLe(pts[1304], pts[1307], A24plus[163], C24[163], 2);
                get_4_isog(pts[1307], A24plus[164], C24[164], coeff[163]);
                lock[163][0] = 0;
                while(lock[163][1]) {
                    #pragma omp flush(lock[163][1])
                }

                eval_4_isog_mod(pts[1305], pts[1308], coeff[162]);
                eval_4_isog_mod(pts[1304], pts[1311], coeff[163]);
                get_4_isog(pts[1311], A24plus[165], C24[165], coeff[164]);
                eval_4_isog_mod(pts[1308], pts[1312], coeff[163]);
                eval_4_isog_mod(pts[1312], pts[1315], coeff[164]);
                lock[164][0] = 0;
                while(lock[164][1]) {
                    #pragma omp flush(lock[164][1])
                }

                eval_4_isog_mod(pts[1313], pts[1316], coeff[163]);
                eval_4_isog_mod(pts[1316], pts[1319], coeff[164]);
                eval_4_isog_mod(pts[1280], pts[1321], coeff[160]);
                lock[165][0] = 0;
                while(lock[165][1]) {
                    #pragma omp flush(lock[165][1])
                }

                eval_4_isog_mod(pts[1319], pts[1323], coeff[165]);
                eval_4_isog_mod(pts[1321], pts[1325], coeff[161]);
                lock[166][0] = 0;
                while(lock[166][1]) {
                    #pragma omp flush(lock[166][1])
                }

                eval_4_isog_mod(pts[1323], pts[1326], coeff[166]);
                xDBLe(pts[1326], pts[1329], A24plus[167], C24[167], 2);
                get_4_isog(pts[1329], A24plus[168], C24[168], coeff[167]);
                lock[167][0] = 0;
                while(lock[167][1]) {
                    #pragma omp flush(lock[167][1])
                }

                eval_4_isog_mod(pts[1328], pts[1331], coeff[163]);
                eval_4_isog_mod(pts[1326], pts[1332], coeff[167]);
                get_4_isog(pts[1332], A24plus[169], C24[169], coeff[168]);
                lock[168][0] = 0;
                while(lock[168][1]) {
                    #pragma omp flush(lock[168][1])
                }

                eval_4_isog_mod(pts[1333], pts[1335], coeff[168]);
                eval_4_isog_mod(pts[1272], pts[1337], coeff[160]);
                xDBLe(pts[1335], pts[1338], A24plus[169], C24[169], 2);
                lock[169][0] = 0;
                while(lock[169][1]) {
                    #pragma omp flush(lock[169][1])
                }

                eval_4_isog_mod(pts[1337], pts[1340], coeff[161]);
                eval_4_isog_mod(pts[1340], pts[1343], coeff[162]);
                lock[170][0] = 0;
                while(lock[170][1]) {
                    #pragma omp flush(lock[170][1])
                }

                eval_4_isog_mod(pts[1342], pts[1345], coeff[168]);
                eval_4_isog_mod(pts[1343], pts[1346], coeff[163]);
                lock[171][0] = 0;
                while(lock[171][1]) {
                    #pragma omp flush(lock[171][1])
                }

                eval_4_isog_mod(pts[1338], pts[1348], coeff[169]);
                eval_4_isog_mod(pts[1345], pts[1350], coeff[169]);
                eval_4_isog_mod(pts[1348], pts[1352], coeff[170]);
                get_4_isog(pts[1352], A24plus[172], C24[172], coeff[171]);
                eval_4_isog_mod(pts[1350], pts[1354], coeff[170]);
                lock[172][0] = 0;
                while(lock[172][1]) {
                    #pragma omp flush(lock[172][1])
                }

                eval_4_isog_mod(pts[1354], pts[1357], coeff[171]);
                lock[173][0] = 0;
                while(lock[173][1]) {
                    #pragma omp flush(lock[173][1])
                }

                eval_4_isog_mod(pts[1355], pts[1358], coeff[166]);
                eval_4_isog_mod(pts[1358], pts[1360], coeff[167]);
                eval_4_isog_mod(pts[1360], pts[1362], coeff[168]);
                eval_4_isog_mod(pts[1362], pts[1364], coeff[169]);
                eval_4_isog_mod(pts[1364], pts[1366], coeff[170]);
                eval_4_isog_mod(pts[1366], pts[1368], coeff[171]);
                lock[174][0] = 0;
                while(lock[174][1]) {
                    #pragma omp flush(lock[174][1])
                }

                eval_4_isog_mod(pts[1363], pts[1370], coeff[173]);
                eval_4_isog_mod(pts[1370], pts[1373], coeff[174]);
                get_4_isog(pts[1373], A24plus[176], C24[176], coeff[175]);
                lock[175][0] = 0;
                while(lock[175][1]) {
                    #pragma omp flush(lock[175][1])
                }

                eval_4_isog_mod(pts[1372], pts[1375], coeff[173]);
                eval_4_isog_mod(pts[1375], pts[1377], coeff[174]);
                eval_4_isog_mod(pts[1377], pts[1379], coeff[175]);
                lock[176][0] = 0;
                while(lock[176][1]) {
                    #pragma omp flush(lock[176][1])
                }

                eval_4_isog_mod(pts[1379], pts[1381], coeff[176]);
                lock[177][0] = 0;
                while(lock[177][1]) {
                    #pragma omp flush(lock[177][1])
                }

                eval_4_isog_mod(pts[1381], pts[1382], coeff[177]);
                xDBLe(pts[1382], pts[1383], A24plus[178], C24[178], 2);
                xDBLe(pts[1383], pts[1384], A24plus[178], C24[178], 2);
                xDBLe(pts[1384], pts[1385], A24plus[178], C24[178], 2);
                xDBLe(pts[1385], pts[1386], A24plus[178], C24[178], 2);
                xDBLe(pts[1386], pts[1387], A24plus[178], C24[178], 2);
                xDBLe(pts[1387], pts[1388], A24plus[178], C24[178], 2);
                xDBLe(pts[1388], pts[1389], A24plus[178], C24[178], 2);
                get_4_isog(pts[1389], A24plus[179], C24[179], coeff[178]);
                lock[178][0] = 0;
                while(lock[178][1]) {
                    #pragma omp flush(lock[178][1])
                }

                eval_4_isog_mod(pts[1388], pts[1390], coeff[178]);
                get_4_isog(pts[1390], A24plus[180], C24[180], coeff[179]);
                lock[179][0] = 0;
                while(lock[179][1]) {
                    #pragma omp flush(lock[179][1])
                }

                eval_4_isog_mod(pts[1391], pts[1393], coeff[179]);
                get_4_isog(pts[1393], A24plus[181], C24[181], coeff[180]);
                eval_4_isog_mod(pts[1382], pts[1395], coeff[178]);
                lock[180][0] = 0;
                while(lock[180][1]) {
                    #pragma omp flush(lock[180][1])
                }

                eval_4_isog_mod(pts[1394], pts[1396], coeff[180]);
                xDBLe(pts[1396], pts[1398], A24plus[181], C24[181], 2);
                get_4_isog(pts[1398], A24plus[182], C24[182], coeff[181]);
                lock[181][0] = 0;
                while(lock[181][1]) {
                    #pragma omp flush(lock[181][1])
                }

                eval_4_isog_mod(pts[1396], pts[1400], coeff[181]);
                get_4_isog(pts[1400], A24plus[183], C24[183], coeff[182]);
                lock[182][0] = 0;
                while(lock[182][1]) {
                    #pragma omp flush(lock[182][1])
                }

                eval_4_isog_mod(pts[1401], pts[1402], coeff[182]);
                xDBLe(pts[1402], pts[1403], A24plus[183], C24[183], 2);
                xDBLe(pts[1403], pts[1404], A24plus[183], C24[183], 2);
                get_4_isog(pts[1404], A24plus[184], C24[184], coeff[183]);
                lock[183][0] = 0;
                while(lock[183][1]) {
                    #pragma omp flush(lock[183][1])
                }

                eval_4_isog_mod(pts[1402], pts[1406], coeff[183]);
            }
            #pragma omp section
            {
                LADDER3PT_NS_prcmp(&PA_prcmp[2*NWORDS_FIELD * 96], &RA_prcmp[2*NWORDS_FIELD * 96], (digit_t*)PrivateKeyA, ALICE, pts[1], A, 2*90);
                for(int i = 1; i < 90; i++)
                    xDBLe(pts[i], pts[i+1], A24plus[0], C24[0], 2);
                get_4_isog(pts[90], A24plus[1], C24[1], coeff[0]);
                eval_4_isog_mod(pts[89], pts[91], coeff[0]);
                get_4_isog(pts[91], A24plus[2], C24[2], coeff[1]);
                eval_4_isog_mod(pts[88], pts[92], coeff[0]);
                eval_4_isog_mod(pts[87], pts[93], coeff[0]);
                eval_4_isog_mod(pts[86], pts[94], coeff[0]);
                eval_4_isog_mod(pts[84], pts[95], coeff[0]);
                eval_4_isog_mod(pts[92], pts[96], coeff[1]);
                get_4_isog(pts[96], A24plus[3], C24[3], coeff[2]);
                eval_4_isog_mod(pts[93], pts[97], coeff[1]);
                eval_4_isog_mod(pts[94], pts[98], coeff[1]);
                eval_4_isog_mod(pts[95], pts[99], coeff[1]);
                lock1[1] = 0;
                while(lock1[0]) {
                    #pragma omp flush(lock1[0])
                }

                eval_4_isog_mod(pts[97], pts[101], coeff[2]);
                get_4_isog(pts[101], A24plus[4], C24[4], coeff[3]);
                eval_4_isog_mod(pts[98], pts[102], coeff[2]);
                eval_4_isog_mod(pts[102], pts[105], coeff[3]);
                get_4_isog(pts[105], A24plus[5], C24[5], coeff[4]);
                lock[0][1] = 0;
                while(lock[0][0]) {
                    #pragma omp flush(lock[0][0])
                }

                eval_4_isog_mod(pts[103], pts[106], coeff[3]);
                eval_4_isog_mod(pts[106], pts[109], coeff[4]);
                lock[1][1] = 0;
                while(lock[1][0]) {
                    #pragma omp flush(lock[1][0])
                }

                eval_4_isog_mod(pts[107], pts[110], coeff[3]);
                eval_4_isog_mod(pts[110], pts[113], coeff[4]);
                lock[2][1] = 0;
                while(lock[2][0]) {
                    #pragma omp flush(lock[2][0])
                }

                eval_4_isog_mod(pts[111], pts[114], coeff[2]);
                eval_4_isog_mod(pts[114], pts[117], coeff[3]);
                eval_4_isog_mod(pts[117], pts[119], coeff[4]);
                eval_4_isog_mod(pts[119], pts[121], coeff[5]);
                eval_4_isog_mod(pts[68], pts[122], coeff[0]);
                lock[3][1] = 0;
                while(lock[3][0]) {
                    #pragma omp flush(lock[3][0])
                }

                eval_4_isog_mod(pts[122], pts[125], coeff[1]);
                eval_4_isog_mod(pts[120], pts[126], coeff[7]);
                get_4_isog(pts[126], A24plus[9], C24[9], coeff[8]);
                eval_4_isog_mod(pts[125], pts[129], coeff[2]);
                lock[4][1] = 0;
                while(lock[4][0]) {
                    #pragma omp flush(lock[4][0])
                }

                eval_4_isog_mod(pts[127], pts[130], coeff[8]);
                get_4_isog(pts[130], A24plus[10], C24[10], coeff[9]);
                lock[5][1] = 0;
                while(lock[5][0]) {
                    #pragma omp flush(lock[5][0])
                }

                eval_4_isog_mod(pts[129], pts[132], coeff[3]);
                eval_4_isog_mod(pts[132], pts[134], coeff[4]);
                eval_4_isog_mod(pts[134], pts[136], coeff[5]);
                eval_4_isog_mod(pts[136], pts[138], coeff[6]);
                eval_4_isog_mod(pts[138], pts[140], coeff[7]);
                eval_4_isog_mod(pts[140], pts[142], coeff[8]);
                lock[6][1] = 0;
                while(lock[6][0]) {
                    #pragma omp flush(lock[6][0])
                }

                eval_4_isog_mod(pts[133], pts[145], coeff[10]);
                eval_4_isog_mod(pts[142], pts[146], coeff[9]);
                lock[7][1] = 0;
                while(lock[7][0]) {
                    #pragma omp flush(lock[7][0])
                }

                eval_4_isog_mod(pts[145], pts[148], coeff[11]);
                eval_4_isog_mod(pts[148], pts[151], coeff[12]);
                lock[8][1] = 0;
                while(lock[8][0]) {
                    #pragma omp flush(lock[8][0])
                }

                eval_4_isog_mod(pts[150], pts[153], coeff[1]);
                xDBLe(pts[151], pts[154], A24plus[13], C24[13], 2);
                get_4_isog(pts[154], A24plus[14], C24[14], coeff[13]);
                lock[9][1] = 0;
                while(lock[9][0]) {
                    #pragma omp flush(lock[9][0])
                }

                eval_4_isog_mod(pts[151], pts[157], coeff[13]);
                get_4_isog(pts[157], A24plus[15], C24[15], coeff[14]);
                eval_4_isog_mod(pts[155], pts[158], coeff[13]);
                eval_4_isog_mod(pts[158], pts[160], coeff[14]);
                xDBLe(pts[160], pts[162], A24plus[15], C24[15], 2);
                xDBLe(pts[162], pts[164], A24plus[15], C24[15], 2);
                xDBLe(pts[164], pts[166], A24plus[15], C24[15], 2);
                xDBLe(pts[166], pts[168], A24plus[15], C24[15], 2);
                xDBLe(pts[168], pts[170], A24plus[15], C24[15], 2);
                xDBLe(pts[170], pts[172], A24plus[15], C24[15], 2);
                xDBLe(pts[172], pts[174], A24plus[15], C24[15], 2);
                get_4_isog(pts[174], A24plus[16], C24[16], coeff[15]);
                lock[10][1] = 0;
                while(lock[10][0]) {
                    #pragma omp flush(lock[10][0])
                }

                eval_4_isog_mod(pts[172], pts[176], coeff[15]);
                get_4_isog(pts[176], A24plus[17], C24[17], coeff[16]);
                eval_4_isog_mod(pts[175], pts[179], coeff[12]);
                lock[11][1] = 0;
                while(lock[11][0]) {
                    #pragma omp flush(lock[11][0])
                }

                eval_4_isog_mod(pts[177], pts[180], coeff[16]);
                get_4_isog(pts[180], A24plus[18], C24[18], coeff[17]);
                eval_4_isog_mod(pts[160], pts[182], coeff[15]);
                lock[12][1] = 0;
                while(lock[12][0]) {
                    #pragma omp flush(lock[12][0])
                }

                eval_4_isog_mod(pts[181], pts[184], coeff[17]);
                xDBLe(pts[184], pts[187], A24plus[18], C24[18], 2);
                get_4_isog(pts[187], A24plus[19], C24[19], coeff[18]);
                lock[13][1] = 0;
                while(lock[13][0]) {
                    #pragma omp flush(lock[13][0])
                }

                eval_4_isog_mod(pts[185], pts[188], coeff[17]);
                eval_4_isog_mod(pts[188], pts[191], coeff[18]);
                lock[14][1] = 0;
                while(lock[14][0]) {
                    #pragma omp flush(lock[14][0])
                }

                eval_4_isog_mod(pts[191], pts[193], coeff[19]);
                xDBLe(pts[193], pts[195], A24plus[20], C24[20], 2);
                xDBLe(pts[195], pts[197], A24plus[20], C24[20], 2);
                get_4_isog(pts[197], A24plus[21], C24[21], coeff[20]);
                eval_4_isog_mod(pts[195], pts[199], coeff[20]);
                get_4_isog(pts[199], A24plus[22], C24[22], coeff[21]);
                lock[15][1] = 0;
                while(lock[15][0]) {
                    #pragma omp flush(lock[15][0])
                }

                eval_4_isog_mod(pts[198], pts[201], coeff[20]);
                eval_4_isog_mod(pts[34], pts[202], coeff[0]);
                lock[16][1] = 0;
                while(lock[16][0]) {
                    #pragma omp flush(lock[16][0])
                }

                eval_4_isog_mod(pts[201], pts[204], coeff[21]);
                eval_4_isog_mod(pts[204], pts[206], coeff[22]);
                xDBLe(pts[206], pts[208], A24plus[23], C24[23], 2);
                xDBLe(pts[208], pts[210], A24plus[23], C24[23], 2);
                xDBLe(pts[210], pts[212], A24plus[23], C24[23], 2);
                xDBLe(pts[212], pts[214], A24plus[23], C24[23], 2);
                xDBLe(pts[214], pts[216], A24plus[23], C24[23], 2);
                xDBLe(pts[216], pts[218], A24plus[23], C24[23], 2);
                xDBLe(pts[218], pts[220], A24plus[23], C24[23], 2);
                xDBLe(pts[220], pts[222], A24plus[23], C24[23], 2);
                xDBLe(pts[222], pts[224], A24plus[23], C24[23], 2);
                xDBLe(pts[224], pts[226], A24plus[23], C24[23], 2);
                xDBLe(pts[226], pts[228], A24plus[23], C24[23], 2);
                xDBLe(pts[228], pts[230], A24plus[23], C24[23], 2);
                get_4_isog(pts[230], A24plus[24], C24[24], coeff[23]);
                lock[17][1] = 0;
                while(lock[17][0]) {
                    #pragma omp flush(lock[17][0])
                }

                eval_4_isog_mod(pts[228], pts[232], coeff[23]);
                get_4_isog(pts[232], A24plus[25], C24[25], coeff[24]);
                eval_4_isog_mod(pts[222], pts[234], coeff[23]);
                lock[18][1] = 0;
                while(lock[18][0]) {
                    #pragma omp flush(lock[18][0])
                }

                eval_4_isog_mod(pts[234], pts[237], coeff[24]);
                eval_4_isog_mod(pts[235], pts[239], coeff[16]);
                lock[19][1] = 0;
                while(lock[19][0]) {
                    #pragma omp flush(lock[19][0])
                }

                eval_4_isog_mod(pts[237], pts[240], coeff[25]);
                xDBLe(pts[240], pts[243], A24plus[26], C24[26], 2);
                get_4_isog(pts[243], A24plus[27], C24[27], coeff[26]);
                eval_4_isog_mod(pts[206], pts[245], coeff[23]);
                eval_4_isog_mod(pts[240], pts[247], coeff[26]);
                get_4_isog(pts[247], A24plus[28], C24[28], coeff[27]);
                lock[20][1] = 0;
                while(lock[20][0]) {
                    #pragma omp flush(lock[20][0])
                }

                eval_4_isog_mod(pts[244], pts[248], coeff[26]);
                eval_4_isog_mod(pts[248], pts[251], coeff[27]);
                lock[21][1] = 0;
                while(lock[21][0]) {
                    #pragma omp flush(lock[21][0])
                }

                eval_4_isog_mod(pts[250], pts[253], coeff[20]);
                xDBLe(pts[251], pts[254], A24plus[28], C24[28], 2);
                lock[22][1] = 0;
                while(lock[22][0]) {
                    #pragma omp flush(lock[22][0])
                }

                xDBLe(pts[254], pts[257], A24plus[28], C24[28], 2);
                get_4_isog(pts[257], A24plus[29], C24[29], coeff[28]);
                eval_4_isog_mod(pts[255], pts[258], coeff[27]);
                lock[23][1] = 0;
                while(lock[23][0]) {
                    #pragma omp flush(lock[23][0])
                }

                eval_4_isog_mod(pts[254], pts[260], coeff[28]);
                get_4_isog(pts[260], A24plus[30], C24[30], coeff[29]);
                eval_4_isog_mod(pts[259], pts[263], coeff[23]);
                lock[24][1] = 0;
                while(lock[24][0]) {
                    #pragma omp flush(lock[24][0])
                }

                eval_4_isog_mod(pts[261], pts[264], coeff[29]);
                get_4_isog(pts[264], A24plus[31], C24[31], coeff[30]);
                lock[25][1] = 0;
                while(lock[25][0]) {
                    #pragma omp flush(lock[25][0])
                }

                eval_4_isog_mod(pts[263], pts[266], coeff[24]);
                eval_4_isog_mod(pts[266], pts[268], coeff[25]);
                eval_4_isog_mod(pts[268], pts[270], coeff[26]);
                eval_4_isog_mod(pts[270], pts[272], coeff[27]);
                eval_4_isog_mod(pts[272], pts[274], coeff[28]);
                eval_4_isog_mod(pts[274], pts[276], coeff[29]);
                lock[26][1] = 0;
                while(lock[26][0]) {
                    #pragma omp flush(lock[26][0])
                }

                eval_4_isog_mod(pts[271], pts[278], coeff[31]);
                eval_4_isog_mod(pts[278], pts[281], coeff[32]);
                get_4_isog(pts[281], A24plus[34], C24[34], coeff[33]);
                lock[27][1] = 0;
                while(lock[27][0]) {
                    #pragma omp flush(lock[27][0])
                }

                eval_4_isog_mod(pts[280], pts[283], coeff[31]);
                eval_4_isog_mod(pts[283], pts[285], coeff[32]);
                eval_4_isog_mod(pts[285], pts[287], coeff[33]);
                lock[28][1] = 0;
                while(lock[28][0]) {
                    #pragma omp flush(lock[28][0])
                }

                eval_4_isog_mod(pts[287], pts[289], coeff[34]);
                lock[29][1] = 0;
                while(lock[29][0]) {
                    #pragma omp flush(lock[29][0])
                }

                eval_4_isog_mod(pts[289], pts[290], coeff[35]);
                xDBLe(pts[290], pts[292], A24plus[36], C24[36], 2);
                xDBLe(pts[292], pts[294], A24plus[36], C24[36], 2);
                xDBLe(pts[294], pts[296], A24plus[36], C24[36], 2);
                xDBLe(pts[296], pts[298], A24plus[36], C24[36], 2);
                xDBLe(pts[298], pts[300], A24plus[36], C24[36], 2);
                xDBLe(pts[300], pts[302], A24plus[36], C24[36], 2);
                xDBLe(pts[302], pts[304], A24plus[36], C24[36], 2);
                xDBLe(pts[304], pts[306], A24plus[36], C24[36], 2);
                xDBLe(pts[306], pts[308], A24plus[36], C24[36], 2);
                xDBLe(pts[308], pts[310], A24plus[36], C24[36], 2);
                xDBLe(pts[310], pts[312], A24plus[36], C24[36], 2);
                xDBLe(pts[312], pts[314], A24plus[36], C24[36], 2);
                xDBLe(pts[314], pts[316], A24plus[36], C24[36], 2);
                xDBLe(pts[316], pts[318], A24plus[36], C24[36], 2);
                xDBLe(pts[318], pts[320], A24plus[36], C24[36], 2);
                xDBLe(pts[320], pts[322], A24plus[36], C24[36], 2);
                xDBLe(pts[322], pts[324], A24plus[36], C24[36], 2);
                xDBLe(pts[324], pts[326], A24plus[36], C24[36], 2);
                xDBLe(pts[326], pts[328], A24plus[36], C24[36], 2);
                xDBLe(pts[328], pts[330], A24plus[36], C24[36], 2);
                get_4_isog(pts[330], A24plus[37], C24[37], coeff[36]);
                lock[30][1] = 0;
                while(lock[30][0]) {
                    #pragma omp flush(lock[30][0])
                }

                eval_4_isog_mod(pts[326], pts[333], coeff[36]);
                lock[31][1] = 0;
                while(lock[31][0]) {
                    #pragma omp flush(lock[31][0])
                }

                eval_4_isog_mod(pts[333], pts[335], coeff[37]);
                get_4_isog(pts[335], A24plus[39], C24[39], coeff[38]);
                eval_4_isog_mod(pts[316], pts[337], coeff[36]);
                lock[32][1] = 0;
                while(lock[32][0]) {
                    #pragma omp flush(lock[32][0])
                }

                eval_4_isog_mod(pts[337], pts[339], coeff[37]);
                eval_4_isog_mod(pts[339], pts[341], coeff[38]);
                eval_4_isog_mod(pts[306], pts[342], coeff[36]);
                lock[33][1] = 0;
                while(lock[33][0]) {
                    #pragma omp flush(lock[33][0])
                }

                eval_4_isog_mod(pts[338], pts[344], coeff[39]);
                get_4_isog(pts[344], A24plus[41], C24[41], coeff[40]);
                eval_4_isog_mod(pts[343], pts[347], coeff[22]);
                lock[34][1] = 0;
                while(lock[34][0]) {
                    #pragma omp flush(lock[34][0])
                }

                eval_4_isog_mod(pts[346], pts[349], coeff[38]);
                eval_4_isog_mod(pts[347], pts[350], coeff[23]);
                lock[35][1] = 0;
                while(lock[35][0]) {
                    #pragma omp flush(lock[35][0])
                }

                eval_4_isog_mod(pts[350], pts[353], coeff[24]);
                xDBLe(pts[351], pts[354], A24plus[41], C24[41], 2);
                get_4_isog(pts[354], A24plus[42], C24[42], coeff[41]);
                lock[36][1] = 0;
                while(lock[36][0]) {
                    #pragma omp flush(lock[36][0])
                }

                eval_4_isog_mod(pts[353], pts[356], coeff[25]);
                eval_4_isog_mod(pts[348], pts[358], coeff[41]);
                eval_4_isog_mod(pts[356], pts[361], coeff[26]);
                lock[37][1] = 0;
                while(lock[37][0]) {
                    #pragma omp flush(lock[37][0])
                }

                eval_4_isog_mod(pts[358], pts[362], coeff[42]);
                get_4_isog(pts[362], A24plus[44], C24[44], coeff[43]);
                eval_4_isog_mod(pts[361], pts[365], coeff[27]);
                lock[38][1] = 0;
                while(lock[38][0]) {
                    #pragma omp flush(lock[38][0])
                }

                eval_4_isog_mod(pts[364], pts[367], coeff[38]);
                eval_4_isog_mod(pts[365], pts[368], coeff[28]);
                lock[39][1] = 0;
                while(lock[39][0]) {
                    #pragma omp flush(lock[39][0])
                }

                eval_4_isog_mod(pts[367], pts[370], coeff[39]);
                eval_4_isog_mod(pts[370], pts[373], coeff[40]);
                lock[40][1] = 0;
                while(lock[40][0]) {
                    #pragma omp flush(lock[40][0])
                }

                eval_4_isog_mod(pts[371], pts[374], coeff[30]);
                eval_4_isog_mod(pts[374], pts[377], coeff[31]);
                lock[41][1] = 0;
                while(lock[41][0]) {
                    #pragma omp flush(lock[41][0])
                }

                xDBLe(pts[375], pts[378], A24plus[44], C24[44], 2);
                get_4_isog(pts[378], A24plus[45], C24[45], coeff[44]);
                eval_4_isog_mod(pts[375], pts[381], coeff[44]);
                get_4_isog(pts[381], A24plus[46], C24[46], coeff[45]);
                lock[42][1] = 0;
                while(lock[42][0]) {
                    #pragma omp flush(lock[42][0])
                }

                eval_4_isog_mod(pts[372], pts[382], coeff[44]);
                eval_4_isog_mod(pts[380], pts[385], coeff[33]);
                eval_4_isog_mod(pts[382], pts[386], coeff[45]);
                get_4_isog(pts[386], A24plus[47], C24[47], coeff[46]);
                eval_4_isog_mod(pts[385], pts[389], coeff[34]);
                lock[43][1] = 0;
                while(lock[43][0]) {
                    #pragma omp flush(lock[43][0])
                }

                eval_4_isog_mod(pts[388], pts[391], coeff[45]);
                eval_4_isog_mod(pts[389], pts[392], coeff[35]);
                lock[44][1] = 0;
                while(lock[44][0]) {
                    #pragma omp flush(lock[44][0])
                }

                eval_4_isog_mod(pts[392], pts[395], coeff[36]);
                eval_4_isog_mod(pts[390], pts[396], coeff[47]);
                get_4_isog(pts[396], A24plus[49], C24[49], coeff[48]);
                lock[45][1] = 0;
                while(lock[45][0]) {
                    #pragma omp flush(lock[45][0])
                }

                eval_4_isog_mod(pts[395], pts[398], coeff[37]);
                eval_4_isog_mod(pts[398], pts[400], coeff[38]);
                eval_4_isog_mod(pts[400], pts[402], coeff[39]);
                eval_4_isog_mod(pts[402], pts[404], coeff[40]);
                eval_4_isog_mod(pts[404], pts[406], coeff[41]);
                eval_4_isog_mod(pts[406], pts[408], coeff[42]);
                eval_4_isog_mod(pts[408], pts[410], coeff[43]);
                eval_4_isog_mod(pts[410], pts[412], coeff[44]);
                eval_4_isog_mod(pts[412], pts[414], coeff[45]);
                lock[46][1] = 0;
                while(lock[46][0]) {
                    #pragma omp flush(lock[46][0])
                }

                eval_4_isog_mod(pts[405], pts[417], coeff[49]);
                eval_4_isog_mod(pts[414], pts[418], coeff[46]);
                eval_4_isog_mod(pts[417], pts[420], coeff[50]);
                lock[47][1] = 0;
                while(lock[47][0]) {
                    #pragma omp flush(lock[47][0])
                }

                eval_4_isog_mod(pts[420], pts[423], coeff[51]);
                eval_4_isog_mod(pts[421], pts[424], coeff[50]);
                lock[48][1] = 0;
                while(lock[48][0]) {
                    #pragma omp flush(lock[48][0])
                }

                eval_4_isog_mod(pts[424], pts[427], coeff[51]);
                lock[49][1] = 0;
                while(lock[49][0]) {
                    #pragma omp flush(lock[49][0])
                }

                eval_4_isog_mod(pts[423], pts[429], coeff[52]);
                get_4_isog(pts[429], A24plus[54], C24[54], coeff[53]);
                eval_4_isog_mod(pts[427], pts[430], coeff[52]);
                eval_4_isog_mod(pts[430], pts[432], coeff[53]);
                xDBLe(pts[432], pts[434], A24plus[54], C24[54], 2);
                lock[50][1] = 0;
                while(lock[50][0]) {
                    #pragma omp flush(lock[50][0])
                }

                eval_4_isog_mod(pts[435], pts[437], coeff[53]);
                lock[51][1] = 0;
                while(lock[51][0]) {
                    #pragma omp flush(lock[51][0])
                }

                eval_4_isog_mod(pts[434], pts[438], coeff[54]);
                get_4_isog(pts[438], A24plus[56], C24[56], coeff[55]);
                lock[52][1] = 0;
                while(lock[52][0]) {
                    #pragma omp flush(lock[52][0])
                }

                eval_4_isog_mod(pts[439], pts[441], coeff[55]);
                get_4_isog(pts[441], A24plus[57], C24[57], coeff[56]);
                eval_4_isog_mod(pts[0], pts[443], coeff[0]);
                lock[53][1] = 0;
                while(lock[53][0]) {
                    #pragma omp flush(lock[53][0])
                }

                eval_4_isog_mod(pts[443], pts[445], coeff[1]);
                eval_4_isog_mod(pts[445], pts[447], coeff[2]);
                eval_4_isog_mod(pts[447], pts[449], coeff[3]);
                eval_4_isog_mod(pts[449], pts[451], coeff[4]);
                eval_4_isog_mod(pts[451], pts[453], coeff[5]);
                eval_4_isog_mod(pts[453], pts[455], coeff[6]);
                eval_4_isog_mod(pts[455], pts[457], coeff[7]);
                eval_4_isog_mod(pts[457], pts[459], coeff[8]);
                eval_4_isog_mod(pts[459], pts[461], coeff[9]);
                eval_4_isog_mod(pts[461], pts[463], coeff[10]);
                eval_4_isog_mod(pts[463], pts[465], coeff[11]);
                eval_4_isog_mod(pts[465], pts[467], coeff[12]);
                eval_4_isog_mod(pts[467], pts[469], coeff[13]);
                eval_4_isog_mod(pts[469], pts[471], coeff[14]);
                eval_4_isog_mod(pts[471], pts[473], coeff[15]);
                eval_4_isog_mod(pts[473], pts[475], coeff[16]);
                eval_4_isog_mod(pts[475], pts[477], coeff[17]);
                eval_4_isog_mod(pts[477], pts[479], coeff[18]);
                eval_4_isog_mod(pts[479], pts[481], coeff[19]);
                eval_4_isog_mod(pts[481], pts[483], coeff[20]);
                eval_4_isog_mod(pts[483], pts[485], coeff[21]);
                eval_4_isog_mod(pts[485], pts[487], coeff[22]);
                eval_4_isog_mod(pts[487], pts[489], coeff[23]);
                eval_4_isog_mod(pts[489], pts[491], coeff[24]);
                eval_4_isog_mod(pts[491], pts[493], coeff[25]);
                eval_4_isog_mod(pts[493], pts[495], coeff[26]);
                eval_4_isog_mod(pts[495], pts[497], coeff[27]);
                eval_4_isog_mod(pts[497], pts[499], coeff[28]);
                eval_4_isog_mod(pts[499], pts[501], coeff[29]);
                eval_4_isog_mod(pts[501], pts[503], coeff[30]);
                eval_4_isog_mod(pts[503], pts[505], coeff[31]);
                eval_4_isog_mod(pts[505], pts[507], coeff[32]);
                eval_4_isog_mod(pts[507], pts[509], coeff[33]);
                lock[54][1] = 0;
                while(lock[54][0]) {
                    #pragma omp flush(lock[54][0])
                }

                eval_4_isog_mod(pts[504], pts[511], coeff[57]);
                lock[55][1] = 0;
                while(lock[55][0]) {
                    #pragma omp flush(lock[55][0])
                }

                eval_4_isog_mod(pts[500], pts[512], coeff[57]);
                eval_4_isog_mod(pts[512], pts[514], coeff[58]);
                lock[56][1] = 0;
                while(lock[56][0]) {
                    #pragma omp flush(lock[56][0])
                }

                eval_4_isog_mod(pts[514], pts[516], coeff[59]);
                xDBLe(pts[516], pts[518], A24plus[60], C24[60], 2);
                get_4_isog(pts[518], A24plus[61], C24[61], coeff[60]);
                eval_4_isog_mod(pts[516], pts[521], coeff[60]);
                get_4_isog(pts[521], A24plus[62], C24[62], coeff[61]);
                lock[57][1] = 0;
                while(lock[57][0]) {
                    #pragma omp flush(lock[57][0])
                }

                eval_4_isog_mod(pts[519], pts[522], coeff[60]);
                eval_4_isog_mod(pts[522], pts[524], coeff[61]);
                xDBLe(pts[524], pts[526], A24plus[62], C24[62], 2);
                xDBLe(pts[526], pts[528], A24plus[62], C24[62], 2);
                get_4_isog(pts[528], A24plus[63], C24[63], coeff[62]);
                lock[58][1] = 0;
                while(lock[58][0]) {
                    #pragma omp flush(lock[58][0])
                }

                eval_4_isog_mod(pts[524], pts[531], coeff[62]);
                eval_4_isog_mod(pts[468], pts[533], coeff[57]);
                lock[59][1] = 0;
                while(lock[59][0]) {
                    #pragma omp flush(lock[59][0])
                }

                eval_4_isog_mod(pts[532], pts[535], coeff[63]);
                lock[60][1] = 0;
                while(lock[60][0]) {
                    #pragma omp flush(lock[60][0])
                }

                eval_4_isog_mod(pts[533], pts[536], coeff[58]);
                eval_4_isog_mod(pts[536], pts[538], coeff[59]);
                eval_4_isog_mod(pts[538], pts[540], coeff[60]);
                eval_4_isog_mod(pts[540], pts[542], coeff[61]);
                eval_4_isog_mod(pts[542], pts[545], coeff[62]);
                lock[61][1] = 0;
                while(lock[61][0]) {
                    #pragma omp flush(lock[61][0])
                }

                eval_4_isog_mod(pts[543], pts[546], coeff[35]);
                eval_4_isog_mod(pts[546], pts[549], coeff[36]);
                lock[62][1] = 0;
                while(lock[62][0]) {
                    #pragma omp flush(lock[62][0])
                }

                eval_4_isog_mod(pts[541], pts[551], coeff[65]);
                eval_4_isog_mod(pts[537], pts[552], coeff[65]);
                lock[63][1] = 0;
                while(lock[63][0]) {
                    #pragma omp flush(lock[63][0])
                }

                eval_4_isog_mod(pts[551], pts[555], coeff[66]);
                get_4_isog(pts[555], A24plus[68], C24[68], coeff[67]);
                eval_4_isog_mod(pts[553], pts[557], coeff[65]);
                lock[64][1] = 0;
                while(lock[64][0]) {
                    #pragma omp flush(lock[64][0])
                }

                eval_4_isog_mod(pts[556], pts[559], coeff[67]);
                eval_4_isog_mod(pts[557], pts[560], coeff[66]);
                lock[65][1] = 0;
                while(lock[65][0]) {
                    #pragma omp flush(lock[65][0])
                }

                eval_4_isog_mod(pts[560], pts[563], coeff[67]);
                eval_4_isog_mod(pts[444], pts[564], coeff[57]);
                lock[66][1] = 0;
                while(lock[66][0]) {
                    #pragma omp flush(lock[66][0])
                }

                eval_4_isog_mod(pts[563], pts[567], coeff[68]);
                eval_4_isog_mod(pts[565], pts[569], coeff[41]);
                lock[67][1] = 0;
                while(lock[67][0]) {
                    #pragma omp flush(lock[67][0])
                }

                eval_4_isog_mod(pts[568], pts[571], coeff[59]);
                eval_4_isog_mod(pts[569], pts[572], coeff[42]);
                lock[68][1] = 0;
                while(lock[68][0]) {
                    #pragma omp flush(lock[68][0])
                }

                eval_4_isog_mod(pts[571], pts[574], coeff[60]);
                eval_4_isog_mod(pts[574], pts[577], coeff[61]);
                lock[69][1] = 0;
                while(lock[69][0]) {
                    #pragma omp flush(lock[69][0])
                }

                eval_4_isog_mod(pts[575], pts[578], coeff[44]);
                eval_4_isog_mod(pts[578], pts[581], coeff[45]);
                lock[70][1] = 0;
                while(lock[70][0]) {
                    #pragma omp flush(lock[70][0])
                }

                xDBLe(pts[579], pts[582], A24plus[70], C24[70], 2);
                xDBLe(pts[582], pts[585], A24plus[70], C24[70], 2);
                lock[71][1] = 0;
                while(lock[71][0]) {
                    #pragma omp flush(lock[71][0])
                }

                eval_4_isog_mod(pts[584], pts[587], coeff[47]);
                xDBLe(pts[585], pts[588], A24plus[70], C24[70], 2);
                lock[72][1] = 0;
                while(lock[72][0]) {
                    #pragma omp flush(lock[72][0])
                }

                xDBLe(pts[588], pts[591], A24plus[70], C24[70], 2);
                get_4_isog(pts[591], A24plus[71], C24[71], coeff[70]);
                eval_4_isog_mod(pts[589], pts[592], coeff[66]);
                lock[73][1] = 0;
                while(lock[73][0]) {
                    #pragma omp flush(lock[73][0])
                }

                eval_4_isog_mod(pts[585], pts[595], coeff[70]);
                eval_4_isog_mod(pts[592], pts[597], coeff[67]);
                lock[74][1] = 0;
                while(lock[74][0]) {
                    #pragma omp flush(lock[74][0])
                }

                eval_4_isog_mod(pts[595], pts[599], coeff[71]);
                get_4_isog(pts[599], A24plus[73], C24[73], coeff[72]);
                eval_4_isog_mod(pts[596], pts[600], coeff[71]);
                eval_4_isog_mod(pts[597], pts[602], coeff[68]);
                eval_4_isog_mod(pts[600], pts[604], coeff[72]);
                eval_4_isog_mod(pts[602], pts[606], coeff[69]);
                lock[75][1] = 0;
                while(lock[75][0]) {
                    #pragma omp flush(lock[75][0])
                }

                xDBLe(pts[604], pts[608], A24plus[73], C24[73], 2);
                get_4_isog(pts[608], A24plus[74], C24[74], coeff[73]);
                eval_4_isog_mod(pts[607], pts[611], coeff[53]);
                lock[76][1] = 0;
                while(lock[76][0]) {
                    #pragma omp flush(lock[76][0])
                }

                eval_4_isog_mod(pts[604], pts[612], coeff[73]);
                get_4_isog(pts[612], A24plus[75], C24[75], coeff[74]);
                eval_4_isog_mod(pts[611], pts[615], coeff[54]);
                lock[77][1] = 0;
                while(lock[77][0]) {
                    #pragma omp flush(lock[77][0])
                }

                eval_4_isog_mod(pts[614], pts[617], coeff[72]);
                eval_4_isog_mod(pts[615], pts[618], coeff[55]);
                lock[78][1] = 0;
                while(lock[78][0]) {
                    #pragma omp flush(lock[78][0])
                }

                eval_4_isog_mod(pts[617], pts[620], coeff[73]);
                eval_4_isog_mod(pts[620], pts[623], coeff[74]);
                lock[79][1] = 0;
                while(lock[79][0]) {
                    #pragma omp flush(lock[79][0])
                }

                eval_4_isog_mod(pts[621], pts[624], coeff[57]);
                eval_4_isog_mod(pts[623], pts[627], coeff[75]);
                eval_4_isog_mod(pts[624], pts[628], coeff[58]);
                lock[80][1] = 0;
                while(lock[80][0]) {
                    #pragma omp flush(lock[80][0])
                }

                eval_4_isog_mod(pts[628], pts[631], coeff[59]);
                eval_4_isog_mod(pts[631], pts[633], coeff[60]);
                eval_4_isog_mod(pts[633], pts[635], coeff[61]);
                eval_4_isog_mod(pts[635], pts[637], coeff[62]);
                eval_4_isog_mod(pts[637], pts[639], coeff[63]);
                eval_4_isog_mod(pts[639], pts[641], coeff[64]);
                eval_4_isog_mod(pts[641], pts[643], coeff[65]);
                eval_4_isog_mod(pts[643], pts[645], coeff[66]);
                eval_4_isog_mod(pts[645], pts[647], coeff[67]);
                eval_4_isog_mod(pts[647], pts[649], coeff[68]);
                eval_4_isog_mod(pts[649], pts[651], coeff[69]);
                eval_4_isog_mod(pts[651], pts[653], coeff[70]);
                eval_4_isog_mod(pts[653], pts[655], coeff[71]);
                lock[81][1] = 0;
                while(lock[81][0]) {
                    #pragma omp flush(lock[81][0])
                }

                eval_4_isog_mod(pts[652], pts[656], coeff[78]);
                get_4_isog(pts[656], A24plus[80], C24[80], coeff[79]);
                eval_4_isog_mod(pts[646], pts[658], coeff[78]);
                lock[82][1] = 0;
                while(lock[82][0]) {
                    #pragma omp flush(lock[82][0])
                }

                eval_4_isog_mod(pts[657], pts[660], coeff[79]);
                get_4_isog(pts[660], A24plus[81], C24[81], coeff[80]);
                eval_4_isog_mod(pts[659], pts[663], coeff[73]);
                lock[83][1] = 0;
                while(lock[83][0]) {
                    #pragma omp flush(lock[83][0])
                }

                eval_4_isog_mod(pts[661], pts[664], coeff[80]);
                xDBLe(pts[664], pts[667], A24plus[81], C24[81], 2);
                get_4_isog(pts[667], A24plus[82], C24[82], coeff[81]);
                eval_4_isog_mod(pts[632], pts[669], coeff[78]);
                eval_4_isog_mod(pts[664], pts[671], coeff[81]);
                get_4_isog(pts[671], A24plus[83], C24[83], coeff[82]);
                lock[84][1] = 0;
                while(lock[84][0]) {
                    #pragma omp flush(lock[84][0])
                }

                eval_4_isog_mod(pts[668], pts[672], coeff[81]);
                eval_4_isog_mod(pts[672], pts[675], coeff[82]);
                lock[85][1] = 0;
                while(lock[85][0]) {
                    #pragma omp flush(lock[85][0])
                }

                eval_4_isog_mod(pts[674], pts[677], coeff[77]);
                xDBLe(pts[675], pts[678], A24plus[83], C24[83], 2);
                lock[86][1] = 0;
                while(lock[86][0]) {
                    #pragma omp flush(lock[86][0])
                }

                xDBLe(pts[678], pts[681], A24plus[83], C24[83], 2);
                get_4_isog(pts[681], A24plus[84], C24[84], coeff[83]);
                eval_4_isog_mod(pts[679], pts[682], coeff[82]);
                lock[87][1] = 0;
                while(lock[87][0]) {
                    #pragma omp flush(lock[87][0])
                }

                eval_4_isog_mod(pts[675], pts[685], coeff[83]);
                eval_4_isog_mod(pts[683], pts[687], coeff[80]);
                lock[88][1] = 0;
                while(lock[88][0]) {
                    #pragma omp flush(lock[88][0])
                }

                eval_4_isog_mod(pts[685], pts[688], coeff[84]);
                get_4_isog(pts[688], A24plus[86], C24[86], coeff[85]);
                lock[89][1] = 0;
                while(lock[89][0]) {
                    #pragma omp flush(lock[89][0])
                }

                eval_4_isog_mod(pts[687], pts[690], coeff[81]);
                eval_4_isog_mod(pts[690], pts[692], coeff[82]);
                eval_4_isog_mod(pts[692], pts[694], coeff[83]);
                eval_4_isog_mod(pts[694], pts[696], coeff[84]);
                eval_4_isog_mod(pts[696], pts[698], coeff[85]);
                lock[90][1] = 0;
                while(lock[90][0]) {
                    #pragma omp flush(lock[90][0])
                }

                eval_4_isog_mod(pts[691], pts[701], coeff[86]);
                eval_4_isog_mod(pts[698], pts[702], coeff[86]);
                lock[91][1] = 0;
                while(lock[91][0]) {
                    #pragma omp flush(lock[91][0])
                }

                eval_4_isog_mod(pts[702], pts[705], coeff[87]);
                eval_4_isog_mod(pts[705], pts[707], coeff[88]);
                lock[92][1] = 0;
                while(lock[92][0]) {
                    #pragma omp flush(lock[92][0])
                }

                lock[93][1] = 0;
                while(lock[93][0]) {
                    #pragma omp flush(lock[93][0])
                }

                eval_4_isog_mod(pts[802], pts[804], coeff[90]);
                get_4_isog(pts[804], A24plus[92], C24[92], coeff[91]);
                lock[94][1] = 0;
                while(lock[94][0]) {
                    #pragma omp flush(lock[94][0])
                }

                eval_4_isog_mod(pts[805], pts[807], coeff[91]);
                get_4_isog(pts[807], A24plus[93], C24[93], coeff[92]);
                eval_4_isog_mod(pts[796], pts[809], coeff[90]);
                lock[95][1] = 0;
                while(lock[95][0]) {
                    #pragma omp flush(lock[95][0])
                }

                eval_4_isog_mod(pts[809], pts[811], coeff[91]);
                eval_4_isog_mod(pts[811], pts[813], coeff[92]);
                eval_4_isog_mod(pts[791], pts[814], coeff[90]);
                lock[96][1] = 0;
                while(lock[96][0]) {
                    #pragma omp flush(lock[96][0])
                }

                eval_4_isog_mod(pts[813], pts[816], coeff[93]);
                eval_4_isog_mod(pts[816], pts[818], coeff[94]);
                xDBLe(pts[818], pts[820], A24plus[95], C24[95], 2);
                xDBLe(pts[820], pts[822], A24plus[95], C24[95], 2);
                get_4_isog(pts[822], A24plus[96], C24[96], coeff[95]);
                lock[97][1] = 0;
                while(lock[97][0]) {
                    #pragma omp flush(lock[97][0])
                }

                eval_4_isog_mod(pts[818], pts[825], coeff[95]);
                eval_4_isog_mod(pts[783], pts[827], coeff[90]);
                lock[98][1] = 0;
                while(lock[98][0]) {
                    #pragma omp flush(lock[98][0])
                }

                eval_4_isog_mod(pts[825], pts[828], coeff[96]);
                get_4_isog(pts[828], A24plus[98], C24[98], coeff[97]);
                lock[99][1] = 0;
                while(lock[99][0]) {
                    #pragma omp flush(lock[99][0])
                }

                eval_4_isog_mod(pts[827], pts[830], coeff[91]);
                eval_4_isog_mod(pts[830], pts[832], coeff[92]);
                eval_4_isog_mod(pts[832], pts[834], coeff[93]);
                eval_4_isog_mod(pts[834], pts[836], coeff[94]);
                eval_4_isog_mod(pts[836], pts[838], coeff[95]);
                eval_4_isog_mod(pts[838], pts[840], coeff[96]);
                lock[100][1] = 0;
                while(lock[100][0]) {
                    #pragma omp flush(lock[100][0])
                }

                eval_4_isog_mod(pts[831], pts[843], coeff[98]);
                eval_4_isog_mod(pts[840], pts[844], coeff[97]);
                lock[101][1] = 0;
                while(lock[101][0]) {
                    #pragma omp flush(lock[101][0])
                }

                eval_4_isog_mod(pts[843], pts[846], coeff[99]);
                eval_4_isog_mod(pts[846], pts[848], coeff[100]);
                xDBLe(pts[848], pts[850], A24plus[101], C24[101], 2);
                get_4_isog(pts[850], A24plus[102], C24[102], coeff[101]);
                eval_4_isog_mod(pts[848], pts[853], coeff[101]);
                get_4_isog(pts[853], A24plus[103], C24[103], coeff[102]);
                lock[102][1] = 0;
                while(lock[102][0]) {
                    #pragma omp flush(lock[102][0])
                }

                eval_4_isog_mod(pts[851], pts[854], coeff[101]);
                eval_4_isog_mod(pts[854], pts[856], coeff[102]);
                xDBLe(pts[856], pts[858], A24plus[103], C24[103], 2);
                xDBLe(pts[858], pts[860], A24plus[103], C24[103], 2);
                xDBLe(pts[860], pts[862], A24plus[103], C24[103], 2);
                xDBLe(pts[862], pts[864], A24plus[103], C24[103], 2);
                xDBLe(pts[864], pts[866], A24plus[103], C24[103], 2);
                xDBLe(pts[866], pts[868], A24plus[103], C24[103], 2);
                xDBLe(pts[868], pts[870], A24plus[103], C24[103], 2);
                get_4_isog(pts[870], A24plus[104], C24[104], coeff[103]);
                lock[103][1] = 0;
                while(lock[103][0]) {
                    #pragma omp flush(lock[103][0])
                }

                eval_4_isog_mod(pts[866], pts[873], coeff[103]);
                eval_4_isog_mod(pts[871], pts[875], coeff[100]);
                lock[104][1] = 0;
                while(lock[104][0]) {
                    #pragma omp flush(lock[104][0])
                }

                eval_4_isog_mod(pts[874], pts[877], coeff[104]);
                eval_4_isog_mod(pts[856], pts[878], coeff[103]);
                lock[105][1] = 0;
                while(lock[105][0]) {
                    #pragma omp flush(lock[105][0])
                }

                eval_4_isog_mod(pts[878], pts[881], coeff[104]);
                eval_4_isog_mod(pts[879], pts[882], coeff[102]);
                lock[106][1] = 0;
                while(lock[106][0]) {
                    #pragma omp flush(lock[106][0])
                }

                eval_4_isog_mod(pts[882], pts[885], coeff[103]);
                eval_4_isog_mod(pts[880], pts[886], coeff[106]);
                get_4_isog(pts[886], A24plus[108], C24[108], coeff[107]);
                lock[107][1] = 0;
                while(lock[107][0]) {
                    #pragma omp flush(lock[107][0])
                }

                eval_4_isog_mod(pts[885], pts[888], coeff[104]);
                eval_4_isog_mod(pts[888], pts[890], coeff[105]);
                eval_4_isog_mod(pts[890], pts[892], coeff[106]);
                eval_4_isog_mod(pts[892], pts[894], coeff[107]);
                lock[108][1] = 0;
                while(lock[108][0]) {
                    #pragma omp flush(lock[108][0])
                }

                eval_4_isog_mod(pts[891], pts[896], coeff[108]);
                get_4_isog(pts[896], A24plus[110], C24[110], coeff[109]);
                eval_4_isog_mod(pts[894], pts[898], coeff[108]);
                lock[109][1] = 0;
                while(lock[109][0]) {
                    #pragma omp flush(lock[109][0])
                }

                eval_4_isog_mod(pts[897], pts[900], coeff[109]);
                get_4_isog(pts[900], A24plus[111], C24[111], coeff[110]);
                lock[110][1] = 0;
                while(lock[110][0]) {
                    #pragma omp flush(lock[110][0])
                }

                eval_4_isog_mod(pts[899], pts[902], coeff[92]);
                eval_4_isog_mod(pts[902], pts[904], coeff[93]);
                eval_4_isog_mod(pts[904], pts[906], coeff[94]);
                eval_4_isog_mod(pts[906], pts[908], coeff[95]);
                eval_4_isog_mod(pts[908], pts[910], coeff[96]);
                eval_4_isog_mod(pts[910], pts[912], coeff[97]);
                eval_4_isog_mod(pts[912], pts[914], coeff[98]);
                eval_4_isog_mod(pts[914], pts[916], coeff[99]);
                eval_4_isog_mod(pts[916], pts[918], coeff[100]);
                eval_4_isog_mod(pts[918], pts[920], coeff[101]);
                eval_4_isog_mod(pts[920], pts[922], coeff[102]);
                eval_4_isog_mod(pts[922], pts[924], coeff[103]);
                eval_4_isog_mod(pts[924], pts[926], coeff[104]);
                lock[111][1] = 0;
                while(lock[111][0]) {
                    #pragma omp flush(lock[111][0])
                }

                eval_4_isog_mod(pts[921], pts[928], coeff[111]);
                eval_4_isog_mod(pts[928], pts[931], coeff[112]);
                get_4_isog(pts[931], A24plus[114], C24[114], coeff[113]);
                eval_4_isog_mod(pts[911], pts[933], coeff[111]);
                lock[112][1] = 0;
                while(lock[112][0]) {
                    #pragma omp flush(lock[112][0])
                }

                eval_4_isog_mod(pts[932], pts[935], coeff[113]);
                eval_4_isog_mod(pts[933], pts[936], coeff[112]);
                lock[113][1] = 0;
                while(lock[113][0]) {
                    #pragma omp flush(lock[113][0])
                }

                xDBLe(pts[935], pts[938], A24plus[114], C24[114], 2);
                get_4_isog(pts[938], A24plus[115], C24[115], coeff[114]);
                eval_4_isog_mod(pts[903], pts[940], coeff[111]);
                lock[114][1] = 0;
                while(lock[114][0]) {
                    #pragma omp flush(lock[114][0])
                }

                eval_4_isog_mod(pts[935], pts[942], coeff[114]);
                get_4_isog(pts[942], A24plus[116], C24[116], coeff[115]);
                eval_4_isog_mod(pts[940], pts[944], coeff[112]);
                lock[115][1] = 0;
                while(lock[115][0]) {
                    #pragma omp flush(lock[115][0])
                }

                eval_4_isog_mod(pts[943], pts[946], coeff[115]);
                xDBLe(pts[946], pts[949], A24plus[116], C24[116], 2);
                lock[116][1] = 0;
                while(lock[116][0]) {
                    #pragma omp flush(lock[116][0])
                }

                eval_4_isog_mod(pts[947], pts[950], coeff[114]);
                eval_4_isog_mod(pts[950], pts[953], coeff[115]);
                lock[117][1] = 0;
                while(lock[117][0]) {
                    #pragma omp flush(lock[117][0])
                }

                eval_4_isog_mod(pts[951], pts[954], coeff[112]);
                eval_4_isog_mod(pts[953], pts[957], coeff[116]);
                eval_4_isog_mod(pts[954], pts[958], coeff[113]);
                lock[118][1] = 0;
                while(lock[118][0]) {
                    #pragma omp flush(lock[118][0])
                }

                eval_4_isog_mod(pts[958], pts[961], coeff[114]);
                eval_4_isog_mod(pts[961], pts[963], coeff[115]);
                eval_4_isog_mod(pts[963], pts[965], coeff[116]);
                eval_4_isog_mod(pts[734], pts[966], coeff[90]);
                lock[119][1] = 0;
                while(lock[119][0]) {
                    #pragma omp flush(lock[119][0])
                }

                eval_4_isog_mod(pts[965], pts[968], coeff[117]);
                eval_4_isog_mod(pts[968], pts[971], coeff[118]);
                lock[120][1] = 0;
                while(lock[120][0]) {
                    #pragma omp flush(lock[120][0])
                }

                eval_4_isog_mod(pts[969], pts[972], coeff[92]);
                eval_4_isog_mod(pts[962], pts[975], coeff[119]);
                eval_4_isog_mod(pts[972], pts[977], coeff[93]);
                lock[121][1] = 0;
                while(lock[121][0]) {
                    #pragma omp flush(lock[121][0])
                }

                eval_4_isog_mod(pts[974], pts[978], coeff[120]);
                get_4_isog(pts[978], A24plus[122], C24[122], coeff[121]);
                eval_4_isog_mod(pts[976], pts[980], coeff[120]);
                lock[122][1] = 0;
                while(lock[122][0]) {
                    #pragma omp flush(lock[122][0])
                }

                eval_4_isog_mod(pts[980], pts[983], coeff[121]);
                lock[123][1] = 0;
                while(lock[123][0]) {
                    #pragma omp flush(lock[123][0])
                }

                eval_4_isog_mod(pts[981], pts[984], coeff[95]);
                eval_4_isog_mod(pts[984], pts[986], coeff[96]);
                eval_4_isog_mod(pts[986], pts[988], coeff[97]);
                eval_4_isog_mod(pts[988], pts[990], coeff[98]);
                eval_4_isog_mod(pts[990], pts[992], coeff[99]);
                eval_4_isog_mod(pts[992], pts[994], coeff[100]);
                eval_4_isog_mod(pts[994], pts[996], coeff[101]);
                eval_4_isog_mod(pts[996], pts[998], coeff[102]);
                eval_4_isog_mod(pts[998], pts[1000], coeff[103]);
                eval_4_isog_mod(pts[1000], pts[1002], coeff[104]);
                eval_4_isog_mod(pts[1002], pts[1004], coeff[105]);
                eval_4_isog_mod(pts[1004], pts[1006], coeff[106]);
                eval_4_isog_mod(pts[1006], pts[1008], coeff[107]);
                eval_4_isog_mod(pts[1008], pts[1010], coeff[108]);
                eval_4_isog_mod(pts[1010], pts[1012], coeff[109]);
                eval_4_isog_mod(pts[1012], pts[1014], coeff[110]);
                eval_4_isog_mod(pts[1014], pts[1016], coeff[111]);
                eval_4_isog_mod(pts[1016], pts[1018], coeff[112]);
                lock[124][1] = 0;
                while(lock[124][0]) {
                    #pragma omp flush(lock[124][0])
                }

                eval_4_isog_mod(pts[1009], pts[1021], coeff[123]);
                eval_4_isog_mod(pts[1018], pts[1022], coeff[113]);
                eval_4_isog_mod(pts[1021], pts[1024], coeff[124]);
                lock[125][1] = 0;
                while(lock[125][0]) {
                    #pragma omp flush(lock[125][0])
                }

                eval_4_isog_mod(pts[1024], pts[1027], coeff[125]);
                eval_4_isog_mod(pts[1025], pts[1028], coeff[124]);
                lock[126][1] = 0;
                while(lock[126][0]) {
                    #pragma omp flush(lock[126][0])
                }

                eval_4_isog_mod(pts[1028], pts[1031], coeff[125]);
                eval_4_isog_mod(pts[995], pts[1032], coeff[123]);
                lock[127][1] = 0;
                while(lock[127][0]) {
                    #pragma omp flush(lock[127][0])
                }

                eval_4_isog_mod(pts[1031], pts[1035], coeff[126]);
                eval_4_isog_mod(pts[1032], pts[1036], coeff[124]);
                lock[128][1] = 0;
                while(lock[128][0]) {
                    #pragma omp flush(lock[128][0])
                }

                eval_4_isog_mod(pts[1036], pts[1039], coeff[125]);
                eval_4_isog_mod(pts[1037], pts[1040], coeff[118]);
                eval_4_isog_mod(pts[1039], pts[1042], coeff[126]);
                eval_4_isog_mod(pts[1040], pts[1044], coeff[119]);
                eval_4_isog_mod(pts[1042], pts[1046], coeff[127]);
                eval_4_isog_mod(pts[1044], pts[1048], coeff[120]);
                lock[129][1] = 0;
                while(lock[129][0]) {
                    #pragma omp flush(lock[129][0])
                }

                eval_4_isog_mod(pts[1038], pts[1050], coeff[128]);
                eval_4_isog_mod(pts[1048], pts[1053], coeff[121]);
                eval_4_isog_mod(pts[1050], pts[1054], coeff[129]);
                get_4_isog(pts[1054], A24plus[131], C24[131], coeff[130]);
                eval_4_isog_mod(pts[1053], pts[1057], coeff[122]);
                lock[130][1] = 0;
                while(lock[130][0]) {
                    #pragma omp flush(lock[130][0])
                }

                eval_4_isog_mod(pts[1055], pts[1059], coeff[130]);
                eval_4_isog_mod(pts[1057], pts[1061], coeff[123]);
                xDBLe(pts[1059], pts[1063], A24plus[131], C24[131], 2);
                eval_4_isog_mod(pts[1061], pts[1065], coeff[124]);
                xDBLe(pts[1063], pts[1067], A24plus[131], C24[131], 2);
                eval_4_isog_mod(pts[1065], pts[1069], coeff[125]);
                xDBLe(pts[1067], pts[1071], A24plus[131], C24[131], 2);
                get_4_isog(pts[1071], A24plus[132], C24[132], coeff[131]);
                eval_4_isog_mod(pts[1069], pts[1073], coeff[126]);
                eval_4_isog_mod(pts[1067], pts[1075], coeff[131]);
                get_4_isog(pts[1075], A24plus[133], C24[133], coeff[132]);
                lock[131][1] = 0;
                while(lock[131][0]) {
                    #pragma omp flush(lock[131][0])
                }

                eval_4_isog_mod(pts[1059], pts[1077], coeff[131]);
                eval_4_isog_mod(pts[1072], pts[1078], coeff[131]);
                eval_4_isog_mod(pts[1074], pts[1080], coeff[95]);
                lock[132][1] = 0;
                while(lock[132][0]) {
                    #pragma omp flush(lock[132][0])
                }

                eval_4_isog_mod(pts[1078], pts[1083], coeff[132]);
                eval_4_isog_mod(pts[1079], pts[1084], coeff[128]);
                eval_4_isog_mod(pts[1083], pts[1087], coeff[133]);
                eval_4_isog_mod(pts[1084], pts[1088], coeff[129]);
                lock[133][1] = 0;
                while(lock[133][0]) {
                    #pragma omp flush(lock[133][0])
                }

                eval_4_isog_mod(pts[1088], pts[1091], coeff[130]);
                eval_4_isog_mod(pts[1089], pts[1092], coeff[98]);
                lock[134][1] = 0;
                while(lock[134][0]) {
                    #pragma omp flush(lock[134][0])
                }

                eval_4_isog_mod(pts[1092], pts[1095], coeff[99]);
                xDBLe(pts[1093], pts[1096], A24plus[135], C24[135], 2);
                lock[135][1] = 0;
                while(lock[135][0]) {
                    #pragma omp flush(lock[135][0])
                }

                eval_4_isog_mod(pts[1095], pts[1098], coeff[100]);
                eval_4_isog_mod(pts[1098], pts[1101], coeff[101]);
                lock[136][1] = 0;
                while(lock[136][0]) {
                    #pragma omp flush(lock[136][0])
                }

                eval_4_isog_mod(pts[1100], pts[1103], coeff[134]);
                lock[137][1] = 0;
                while(lock[137][0]) {
                    #pragma omp flush(lock[137][0])
                }

                eval_4_isog_mod(pts[1099], pts[1105], coeff[135]);
                get_4_isog(pts[1105], A24plus[137], C24[137], coeff[136]);
                eval_4_isog_mod(pts[1093], pts[1107], coeff[135]);
                eval_4_isog_mod(pts[1090], pts[1108], coeff[135]);
                lock[138][1] = 0;
                while(lock[138][0]) {
                    #pragma omp flush(lock[138][0])
                }

                eval_4_isog_mod(pts[1104], pts[1110], coeff[103]);
                eval_4_isog_mod(pts[1107], pts[1112], coeff[136]);
                eval_4_isog_mod(pts[1110], pts[1115], coeff[104]);
                lock[139][1] = 0;
                while(lock[139][0]) {
                    #pragma omp flush(lock[139][0])
                }

                eval_4_isog_mod(pts[1112], pts[1116], coeff[137]);
                get_4_isog(pts[1116], A24plus[139], C24[139], coeff[138]);
                eval_4_isog_mod(pts[1114], pts[1118], coeff[137]);
                lock[140][1] = 0;
                while(lock[140][0]) {
                    #pragma omp flush(lock[140][0])
                }

                eval_4_isog_mod(pts[1117], pts[1120], coeff[138]);
                get_4_isog(pts[1120], A24plus[140], C24[140], coeff[139]);
                lock[141][1] = 0;
                while(lock[141][0]) {
                    #pragma omp flush(lock[141][0])
                }

                eval_4_isog_mod(pts[1121], pts[1123], coeff[139]);
                xDBLe(pts[1123], pts[1125], A24plus[140], C24[140], 2);
                xDBLe(pts[1125], pts[1127], A24plus[140], C24[140], 2);
                xDBLe(pts[1127], pts[1129], A24plus[140], C24[140], 2);
                xDBLe(pts[1129], pts[1131], A24plus[140], C24[140], 2);
                xDBLe(pts[1131], pts[1133], A24plus[140], C24[140], 2);
                xDBLe(pts[1133], pts[1135], A24plus[140], C24[140], 2);
                xDBLe(pts[1135], pts[1137], A24plus[140], C24[140], 2);
                xDBLe(pts[1137], pts[1139], A24plus[140], C24[140], 2);
                xDBLe(pts[1139], pts[1141], A24plus[140], C24[140], 2);
                xDBLe(pts[1141], pts[1143], A24plus[140], C24[140], 2);
                xDBLe(pts[1143], pts[1145], A24plus[140], C24[140], 2);
                xDBLe(pts[1145], pts[1147], A24plus[140], C24[140], 2);
                xDBLe(pts[1147], pts[1149], A24plus[140], C24[140], 2);
                xDBLe(pts[1149], pts[1151], A24plus[140], C24[140], 2);
                xDBLe(pts[1151], pts[1153], A24plus[140], C24[140], 2);
                xDBLe(pts[1153], pts[1155], A24plus[140], C24[140], 2);
                xDBLe(pts[1155], pts[1157], A24plus[140], C24[140], 2);
                xDBLe(pts[1157], pts[1159], A24plus[140], C24[140], 2);
                xDBLe(pts[1159], pts[1161], A24plus[140], C24[140], 2);
                get_4_isog(pts[1161], A24plus[141], C24[141], coeff[140]);
                eval_4_isog_mod(pts[1159], pts[1163], coeff[140]);
                get_4_isog(pts[1163], A24plus[142], C24[142], coeff[141]);
                lock[142][1] = 0;
                while(lock[142][0]) {
                    #pragma omp flush(lock[142][0])
                }

                eval_4_isog_mod(pts[1157], pts[1164], coeff[140]);
                eval_4_isog_mod(pts[1164], pts[1167], coeff[141]);
                get_4_isog(pts[1167], A24plus[143], C24[143], coeff[142]);
                eval_4_isog_mod(pts[1149], pts[1169], coeff[140]);
                lock[143][1] = 0;
                while(lock[143][0]) {
                    #pragma omp flush(lock[143][0])
                }

                eval_4_isog_mod(pts[1166], pts[1170], coeff[128]);
                eval_4_isog_mod(pts[1169], pts[1172], coeff[141]);
                eval_4_isog_mod(pts[1170], pts[1174], coeff[129]);
                eval_4_isog_mod(pts[1172], pts[1176], coeff[142]);
                eval_4_isog_mod(pts[1174], pts[1178], coeff[130]);
                lock[144][1] = 0;
                while(lock[144][0]) {
                    #pragma omp flush(lock[144][0])
                }

                eval_4_isog_mod(pts[1176], pts[1180], coeff[143]);
                eval_4_isog_mod(pts[1178], pts[1183], coeff[131]);
                eval_4_isog_mod(pts[1180], pts[1184], coeff[144]);
                eval_4_isog_mod(pts[1183], pts[1187], coeff[132]);
                xDBLe(pts[1184], pts[1188], A24plus[145], C24[145], 2);
                get_4_isog(pts[1188], A24plus[146], C24[146], coeff[145]);
                eval_4_isog_mod(pts[1187], pts[1191], coeff[133]);
                lock[145][1] = 0;
                while(lock[145][0]) {
                    #pragma omp flush(lock[145][0])
                }

                eval_4_isog_mod(pts[1184], pts[1192], coeff[145]);
                get_4_isog(pts[1192], A24plus[147], C24[147], coeff[146]);
                eval_4_isog_mod(pts[1190], pts[1194], coeff[143]);
                lock[146][1] = 0;
                while(lock[146][0]) {
                    #pragma omp flush(lock[146][0])
                }

                eval_4_isog_mod(pts[1193], pts[1197], coeff[146]);
                eval_4_isog_mod(pts[1194], pts[1198], coeff[144]);
                xDBLe(pts[1197], pts[1201], A24plus[147], C24[147], 2);
                eval_4_isog_mod(pts[1198], pts[1202], coeff[145]);
                xDBLe(pts[1201], pts[1205], A24plus[147], C24[147], 2);
                get_4_isog(pts[1205], A24plus[148], C24[148], coeff[147]);
                eval_4_isog_mod(pts[1202], pts[1206], coeff[146]);
                eval_4_isog_mod(pts[1201], pts[1209], coeff[147]);
                get_4_isog(pts[1209], A24plus[149], C24[149], coeff[148]);
                lock[147][1] = 0;
                while(lock[147][0]) {
                    #pragma omp flush(lock[147][0])
                }

                eval_4_isog_mod(pts[1206], pts[1211], coeff[147]);
                eval_4_isog_mod(pts[1208], pts[1213], coeff[138]);
                eval_4_isog_mod(pts[1211], pts[1215], coeff[148]);
                eval_4_isog_mod(pts[1213], pts[1217], coeff[139]);
                lock[148][1] = 0;
                while(lock[148][0]) {
                    #pragma omp flush(lock[148][0])
                }

                eval_4_isog_mod(pts[1216], pts[1219], coeff[146]);
                eval_4_isog_mod(pts[1217], pts[1220], coeff[140]);
                lock[149][1] = 0;
                while(lock[149][0]) {
                    #pragma omp flush(lock[149][0])
                }

                eval_4_isog_mod(pts[1220], pts[1223], coeff[141]);
                xDBLe(pts[1221], pts[1224], A24plus[150], C24[150], 2);
                lock[150][1] = 0;
                while(lock[150][0]) {
                    #pragma omp flush(lock[150][0])
                }

                xDBLe(pts[1224], pts[1227], A24plus[150], C24[150], 2);
                get_4_isog(pts[1227], A24plus[151], C24[151], coeff[150]);
                eval_4_isog_mod(pts[1225], pts[1228], coeff[149]);
                lock[151][1] = 0;
                while(lock[151][0]) {
                    #pragma omp flush(lock[151][0])
                }

                eval_4_isog_mod(pts[1221], pts[1231], coeff[150]);
                eval_4_isog_mod(pts[1228], pts[1233], coeff[150]);
                lock[152][1] = 0;
                while(lock[152][0]) {
                    #pragma omp flush(lock[152][0])
                }

                eval_4_isog_mod(pts[1231], pts[1235], coeff[151]);
                get_4_isog(pts[1235], A24plus[153], C24[153], coeff[152]);
                eval_4_isog_mod(pts[1232], pts[1236], coeff[151]);
                eval_4_isog_mod(pts[1236], pts[1239], coeff[152]);
                get_4_isog(pts[1239], A24plus[154], C24[154], coeff[153]);
                lock[153][1] = 0;
                while(lock[153][0]) {
                    #pragma omp flush(lock[153][0])
                }

                eval_4_isog_mod(pts[1238], pts[1241], coeff[146]);
                eval_4_isog_mod(pts[1241], pts[1243], coeff[147]);
                eval_4_isog_mod(pts[1243], pts[1245], coeff[148]);
                eval_4_isog_mod(pts[1245], pts[1247], coeff[149]);
                eval_4_isog_mod(pts[1247], pts[1249], coeff[150]);
                eval_4_isog_mod(pts[1249], pts[1251], coeff[151]);
                eval_4_isog_mod(pts[1251], pts[1253], coeff[152]);
                lock[154][1] = 0;
                while(lock[154][0]) {
                    #pragma omp flush(lock[154][0])
                }

                eval_4_isog_mod(pts[1250], pts[1254], coeff[154]);
                get_4_isog(pts[1254], A24plus[156], C24[156], coeff[155]);
                eval_4_isog_mod(pts[1242], pts[1257], coeff[154]);
                lock[155][1] = 0;
                while(lock[155][0]) {
                    #pragma omp flush(lock[155][0])
                }

                eval_4_isog_mod(pts[1255], pts[1259], coeff[155]);
                get_4_isog(pts[1259], A24plus[157], C24[157], coeff[156]);
                eval_4_isog_mod(pts[1257], pts[1261], coeff[155]);
                lock[156][1] = 0;
                while(lock[156][0]) {
                    #pragma omp flush(lock[156][0])
                }

                eval_4_isog_mod(pts[1260], pts[1263], coeff[156]);
                get_4_isog(pts[1263], A24plus[158], C24[158], coeff[157]);
                eval_4_isog_mod(pts[1261], pts[1264], coeff[156]);
                eval_4_isog_mod(pts[1264], pts[1266], coeff[157]);
                lock[157][1] = 0;
                while(lock[157][0]) {
                    #pragma omp flush(lock[157][0])
                }

                xDBLe(pts[1266], pts[1268], A24plus[158], C24[158], 2);
                get_4_isog(pts[1268], A24plus[159], C24[159], coeff[158]);
                lock[158][1] = 0;
                while(lock[158][0]) {
                    #pragma omp flush(lock[158][0])
                }

                eval_4_isog_mod(pts[1266], pts[1270], coeff[158]);
                get_4_isog(pts[1270], A24plus[160], C24[160], coeff[159]);
                lock[159][1] = 0;
                while(lock[159][0]) {
                    #pragma omp flush(lock[159][0])
                }

                lock[160][1] = 0;
                while(lock[160][0]) {
                    #pragma omp flush(lock[160][0])
                }

                eval_4_isog_mod(pts[1296], pts[1298], coeff[160]);
                get_4_isog(pts[1298], A24plus[162], C24[162], coeff[161]);
                lock[161][1] = 0;
                while(lock[161][0]) {
                    #pragma omp flush(lock[161][0])
                }

                eval_4_isog_mod(pts[1299], pts[1301], coeff[161]);
                get_4_isog(pts[1301], A24plus[163], C24[163], coeff[162]);
                eval_4_isog_mod(pts[1291], pts[1303], coeff[160]);
                lock[162][1] = 0;
                while(lock[162][0]) {
                    #pragma omp flush(lock[162][0])
                }

                eval_4_isog_mod(pts[1303], pts[1305], coeff[161]);
                eval_4_isog_mod(pts[1289], pts[1306], coeff[160]);
                lock[163][1] = 0;
                while(lock[163][0]) {
                    #pragma omp flush(lock[163][0])
                }

                eval_4_isog_mod(pts[1306], pts[1309], coeff[161]);
                eval_4_isog_mod(pts[1285], pts[1310], coeff[160]);
                eval_4_isog_mod(pts[1309], pts[1313], coeff[162]);
                eval_4_isog_mod(pts[1310], pts[1314], coeff[161]);
                lock[164][1] = 0;
                while(lock[164][0]) {
                    #pragma omp flush(lock[164][0])
                }

                eval_4_isog_mod(pts[1314], pts[1317], coeff[162]);
                xDBLe(pts[1315], pts[1318], A24plus[165], C24[165], 2);
                get_4_isog(pts[1318], A24plus[166], C24[166], coeff[165]);
                eval_4_isog_mod(pts[1317], pts[1320], coeff[163]);
                lock[165][1] = 0;
                while(lock[165][0]) {
                    #pragma omp flush(lock[165][0])
                }

                eval_4_isog_mod(pts[1315], pts[1322], coeff[165]);
                get_4_isog(pts[1322], A24plus[167], C24[167], coeff[166]);
                eval_4_isog_mod(pts[1320], pts[1324], coeff[164]);
                lock[166][1] = 0;
                while(lock[166][0]) {
                    #pragma omp flush(lock[166][0])
                }

                eval_4_isog_mod(pts[1324], pts[1327], coeff[165]);
                eval_4_isog_mod(pts[1325], pts[1328], coeff[162]);
                lock[167][1] = 0;
                while(lock[167][0]) {
                    #pragma omp flush(lock[167][0])
                }

                eval_4_isog_mod(pts[1327], pts[1330], coeff[166]);
                eval_4_isog_mod(pts[1330], pts[1333], coeff[167]);
                lock[168][1] = 0;
                while(lock[168][0]) {
                    #pragma omp flush(lock[168][0])
                }

                eval_4_isog_mod(pts[1331], pts[1334], coeff[164]);
                eval_4_isog_mod(pts[1334], pts[1336], coeff[165]);
                eval_4_isog_mod(pts[1336], pts[1339], coeff[166]);
                lock[169][1] = 0;
                while(lock[169][0]) {
                    #pragma omp flush(lock[169][0])
                }

                xDBLe(pts[1338], pts[1341], A24plus[169], C24[169], 2);
                eval_4_isog_mod(pts[1339], pts[1342], coeff[167]);
                lock[170][1] = 0;
                while(lock[170][0]) {
                    #pragma omp flush(lock[170][0])
                }

                xDBLe(pts[1341], pts[1344], A24plus[169], C24[169], 2);
                get_4_isog(pts[1344], A24plus[170], C24[170], coeff[169]);
                eval_4_isog_mod(pts[1341], pts[1347], coeff[169]);
                get_4_isog(pts[1347], A24plus[171], C24[171], coeff[170]);
                lock[171][1] = 0;
                while(lock[171][0]) {
                    #pragma omp flush(lock[171][0])
                }

                eval_4_isog_mod(pts[1335], pts[1349], coeff[169]);
                eval_4_isog_mod(pts[1346], pts[1351], coeff[164]);
                eval_4_isog_mod(pts[1349], pts[1353], coeff[170]);
                eval_4_isog_mod(pts[1351], pts[1355], coeff[165]);
                lock[172][1] = 0;
                while(lock[172][0]) {
                    #pragma omp flush(lock[172][0])
                }

                eval_4_isog_mod(pts[1353], pts[1356], coeff[171]);
                get_4_isog(pts[1356], A24plus[173], C24[173], coeff[172]);
                lock[173][1] = 0;
                while(lock[173][0]) {
                    #pragma omp flush(lock[173][0])
                }

                eval_4_isog_mod(pts[1357], pts[1359], coeff[172]);
                xDBLe(pts[1359], pts[1361], A24plus[173], C24[173], 2);
                xDBLe(pts[1361], pts[1363], A24plus[173], C24[173], 2);
                xDBLe(pts[1363], pts[1365], A24plus[173], C24[173], 2);
                xDBLe(pts[1365], pts[1367], A24plus[173], C24[173], 2);
                get_4_isog(pts[1367], A24plus[174], C24[174], coeff[173]);
                eval_4_isog_mod(pts[1365], pts[1369], coeff[173]);
                get_4_isog(pts[1369], A24plus[175], C24[175], coeff[174]);
                lock[174][1] = 0;
                while(lock[174][0]) {
                    #pragma omp flush(lock[174][0])
                }

                eval_4_isog_mod(pts[1359], pts[1371], coeff[173]);
                eval_4_isog_mod(pts[1368], pts[1372], coeff[172]);
                lock[175][1] = 0;
                while(lock[175][0]) {
                    #pragma omp flush(lock[175][0])
                }

                eval_4_isog_mod(pts[1371], pts[1374], coeff[174]);
                eval_4_isog_mod(pts[1374], pts[1376], coeff[175]);
                xDBLe(pts[1376], pts[1378], A24plus[176], C24[176], 2);
                get_4_isog(pts[1378], A24plus[177], C24[177], coeff[176]);
                lock[176][1] = 0;
                while(lock[176][0]) {
                    #pragma omp flush(lock[176][0])
                }

                eval_4_isog_mod(pts[1376], pts[1380], coeff[176]);
                get_4_isog(pts[1380], A24plus[178], C24[178], coeff[177]);
                lock[177][1] = 0;
                while(lock[177][0]) {
                    #pragma omp flush(lock[177][0])
                }

                lock[178][1] = 0;
                while(lock[178][0]) {
                    #pragma omp flush(lock[178][0])
                }

                eval_4_isog_mod(pts[1387], pts[1391], coeff[178]);
                lock[179][1] = 0;
                while(lock[179][0]) {
                    #pragma omp flush(lock[179][0])
                }

                eval_4_isog_mod(pts[1385], pts[1392], coeff[178]);
                eval_4_isog_mod(pts[1392], pts[1394], coeff[179]);
                lock[180][1] = 0;
                while(lock[180][0]) {
                    #pragma omp flush(lock[180][0])
                }

                eval_4_isog_mod(pts[1395], pts[1397], coeff[179]);
                eval_4_isog_mod(pts[1397], pts[1399], coeff[180]);
                lock[181][1] = 0;
                while(lock[181][0]) {
                    #pragma omp flush(lock[181][0])
                }

                eval_4_isog_mod(pts[1399], pts[1401], coeff[181]);
                lock[182][1] = 0;
                while(lock[182][0]) {
                    #pragma omp flush(lock[182][0])
                }

                lock[183][1] = 0;
                while(lock[183][0]) {
                    #pragma omp flush(lock[183][0])
                }

                eval_4_isog_mod(pts[1403], pts[1405], coeff[183]);
                get_4_isog(pts[1405], A24plus[185], C24[185], coeff[184]);
            }
        }
    }

    eval_4_isog(pts[1406], coeff[184]);
    get_4_isog(pts[1406], A24plus[186], C24[186], coeff[185]);

    for(int i = 0; i < MAX_Alice; i++) {
        eval_4_isog(phiP, coeff[i]);
        eval_4_isog(phiQ, coeff[i]);
        eval_4_isog(phiR, coeff[i]);
    }

    inv_3_way(phiP->Z, phiQ->Z, phiR->Z);
    fp2mul_mont(phiP->X, phiP->Z, phiP->X);
    fp2mul_mont(phiQ->X, phiQ->Z, phiQ->X);
    fp2mul_mont(phiR->X, phiR->Z, phiR->X);

    fp2_encode(phiP->X, PublicKeyA);
    fp2_encode(phiQ->X, PublicKeyA + FP2_ENCODED_BYTES);
    fp2_encode(phiR->X, PublicKeyA + 2*FP2_ENCODED_BYTES);

    return 0;
}

int EphemeralSecretAgreement_A(const unsigned char* PrivateKeyA, const unsigned char* PublicKeyB, unsigned char* SharedSecretA) {
    point_proj_t pts[1407];
    f2elm_t coeff[MAX_Alice][3], A24plus[MAX_Alice+1] = {0}, C24[MAX_Alice+1] = {0}, A = {0}, PKB[3], jinv;
    char lock1[2], lock[183][2];

    for(int i = 0; i < 2; i++)
        lock1[i] = 1;

    for(int i = 0; i < 183; i++)
        for(int j = 0; j < 2; j++)
            lock[i][j] = 1;

    fp2_decode(PublicKeyB, PKB[0]);
    fp2_decode(PublicKeyB + FP2_ENCODED_BYTES, PKB[1]);
    fp2_decode(PublicKeyB + 2*FP2_ENCODED_BYTES, PKB[2]);
    get_A(PKB[0], PKB[1], PKB[2], A);
    fpadd((digit_t*)&Montgomery_one, (digit_t*)&Montgomery_one, C24[0][0]);
    fp2add(A, C24[0], A24plus[0]);
    fpadd(C24[0][0], C24[0][0], C24[0][0]);

    omp_set_num_threads(2);
    #pragma omp parallel
    {
        #pragma omp sections
        {
            #pragma omp section
            {
                LADDER3PT(PKB[0], PKB[1], PKB[2], (digit_t*)PrivateKeyA, ALICE, pts[0], A);
                // LADDER3PT_NS(PKB[0], PKB[1], PKB[2], (digit_t*)PrivateKeyA, ALICE, pts[0], A, 2*186);
                lock1[0] = 0;
                while(lock1[1]) {
                    #pragma omp flush(lock1[1])
                }

                eval_4_isog_mod(pts[81], pts[100], coeff[0]);
                eval_4_isog_mod(pts[98], pts[102], coeff[2]);
                lock[0][0] = 0;
                while(lock[0][1]) {
                    #pragma omp flush(lock[0][1])
                }

                eval_4_isog_mod(pts[102], pts[105], coeff[3]);
                get_4_isog(pts[105], A24plus[5], C24[5], coeff[4]);
                eval_4_isog_mod(pts[103], pts[106], coeff[3]);
                eval_4_isog_mod(pts[106], pts[109], coeff[4]);
                lock[1][0] = 0;
                while(lock[1][1]) {
                    #pragma omp flush(lock[1][1])
                }

                eval_4_isog_mod(pts[108], pts[111], coeff[1]);
                xDBLe(pts[109], pts[112], A24plus[5], C24[5], 2);
                get_4_isog(pts[112], A24plus[6], C24[6], coeff[5]);
                lock[2][0] = 0;
                while(lock[2][1]) {
                    #pragma omp flush(lock[2][1])
                }

                eval_4_isog_mod(pts[111], pts[114], coeff[2]);
                eval_4_isog_mod(pts[114], pts[117], coeff[3]);
                eval_4_isog_mod(pts[117], pts[119], coeff[4]);
                eval_4_isog_mod(pts[119], pts[121], coeff[5]);
                eval_4_isog_mod(pts[68], pts[122], coeff[0]);
                lock[3][0] = 0;
                while(lock[3][1]) {
                    #pragma omp flush(lock[3][1])
                }

                eval_4_isog_mod(pts[121], pts[124], coeff[6]);
                eval_4_isog_mod(pts[118], pts[127], coeff[7]);
                eval_4_isog_mod(pts[124], pts[128], coeff[7]);
                lock[4][0] = 0;
                while(lock[4][1]) {
                    #pragma omp flush(lock[4][1])
                }

                eval_4_isog_mod(pts[128], pts[131], coeff[8]);
                lock[5][0] = 0;
                while(lock[5][1]) {
                    #pragma omp flush(lock[5][1])
                }

                eval_4_isog_mod(pts[129], pts[132], coeff[3]);
                eval_4_isog_mod(pts[132], pts[134], coeff[4]);
                eval_4_isog_mod(pts[134], pts[136], coeff[5]);
                eval_4_isog_mod(pts[136], pts[138], coeff[6]);
                eval_4_isog_mod(pts[138], pts[140], coeff[7]);
                eval_4_isog_mod(pts[140], pts[142], coeff[8]);
                lock[6][0] = 0;
                while(lock[6][1]) {
                    #pragma omp flush(lock[6][1])
                }

                eval_4_isog_mod(pts[137], pts[144], coeff[10]);
                eval_4_isog_mod(pts[144], pts[147], coeff[11]);
                get_4_isog(pts[147], A24plus[13], C24[13], coeff[12]);
                lock[7][0] = 0;
                while(lock[7][1]) {
                    #pragma omp flush(lock[7][1])
                }

                eval_4_isog_mod(pts[146], pts[149], coeff[10]);
                eval_4_isog_mod(pts[55], pts[150], coeff[0]);
                lock[8][0] = 0;
                while(lock[8][1]) {
                    #pragma omp flush(lock[8][1])
                }

                eval_4_isog_mod(pts[149], pts[152], coeff[11]);
                eval_4_isog_mod(pts[152], pts[155], coeff[12]);
                lock[9][0] = 0;
                while(lock[9][1]) {
                    #pragma omp flush(lock[9][1])
                }

                eval_4_isog_mod(pts[151], pts[157], coeff[13]);
                get_4_isog(pts[157], A24plus[15], C24[15], coeff[14]);
                eval_4_isog_mod(pts[155], pts[158], coeff[13]);
                eval_4_isog_mod(pts[158], pts[160], coeff[14]);
                xDBLe(pts[160], pts[162], A24plus[15], C24[15], 2);
                xDBLe(pts[162], pts[164], A24plus[15], C24[15], 2);
                xDBLe(pts[164], pts[166], A24plus[15], C24[15], 2);
                xDBLe(pts[166], pts[168], A24plus[15], C24[15], 2);
                xDBLe(pts[168], pts[170], A24plus[15], C24[15], 2);
                xDBLe(pts[170], pts[172], A24plus[15], C24[15], 2);
                xDBLe(pts[172], pts[174], A24plus[15], C24[15], 2);
                get_4_isog(pts[174], A24plus[16], C24[16], coeff[15]);
                lock[10][0] = 0;
                while(lock[10][1]) {
                    #pragma omp flush(lock[10][1])
                }

                eval_4_isog_mod(pts[172], pts[176], coeff[15]);
                get_4_isog(pts[176], A24plus[17], C24[17], coeff[16]);
                eval_4_isog_mod(pts[166], pts[178], coeff[15]);
                lock[11][0] = 0;
                while(lock[11][1]) {
                    #pragma omp flush(lock[11][1])
                }

                eval_4_isog_mod(pts[178], pts[181], coeff[16]);
                eval_4_isog_mod(pts[160], pts[182], coeff[15]);
                lock[12][0] = 0;
                while(lock[12][1]) {
                    #pragma omp flush(lock[12][1])
                }

                eval_4_isog_mod(pts[182], pts[185], coeff[16]);
                eval_4_isog_mod(pts[183], pts[186], coeff[14]);
                lock[13][0] = 0;
                while(lock[13][1]) {
                    #pragma omp flush(lock[13][1])
                }

                eval_4_isog_mod(pts[186], pts[189], coeff[15]);
                eval_4_isog_mod(pts[184], pts[190], coeff[18]);
                get_4_isog(pts[190], A24plus[20], C24[20], coeff[19]);
                lock[14][0] = 0;
                while(lock[14][1]) {
                    #pragma omp flush(lock[14][1])
                }

                eval_4_isog_mod(pts[189], pts[192], coeff[16]);
                eval_4_isog_mod(pts[192], pts[194], coeff[17]);
                eval_4_isog_mod(pts[194], pts[196], coeff[18]);
                eval_4_isog_mod(pts[196], pts[198], coeff[19]);
                lock[15][0] = 0;
                while(lock[15][1]) {
                    #pragma omp flush(lock[15][1])
                }

                eval_4_isog_mod(pts[193], pts[200], coeff[20]);
                eval_4_isog_mod(pts[200], pts[203], coeff[21]);
                get_4_isog(pts[203], A24plus[23], C24[23], coeff[22]);
                lock[16][0] = 0;
                while(lock[16][1]) {
                    #pragma omp flush(lock[16][1])
                }

                eval_4_isog_mod(pts[202], pts[205], coeff[1]);
                eval_4_isog_mod(pts[205], pts[207], coeff[2]);
                eval_4_isog_mod(pts[207], pts[209], coeff[3]);
                eval_4_isog_mod(pts[209], pts[211], coeff[4]);
                eval_4_isog_mod(pts[211], pts[213], coeff[5]);
                eval_4_isog_mod(pts[213], pts[215], coeff[6]);
                eval_4_isog_mod(pts[215], pts[217], coeff[7]);
                eval_4_isog_mod(pts[217], pts[219], coeff[8]);
                eval_4_isog_mod(pts[219], pts[221], coeff[9]);
                eval_4_isog_mod(pts[221], pts[223], coeff[10]);
                eval_4_isog_mod(pts[223], pts[225], coeff[11]);
                eval_4_isog_mod(pts[225], pts[227], coeff[12]);
                eval_4_isog_mod(pts[227], pts[229], coeff[13]);
                eval_4_isog_mod(pts[229], pts[231], coeff[14]);
                lock[17][0] = 0;
                while(lock[17][1]) {
                    #pragma omp flush(lock[17][1])
                }

                eval_4_isog_mod(pts[226], pts[233], coeff[23]);
                eval_4_isog_mod(pts[231], pts[235], coeff[15]);
                lock[18][0] = 0;
                while(lock[18][1]) {
                    #pragma omp flush(lock[18][1])
                }

                eval_4_isog_mod(pts[234], pts[237], coeff[24]);
                eval_4_isog_mod(pts[216], pts[238], coeff[23]);
                lock[19][0] = 0;
                while(lock[19][1]) {
                    #pragma omp flush(lock[19][1])
                }

                eval_4_isog_mod(pts[237], pts[240], coeff[25]);
                xDBLe(pts[240], pts[243], A24plus[26], C24[26], 2);
                get_4_isog(pts[243], A24plus[27], C24[27], coeff[26]);
                eval_4_isog_mod(pts[206], pts[245], coeff[23]);
                eval_4_isog_mod(pts[240], pts[247], coeff[26]);
                get_4_isog(pts[247], A24plus[28], C24[28], coeff[27]);
                lock[20][0] = 0;
                while(lock[20][1]) {
                    #pragma omp flush(lock[20][1])
                }

                eval_4_isog_mod(pts[244], pts[248], coeff[26]);
                eval_4_isog_mod(pts[248], pts[251], coeff[27]);
                lock[21][0] = 0;
                while(lock[21][1]) {
                    #pragma omp flush(lock[21][1])
                }

                eval_4_isog_mod(pts[250], pts[253], coeff[20]);
                xDBLe(pts[251], pts[254], A24plus[28], C24[28], 2);
                lock[22][0] = 0;
                while(lock[22][1]) {
                    #pragma omp flush(lock[22][1])
                }

                eval_4_isog_mod(pts[253], pts[256], coeff[21]);
                eval_4_isog_mod(pts[256], pts[259], coeff[22]);
                lock[23][0] = 0;
                while(lock[23][1]) {
                    #pragma omp flush(lock[23][1])
                }

                eval_4_isog_mod(pts[251], pts[261], coeff[28]);
                eval_4_isog_mod(pts[258], pts[262], coeff[28]);
                lock[24][0] = 0;
                while(lock[24][1]) {
                    #pragma omp flush(lock[24][1])
                }

                eval_4_isog_mod(pts[261], pts[264], coeff[29]);
                get_4_isog(pts[264], A24plus[31], C24[31], coeff[30]);
                lock[25][0] = 0;
                while(lock[25][1]) {
                    #pragma omp flush(lock[25][1])
                }

                eval_4_isog_mod(pts[263], pts[266], coeff[24]);
                eval_4_isog_mod(pts[266], pts[268], coeff[25]);
                eval_4_isog_mod(pts[268], pts[270], coeff[26]);
                eval_4_isog_mod(pts[270], pts[272], coeff[27]);
                eval_4_isog_mod(pts[272], pts[274], coeff[28]);
                eval_4_isog_mod(pts[274], pts[276], coeff[29]);
                lock[26][0] = 0;
                while(lock[26][1]) {
                    #pragma omp flush(lock[26][1])
                }

                eval_4_isog_mod(pts[267], pts[279], coeff[31]);
                eval_4_isog_mod(pts[276], pts[280], coeff[30]);
                lock[27][0] = 0;
                while(lock[27][1]) {
                    #pragma omp flush(lock[27][1])
                }

                eval_4_isog_mod(pts[280], pts[283], coeff[31]);
                eval_4_isog_mod(pts[283], pts[285], coeff[32]);
                eval_4_isog_mod(pts[285], pts[287], coeff[33]);
                lock[28][0] = 0;
                while(lock[28][1]) {
                    #pragma omp flush(lock[28][1])
                }

                eval_4_isog_mod(pts[284], pts[288], coeff[34]);
                get_4_isog(pts[288], A24plus[36], C24[36], coeff[35]);
                lock[29][0] = 0;
                while(lock[29][1]) {
                    #pragma omp flush(lock[29][1])
                }

                eval_4_isog_mod(pts[1], pts[291], coeff[0]);
                eval_4_isog_mod(pts[291], pts[293], coeff[1]);
                eval_4_isog_mod(pts[293], pts[295], coeff[2]);
                eval_4_isog_mod(pts[295], pts[297], coeff[3]);
                eval_4_isog_mod(pts[297], pts[299], coeff[4]);
                eval_4_isog_mod(pts[299], pts[301], coeff[5]);
                eval_4_isog_mod(pts[301], pts[303], coeff[6]);
                eval_4_isog_mod(pts[303], pts[305], coeff[7]);
                eval_4_isog_mod(pts[305], pts[307], coeff[8]);
                eval_4_isog_mod(pts[307], pts[309], coeff[9]);
                eval_4_isog_mod(pts[309], pts[311], coeff[10]);
                eval_4_isog_mod(pts[311], pts[313], coeff[11]);
                eval_4_isog_mod(pts[313], pts[315], coeff[12]);
                eval_4_isog_mod(pts[315], pts[317], coeff[13]);
                eval_4_isog_mod(pts[317], pts[319], coeff[14]);
                eval_4_isog_mod(pts[319], pts[321], coeff[15]);
                eval_4_isog_mod(pts[321], pts[323], coeff[16]);
                eval_4_isog_mod(pts[323], pts[325], coeff[17]);
                eval_4_isog_mod(pts[325], pts[327], coeff[18]);
                eval_4_isog_mod(pts[327], pts[329], coeff[19]);
                eval_4_isog_mod(pts[329], pts[331], coeff[20]);
                lock[30][0] = 0;
                while(lock[30][1]) {
                    #pragma omp flush(lock[30][1])
                }

                eval_4_isog_mod(pts[326], pts[333], coeff[36]);
                lock[31][0] = 0;
                while(lock[31][1]) {
                    #pragma omp flush(lock[31][1])
                }

                eval_4_isog_mod(pts[322], pts[334], coeff[36]);
                eval_4_isog_mod(pts[334], pts[336], coeff[37]);
                lock[32][0] = 0;
                while(lock[32][1]) {
                    #pragma omp flush(lock[32][1])
                }

                eval_4_isog_mod(pts[336], pts[338], coeff[38]);
                xDBLe(pts[338], pts[340], A24plus[39], C24[39], 2);
                get_4_isog(pts[340], A24plus[40], C24[40], coeff[39]);
                eval_4_isog_mod(pts[306], pts[342], coeff[36]);
                lock[33][0] = 0;
                while(lock[33][1]) {
                    #pragma omp flush(lock[33][1])
                }

                eval_4_isog_mod(pts[341], pts[345], coeff[39]);
                eval_4_isog_mod(pts[343], pts[347], coeff[22]);
                lock[34][0] = 0;
                while(lock[34][1]) {
                    #pragma omp flush(lock[34][1])
                }

                eval_4_isog_mod(pts[345], pts[348], coeff[40]);
                xDBLe(pts[348], pts[351], A24plus[41], C24[41], 2);
                lock[35][0] = 0;
                while(lock[35][1]) {
                    #pragma omp flush(lock[35][1])
                }

                eval_4_isog_mod(pts[349], pts[352], coeff[39]);
                eval_4_isog_mod(pts[352], pts[355], coeff[40]);
                lock[36][0] = 0;
                while(lock[36][1]) {
                    #pragma omp flush(lock[36][1])
                }

                eval_4_isog_mod(pts[353], pts[356], coeff[25]);
                eval_4_isog_mod(pts[355], pts[359], coeff[41]);
                eval_4_isog_mod(pts[356], pts[361], coeff[26]);
                lock[37][0] = 0;
                while(lock[37][1]) {
                    #pragma omp flush(lock[37][1])
                }

                eval_4_isog_mod(pts[359], pts[363], coeff[42]);
                eval_4_isog_mod(pts[360], pts[364], coeff[37]);
                lock[38][0] = 0;
                while(lock[38][1]) {
                    #pragma omp flush(lock[38][1])
                }

                eval_4_isog_mod(pts[363], pts[366], coeff[43]);
                xDBLe(pts[366], pts[369], A24plus[44], C24[44], 2);
                lock[39][0] = 0;
                while(lock[39][1]) {
                    #pragma omp flush(lock[39][1])
                }

                eval_4_isog_mod(pts[368], pts[371], coeff[29]);
                xDBLe(pts[369], pts[372], A24plus[44], C24[44], 2);
                lock[40][0] = 0;
                while(lock[40][1]) {
                    #pragma omp flush(lock[40][1])
                }

                xDBLe(pts[372], pts[375], A24plus[44], C24[44], 2);
                eval_4_isog_mod(pts[373], pts[376], coeff[41]);
                lock[41][0] = 0;
                while(lock[41][1]) {
                    #pragma omp flush(lock[41][1])
                }

                eval_4_isog_mod(pts[376], pts[379], coeff[42]);
                eval_4_isog_mod(pts[377], pts[380], coeff[32]);
                lock[42][0] = 0;
                while(lock[42][1]) {
                    #pragma omp flush(lock[42][1])
                }

                eval_4_isog_mod(pts[366], pts[383], coeff[44]);
                eval_4_isog_mod(pts[380], pts[385], coeff[33]);
                eval_4_isog_mod(pts[383], pts[387], coeff[45]);
                eval_4_isog_mod(pts[385], pts[389], coeff[34]);
                lock[43][0] = 0;
                while(lock[43][1]) {
                    #pragma omp flush(lock[43][1])
                }

                eval_4_isog_mod(pts[387], pts[390], coeff[46]);
                xDBLe(pts[390], pts[393], A24plus[47], C24[47], 2);
                get_4_isog(pts[393], A24plus[48], C24[48], coeff[47]);
                lock[44][0] = 0;
                while(lock[44][1]) {
                    #pragma omp flush(lock[44][1])
                }

                eval_4_isog_mod(pts[392], pts[395], coeff[36]);
                eval_4_isog_mod(pts[390], pts[396], coeff[47]);
                get_4_isog(pts[396], A24plus[49], C24[49], coeff[48]);
                lock[45][0] = 0;
                while(lock[45][1]) {
                    #pragma omp flush(lock[45][1])
                }

                eval_4_isog_mod(pts[395], pts[398], coeff[37]);
                eval_4_isog_mod(pts[398], pts[400], coeff[38]);
                eval_4_isog_mod(pts[400], pts[402], coeff[39]);
                eval_4_isog_mod(pts[402], pts[404], coeff[40]);
                eval_4_isog_mod(pts[404], pts[406], coeff[41]);
                eval_4_isog_mod(pts[406], pts[408], coeff[42]);
                eval_4_isog_mod(pts[408], pts[410], coeff[43]);
                eval_4_isog_mod(pts[410], pts[412], coeff[44]);
                eval_4_isog_mod(pts[412], pts[414], coeff[45]);
                lock[46][0] = 0;
                while(lock[46][1]) {
                    #pragma omp flush(lock[46][1])
                }

                eval_4_isog_mod(pts[405], pts[417], coeff[49]);
                eval_4_isog_mod(pts[414], pts[418], coeff[46]);
                eval_4_isog_mod(pts[417], pts[420], coeff[50]);
                lock[47][0] = 0;
                while(lock[47][1]) {
                    #pragma omp flush(lock[47][1])
                }

                eval_4_isog_mod(pts[418], pts[422], coeff[47]);
                eval_4_isog_mod(pts[422], pts[425], coeff[48]);
                lock[48][0] = 0;
                while(lock[48][1]) {
                    #pragma omp flush(lock[48][1])
                }

                xDBLe(pts[423], pts[426], A24plus[52], C24[52], 2);
                get_4_isog(pts[426], A24plus[53], C24[53], coeff[52]);
                lock[49][0] = 0;
                while(lock[49][1]) {
                    #pragma omp flush(lock[49][1])
                }

                eval_4_isog_mod(pts[425], pts[428], coeff[49]);
                eval_4_isog_mod(pts[428], pts[431], coeff[50]);
                eval_4_isog_mod(pts[431], pts[433], coeff[51]);
                eval_4_isog_mod(pts[433], pts[435], coeff[52]);
                lock[50][0] = 0;
                while(lock[50][1]) {
                    #pragma omp flush(lock[50][1])
                }

                xDBLe(pts[434], pts[436], A24plus[54], C24[54], 2);
                get_4_isog(pts[436], A24plus[55], C24[55], coeff[54]);
                lock[51][0] = 0;
                while(lock[51][1]) {
                    #pragma omp flush(lock[51][1])
                }

                eval_4_isog_mod(pts[434], pts[438], coeff[54]);
                get_4_isog(pts[438], A24plus[56], C24[56], coeff[55]);
                lock[52][0] = 0;
                while(lock[52][1]) {
                    #pragma omp flush(lock[52][1])
                }

                eval_4_isog_mod(pts[437], pts[440], coeff[54]);
                eval_4_isog_mod(pts[440], pts[442], coeff[55]);
                lock[53][0] = 0;
                while(lock[53][1]) {
                    #pragma omp flush(lock[53][1])
                }

                eval_4_isog_mod(pts[442], pts[444], coeff[56]);
                xDBLe(pts[444], pts[446], A24plus[57], C24[57], 2);
                xDBLe(pts[446], pts[448], A24plus[57], C24[57], 2);
                xDBLe(pts[448], pts[450], A24plus[57], C24[57], 2);
                xDBLe(pts[450], pts[452], A24plus[57], C24[57], 2);
                xDBLe(pts[452], pts[454], A24plus[57], C24[57], 2);
                xDBLe(pts[454], pts[456], A24plus[57], C24[57], 2);
                xDBLe(pts[456], pts[458], A24plus[57], C24[57], 2);
                xDBLe(pts[458], pts[460], A24plus[57], C24[57], 2);
                xDBLe(pts[460], pts[462], A24plus[57], C24[57], 2);
                xDBLe(pts[462], pts[464], A24plus[57], C24[57], 2);
                xDBLe(pts[464], pts[466], A24plus[57], C24[57], 2);
                xDBLe(pts[466], pts[468], A24plus[57], C24[57], 2);
                xDBLe(pts[468], pts[470], A24plus[57], C24[57], 2);
                xDBLe(pts[470], pts[472], A24plus[57], C24[57], 2);
                xDBLe(pts[472], pts[474], A24plus[57], C24[57], 2);
                xDBLe(pts[474], pts[476], A24plus[57], C24[57], 2);
                xDBLe(pts[476], pts[478], A24plus[57], C24[57], 2);
                xDBLe(pts[478], pts[480], A24plus[57], C24[57], 2);
                xDBLe(pts[480], pts[482], A24plus[57], C24[57], 2);
                xDBLe(pts[482], pts[484], A24plus[57], C24[57], 2);
                xDBLe(pts[484], pts[486], A24plus[57], C24[57], 2);
                xDBLe(pts[486], pts[488], A24plus[57], C24[57], 2);
                xDBLe(pts[488], pts[490], A24plus[57], C24[57], 2);
                xDBLe(pts[490], pts[492], A24plus[57], C24[57], 2);
                xDBLe(pts[492], pts[494], A24plus[57], C24[57], 2);
                xDBLe(pts[494], pts[496], A24plus[57], C24[57], 2);
                xDBLe(pts[496], pts[498], A24plus[57], C24[57], 2);
                xDBLe(pts[498], pts[500], A24plus[57], C24[57], 2);
                xDBLe(pts[500], pts[502], A24plus[57], C24[57], 2);
                xDBLe(pts[502], pts[504], A24plus[57], C24[57], 2);
                xDBLe(pts[504], pts[506], A24plus[57], C24[57], 2);
                xDBLe(pts[506], pts[508], A24plus[57], C24[57], 2);
                get_4_isog(pts[508], A24plus[58], C24[58], coeff[57]);
                lock[54][0] = 0;
                while(lock[54][1]) {
                    #pragma omp flush(lock[54][1])
                }

                eval_4_isog_mod(pts[504], pts[511], coeff[57]);
                lock[55][0] = 0;
                while(lock[55][1]) {
                    #pragma omp flush(lock[55][1])
                }

                eval_4_isog_mod(pts[511], pts[513], coeff[58]);
                get_4_isog(pts[513], A24plus[60], C24[60], coeff[59]);
                eval_4_isog_mod(pts[494], pts[515], coeff[57]);
                lock[56][0] = 0;
                while(lock[56][1]) {
                    #pragma omp flush(lock[56][1])
                }

                eval_4_isog_mod(pts[515], pts[517], coeff[58]);
                eval_4_isog_mod(pts[517], pts[519], coeff[59]);
                eval_4_isog_mod(pts[484], pts[520], coeff[57]);
                lock[57][0] = 0;
                while(lock[57][1]) {
                    #pragma omp flush(lock[57][1])
                }

                eval_4_isog_mod(pts[520], pts[523], coeff[58]);
                eval_4_isog_mod(pts[523], pts[525], coeff[59]);
                eval_4_isog_mod(pts[525], pts[527], coeff[60]);
                eval_4_isog_mod(pts[527], pts[529], coeff[61]);
                lock[58][0] = 0;
                while(lock[58][1]) {
                    #pragma omp flush(lock[58][1])
                }

                eval_4_isog_mod(pts[524], pts[531], coeff[62]);
                eval_4_isog_mod(pts[529], pts[532], coeff[62]);
                lock[59][0] = 0;
                while(lock[59][1]) {
                    #pragma omp flush(lock[59][1])
                }

                eval_4_isog_mod(pts[532], pts[535], coeff[63]);
                lock[60][0] = 0;
                while(lock[60][1]) {
                    #pragma omp flush(lock[60][1])
                }

                eval_4_isog_mod(pts[535], pts[537], coeff[64]);
                xDBLe(pts[537], pts[539], A24plus[65], C24[65], 2);
                xDBLe(pts[539], pts[541], A24plus[65], C24[65], 2);
                eval_4_isog_mod(pts[509], pts[543], coeff[34]);
                xDBLe(pts[541], pts[544], A24plus[65], C24[65], 2);
                lock[61][0] = 0;
                while(lock[61][1]) {
                    #pragma omp flush(lock[61][1])
                }

                eval_4_isog_mod(pts[543], pts[546], coeff[35]);
                eval_4_isog_mod(pts[546], pts[549], coeff[36]);
                lock[62][0] = 0;
                while(lock[62][1]) {
                    #pragma omp flush(lock[62][1])
                }

                eval_4_isog_mod(pts[544], pts[550], coeff[65]);
                get_4_isog(pts[550], A24plus[67], C24[67], coeff[66]);
                eval_4_isog_mod(pts[537], pts[552], coeff[65]);
                lock[63][0] = 0;
                while(lock[63][1]) {
                    #pragma omp flush(lock[63][1])
                }

                eval_4_isog_mod(pts[549], pts[554], coeff[37]);
                eval_4_isog_mod(pts[552], pts[556], coeff[66]);
                lock[64][0] = 0;
                while(lock[64][1]) {
                    #pragma omp flush(lock[64][1])
                }

                eval_4_isog_mod(pts[554], pts[558], coeff[38]);
                eval_4_isog_mod(pts[558], pts[561], coeff[39]);
                lock[65][0] = 0;
                while(lock[65][1]) {
                    #pragma omp flush(lock[65][1])
                }

                xDBLe(pts[559], pts[562], A24plus[68], C24[68], 2);
                get_4_isog(pts[562], A24plus[69], C24[69], coeff[68]);
                eval_4_isog_mod(pts[444], pts[564], coeff[57]);
                lock[66][0] = 0;
                while(lock[66][1]) {
                    #pragma omp flush(lock[66][1])
                }

                eval_4_isog_mod(pts[563], pts[567], coeff[68]);
                eval_4_isog_mod(pts[565], pts[569], coeff[41]);
                lock[67][0] = 0;
                while(lock[67][1]) {
                    #pragma omp flush(lock[67][1])
                }

                eval_4_isog_mod(pts[568], pts[571], coeff[59]);
                eval_4_isog_mod(pts[569], pts[572], coeff[42]);
                lock[68][0] = 0;
                while(lock[68][1]) {
                    #pragma omp flush(lock[68][1])
                }

                eval_4_isog_mod(pts[571], pts[574], coeff[60]);
                eval_4_isog_mod(pts[574], pts[577], coeff[61]);
                lock[69][0] = 0;
                while(lock[69][1]) {
                    #pragma omp flush(lock[69][1])
                }

                xDBLe(pts[576], pts[579], A24plus[70], C24[70], 2);
                eval_4_isog_mod(pts[577], pts[580], coeff[62]);
                lock[70][0] = 0;
                while(lock[70][1]) {
                    #pragma omp flush(lock[70][1])
                }

                eval_4_isog_mod(pts[580], pts[583], coeff[63]);
                eval_4_isog_mod(pts[581], pts[584], coeff[46]);
                lock[71][0] = 0;
                while(lock[71][1]) {
                    #pragma omp flush(lock[71][1])
                }

                eval_4_isog_mod(pts[583], pts[586], coeff[64]);
                eval_4_isog_mod(pts[586], pts[589], coeff[65]);
                lock[72][0] = 0;
                while(lock[72][1]) {
                    #pragma omp flush(lock[72][1])
                }

                xDBLe(pts[588], pts[591], A24plus[70], C24[70], 2);
                get_4_isog(pts[591], A24plus[71], C24[71], coeff[70]);
                eval_4_isog_mod(pts[589], pts[592], coeff[66]);
                lock[73][0] = 0;
                while(lock[73][1]) {
                    #pragma omp flush(lock[73][1])
                }

                eval_4_isog_mod(pts[585], pts[595], coeff[70]);
                eval_4_isog_mod(pts[579], pts[596], coeff[70]);
                lock[74][0] = 0;
                while(lock[74][1]) {
                    #pragma omp flush(lock[74][1])
                }

                eval_4_isog_mod(pts[595], pts[599], coeff[71]);
                get_4_isog(pts[599], A24plus[73], C24[73], coeff[72]);
                eval_4_isog_mod(pts[570], pts[601], coeff[70]);
                eval_4_isog_mod(pts[597], pts[602], coeff[68]);
                lock[75][0] = 0;
                while(lock[75][1]) {
                    #pragma omp flush(lock[75][1])
                }

                eval_4_isog_mod(pts[601], pts[605], coeff[71]);
                eval_4_isog_mod(pts[603], pts[607], coeff[52]);
                eval_4_isog_mod(pts[605], pts[609], coeff[72]);
                eval_4_isog_mod(pts[607], pts[611], coeff[53]);
                lock[76][0] = 0;
                while(lock[76][1]) {
                    #pragma omp flush(lock[76][1])
                }

                eval_4_isog_mod(pts[604], pts[612], coeff[73]);
                get_4_isog(pts[612], A24plus[75], C24[75], coeff[74]);
                eval_4_isog_mod(pts[611], pts[615], coeff[54]);
                lock[77][0] = 0;
                while(lock[77][1]) {
                    #pragma omp flush(lock[77][1])
                }

                eval_4_isog_mod(pts[614], pts[617], coeff[72]);
                eval_4_isog_mod(pts[615], pts[618], coeff[55]);
                lock[78][0] = 0;
                while(lock[78][1]) {
                    #pragma omp flush(lock[78][1])
                }

                eval_4_isog_mod(pts[618], pts[621], coeff[56]);
                xDBLe(pts[619], pts[622], A24plus[75], C24[75], 2);
                get_4_isog(pts[622], A24plus[76], C24[76], coeff[75]);
                lock[79][0] = 0;
                while(lock[79][1]) {
                    #pragma omp flush(lock[79][1])
                }

                eval_4_isog_mod(pts[619], pts[625], coeff[75]);
                get_4_isog(pts[625], A24plus[77], C24[77], coeff[76]);
                eval_4_isog_mod(pts[616], pts[626], coeff[75]);
                eval_4_isog_mod(pts[626], pts[629], coeff[76]);
                get_4_isog(pts[629], A24plus[78], C24[78], coeff[77]);
                lock[80][0] = 0;
                while(lock[80][1]) {
                    #pragma omp flush(lock[80][1])
                }

                eval_4_isog_mod(pts[628], pts[631], coeff[59]);
                eval_4_isog_mod(pts[631], pts[633], coeff[60]);
                eval_4_isog_mod(pts[633], pts[635], coeff[61]);
                eval_4_isog_mod(pts[635], pts[637], coeff[62]);
                eval_4_isog_mod(pts[637], pts[639], coeff[63]);
                eval_4_isog_mod(pts[639], pts[641], coeff[64]);
                eval_4_isog_mod(pts[641], pts[643], coeff[65]);
                eval_4_isog_mod(pts[643], pts[645], coeff[66]);
                eval_4_isog_mod(pts[645], pts[647], coeff[67]);
                eval_4_isog_mod(pts[647], pts[649], coeff[68]);
                eval_4_isog_mod(pts[649], pts[651], coeff[69]);
                eval_4_isog_mod(pts[651], pts[653], coeff[70]);
                eval_4_isog_mod(pts[653], pts[655], coeff[71]);
                lock[81][0] = 0;
                while(lock[81][1]) {
                    #pragma omp flush(lock[81][1])
                }

                eval_4_isog_mod(pts[652], pts[656], coeff[78]);
                get_4_isog(pts[656], A24plus[80], C24[80], coeff[79]);
                eval_4_isog_mod(pts[655], pts[659], coeff[72]);
                lock[82][0] = 0;
                while(lock[82][1]) {
                    #pragma omp flush(lock[82][1])
                }

                eval_4_isog_mod(pts[658], pts[661], coeff[79]);
                eval_4_isog_mod(pts[659], pts[663], coeff[73]);
                lock[83][0] = 0;
                while(lock[83][1]) {
                    #pragma omp flush(lock[83][1])
                }

                eval_4_isog_mod(pts[661], pts[664], coeff[80]);
                xDBLe(pts[664], pts[667], A24plus[81], C24[81], 2);
                get_4_isog(pts[667], A24plus[82], C24[82], coeff[81]);
                eval_4_isog_mod(pts[632], pts[669], coeff[78]);
                eval_4_isog_mod(pts[664], pts[671], coeff[81]);
                get_4_isog(pts[671], A24plus[83], C24[83], coeff[82]);
                lock[84][0] = 0;
                while(lock[84][1]) {
                    #pragma omp flush(lock[84][1])
                }

                eval_4_isog_mod(pts[669], pts[673], coeff[79]);
                eval_4_isog_mod(pts[670], pts[674], coeff[76]);
                lock[85][0] = 0;
                while(lock[85][1]) {
                    #pragma omp flush(lock[85][1])
                }

                eval_4_isog_mod(pts[674], pts[677], coeff[77]);
                xDBLe(pts[675], pts[678], A24plus[83], C24[83], 2);
                lock[86][0] = 0;
                while(lock[86][1]) {
                    #pragma omp flush(lock[86][1])
                }

                eval_4_isog_mod(pts[677], pts[680], coeff[78]);
                eval_4_isog_mod(pts[680], pts[683], coeff[79]);
                lock[87][0] = 0;
                while(lock[87][1]) {
                    #pragma omp flush(lock[87][1])
                }

                eval_4_isog_mod(pts[678], pts[684], coeff[83]);
                get_4_isog(pts[684], A24plus[85], C24[85], coeff[84]);
                eval_4_isog_mod(pts[683], pts[687], coeff[80]);
                lock[88][0] = 0;
                while(lock[88][1]) {
                    #pragma omp flush(lock[88][1])
                }

                eval_4_isog_mod(pts[685], pts[688], coeff[84]);
                get_4_isog(pts[688], A24plus[86], C24[86], coeff[85]);
                lock[89][0] = 0;
                while(lock[89][1]) {
                    #pragma omp flush(lock[89][1])
                }

                eval_4_isog_mod(pts[689], pts[691], coeff[85]);
                xDBLe(pts[691], pts[693], A24plus[86], C24[86], 2);
                xDBLe(pts[693], pts[695], A24plus[86], C24[86], 2);
                xDBLe(pts[695], pts[697], A24plus[86], C24[86], 2);
                get_4_isog(pts[697], A24plus[87], C24[87], coeff[86]);
                eval_4_isog_mod(pts[695], pts[699], coeff[86]);
                get_4_isog(pts[699], A24plus[88], C24[88], coeff[87]);
                lock[90][0] = 0;
                while(lock[90][1]) {
                    #pragma omp flush(lock[90][1])
                }

                eval_4_isog_mod(pts[691], pts[701], coeff[86]);
                eval_4_isog_mod(pts[698], pts[702], coeff[86]);
                lock[91][0] = 0;
                while(lock[91][1]) {
                    #pragma omp flush(lock[91][1])
                }

                eval_4_isog_mod(pts[701], pts[704], coeff[87]);
                eval_4_isog_mod(pts[704], pts[706], coeff[88]);
                get_4_isog(pts[706], A24plus[90], C24[90], coeff[89]);
                lock[92][0] = 0;
                while(lock[92][1]) {
                    #pragma omp flush(lock[92][1])
                }

                eval_4_isog_mod(pts[707], pts[708], coeff[89]);
                xDBLe(pts[708], pts[709], A24plus[90], C24[90], 2);
                xDBLe(pts[709], pts[710], A24plus[90], C24[90], 2);
                xDBLe(pts[710], pts[711], A24plus[90], C24[90], 2);
                xDBLe(pts[711], pts[712], A24plus[90], C24[90], 2);
                xDBLe(pts[712], pts[713], A24plus[90], C24[90], 2);
                xDBLe(pts[713], pts[714], A24plus[90], C24[90], 2);
                xDBLe(pts[714], pts[715], A24plus[90], C24[90], 2);
                xDBLe(pts[715], pts[716], A24plus[90], C24[90], 2);
                xDBLe(pts[716], pts[717], A24plus[90], C24[90], 2);
                xDBLe(pts[717], pts[718], A24plus[90], C24[90], 2);
                xDBLe(pts[718], pts[719], A24plus[90], C24[90], 2);
                xDBLe(pts[719], pts[720], A24plus[90], C24[90], 2);
                xDBLe(pts[720], pts[721], A24plus[90], C24[90], 2);
                xDBLe(pts[721], pts[722], A24plus[90], C24[90], 2);
                xDBLe(pts[722], pts[723], A24plus[90], C24[90], 2);
                xDBLe(pts[723], pts[724], A24plus[90], C24[90], 2);
                xDBLe(pts[724], pts[725], A24plus[90], C24[90], 2);
                xDBLe(pts[725], pts[726], A24plus[90], C24[90], 2);
                xDBLe(pts[726], pts[727], A24plus[90], C24[90], 2);
                xDBLe(pts[727], pts[728], A24plus[90], C24[90], 2);
                xDBLe(pts[728], pts[729], A24plus[90], C24[90], 2);
                xDBLe(pts[729], pts[730], A24plus[90], C24[90], 2);
                xDBLe(pts[730], pts[731], A24plus[90], C24[90], 2);
                xDBLe(pts[731], pts[732], A24plus[90], C24[90], 2);
                xDBLe(pts[732], pts[733], A24plus[90], C24[90], 2);
                xDBLe(pts[733], pts[734], A24plus[90], C24[90], 2);
                xDBLe(pts[734], pts[735], A24plus[90], C24[90], 2);
                xDBLe(pts[735], pts[736], A24plus[90], C24[90], 2);
                xDBLe(pts[736], pts[737], A24plus[90], C24[90], 2);
                xDBLe(pts[737], pts[738], A24plus[90], C24[90], 2);
                xDBLe(pts[738], pts[739], A24plus[90], C24[90], 2);
                xDBLe(pts[739], pts[740], A24plus[90], C24[90], 2);
                xDBLe(pts[740], pts[741], A24plus[90], C24[90], 2);
                xDBLe(pts[741], pts[742], A24plus[90], C24[90], 2);
                xDBLe(pts[742], pts[743], A24plus[90], C24[90], 2);
                xDBLe(pts[743], pts[744], A24plus[90], C24[90], 2);
                xDBLe(pts[744], pts[745], A24plus[90], C24[90], 2);
                xDBLe(pts[745], pts[746], A24plus[90], C24[90], 2);
                xDBLe(pts[746], pts[747], A24plus[90], C24[90], 2);
                xDBLe(pts[747], pts[748], A24plus[90], C24[90], 2);
                xDBLe(pts[748], pts[749], A24plus[90], C24[90], 2);
                xDBLe(pts[749], pts[750], A24plus[90], C24[90], 2);
                xDBLe(pts[750], pts[751], A24plus[90], C24[90], 2);
                xDBLe(pts[751], pts[752], A24plus[90], C24[90], 2);
                xDBLe(pts[752], pts[753], A24plus[90], C24[90], 2);
                xDBLe(pts[753], pts[754], A24plus[90], C24[90], 2);
                xDBLe(pts[754], pts[755], A24plus[90], C24[90], 2);
                xDBLe(pts[755], pts[756], A24plus[90], C24[90], 2);
                xDBLe(pts[756], pts[757], A24plus[90], C24[90], 2);
                xDBLe(pts[757], pts[758], A24plus[90], C24[90], 2);
                xDBLe(pts[758], pts[759], A24plus[90], C24[90], 2);
                xDBLe(pts[759], pts[760], A24plus[90], C24[90], 2);
                xDBLe(pts[760], pts[761], A24plus[90], C24[90], 2);
                xDBLe(pts[761], pts[762], A24plus[90], C24[90], 2);
                xDBLe(pts[762], pts[763], A24plus[90], C24[90], 2);
                xDBLe(pts[763], pts[764], A24plus[90], C24[90], 2);
                xDBLe(pts[764], pts[765], A24plus[90], C24[90], 2);
                xDBLe(pts[765], pts[766], A24plus[90], C24[90], 2);
                xDBLe(pts[766], pts[767], A24plus[90], C24[90], 2);
                xDBLe(pts[767], pts[768], A24plus[90], C24[90], 2);
                xDBLe(pts[768], pts[769], A24plus[90], C24[90], 2);
                xDBLe(pts[769], pts[770], A24plus[90], C24[90], 2);
                xDBLe(pts[770], pts[771], A24plus[90], C24[90], 2);
                xDBLe(pts[771], pts[772], A24plus[90], C24[90], 2);
                xDBLe(pts[772], pts[773], A24plus[90], C24[90], 2);
                xDBLe(pts[773], pts[774], A24plus[90], C24[90], 2);
                xDBLe(pts[774], pts[775], A24plus[90], C24[90], 2);
                xDBLe(pts[775], pts[776], A24plus[90], C24[90], 2);
                xDBLe(pts[776], pts[777], A24plus[90], C24[90], 2);
                xDBLe(pts[777], pts[778], A24plus[90], C24[90], 2);
                xDBLe(pts[778], pts[779], A24plus[90], C24[90], 2);
                xDBLe(pts[779], pts[780], A24plus[90], C24[90], 2);
                xDBLe(pts[780], pts[781], A24plus[90], C24[90], 2);
                xDBLe(pts[781], pts[782], A24plus[90], C24[90], 2);
                xDBLe(pts[782], pts[783], A24plus[90], C24[90], 2);
                xDBLe(pts[783], pts[784], A24plus[90], C24[90], 2);
                xDBLe(pts[784], pts[785], A24plus[90], C24[90], 2);
                xDBLe(pts[785], pts[786], A24plus[90], C24[90], 2);
                xDBLe(pts[786], pts[787], A24plus[90], C24[90], 2);
                xDBLe(pts[787], pts[788], A24plus[90], C24[90], 2);
                xDBLe(pts[788], pts[789], A24plus[90], C24[90], 2);
                xDBLe(pts[789], pts[790], A24plus[90], C24[90], 2);
                xDBLe(pts[790], pts[791], A24plus[90], C24[90], 2);
                xDBLe(pts[791], pts[792], A24plus[90], C24[90], 2);
                xDBLe(pts[792], pts[793], A24plus[90], C24[90], 2);
                xDBLe(pts[793], pts[794], A24plus[90], C24[90], 2);
                xDBLe(pts[794], pts[795], A24plus[90], C24[90], 2);
                xDBLe(pts[795], pts[796], A24plus[90], C24[90], 2);
                xDBLe(pts[796], pts[797], A24plus[90], C24[90], 2);
                xDBLe(pts[797], pts[798], A24plus[90], C24[90], 2);
                xDBLe(pts[798], pts[799], A24plus[90], C24[90], 2);
                xDBLe(pts[799], pts[800], A24plus[90], C24[90], 2);
                xDBLe(pts[800], pts[801], A24plus[90], C24[90], 2);
                xDBLe(pts[801], pts[802], A24plus[90], C24[90], 2);
                xDBLe(pts[802], pts[803], A24plus[90], C24[90], 2);
                get_4_isog(pts[803], A24plus[91], C24[91], coeff[90]);
                lock[93][0] = 0;
                while(lock[93][1]) {
                    #pragma omp flush(lock[93][1])
                }

                eval_4_isog_mod(pts[802], pts[804], coeff[90]);
                get_4_isog(pts[804], A24plus[92], C24[92], coeff[91]);
                lock[94][0] = 0;
                while(lock[94][1]) {
                    #pragma omp flush(lock[94][1])
                }

                eval_4_isog_mod(pts[805], pts[807], coeff[91]);
                get_4_isog(pts[807], A24plus[93], C24[93], coeff[92]);
                eval_4_isog_mod(pts[796], pts[809], coeff[90]);
                lock[95][0] = 0;
                while(lock[95][1]) {
                    #pragma omp flush(lock[95][1])
                }

                eval_4_isog_mod(pts[808], pts[810], coeff[92]);
                xDBLe(pts[810], pts[812], A24plus[93], C24[93], 2);
                get_4_isog(pts[812], A24plus[94], C24[94], coeff[93]);
                eval_4_isog_mod(pts[810], pts[815], coeff[93]);
                get_4_isog(pts[815], A24plus[95], C24[95], coeff[94]);
                lock[96][0] = 0;
                while(lock[96][1]) {
                    #pragma omp flush(lock[96][1])
                }

                eval_4_isog_mod(pts[814], pts[817], coeff[91]);
                eval_4_isog_mod(pts[817], pts[819], coeff[92]);
                eval_4_isog_mod(pts[819], pts[821], coeff[93]);
                eval_4_isog_mod(pts[821], pts[823], coeff[94]);
                lock[97][0] = 0;
                while(lock[97][1]) {
                    #pragma omp flush(lock[97][1])
                }

                eval_4_isog_mod(pts[818], pts[825], coeff[95]);
                eval_4_isog_mod(pts[783], pts[827], coeff[90]);
                lock[98][0] = 0;
                while(lock[98][1]) {
                    #pragma omp flush(lock[98][1])
                }

                eval_4_isog_mod(pts[825], pts[828], coeff[96]);
                get_4_isog(pts[828], A24plus[98], C24[98], coeff[97]);
                lock[99][0] = 0;
                while(lock[99][1]) {
                    #pragma omp flush(lock[99][1])
                }

                eval_4_isog_mod(pts[829], pts[831], coeff[97]);
                xDBLe(pts[831], pts[833], A24plus[98], C24[98], 2);
                xDBLe(pts[833], pts[835], A24plus[98], C24[98], 2);
                xDBLe(pts[835], pts[837], A24plus[98], C24[98], 2);
                xDBLe(pts[837], pts[839], A24plus[98], C24[98], 2);
                get_4_isog(pts[839], A24plus[99], C24[99], coeff[98]);
                eval_4_isog_mod(pts[837], pts[841], coeff[98]);
                get_4_isog(pts[841], A24plus[100], C24[100], coeff[99]);
                lock[100][0] = 0;
                while(lock[100][1]) {
                    #pragma omp flush(lock[100][1])
                }

                eval_4_isog_mod(pts[835], pts[842], coeff[98]);
                eval_4_isog_mod(pts[842], pts[845], coeff[99]);
                get_4_isog(pts[845], A24plus[101], C24[101], coeff[100]);
                lock[101][0] = 0;
                while(lock[101][1]) {
                    #pragma omp flush(lock[101][1])
                }

                eval_4_isog_mod(pts[843], pts[846], coeff[99]);
                eval_4_isog_mod(pts[846], pts[848], coeff[100]);
                xDBLe(pts[848], pts[850], A24plus[101], C24[101], 2);
                get_4_isog(pts[850], A24plus[102], C24[102], coeff[101]);
                eval_4_isog_mod(pts[848], pts[853], coeff[101]);
                get_4_isog(pts[853], A24plus[103], C24[103], coeff[102]);
                lock[102][0] = 0;
                while(lock[102][1]) {
                    #pragma omp flush(lock[102][1])
                }

                eval_4_isog_mod(pts[852], pts[855], coeff[91]);
                eval_4_isog_mod(pts[855], pts[857], coeff[92]);
                eval_4_isog_mod(pts[857], pts[859], coeff[93]);
                eval_4_isog_mod(pts[859], pts[861], coeff[94]);
                eval_4_isog_mod(pts[861], pts[863], coeff[95]);
                eval_4_isog_mod(pts[863], pts[865], coeff[96]);
                eval_4_isog_mod(pts[865], pts[867], coeff[97]);
                eval_4_isog_mod(pts[867], pts[869], coeff[98]);
                eval_4_isog_mod(pts[869], pts[871], coeff[99]);
                lock[103][0] = 0;
                while(lock[103][1]) {
                    #pragma omp flush(lock[103][1])
                }

                eval_4_isog_mod(pts[866], pts[873], coeff[103]);
                eval_4_isog_mod(pts[871], pts[875], coeff[100]);
                lock[104][0] = 0;
                while(lock[104][1]) {
                    #pragma omp flush(lock[104][1])
                }

                eval_4_isog_mod(pts[874], pts[877], coeff[104]);
                eval_4_isog_mod(pts[875], pts[879], coeff[101]);
                lock[105][0] = 0;
                while(lock[105][1]) {
                    #pragma omp flush(lock[105][1])
                }

                eval_4_isog_mod(pts[878], pts[881], coeff[104]);
                eval_4_isog_mod(pts[879], pts[882], coeff[102]);
                lock[106][0] = 0;
                while(lock[106][1]) {
                    #pragma omp flush(lock[106][1])
                }

                eval_4_isog_mod(pts[881], pts[884], coeff[105]);
                eval_4_isog_mod(pts[884], pts[887], coeff[106]);
                lock[107][0] = 0;
                while(lock[107][1]) {
                    #pragma omp flush(lock[107][1])
                }

                eval_4_isog_mod(pts[885], pts[888], coeff[104]);
                eval_4_isog_mod(pts[888], pts[890], coeff[105]);
                eval_4_isog_mod(pts[890], pts[892], coeff[106]);
                eval_4_isog_mod(pts[892], pts[894], coeff[107]);
                lock[108][0] = 0;
                while(lock[108][1]) {
                    #pragma omp flush(lock[108][1])
                }

                eval_4_isog_mod(pts[889], pts[897], coeff[108]);
                eval_4_isog_mod(pts[895], pts[899], coeff[91]);
                lock[109][0] = 0;
                while(lock[109][1]) {
                    #pragma omp flush(lock[109][1])
                }

                eval_4_isog_mod(pts[898], pts[901], coeff[109]);
                lock[110][0] = 0;
                while(lock[110][1]) {
                    #pragma omp flush(lock[110][1])
                }

                eval_4_isog_mod(pts[901], pts[903], coeff[110]);
                xDBLe(pts[903], pts[905], A24plus[111], C24[111], 2);
                xDBLe(pts[905], pts[907], A24plus[111], C24[111], 2);
                xDBLe(pts[907], pts[909], A24plus[111], C24[111], 2);
                xDBLe(pts[909], pts[911], A24plus[111], C24[111], 2);
                xDBLe(pts[911], pts[913], A24plus[111], C24[111], 2);
                xDBLe(pts[913], pts[915], A24plus[111], C24[111], 2);
                xDBLe(pts[915], pts[917], A24plus[111], C24[111], 2);
                xDBLe(pts[917], pts[919], A24plus[111], C24[111], 2);
                xDBLe(pts[919], pts[921], A24plus[111], C24[111], 2);
                xDBLe(pts[921], pts[923], A24plus[111], C24[111], 2);
                xDBLe(pts[923], pts[925], A24plus[111], C24[111], 2);
                get_4_isog(pts[925], A24plus[112], C24[112], coeff[111]);
                eval_4_isog_mod(pts[923], pts[927], coeff[111]);
                get_4_isog(pts[927], A24plus[113], C24[113], coeff[112]);
                lock[111][0] = 0;
                while(lock[111][1]) {
                    #pragma omp flush(lock[111][1])
                }

                eval_4_isog_mod(pts[917], pts[929], coeff[111]);
                eval_4_isog_mod(pts[926], pts[930], coeff[105]);
                eval_4_isog_mod(pts[929], pts[932], coeff[112]);
                lock[112][0] = 0;
                while(lock[112][1]) {
                    #pragma omp flush(lock[112][1])
                }

                eval_4_isog_mod(pts[932], pts[935], coeff[113]);
                eval_4_isog_mod(pts[933], pts[936], coeff[112]);
                lock[113][0] = 0;
                while(lock[113][1]) {
                    #pragma omp flush(lock[113][1])
                }

                eval_4_isog_mod(pts[936], pts[939], coeff[113]);
                eval_4_isog_mod(pts[903], pts[940], coeff[111]);
                lock[114][0] = 0;
                while(lock[114][1]) {
                    #pragma omp flush(lock[114][1])
                }

                eval_4_isog_mod(pts[939], pts[943], coeff[114]);
                eval_4_isog_mod(pts[940], pts[944], coeff[112]);
                lock[115][0] = 0;
                while(lock[115][1]) {
                    #pragma omp flush(lock[115][1])
                }

                eval_4_isog_mod(pts[943], pts[946], coeff[115]);
                xDBLe(pts[946], pts[949], A24plus[116], C24[116], 2);
                lock[116][0] = 0;
                while(lock[116][1]) {
                    #pragma omp flush(lock[116][1])
                }

                eval_4_isog_mod(pts[948], pts[951], coeff[111]);
                xDBLe(pts[949], pts[952], A24plus[116], C24[116], 2);
                get_4_isog(pts[952], A24plus[117], C24[117], coeff[116]);
                lock[117][0] = 0;
                while(lock[117][1]) {
                    #pragma omp flush(lock[117][1])
                }

                eval_4_isog_mod(pts[949], pts[955], coeff[116]);
                get_4_isog(pts[955], A24plus[118], C24[118], coeff[117]);
                eval_4_isog_mod(pts[953], pts[957], coeff[116]);
                lock[118][0] = 0;
                while(lock[118][1]) {
                    #pragma omp flush(lock[118][1])
                }

                eval_4_isog_mod(pts[956], pts[959], coeff[117]);
                get_4_isog(pts[959], A24plus[119], C24[119], coeff[118]);
                eval_4_isog_mod(pts[957], pts[960], coeff[117]);
                eval_4_isog_mod(pts[960], pts[962], coeff[118]);
                xDBLe(pts[962], pts[964], A24plus[119], C24[119], 2);
                xDBLe(pts[964], pts[967], A24plus[119], C24[119], 2);
                lock[119][0] = 0;
                while(lock[119][1]) {
                    #pragma omp flush(lock[119][1])
                }

                eval_4_isog_mod(pts[966], pts[969], coeff[91]);
                xDBLe(pts[967], pts[970], A24plus[119], C24[119], 2);
                get_4_isog(pts[970], A24plus[120], C24[120], coeff[119]);
                lock[120][0] = 0;
                while(lock[120][1]) {
                    #pragma omp flush(lock[120][1])
                }

                eval_4_isog_mod(pts[967], pts[973], coeff[119]);
                get_4_isog(pts[973], A24plus[121], C24[121], coeff[120]);
                eval_4_isog_mod(pts[964], pts[974], coeff[119]);
                eval_4_isog_mod(pts[971], pts[976], coeff[119]);
                lock[121][0] = 0;
                while(lock[121][1]) {
                    #pragma omp flush(lock[121][1])
                }

                eval_4_isog_mod(pts[975], pts[979], coeff[120]);
                eval_4_isog_mod(pts[976], pts[980], coeff[120]);
                lock[122][0] = 0;
                while(lock[122][1]) {
                    #pragma omp flush(lock[122][1])
                }

                eval_4_isog_mod(pts[979], pts[982], coeff[121]);
                get_4_isog(pts[982], A24plus[123], C24[123], coeff[122]);
                lock[123][0] = 0;
                while(lock[123][1]) {
                    #pragma omp flush(lock[123][1])
                }

                eval_4_isog_mod(pts[983], pts[985], coeff[122]);
                xDBLe(pts[985], pts[987], A24plus[123], C24[123], 2);
                xDBLe(pts[987], pts[989], A24plus[123], C24[123], 2);
                xDBLe(pts[989], pts[991], A24plus[123], C24[123], 2);
                xDBLe(pts[991], pts[993], A24plus[123], C24[123], 2);
                xDBLe(pts[993], pts[995], A24plus[123], C24[123], 2);
                xDBLe(pts[995], pts[997], A24plus[123], C24[123], 2);
                xDBLe(pts[997], pts[999], A24plus[123], C24[123], 2);
                xDBLe(pts[999], pts[1001], A24plus[123], C24[123], 2);
                xDBLe(pts[1001], pts[1003], A24plus[123], C24[123], 2);
                xDBLe(pts[1003], pts[1005], A24plus[123], C24[123], 2);
                xDBLe(pts[1005], pts[1007], A24plus[123], C24[123], 2);
                xDBLe(pts[1007], pts[1009], A24plus[123], C24[123], 2);
                xDBLe(pts[1009], pts[1011], A24plus[123], C24[123], 2);
                xDBLe(pts[1011], pts[1013], A24plus[123], C24[123], 2);
                xDBLe(pts[1013], pts[1015], A24plus[123], C24[123], 2);
                xDBLe(pts[1015], pts[1017], A24plus[123], C24[123], 2);
                get_4_isog(pts[1017], A24plus[124], C24[124], coeff[123]);
                eval_4_isog_mod(pts[1015], pts[1019], coeff[123]);
                get_4_isog(pts[1019], A24plus[125], C24[125], coeff[124]);
                lock[124][0] = 0;
                while(lock[124][1]) {
                    #pragma omp flush(lock[124][1])
                }

                eval_4_isog_mod(pts[1013], pts[1020], coeff[123]);
                eval_4_isog_mod(pts[1020], pts[1023], coeff[124]);
                get_4_isog(pts[1023], A24plus[126], C24[126], coeff[125]);
                eval_4_isog_mod(pts[1003], pts[1025], coeff[123]);
                lock[125][0] = 0;
                while(lock[125][1]) {
                    #pragma omp flush(lock[125][1])
                }

                eval_4_isog_mod(pts[1024], pts[1027], coeff[125]);
                eval_4_isog_mod(pts[1025], pts[1028], coeff[124]);
                lock[126][0] = 0;
                while(lock[126][1]) {
                    #pragma omp flush(lock[126][1])
                }

                xDBLe(pts[1027], pts[1030], A24plus[126], C24[126], 2);
                get_4_isog(pts[1030], A24plus[127], C24[127], coeff[126]);
                eval_4_isog_mod(pts[995], pts[1032], coeff[123]);
                lock[127][0] = 0;
                while(lock[127][1]) {
                    #pragma omp flush(lock[127][1])
                }

                eval_4_isog_mod(pts[1027], pts[1034], coeff[126]);
                get_4_isog(pts[1034], A24plus[128], C24[128], coeff[127]);
                eval_4_isog_mod(pts[1032], pts[1036], coeff[124]);
                lock[128][0] = 0;
                while(lock[128][1]) {
                    #pragma omp flush(lock[128][1])
                }

                eval_4_isog_mod(pts[1036], pts[1039], coeff[125]);
                eval_4_isog_mod(pts[1037], pts[1040], coeff[118]);
                eval_4_isog_mod(pts[1039], pts[1042], coeff[126]);
                eval_4_isog_mod(pts[1040], pts[1044], coeff[119]);
                eval_4_isog_mod(pts[1042], pts[1046], coeff[127]);
                eval_4_isog_mod(pts[1044], pts[1048], coeff[120]);
                lock[129][0] = 0;
                while(lock[129][1]) {
                    #pragma omp flush(lock[129][1])
                }

                eval_4_isog_mod(pts[1038], pts[1050], coeff[128]);
                eval_4_isog_mod(pts[1047], pts[1052], coeff[125]);
                eval_4_isog_mod(pts[1050], pts[1054], coeff[129]);
                get_4_isog(pts[1054], A24plus[131], C24[131], coeff[130]);
                eval_4_isog_mod(pts[1052], pts[1056], coeff[126]);
                lock[130][0] = 0;
                while(lock[130][1]) {
                    #pragma omp flush(lock[130][1])
                }

                eval_4_isog_mod(pts[708], pts[1058], coeff[90]);
                eval_4_isog_mod(pts[1056], pts[1060], coeff[127]);
                eval_4_isog_mod(pts[1058], pts[1062], coeff[91]);
                eval_4_isog_mod(pts[1060], pts[1064], coeff[128]);
                eval_4_isog_mod(pts[1062], pts[1066], coeff[92]);
                eval_4_isog_mod(pts[1064], pts[1068], coeff[129]);
                eval_4_isog_mod(pts[1066], pts[1070], coeff[93]);
                eval_4_isog_mod(pts[1068], pts[1072], coeff[130]);
                eval_4_isog_mod(pts[1070], pts[1074], coeff[94]);
                lock[131][0] = 0;
                while(lock[131][1]) {
                    #pragma omp flush(lock[131][1])
                }

                eval_4_isog_mod(pts[1059], pts[1077], coeff[131]);
                eval_4_isog_mod(pts[1073], pts[1079], coeff[127]);
                eval_4_isog_mod(pts[1074], pts[1080], coeff[95]);
                eval_4_isog_mod(pts[1077], pts[1082], coeff[132]);
                lock[132][0] = 0;
                while(lock[132][1]) {
                    #pragma omp flush(lock[132][1])
                }

                eval_4_isog_mod(pts[1080], pts[1085], coeff[96]);
                eval_4_isog_mod(pts[1083], pts[1087], coeff[133]);
                eval_4_isog_mod(pts[1085], pts[1089], coeff[97]);
                lock[133][0] = 0;
                while(lock[133][1]) {
                    #pragma omp flush(lock[133][1])
                }

                eval_4_isog_mod(pts[1088], pts[1091], coeff[130]);
                eval_4_isog_mod(pts[1089], pts[1092], coeff[98]);
                lock[134][0] = 0;
                while(lock[134][1]) {
                    #pragma omp flush(lock[134][1])
                }

                eval_4_isog_mod(pts[1092], pts[1095], coeff[99]);
                xDBLe(pts[1093], pts[1096], A24plus[135], C24[135], 2);
                lock[135][0] = 0;
                while(lock[135][1]) {
                    #pragma omp flush(lock[135][1])
                }

                xDBLe(pts[1096], pts[1099], A24plus[135], C24[135], 2);
                eval_4_isog_mod(pts[1097], pts[1100], coeff[133]);
                lock[136][0] = 0;
                while(lock[136][1]) {
                    #pragma omp flush(lock[136][1])
                }

                xDBLe(pts[1099], pts[1102], A24plus[135], C24[135], 2);
                get_4_isog(pts[1102], A24plus[136], C24[136], coeff[135]);
                lock[137][0] = 0;
                while(lock[137][1]) {
                    #pragma omp flush(lock[137][1])
                }

                eval_4_isog_mod(pts[1101], pts[1104], coeff[102]);
                eval_4_isog_mod(pts[1093], pts[1107], coeff[135]);
                eval_4_isog_mod(pts[1103], pts[1109], coeff[135]);
                eval_4_isog_mod(pts[1104], pts[1110], coeff[103]);
                lock[138][0] = 0;
                while(lock[138][1]) {
                    #pragma omp flush(lock[138][1])
                }

                eval_4_isog_mod(pts[1108], pts[1113], coeff[136]);
                eval_4_isog_mod(pts[1109], pts[1114], coeff[136]);
                eval_4_isog_mod(pts[1113], pts[1117], coeff[137]);
                eval_4_isog_mod(pts[1114], pts[1118], coeff[137]);
                lock[139][0] = 0;
                while(lock[139][1]) {
                    #pragma omp flush(lock[139][1])
                }

                eval_4_isog_mod(pts[1117], pts[1120], coeff[138]);
                get_4_isog(pts[1120], A24plus[140], C24[140], coeff[139]);
                lock[140][0] = 0;
                while(lock[140][1]) {
                    #pragma omp flush(lock[140][1])
                }

                eval_4_isog_mod(pts[1119], pts[1122], coeff[106]);
                eval_4_isog_mod(pts[1122], pts[1124], coeff[107]);
                eval_4_isog_mod(pts[1124], pts[1126], coeff[108]);
                eval_4_isog_mod(pts[1126], pts[1128], coeff[109]);
                eval_4_isog_mod(pts[1128], pts[1130], coeff[110]);
                eval_4_isog_mod(pts[1130], pts[1132], coeff[111]);
                eval_4_isog_mod(pts[1132], pts[1134], coeff[112]);
                eval_4_isog_mod(pts[1134], pts[1136], coeff[113]);
                eval_4_isog_mod(pts[1136], pts[1138], coeff[114]);
                eval_4_isog_mod(pts[1138], pts[1140], coeff[115]);
                eval_4_isog_mod(pts[1140], pts[1142], coeff[116]);
                eval_4_isog_mod(pts[1142], pts[1144], coeff[117]);
                eval_4_isog_mod(pts[1144], pts[1146], coeff[118]);
                eval_4_isog_mod(pts[1146], pts[1148], coeff[119]);
                eval_4_isog_mod(pts[1148], pts[1150], coeff[120]);
                eval_4_isog_mod(pts[1150], pts[1152], coeff[121]);
                eval_4_isog_mod(pts[1152], pts[1154], coeff[122]);
                eval_4_isog_mod(pts[1154], pts[1156], coeff[123]);
                eval_4_isog_mod(pts[1156], pts[1158], coeff[124]);
                eval_4_isog_mod(pts[1158], pts[1160], coeff[125]);
                eval_4_isog_mod(pts[1160], pts[1162], coeff[126]);
                lock[141][0] = 0;
                while(lock[141][1]) {
                    #pragma omp flush(lock[141][1])
                }

                eval_4_isog_mod(pts[1157], pts[1164], coeff[140]);
                eval_4_isog_mod(pts[1164], pts[1167], coeff[141]);
                get_4_isog(pts[1167], A24plus[143], C24[143], coeff[142]);
                eval_4_isog_mod(pts[1149], pts[1169], coeff[140]);
                lock[142][0] = 0;
                while(lock[142][1]) {
                    #pragma omp flush(lock[142][1])
                }

                eval_4_isog_mod(pts[1168], pts[1171], coeff[142]);
                eval_4_isog_mod(pts[1169], pts[1172], coeff[141]);
                xDBLe(pts[1171], pts[1175], A24plus[143], C24[143], 2);
                get_4_isog(pts[1175], A24plus[144], C24[144], coeff[143]);
                eval_4_isog_mod(pts[1172], pts[1176], coeff[142]);
                eval_4_isog_mod(pts[1171], pts[1179], coeff[143]);
                get_4_isog(pts[1179], A24plus[145], C24[145], coeff[144]);
                eval_4_isog_mod(pts[1176], pts[1180], coeff[143]);
                eval_4_isog_mod(pts[1135], pts[1182], coeff[140]);
                lock[143][0] = 0;
                while(lock[143][1]) {
                    #pragma omp flush(lock[143][1])
                }

                eval_4_isog_mod(pts[1181], pts[1185], coeff[143]);
                eval_4_isog_mod(pts[1182], pts[1186], coeff[141]);
                eval_4_isog_mod(pts[1185], pts[1189], coeff[144]);
                eval_4_isog_mod(pts[1186], pts[1190], coeff[142]);
                lock[144][0] = 0;
                while(lock[144][1]) {
                    #pragma omp flush(lock[144][1])
                }

                eval_4_isog_mod(pts[1184], pts[1192], coeff[145]);
                get_4_isog(pts[1192], A24plus[147], C24[147], coeff[146]);
                eval_4_isog_mod(pts[1190], pts[1194], coeff[143]);
                lock[145][0] = 0;
                while(lock[145][1]) {
                    #pragma omp flush(lock[145][1])
                }

                eval_4_isog_mod(pts[1193], pts[1197], coeff[146]);
                eval_4_isog_mod(pts[1194], pts[1198], coeff[144]);
                xDBLe(pts[1197], pts[1201], A24plus[147], C24[147], 2);
                eval_4_isog_mod(pts[1198], pts[1202], coeff[145]);
                xDBLe(pts[1201], pts[1205], A24plus[147], C24[147], 2);
                get_4_isog(pts[1205], A24plus[148], C24[148], coeff[147]);
                eval_4_isog_mod(pts[1202], pts[1206], coeff[146]);
                eval_4_isog_mod(pts[1201], pts[1209], coeff[147]);
                get_4_isog(pts[1209], A24plus[149], C24[149], coeff[148]);
                lock[146][0] = 0;
                while(lock[146][1]) {
                    #pragma omp flush(lock[146][1])
                }

                eval_4_isog_mod(pts[1197], pts[1210], coeff[147]);
                eval_4_isog_mod(pts[1207], pts[1212], coeff[144]);
                eval_4_isog_mod(pts[1210], pts[1214], coeff[148]);
                get_4_isog(pts[1214], A24plus[150], C24[150], coeff[149]);
                eval_4_isog_mod(pts[1212], pts[1216], coeff[145]);
                lock[147][0] = 0;
                while(lock[147][1]) {
                    #pragma omp flush(lock[147][1])
                }

                eval_4_isog_mod(pts[1215], pts[1218], coeff[149]);
                xDBLe(pts[1218], pts[1221], A24plus[150], C24[150], 2);
                lock[148][0] = 0;
                while(lock[148][1]) {
                    #pragma omp flush(lock[148][1])
                }

                eval_4_isog_mod(pts[1220], pts[1223], coeff[141]);
                xDBLe(pts[1221], pts[1224], A24plus[150], C24[150], 2);
                lock[149][0] = 0;
                while(lock[149][1]) {
                    #pragma omp flush(lock[149][1])
                }

                xDBLe(pts[1224], pts[1227], A24plus[150], C24[150], 2);
                get_4_isog(pts[1227], A24plus[151], C24[151], coeff[150]);
                eval_4_isog_mod(pts[1225], pts[1228], coeff[149]);
                lock[150][0] = 0;
                while(lock[150][1]) {
                    #pragma omp flush(lock[150][1])
                }

                eval_4_isog_mod(pts[1221], pts[1231], coeff[150]);
                eval_4_isog_mod(pts[1228], pts[1233], coeff[150]);
                lock[151][0] = 0;
                while(lock[151][1]) {
                    #pragma omp flush(lock[151][1])
                }

                eval_4_isog_mod(pts[1229], pts[1234], coeff[144]);
                eval_4_isog_mod(pts[1232], pts[1236], coeff[151]);
                lock[152][0] = 0;
                while(lock[152][1]) {
                    #pragma omp flush(lock[152][1])
                }

                eval_4_isog_mod(pts[1236], pts[1239], coeff[152]);
                get_4_isog(pts[1239], A24plus[154], C24[154], coeff[153]);
                eval_4_isog_mod(pts[1237], pts[1240], coeff[152]);
                eval_4_isog_mod(pts[1240], pts[1242], coeff[153]);
                xDBLe(pts[1242], pts[1244], A24plus[154], C24[154], 2);
                xDBLe(pts[1244], pts[1246], A24plus[154], C24[154], 2);
                xDBLe(pts[1246], pts[1248], A24plus[154], C24[154], 2);
                xDBLe(pts[1248], pts[1250], A24plus[154], C24[154], 2);
                xDBLe(pts[1250], pts[1252], A24plus[154], C24[154], 2);
                get_4_isog(pts[1252], A24plus[155], C24[155], coeff[154]);
                lock[153][0] = 0;
                while(lock[153][1]) {
                    #pragma omp flush(lock[153][1])
                }

                eval_4_isog_mod(pts[1250], pts[1254], coeff[154]);
                get_4_isog(pts[1254], A24plus[156], C24[156], coeff[155]);
                eval_4_isog_mod(pts[1242], pts[1257], coeff[154]);
                lock[154][0] = 0;
                while(lock[154][1]) {
                    #pragma omp flush(lock[154][1])
                }

                eval_4_isog_mod(pts[1253], pts[1258], coeff[153]);
                eval_4_isog_mod(pts[1257], pts[1261], coeff[155]);
                eval_4_isog_mod(pts[1258], pts[1262], coeff[154]);
                lock[155][0] = 0;
                while(lock[155][1]) {
                    #pragma omp flush(lock[155][1])
                }

                eval_4_isog_mod(pts[1261], pts[1264], coeff[156]);
                eval_4_isog_mod(pts[1264], pts[1266], coeff[157]);
                xDBLe(pts[1266], pts[1268], A24plus[158], C24[158], 2);
                get_4_isog(pts[1268], A24plus[159], C24[159], coeff[158]);
                lock[156][0] = 0;
                while(lock[156][1]) {
                    #pragma omp flush(lock[156][1])
                }

                eval_4_isog_mod(pts[1266], pts[1270], coeff[158]);
                get_4_isog(pts[1270], A24plus[160], C24[160], coeff[159]);
                lock[157][0] = 0;
                while(lock[157][1]) {
                    #pragma omp flush(lock[157][1])
                }

                eval_4_isog_mod(pts[1271], pts[1272], coeff[159]);
                xDBLe(pts[1272], pts[1273], A24plus[160], C24[160], 2);
                xDBLe(pts[1273], pts[1274], A24plus[160], C24[160], 2);
                xDBLe(pts[1274], pts[1275], A24plus[160], C24[160], 2);
                xDBLe(pts[1275], pts[1276], A24plus[160], C24[160], 2);
                xDBLe(pts[1276], pts[1277], A24plus[160], C24[160], 2);
                xDBLe(pts[1277], pts[1278], A24plus[160], C24[160], 2);
                xDBLe(pts[1278], pts[1279], A24plus[160], C24[160], 2);
                xDBLe(pts[1279], pts[1280], A24plus[160], C24[160], 2);
                xDBLe(pts[1280], pts[1281], A24plus[160], C24[160], 2);
                xDBLe(pts[1281], pts[1282], A24plus[160], C24[160], 2);
                xDBLe(pts[1282], pts[1283], A24plus[160], C24[160], 2);
                xDBLe(pts[1283], pts[1284], A24plus[160], C24[160], 2);
                xDBLe(pts[1284], pts[1285], A24plus[160], C24[160], 2);
                xDBLe(pts[1285], pts[1286], A24plus[160], C24[160], 2);
                xDBLe(pts[1286], pts[1287], A24plus[160], C24[160], 2);
                xDBLe(pts[1287], pts[1288], A24plus[160], C24[160], 2);
                xDBLe(pts[1288], pts[1289], A24plus[160], C24[160], 2);
                xDBLe(pts[1289], pts[1290], A24plus[160], C24[160], 2);
                xDBLe(pts[1290], pts[1291], A24plus[160], C24[160], 2);
                xDBLe(pts[1291], pts[1292], A24plus[160], C24[160], 2);
                xDBLe(pts[1292], pts[1293], A24plus[160], C24[160], 2);
                xDBLe(pts[1293], pts[1294], A24plus[160], C24[160], 2);
                xDBLe(pts[1294], pts[1295], A24plus[160], C24[160], 2);
                xDBLe(pts[1295], pts[1296], A24plus[160], C24[160], 2);
                xDBLe(pts[1296], pts[1297], A24plus[160], C24[160], 2);
                get_4_isog(pts[1297], A24plus[161], C24[161], coeff[160]);
                lock[158][0] = 0;
                while(lock[158][1]) {
                    #pragma omp flush(lock[158][1])
                }

                eval_4_isog_mod(pts[1296], pts[1298], coeff[160]);
                get_4_isog(pts[1298], A24plus[162], C24[162], coeff[161]);
                lock[159][0] = 0;
                while(lock[159][1]) {
                    #pragma omp flush(lock[159][1])
                }

                eval_4_isog_mod(pts[1293], pts[1300], coeff[160]);
                eval_4_isog_mod(pts[1300], pts[1302], coeff[161]);
                lock[160][0] = 0;
                while(lock[160][1]) {
                    #pragma omp flush(lock[160][1])
                }

                eval_4_isog_mod(pts[1303], pts[1305], coeff[161]);
                eval_4_isog_mod(pts[1289], pts[1306], coeff[160]);
                lock[161][0] = 0;
                while(lock[161][1]) {
                    #pragma omp flush(lock[161][1])
                }

                eval_4_isog_mod(pts[1305], pts[1308], coeff[162]);
                eval_4_isog_mod(pts[1304], pts[1311], coeff[163]);
                get_4_isog(pts[1311], A24plus[165], C24[165], coeff[164]);
                eval_4_isog_mod(pts[1308], pts[1312], coeff[163]);
                eval_4_isog_mod(pts[1312], pts[1315], coeff[164]);
                lock[162][0] = 0;
                while(lock[162][1]) {
                    #pragma omp flush(lock[162][1])
                }

                eval_4_isog_mod(pts[1314], pts[1317], coeff[162]);
                xDBLe(pts[1315], pts[1318], A24plus[165], C24[165], 2);
                get_4_isog(pts[1318], A24plus[166], C24[166], coeff[165]);
                eval_4_isog_mod(pts[1317], pts[1320], coeff[163]);
                lock[163][0] = 0;
                while(lock[163][1]) {
                    #pragma omp flush(lock[163][1])
                }

                eval_4_isog_mod(pts[1315], pts[1322], coeff[165]);
                get_4_isog(pts[1322], A24plus[167], C24[167], coeff[166]);
                eval_4_isog_mod(pts[1320], pts[1324], coeff[164]);
                lock[164][0] = 0;
                while(lock[164][1]) {
                    #pragma omp flush(lock[164][1])
                }

                eval_4_isog_mod(pts[1324], pts[1327], coeff[165]);
                eval_4_isog_mod(pts[1325], pts[1328], coeff[162]);
                lock[165][0] = 0;
                while(lock[165][1]) {
                    #pragma omp flush(lock[165][1])
                }

                eval_4_isog_mod(pts[1328], pts[1331], coeff[163]);
                eval_4_isog_mod(pts[1326], pts[1332], coeff[167]);
                get_4_isog(pts[1332], A24plus[169], C24[169], coeff[168]);
                lock[166][0] = 0;
                while(lock[166][1]) {
                    #pragma omp flush(lock[166][1])
                }

                eval_4_isog_mod(pts[1333], pts[1335], coeff[168]);
                eval_4_isog_mod(pts[1272], pts[1337], coeff[160]);
                xDBLe(pts[1335], pts[1338], A24plus[169], C24[169], 2);
                lock[167][0] = 0;
                while(lock[167][1]) {
                    #pragma omp flush(lock[167][1])
                }

                eval_4_isog_mod(pts[1337], pts[1340], coeff[161]);
                eval_4_isog_mod(pts[1340], pts[1343], coeff[162]);
                lock[168][0] = 0;
                while(lock[168][1]) {
                    #pragma omp flush(lock[168][1])
                }

                xDBLe(pts[1341], pts[1344], A24plus[169], C24[169], 2);
                get_4_isog(pts[1344], A24plus[170], C24[170], coeff[169]);
                lock[169][0] = 0;
                while(lock[169][1]) {
                    #pragma omp flush(lock[169][1])
                }

                eval_4_isog_mod(pts[1343], pts[1346], coeff[163]);
                eval_4_isog_mod(pts[1335], pts[1349], coeff[169]);
                eval_4_isog_mod(pts[1346], pts[1351], coeff[164]);
                lock[170][0] = 0;
                while(lock[170][1]) {
                    #pragma omp flush(lock[170][1])
                }

                eval_4_isog_mod(pts[1348], pts[1352], coeff[170]);
                get_4_isog(pts[1352], A24plus[172], C24[172], coeff[171]);
                eval_4_isog_mod(pts[1351], pts[1355], coeff[165]);
                lock[171][0] = 0;
                while(lock[171][1]) {
                    #pragma omp flush(lock[171][1])
                }

                eval_4_isog_mod(pts[1353], pts[1356], coeff[171]);
                get_4_isog(pts[1356], A24plus[173], C24[173], coeff[172]);
                lock[172][0] = 0;
                while(lock[172][1]) {
                    #pragma omp flush(lock[172][1])
                }

                eval_4_isog_mod(pts[1355], pts[1358], coeff[166]);
                eval_4_isog_mod(pts[1358], pts[1360], coeff[167]);
                eval_4_isog_mod(pts[1360], pts[1362], coeff[168]);
                eval_4_isog_mod(pts[1362], pts[1364], coeff[169]);
                eval_4_isog_mod(pts[1364], pts[1366], coeff[170]);
                eval_4_isog_mod(pts[1366], pts[1368], coeff[171]);
                lock[173][0] = 0;
                while(lock[173][1]) {
                    #pragma omp flush(lock[173][1])
                }

                eval_4_isog_mod(pts[1359], pts[1371], coeff[173]);
                eval_4_isog_mod(pts[1368], pts[1372], coeff[172]);
                lock[174][0] = 0;
                while(lock[174][1]) {
                    #pragma omp flush(lock[174][1])
                }

                eval_4_isog_mod(pts[1371], pts[1374], coeff[174]);
                eval_4_isog_mod(pts[1374], pts[1376], coeff[175]);
                xDBLe(pts[1376], pts[1378], A24plus[176], C24[176], 2);
                get_4_isog(pts[1378], A24plus[177], C24[177], coeff[176]);
                lock[175][0] = 0;
                while(lock[175][1]) {
                    #pragma omp flush(lock[175][1])
                }

                eval_4_isog_mod(pts[1379], pts[1381], coeff[176]);
                lock[176][0] = 0;
                while(lock[176][1]) {
                    #pragma omp flush(lock[176][1])
                }

                eval_4_isog_mod(pts[1381], pts[1382], coeff[177]);
                xDBLe(pts[1382], pts[1383], A24plus[178], C24[178], 2);
                xDBLe(pts[1383], pts[1384], A24plus[178], C24[178], 2);
                xDBLe(pts[1384], pts[1385], A24plus[178], C24[178], 2);
                xDBLe(pts[1385], pts[1386], A24plus[178], C24[178], 2);
                xDBLe(pts[1386], pts[1387], A24plus[178], C24[178], 2);
                xDBLe(pts[1387], pts[1388], A24plus[178], C24[178], 2);
                xDBLe(pts[1388], pts[1389], A24plus[178], C24[178], 2);
                get_4_isog(pts[1389], A24plus[179], C24[179], coeff[178]);
                lock[177][0] = 0;
                while(lock[177][1]) {
                    #pragma omp flush(lock[177][1])
                }

                eval_4_isog_mod(pts[1388], pts[1390], coeff[178]);
                get_4_isog(pts[1390], A24plus[180], C24[180], coeff[179]);
                lock[178][0] = 0;
                while(lock[178][1]) {
                    #pragma omp flush(lock[178][1])
                }

                eval_4_isog_mod(pts[1385], pts[1392], coeff[178]);
                eval_4_isog_mod(pts[1392], pts[1394], coeff[179]);
                lock[179][0] = 0;
                while(lock[179][1]) {
                    #pragma omp flush(lock[179][1])
                }

                eval_4_isog_mod(pts[1394], pts[1396], coeff[180]);
                xDBLe(pts[1396], pts[1398], A24plus[181], C24[181], 2);
                get_4_isog(pts[1398], A24plus[182], C24[182], coeff[181]);
                lock[180][0] = 0;
                while(lock[180][1]) {
                    #pragma omp flush(lock[180][1])
                }

                eval_4_isog_mod(pts[1399], pts[1401], coeff[181]);
                lock[181][0] = 0;
                while(lock[181][1]) {
                    #pragma omp flush(lock[181][1])
                }

                eval_4_isog_mod(pts[1401], pts[1402], coeff[182]);
                xDBLe(pts[1402], pts[1403], A24plus[183], C24[183], 2);
                xDBLe(pts[1403], pts[1404], A24plus[183], C24[183], 2);
                get_4_isog(pts[1404], A24plus[184], C24[184], coeff[183]);
                lock[182][0] = 0;
                while(lock[182][1]) {
                    #pragma omp flush(lock[182][1])
                }

                eval_4_isog_mod(pts[1403], pts[1405], coeff[183]);
                get_4_isog(pts[1405], A24plus[185], C24[185], coeff[184]);
            }
            #pragma omp section
            {
                LADDER3PT_NS(PKB[0], PKB[1], PKB[2], (digit_t*)PrivateKeyA, ALICE, pts[1], A, 2*90);
                xDBLe(pts[1], pts[1], A24plus[0], C24[0], 2*96);
                for(int i = 1; i < 90; i++)
                    xDBLe(pts[i], pts[i+1], A24plus[0], C24[0], 2);
                get_4_isog(pts[90], A24plus[1], C24[1], coeff[0]);
                eval_4_isog_mod(pts[89], pts[91], coeff[0]);
                get_4_isog(pts[91], A24plus[2], C24[2], coeff[1]);
                eval_4_isog_mod(pts[88], pts[92], coeff[0]);
                eval_4_isog_mod(pts[87], pts[93], coeff[0]);
                eval_4_isog_mod(pts[86], pts[94], coeff[0]);
                eval_4_isog_mod(pts[84], pts[95], coeff[0]);
                eval_4_isog_mod(pts[92], pts[96], coeff[1]);
                get_4_isog(pts[96], A24plus[3], C24[3], coeff[2]);
                eval_4_isog_mod(pts[93], pts[97], coeff[1]);
                eval_4_isog_mod(pts[94], pts[98], coeff[1]);
                eval_4_isog_mod(pts[95], pts[99], coeff[1]);
                lock1[1] = 0;
                while(lock1[0]) {
                    #pragma omp flush(lock1[0])
                }

                eval_4_isog_mod(pts[97], pts[101], coeff[2]);
                get_4_isog(pts[101], A24plus[4], C24[4], coeff[3]);
                eval_4_isog_mod(pts[99], pts[103], coeff[2]);
                lock[0][1] = 0;
                while(lock[0][0]) {
                    #pragma omp flush(lock[0][0])
                }

                eval_4_isog_mod(pts[100], pts[104], coeff[1]);
                eval_4_isog_mod(pts[104], pts[107], coeff[2]);
                eval_4_isog_mod(pts[76], pts[108], coeff[0]);
                lock[1][1] = 0;
                while(lock[1][0]) {
                    #pragma omp flush(lock[1][0])
                }

                eval_4_isog_mod(pts[107], pts[110], coeff[3]);
                eval_4_isog_mod(pts[110], pts[113], coeff[4]);
                lock[2][1] = 0;
                while(lock[2][0]) {
                    #pragma omp flush(lock[2][0])
                }

                eval_4_isog_mod(pts[109], pts[115], coeff[5]);
                get_4_isog(pts[115], A24plus[7], C24[7], coeff[6]);
                eval_4_isog_mod(pts[113], pts[116], coeff[5]);
                eval_4_isog_mod(pts[116], pts[118], coeff[6]);
                xDBLe(pts[118], pts[120], A24plus[7], C24[7], 2);
                xDBLe(pts[120], pts[123], A24plus[7], C24[7], 2);
                get_4_isog(pts[123], A24plus[8], C24[8], coeff[7]);
                lock[3][1] = 0;
                while(lock[3][0]) {
                    #pragma omp flush(lock[3][0])
                }

                eval_4_isog_mod(pts[122], pts[125], coeff[1]);
                eval_4_isog_mod(pts[120], pts[126], coeff[7]);
                get_4_isog(pts[126], A24plus[9], C24[9], coeff[8]);
                eval_4_isog_mod(pts[125], pts[129], coeff[2]);
                lock[4][1] = 0;
                while(lock[4][0]) {
                    #pragma omp flush(lock[4][0])
                }

                eval_4_isog_mod(pts[127], pts[130], coeff[8]);
                get_4_isog(pts[130], A24plus[10], C24[10], coeff[9]);
                lock[5][1] = 0;
                while(lock[5][0]) {
                    #pragma omp flush(lock[5][0])
                }

                eval_4_isog_mod(pts[131], pts[133], coeff[9]);
                xDBLe(pts[133], pts[135], A24plus[10], C24[10], 2);
                xDBLe(pts[135], pts[137], A24plus[10], C24[10], 2);
                xDBLe(pts[137], pts[139], A24plus[10], C24[10], 2);
                xDBLe(pts[139], pts[141], A24plus[10], C24[10], 2);
                get_4_isog(pts[141], A24plus[11], C24[11], coeff[10]);
                eval_4_isog_mod(pts[139], pts[143], coeff[10]);
                get_4_isog(pts[143], A24plus[12], C24[12], coeff[11]);
                lock[6][1] = 0;
                while(lock[6][0]) {
                    #pragma omp flush(lock[6][0])
                }

                eval_4_isog_mod(pts[133], pts[145], coeff[10]);
                eval_4_isog_mod(pts[142], pts[146], coeff[9]);
                lock[7][1] = 0;
                while(lock[7][0]) {
                    #pragma omp flush(lock[7][0])
                }

                eval_4_isog_mod(pts[145], pts[148], coeff[11]);
                eval_4_isog_mod(pts[148], pts[151], coeff[12]);
                lock[8][1] = 0;
                while(lock[8][0]) {
                    #pragma omp flush(lock[8][0])
                }

                eval_4_isog_mod(pts[150], pts[153], coeff[1]);
                xDBLe(pts[151], pts[154], A24plus[13], C24[13], 2);
                get_4_isog(pts[154], A24plus[14], C24[14], coeff[13]);
                lock[9][1] = 0;
                while(lock[9][0]) {
                    #pragma omp flush(lock[9][0])
                }

                eval_4_isog_mod(pts[153], pts[156], coeff[2]);
                eval_4_isog_mod(pts[156], pts[159], coeff[3]);
                eval_4_isog_mod(pts[159], pts[161], coeff[4]);
                eval_4_isog_mod(pts[161], pts[163], coeff[5]);
                eval_4_isog_mod(pts[163], pts[165], coeff[6]);
                eval_4_isog_mod(pts[165], pts[167], coeff[7]);
                eval_4_isog_mod(pts[167], pts[169], coeff[8]);
                eval_4_isog_mod(pts[169], pts[171], coeff[9]);
                eval_4_isog_mod(pts[171], pts[173], coeff[10]);
                eval_4_isog_mod(pts[173], pts[175], coeff[11]);
                lock[10][1] = 0;
                while(lock[10][0]) {
                    #pragma omp flush(lock[10][0])
                }

                eval_4_isog_mod(pts[170], pts[177], coeff[15]);
                eval_4_isog_mod(pts[175], pts[179], coeff[12]);
                lock[11][1] = 0;
                while(lock[11][0]) {
                    #pragma omp flush(lock[11][0])
                }

                eval_4_isog_mod(pts[177], pts[180], coeff[16]);
                get_4_isog(pts[180], A24plus[18], C24[18], coeff[17]);
                eval_4_isog_mod(pts[179], pts[183], coeff[13]);
                lock[12][1] = 0;
                while(lock[12][0]) {
                    #pragma omp flush(lock[12][0])
                }

                eval_4_isog_mod(pts[181], pts[184], coeff[17]);
                xDBLe(pts[184], pts[187], A24plus[18], C24[18], 2);
                get_4_isog(pts[187], A24plus[19], C24[19], coeff[18]);
                lock[13][1] = 0;
                while(lock[13][0]) {
                    #pragma omp flush(lock[13][0])
                }

                eval_4_isog_mod(pts[185], pts[188], coeff[17]);
                eval_4_isog_mod(pts[188], pts[191], coeff[18]);
                lock[14][1] = 0;
                while(lock[14][0]) {
                    #pragma omp flush(lock[14][0])
                }

                eval_4_isog_mod(pts[191], pts[193], coeff[19]);
                xDBLe(pts[193], pts[195], A24plus[20], C24[20], 2);
                xDBLe(pts[195], pts[197], A24plus[20], C24[20], 2);
                get_4_isog(pts[197], A24plus[21], C24[21], coeff[20]);
                eval_4_isog_mod(pts[195], pts[199], coeff[20]);
                get_4_isog(pts[199], A24plus[22], C24[22], coeff[21]);
                lock[15][1] = 0;
                while(lock[15][0]) {
                    #pragma omp flush(lock[15][0])
                }

                eval_4_isog_mod(pts[198], pts[201], coeff[20]);
                eval_4_isog_mod(pts[34], pts[202], coeff[0]);
                lock[16][1] = 0;
                while(lock[16][0]) {
                    #pragma omp flush(lock[16][0])
                }

                eval_4_isog_mod(pts[201], pts[204], coeff[21]);
                eval_4_isog_mod(pts[204], pts[206], coeff[22]);
                xDBLe(pts[206], pts[208], A24plus[23], C24[23], 2);
                xDBLe(pts[208], pts[210], A24plus[23], C24[23], 2);
                xDBLe(pts[210], pts[212], A24plus[23], C24[23], 2);
                xDBLe(pts[212], pts[214], A24plus[23], C24[23], 2);
                xDBLe(pts[214], pts[216], A24plus[23], C24[23], 2);
                xDBLe(pts[216], pts[218], A24plus[23], C24[23], 2);
                xDBLe(pts[218], pts[220], A24plus[23], C24[23], 2);
                xDBLe(pts[220], pts[222], A24plus[23], C24[23], 2);
                xDBLe(pts[222], pts[224], A24plus[23], C24[23], 2);
                xDBLe(pts[224], pts[226], A24plus[23], C24[23], 2);
                xDBLe(pts[226], pts[228], A24plus[23], C24[23], 2);
                xDBLe(pts[228], pts[230], A24plus[23], C24[23], 2);
                get_4_isog(pts[230], A24plus[24], C24[24], coeff[23]);
                lock[17][1] = 0;
                while(lock[17][0]) {
                    #pragma omp flush(lock[17][0])
                }

                eval_4_isog_mod(pts[228], pts[232], coeff[23]);
                get_4_isog(pts[232], A24plus[25], C24[25], coeff[24]);
                eval_4_isog_mod(pts[222], pts[234], coeff[23]);
                lock[18][1] = 0;
                while(lock[18][0]) {
                    #pragma omp flush(lock[18][0])
                }

                eval_4_isog_mod(pts[233], pts[236], coeff[24]);
                get_4_isog(pts[236], A24plus[26], C24[26], coeff[25]);
                eval_4_isog_mod(pts[235], pts[239], coeff[16]);
                lock[19][1] = 0;
                while(lock[19][0]) {
                    #pragma omp flush(lock[19][0])
                }

                eval_4_isog_mod(pts[238], pts[241], coeff[24]);
                eval_4_isog_mod(pts[239], pts[242], coeff[17]);
                eval_4_isog_mod(pts[241], pts[244], coeff[25]);
                eval_4_isog_mod(pts[242], pts[246], coeff[18]);
                lock[20][1] = 0;
                while(lock[20][0]) {
                    #pragma omp flush(lock[20][0])
                }

                eval_4_isog_mod(pts[245], pts[249], coeff[24]);
                eval_4_isog_mod(pts[246], pts[250], coeff[19]);
                lock[21][1] = 0;
                while(lock[21][0]) {
                    #pragma omp flush(lock[21][0])
                }

                eval_4_isog_mod(pts[249], pts[252], coeff[25]);
                eval_4_isog_mod(pts[252], pts[255], coeff[26]);
                lock[22][1] = 0;
                while(lock[22][0]) {
                    #pragma omp flush(lock[22][0])
                }

                xDBLe(pts[254], pts[257], A24plus[28], C24[28], 2);
                get_4_isog(pts[257], A24plus[29], C24[29], coeff[28]);
                eval_4_isog_mod(pts[255], pts[258], coeff[27]);
                lock[23][1] = 0;
                while(lock[23][0]) {
                    #pragma omp flush(lock[23][0])
                }

                eval_4_isog_mod(pts[254], pts[260], coeff[28]);
                get_4_isog(pts[260], A24plus[30], C24[30], coeff[29]);
                eval_4_isog_mod(pts[259], pts[263], coeff[23]);
                lock[24][1] = 0;
                while(lock[24][0]) {
                    #pragma omp flush(lock[24][0])
                }

                eval_4_isog_mod(pts[262], pts[265], coeff[29]);
                lock[25][1] = 0;
                while(lock[25][0]) {
                    #pragma omp flush(lock[25][0])
                }

                eval_4_isog_mod(pts[265], pts[267], coeff[30]);
                xDBLe(pts[267], pts[269], A24plus[31], C24[31], 2);
                xDBLe(pts[269], pts[271], A24plus[31], C24[31], 2);
                xDBLe(pts[271], pts[273], A24plus[31], C24[31], 2);
                xDBLe(pts[273], pts[275], A24plus[31], C24[31], 2);
                get_4_isog(pts[275], A24plus[32], C24[32], coeff[31]);
                eval_4_isog_mod(pts[273], pts[277], coeff[31]);
                get_4_isog(pts[277], A24plus[33], C24[33], coeff[32]);
                lock[26][1] = 0;
                while(lock[26][0]) {
                    #pragma omp flush(lock[26][0])
                }

                eval_4_isog_mod(pts[271], pts[278], coeff[31]);
                eval_4_isog_mod(pts[278], pts[281], coeff[32]);
                get_4_isog(pts[281], A24plus[34], C24[34], coeff[33]);
                lock[27][1] = 0;
                while(lock[27][0]) {
                    #pragma omp flush(lock[27][0])
                }

                eval_4_isog_mod(pts[279], pts[282], coeff[32]);
                eval_4_isog_mod(pts[282], pts[284], coeff[33]);
                xDBLe(pts[284], pts[286], A24plus[34], C24[34], 2);
                get_4_isog(pts[286], A24plus[35], C24[35], coeff[34]);
                lock[28][1] = 0;
                while(lock[28][0]) {
                    #pragma omp flush(lock[28][0])
                }

                eval_4_isog_mod(pts[287], pts[289], coeff[34]);
                lock[29][1] = 0;
                while(lock[29][0]) {
                    #pragma omp flush(lock[29][0])
                }

                eval_4_isog_mod(pts[289], pts[290], coeff[35]);
                xDBLe(pts[290], pts[292], A24plus[36], C24[36], 2);
                xDBLe(pts[292], pts[294], A24plus[36], C24[36], 2);
                xDBLe(pts[294], pts[296], A24plus[36], C24[36], 2);
                xDBLe(pts[296], pts[298], A24plus[36], C24[36], 2);
                xDBLe(pts[298], pts[300], A24plus[36], C24[36], 2);
                xDBLe(pts[300], pts[302], A24plus[36], C24[36], 2);
                xDBLe(pts[302], pts[304], A24plus[36], C24[36], 2);
                xDBLe(pts[304], pts[306], A24plus[36], C24[36], 2);
                xDBLe(pts[306], pts[308], A24plus[36], C24[36], 2);
                xDBLe(pts[308], pts[310], A24plus[36], C24[36], 2);
                xDBLe(pts[310], pts[312], A24plus[36], C24[36], 2);
                xDBLe(pts[312], pts[314], A24plus[36], C24[36], 2);
                xDBLe(pts[314], pts[316], A24plus[36], C24[36], 2);
                xDBLe(pts[316], pts[318], A24plus[36], C24[36], 2);
                xDBLe(pts[318], pts[320], A24plus[36], C24[36], 2);
                xDBLe(pts[320], pts[322], A24plus[36], C24[36], 2);
                xDBLe(pts[322], pts[324], A24plus[36], C24[36], 2);
                xDBLe(pts[324], pts[326], A24plus[36], C24[36], 2);
                xDBLe(pts[326], pts[328], A24plus[36], C24[36], 2);
                xDBLe(pts[328], pts[330], A24plus[36], C24[36], 2);
                get_4_isog(pts[330], A24plus[37], C24[37], coeff[36]);
                lock[30][1] = 0;
                while(lock[30][0]) {
                    #pragma omp flush(lock[30][0])
                }

                eval_4_isog_mod(pts[328], pts[332], coeff[36]);
                get_4_isog(pts[332], A24plus[38], C24[38], coeff[37]);
                lock[31][1] = 0;
                while(lock[31][0]) {
                    #pragma omp flush(lock[31][0])
                }

                eval_4_isog_mod(pts[333], pts[335], coeff[37]);
                get_4_isog(pts[335], A24plus[39], C24[39], coeff[38]);
                eval_4_isog_mod(pts[316], pts[337], coeff[36]);
                lock[32][1] = 0;
                while(lock[32][0]) {
                    #pragma omp flush(lock[32][0])
                }

                eval_4_isog_mod(pts[337], pts[339], coeff[37]);
                eval_4_isog_mod(pts[339], pts[341], coeff[38]);
                eval_4_isog_mod(pts[331], pts[343], coeff[21]);
                lock[33][1] = 0;
                while(lock[33][0]) {
                    #pragma omp flush(lock[33][0])
                }

                eval_4_isog_mod(pts[338], pts[344], coeff[39]);
                get_4_isog(pts[344], A24plus[41], C24[41], coeff[40]);
                eval_4_isog_mod(pts[342], pts[346], coeff[37]);
                lock[34][1] = 0;
                while(lock[34][0]) {
                    #pragma omp flush(lock[34][0])
                }

                eval_4_isog_mod(pts[346], pts[349], coeff[38]);
                eval_4_isog_mod(pts[347], pts[350], coeff[23]);
                lock[35][1] = 0;
                while(lock[35][0]) {
                    #pragma omp flush(lock[35][0])
                }

                eval_4_isog_mod(pts[350], pts[353], coeff[24]);
                xDBLe(pts[351], pts[354], A24plus[41], C24[41], 2);
                get_4_isog(pts[354], A24plus[42], C24[42], coeff[41]);
                lock[36][1] = 0;
                while(lock[36][0]) {
                    #pragma omp flush(lock[36][0])
                }

                eval_4_isog_mod(pts[351], pts[357], coeff[41]);
                get_4_isog(pts[357], A24plus[43], C24[43], coeff[42]);
                eval_4_isog_mod(pts[348], pts[358], coeff[41]);
                eval_4_isog_mod(pts[290], pts[360], coeff[36]);
                lock[37][1] = 0;
                while(lock[37][0]) {
                    #pragma omp flush(lock[37][0])
                }

                eval_4_isog_mod(pts[358], pts[362], coeff[42]);
                get_4_isog(pts[362], A24plus[44], C24[44], coeff[43]);
                eval_4_isog_mod(pts[361], pts[365], coeff[27]);
                lock[38][1] = 0;
                while(lock[38][0]) {
                    #pragma omp flush(lock[38][0])
                }

                eval_4_isog_mod(pts[364], pts[367], coeff[38]);
                eval_4_isog_mod(pts[365], pts[368], coeff[28]);
                lock[39][1] = 0;
                while(lock[39][0]) {
                    #pragma omp flush(lock[39][0])
                }

                eval_4_isog_mod(pts[367], pts[370], coeff[39]);
                eval_4_isog_mod(pts[370], pts[373], coeff[40]);
                lock[40][1] = 0;
                while(lock[40][0]) {
                    #pragma omp flush(lock[40][0])
                }

                eval_4_isog_mod(pts[371], pts[374], coeff[30]);
                eval_4_isog_mod(pts[374], pts[377], coeff[31]);
                lock[41][1] = 0;
                while(lock[41][0]) {
                    #pragma omp flush(lock[41][0])
                }

                xDBLe(pts[375], pts[378], A24plus[44], C24[44], 2);
                get_4_isog(pts[378], A24plus[45], C24[45], coeff[44]);
                eval_4_isog_mod(pts[375], pts[381], coeff[44]);
                get_4_isog(pts[381], A24plus[46], C24[46], coeff[45]);
                lock[42][1] = 0;
                while(lock[42][0]) {
                    #pragma omp flush(lock[42][0])
                }

                eval_4_isog_mod(pts[372], pts[382], coeff[44]);
                eval_4_isog_mod(pts[379], pts[384], coeff[43]);
                eval_4_isog_mod(pts[382], pts[386], coeff[45]);
                get_4_isog(pts[386], A24plus[47], C24[47], coeff[46]);
                eval_4_isog_mod(pts[384], pts[388], coeff[44]);
                lock[43][1] = 0;
                while(lock[43][0]) {
                    #pragma omp flush(lock[43][0])
                }

                eval_4_isog_mod(pts[388], pts[391], coeff[45]);
                eval_4_isog_mod(pts[389], pts[392], coeff[35]);
                lock[44][1] = 0;
                while(lock[44][0]) {
                    #pragma omp flush(lock[44][0])
                }

                eval_4_isog_mod(pts[391], pts[394], coeff[46]);
                eval_4_isog_mod(pts[394], pts[397], coeff[47]);
                lock[45][1] = 0;
                while(lock[45][0]) {
                    #pragma omp flush(lock[45][0])
                }

                eval_4_isog_mod(pts[397], pts[399], coeff[48]);
                xDBLe(pts[399], pts[401], A24plus[49], C24[49], 2);
                xDBLe(pts[401], pts[403], A24plus[49], C24[49], 2);
                xDBLe(pts[403], pts[405], A24plus[49], C24[49], 2);
                xDBLe(pts[405], pts[407], A24plus[49], C24[49], 2);
                xDBLe(pts[407], pts[409], A24plus[49], C24[49], 2);
                xDBLe(pts[409], pts[411], A24plus[49], C24[49], 2);
                xDBLe(pts[411], pts[413], A24plus[49], C24[49], 2);
                get_4_isog(pts[413], A24plus[50], C24[50], coeff[49]);
                eval_4_isog_mod(pts[411], pts[415], coeff[49]);
                get_4_isog(pts[415], A24plus[51], C24[51], coeff[50]);
                lock[46][1] = 0;
                while(lock[46][0]) {
                    #pragma omp flush(lock[46][0])
                }

                eval_4_isog_mod(pts[409], pts[416], coeff[49]);
                eval_4_isog_mod(pts[416], pts[419], coeff[50]);
                get_4_isog(pts[419], A24plus[52], C24[52], coeff[51]);
                eval_4_isog_mod(pts[399], pts[421], coeff[49]);
                lock[47][1] = 0;
                while(lock[47][0]) {
                    #pragma omp flush(lock[47][0])
                }

                eval_4_isog_mod(pts[420], pts[423], coeff[51]);
                eval_4_isog_mod(pts[421], pts[424], coeff[50]);
                lock[48][1] = 0;
                while(lock[48][0]) {
                    #pragma omp flush(lock[48][0])
                }

                eval_4_isog_mod(pts[424], pts[427], coeff[51]);
                lock[49][1] = 0;
                while(lock[49][0]) {
                    #pragma omp flush(lock[49][0])
                }

                eval_4_isog_mod(pts[423], pts[429], coeff[52]);
                get_4_isog(pts[429], A24plus[54], C24[54], coeff[53]);
                eval_4_isog_mod(pts[427], pts[430], coeff[52]);
                eval_4_isog_mod(pts[430], pts[432], coeff[53]);
                xDBLe(pts[432], pts[434], A24plus[54], C24[54], 2);
                lock[50][1] = 0;
                while(lock[50][0]) {
                    #pragma omp flush(lock[50][0])
                }

                eval_4_isog_mod(pts[435], pts[437], coeff[53]);
                lock[51][1] = 0;
                while(lock[51][0]) {
                    #pragma omp flush(lock[51][0])
                }

                eval_4_isog_mod(pts[432], pts[439], coeff[54]);
                lock[52][1] = 0;
                while(lock[52][0]) {
                    #pragma omp flush(lock[52][0])
                }

                eval_4_isog_mod(pts[439], pts[441], coeff[55]);
                get_4_isog(pts[441], A24plus[57], C24[57], coeff[56]);
                eval_4_isog_mod(pts[0], pts[443], coeff[0]);
                lock[53][1] = 0;
                while(lock[53][0]) {
                    #pragma omp flush(lock[53][0])
                }

                eval_4_isog_mod(pts[443], pts[445], coeff[1]);
                eval_4_isog_mod(pts[445], pts[447], coeff[2]);
                eval_4_isog_mod(pts[447], pts[449], coeff[3]);
                eval_4_isog_mod(pts[449], pts[451], coeff[4]);
                eval_4_isog_mod(pts[451], pts[453], coeff[5]);
                eval_4_isog_mod(pts[453], pts[455], coeff[6]);
                eval_4_isog_mod(pts[455], pts[457], coeff[7]);
                eval_4_isog_mod(pts[457], pts[459], coeff[8]);
                eval_4_isog_mod(pts[459], pts[461], coeff[9]);
                eval_4_isog_mod(pts[461], pts[463], coeff[10]);
                eval_4_isog_mod(pts[463], pts[465], coeff[11]);
                eval_4_isog_mod(pts[465], pts[467], coeff[12]);
                eval_4_isog_mod(pts[467], pts[469], coeff[13]);
                eval_4_isog_mod(pts[469], pts[471], coeff[14]);
                eval_4_isog_mod(pts[471], pts[473], coeff[15]);
                eval_4_isog_mod(pts[473], pts[475], coeff[16]);
                eval_4_isog_mod(pts[475], pts[477], coeff[17]);
                eval_4_isog_mod(pts[477], pts[479], coeff[18]);
                eval_4_isog_mod(pts[479], pts[481], coeff[19]);
                eval_4_isog_mod(pts[481], pts[483], coeff[20]);
                eval_4_isog_mod(pts[483], pts[485], coeff[21]);
                eval_4_isog_mod(pts[485], pts[487], coeff[22]);
                eval_4_isog_mod(pts[487], pts[489], coeff[23]);
                eval_4_isog_mod(pts[489], pts[491], coeff[24]);
                eval_4_isog_mod(pts[491], pts[493], coeff[25]);
                eval_4_isog_mod(pts[493], pts[495], coeff[26]);
                eval_4_isog_mod(pts[495], pts[497], coeff[27]);
                eval_4_isog_mod(pts[497], pts[499], coeff[28]);
                eval_4_isog_mod(pts[499], pts[501], coeff[29]);
                eval_4_isog_mod(pts[501], pts[503], coeff[30]);
                eval_4_isog_mod(pts[503], pts[505], coeff[31]);
                eval_4_isog_mod(pts[505], pts[507], coeff[32]);
                eval_4_isog_mod(pts[507], pts[509], coeff[33]);
                lock[54][1] = 0;
                while(lock[54][0]) {
                    #pragma omp flush(lock[54][0])
                }

                eval_4_isog_mod(pts[506], pts[510], coeff[57]);
                get_4_isog(pts[510], A24plus[59], C24[59], coeff[58]);
                lock[55][1] = 0;
                while(lock[55][0]) {
                    #pragma omp flush(lock[55][0])
                }

                eval_4_isog_mod(pts[500], pts[512], coeff[57]);
                eval_4_isog_mod(pts[512], pts[514], coeff[58]);
                lock[56][1] = 0;
                while(lock[56][0]) {
                    #pragma omp flush(lock[56][0])
                }

                eval_4_isog_mod(pts[514], pts[516], coeff[59]);
                xDBLe(pts[516], pts[518], A24plus[60], C24[60], 2);
                get_4_isog(pts[518], A24plus[61], C24[61], coeff[60]);
                eval_4_isog_mod(pts[516], pts[521], coeff[60]);
                get_4_isog(pts[521], A24plus[62], C24[62], coeff[61]);
                lock[57][1] = 0;
                while(lock[57][0]) {
                    #pragma omp flush(lock[57][0])
                }

                eval_4_isog_mod(pts[519], pts[522], coeff[60]);
                eval_4_isog_mod(pts[522], pts[524], coeff[61]);
                xDBLe(pts[524], pts[526], A24plus[62], C24[62], 2);
                xDBLe(pts[526], pts[528], A24plus[62], C24[62], 2);
                get_4_isog(pts[528], A24plus[63], C24[63], coeff[62]);
                lock[58][1] = 0;
                while(lock[58][0]) {
                    #pragma omp flush(lock[58][0])
                }

                eval_4_isog_mod(pts[526], pts[530], coeff[62]);
                get_4_isog(pts[530], A24plus[64], C24[64], coeff[63]);
                eval_4_isog_mod(pts[468], pts[533], coeff[57]);
                lock[59][1] = 0;
                while(lock[59][0]) {
                    #pragma omp flush(lock[59][0])
                }

                eval_4_isog_mod(pts[531], pts[534], coeff[63]);
                get_4_isog(pts[534], A24plus[65], C24[65], coeff[64]);
                lock[60][1] = 0;
                while(lock[60][0]) {
                    #pragma omp flush(lock[60][0])
                }

                eval_4_isog_mod(pts[533], pts[536], coeff[58]);
                eval_4_isog_mod(pts[536], pts[538], coeff[59]);
                eval_4_isog_mod(pts[538], pts[540], coeff[60]);
                eval_4_isog_mod(pts[540], pts[542], coeff[61]);
                eval_4_isog_mod(pts[542], pts[545], coeff[62]);
                lock[61][1] = 0;
                while(lock[61][0]) {
                    #pragma omp flush(lock[61][0])
                }

                xDBLe(pts[544], pts[547], A24plus[65], C24[65], 2);
                get_4_isog(pts[547], A24plus[66], C24[66], coeff[65]);
                eval_4_isog_mod(pts[545], pts[548], coeff[63]);
                lock[62][1] = 0;
                while(lock[62][0]) {
                    #pragma omp flush(lock[62][0])
                }

                eval_4_isog_mod(pts[541], pts[551], coeff[65]);
                eval_4_isog_mod(pts[548], pts[553], coeff[64]);
                lock[63][1] = 0;
                while(lock[63][0]) {
                    #pragma omp flush(lock[63][0])
                }

                eval_4_isog_mod(pts[551], pts[555], coeff[66]);
                get_4_isog(pts[555], A24plus[68], C24[68], coeff[67]);
                eval_4_isog_mod(pts[553], pts[557], coeff[65]);
                lock[64][1] = 0;
                while(lock[64][0]) {
                    #pragma omp flush(lock[64][0])
                }

                eval_4_isog_mod(pts[556], pts[559], coeff[67]);
                eval_4_isog_mod(pts[557], pts[560], coeff[66]);
                lock[65][1] = 0;
                while(lock[65][0]) {
                    #pragma omp flush(lock[65][0])
                }

                eval_4_isog_mod(pts[560], pts[563], coeff[67]);
                eval_4_isog_mod(pts[561], pts[565], coeff[40]);
                lock[66][1] = 0;
                while(lock[66][0]) {
                    #pragma omp flush(lock[66][0])
                }

                eval_4_isog_mod(pts[559], pts[566], coeff[68]);
                get_4_isog(pts[566], A24plus[70], C24[70], coeff[69]);
                eval_4_isog_mod(pts[564], pts[568], coeff[58]);
                lock[67][1] = 0;
                while(lock[67][0]) {
                    #pragma omp flush(lock[67][0])
                }

                eval_4_isog_mod(pts[567], pts[570], coeff[69]);
                xDBLe(pts[570], pts[573], A24plus[70], C24[70], 2);
                lock[68][1] = 0;
                while(lock[68][0]) {
                    #pragma omp flush(lock[68][0])
                }

                eval_4_isog_mod(pts[572], pts[575], coeff[43]);
                xDBLe(pts[573], pts[576], A24plus[70], C24[70], 2);
                lock[69][1] = 0;
                while(lock[69][0]) {
                    #pragma omp flush(lock[69][0])
                }

                eval_4_isog_mod(pts[575], pts[578], coeff[44]);
                eval_4_isog_mod(pts[578], pts[581], coeff[45]);
                lock[70][1] = 0;
                while(lock[70][0]) {
                    #pragma omp flush(lock[70][0])
                }

                xDBLe(pts[579], pts[582], A24plus[70], C24[70], 2);
                xDBLe(pts[582], pts[585], A24plus[70], C24[70], 2);
                lock[71][1] = 0;
                while(lock[71][0]) {
                    #pragma omp flush(lock[71][0])
                }

                eval_4_isog_mod(pts[584], pts[587], coeff[47]);
                xDBLe(pts[585], pts[588], A24plus[70], C24[70], 2);
                lock[72][1] = 0;
                while(lock[72][0]) {
                    #pragma omp flush(lock[72][0])
                }

                eval_4_isog_mod(pts[587], pts[590], coeff[48]);
                eval_4_isog_mod(pts[590], pts[593], coeff[49]);
                lock[73][1] = 0;
                while(lock[73][0]) {
                    #pragma omp flush(lock[73][0])
                }

                eval_4_isog_mod(pts[588], pts[594], coeff[70]);
                get_4_isog(pts[594], A24plus[72], C24[72], coeff[71]);
                eval_4_isog_mod(pts[592], pts[597], coeff[67]);
                lock[74][1] = 0;
                while(lock[74][0]) {
                    #pragma omp flush(lock[74][0])
                }

                eval_4_isog_mod(pts[593], pts[598], coeff[50]);
                eval_4_isog_mod(pts[596], pts[600], coeff[71]);
                eval_4_isog_mod(pts[598], pts[603], coeff[51]);
                lock[75][1] = 0;
                while(lock[75][0]) {
                    #pragma omp flush(lock[75][0])
                }

                eval_4_isog_mod(pts[600], pts[604], coeff[72]);
                eval_4_isog_mod(pts[602], pts[606], coeff[69]);
                xDBLe(pts[604], pts[608], A24plus[73], C24[73], 2);
                get_4_isog(pts[608], A24plus[74], C24[74], coeff[73]);
                eval_4_isog_mod(pts[606], pts[610], coeff[70]);
                lock[76][1] = 0;
                while(lock[76][0]) {
                    #pragma omp flush(lock[76][0])
                }

                eval_4_isog_mod(pts[609], pts[613], coeff[73]);
                eval_4_isog_mod(pts[610], pts[614], coeff[71]);
                lock[77][1] = 0;
                while(lock[77][0]) {
                    #pragma omp flush(lock[77][0])
                }

                eval_4_isog_mod(pts[613], pts[616], coeff[74]);
                xDBLe(pts[616], pts[619], A24plus[75], C24[75], 2);
                lock[78][1] = 0;
                while(lock[78][0]) {
                    #pragma omp flush(lock[78][0])
                }

                eval_4_isog_mod(pts[617], pts[620], coeff[73]);
                eval_4_isog_mod(pts[620], pts[623], coeff[74]);
                lock[79][1] = 0;
                while(lock[79][0]) {
                    #pragma omp flush(lock[79][0])
                }

                eval_4_isog_mod(pts[621], pts[624], coeff[57]);
                eval_4_isog_mod(pts[623], pts[627], coeff[75]);
                eval_4_isog_mod(pts[624], pts[628], coeff[58]);
                lock[80][1] = 0;
                while(lock[80][0]) {
                    #pragma omp flush(lock[80][0])
                }

                eval_4_isog_mod(pts[627], pts[630], coeff[76]);
                eval_4_isog_mod(pts[630], pts[632], coeff[77]);
                xDBLe(pts[632], pts[634], A24plus[78], C24[78], 2);
                xDBLe(pts[634], pts[636], A24plus[78], C24[78], 2);
                xDBLe(pts[636], pts[638], A24plus[78], C24[78], 2);
                xDBLe(pts[638], pts[640], A24plus[78], C24[78], 2);
                xDBLe(pts[640], pts[642], A24plus[78], C24[78], 2);
                xDBLe(pts[642], pts[644], A24plus[78], C24[78], 2);
                xDBLe(pts[644], pts[646], A24plus[78], C24[78], 2);
                xDBLe(pts[646], pts[648], A24plus[78], C24[78], 2);
                xDBLe(pts[648], pts[650], A24plus[78], C24[78], 2);
                xDBLe(pts[650], pts[652], A24plus[78], C24[78], 2);
                xDBLe(pts[652], pts[654], A24plus[78], C24[78], 2);
                get_4_isog(pts[654], A24plus[79], C24[79], coeff[78]);
                lock[81][1] = 0;
                while(lock[81][0]) {
                    #pragma omp flush(lock[81][0])
                }

                eval_4_isog_mod(pts[650], pts[657], coeff[78]);
                eval_4_isog_mod(pts[646], pts[658], coeff[78]);
                lock[82][1] = 0;
                while(lock[82][0]) {
                    #pragma omp flush(lock[82][0])
                }

                eval_4_isog_mod(pts[657], pts[660], coeff[79]);
                get_4_isog(pts[660], A24plus[81], C24[81], coeff[80]);
                eval_4_isog_mod(pts[640], pts[662], coeff[78]);
                lock[83][1] = 0;
                while(lock[83][0]) {
                    #pragma omp flush(lock[83][0])
                }

                eval_4_isog_mod(pts[662], pts[665], coeff[79]);
                eval_4_isog_mod(pts[663], pts[666], coeff[74]);
                eval_4_isog_mod(pts[665], pts[668], coeff[80]);
                eval_4_isog_mod(pts[666], pts[670], coeff[75]);
                lock[84][1] = 0;
                while(lock[84][0]) {
                    #pragma omp flush(lock[84][0])
                }

                eval_4_isog_mod(pts[668], pts[672], coeff[81]);
                eval_4_isog_mod(pts[672], pts[675], coeff[82]);
                lock[85][1] = 0;
                while(lock[85][0]) {
                    #pragma omp flush(lock[85][0])
                }

                eval_4_isog_mod(pts[673], pts[676], coeff[80]);
                eval_4_isog_mod(pts[676], pts[679], coeff[81]);
                lock[86][1] = 0;
                while(lock[86][0]) {
                    #pragma omp flush(lock[86][0])
                }

                xDBLe(pts[678], pts[681], A24plus[83], C24[83], 2);
                get_4_isog(pts[681], A24plus[84], C24[84], coeff[83]);
                eval_4_isog_mod(pts[679], pts[682], coeff[82]);
                lock[87][1] = 0;
                while(lock[87][0]) {
                    #pragma omp flush(lock[87][0])
                }

                eval_4_isog_mod(pts[675], pts[685], coeff[83]);
                eval_4_isog_mod(pts[682], pts[686], coeff[83]);
                lock[88][1] = 0;
                while(lock[88][0]) {
                    #pragma omp flush(lock[88][0])
                }

                eval_4_isog_mod(pts[686], pts[689], coeff[84]);
                lock[89][1] = 0;
                while(lock[89][0]) {
                    #pragma omp flush(lock[89][0])
                }

                eval_4_isog_mod(pts[687], pts[690], coeff[81]);
                eval_4_isog_mod(pts[690], pts[692], coeff[82]);
                eval_4_isog_mod(pts[692], pts[694], coeff[83]);
                eval_4_isog_mod(pts[694], pts[696], coeff[84]);
                eval_4_isog_mod(pts[696], pts[698], coeff[85]);
                lock[90][1] = 0;
                while(lock[90][0]) {
                    #pragma omp flush(lock[90][0])
                }

                eval_4_isog_mod(pts[693], pts[700], coeff[86]);
                eval_4_isog_mod(pts[700], pts[703], coeff[87]);
                get_4_isog(pts[703], A24plus[89], C24[89], coeff[88]);
                lock[91][1] = 0;
                while(lock[91][0]) {
                    #pragma omp flush(lock[91][0])
                }

                eval_4_isog_mod(pts[702], pts[705], coeff[87]);
                eval_4_isog_mod(pts[705], pts[707], coeff[88]);
                lock[92][1] = 0;
                while(lock[92][0]) {
                    #pragma omp flush(lock[92][0])
                }

                lock[93][1] = 0;
                while(lock[93][0]) {
                    #pragma omp flush(lock[93][0])
                }

                eval_4_isog_mod(pts[801], pts[805], coeff[90]);
                lock[94][1] = 0;
                while(lock[94][0]) {
                    #pragma omp flush(lock[94][0])
                }

                eval_4_isog_mod(pts[799], pts[806], coeff[90]);
                eval_4_isog_mod(pts[806], pts[808], coeff[91]);
                lock[95][1] = 0;
                while(lock[95][0]) {
                    #pragma omp flush(lock[95][0])
                }

                eval_4_isog_mod(pts[809], pts[811], coeff[91]);
                eval_4_isog_mod(pts[811], pts[813], coeff[92]);
                eval_4_isog_mod(pts[791], pts[814], coeff[90]);
                lock[96][1] = 0;
                while(lock[96][0]) {
                    #pragma omp flush(lock[96][0])
                }

                eval_4_isog_mod(pts[813], pts[816], coeff[93]);
                eval_4_isog_mod(pts[816], pts[818], coeff[94]);
                xDBLe(pts[818], pts[820], A24plus[95], C24[95], 2);
                xDBLe(pts[820], pts[822], A24plus[95], C24[95], 2);
                get_4_isog(pts[822], A24plus[96], C24[96], coeff[95]);
                lock[97][1] = 0;
                while(lock[97][0]) {
                    #pragma omp flush(lock[97][0])
                }

                eval_4_isog_mod(pts[820], pts[824], coeff[95]);
                get_4_isog(pts[824], A24plus[97], C24[97], coeff[96]);
                eval_4_isog_mod(pts[823], pts[826], coeff[95]);
                lock[98][1] = 0;
                while(lock[98][0]) {
                    #pragma omp flush(lock[98][0])
                }

                eval_4_isog_mod(pts[826], pts[829], coeff[96]);
                lock[99][1] = 0;
                while(lock[99][0]) {
                    #pragma omp flush(lock[99][0])
                }

                eval_4_isog_mod(pts[827], pts[830], coeff[91]);
                eval_4_isog_mod(pts[830], pts[832], coeff[92]);
                eval_4_isog_mod(pts[832], pts[834], coeff[93]);
                eval_4_isog_mod(pts[834], pts[836], coeff[94]);
                eval_4_isog_mod(pts[836], pts[838], coeff[95]);
                eval_4_isog_mod(pts[838], pts[840], coeff[96]);
                lock[100][1] = 0;
                while(lock[100][0]) {
                    #pragma omp flush(lock[100][0])
                }

                eval_4_isog_mod(pts[831], pts[843], coeff[98]);
                eval_4_isog_mod(pts[840], pts[844], coeff[97]);
                lock[101][1] = 0;
                while(lock[101][0]) {
                    #pragma omp flush(lock[101][0])
                }

                eval_4_isog_mod(pts[844], pts[847], coeff[98]);
                eval_4_isog_mod(pts[847], pts[849], coeff[99]);
                eval_4_isog_mod(pts[849], pts[851], coeff[100]);
                eval_4_isog_mod(pts[771], pts[852], coeff[90]);
                lock[102][1] = 0;
                while(lock[102][0]) {
                    #pragma omp flush(lock[102][0])
                }

                eval_4_isog_mod(pts[851], pts[854], coeff[101]);
                eval_4_isog_mod(pts[854], pts[856], coeff[102]);
                xDBLe(pts[856], pts[858], A24plus[103], C24[103], 2);
                xDBLe(pts[858], pts[860], A24plus[103], C24[103], 2);
                xDBLe(pts[860], pts[862], A24plus[103], C24[103], 2);
                xDBLe(pts[862], pts[864], A24plus[103], C24[103], 2);
                xDBLe(pts[864], pts[866], A24plus[103], C24[103], 2);
                xDBLe(pts[866], pts[868], A24plus[103], C24[103], 2);
                xDBLe(pts[868], pts[870], A24plus[103], C24[103], 2);
                get_4_isog(pts[870], A24plus[104], C24[104], coeff[103]);
                lock[103][1] = 0;
                while(lock[103][0]) {
                    #pragma omp flush(lock[103][0])
                }

                eval_4_isog_mod(pts[868], pts[872], coeff[103]);
                get_4_isog(pts[872], A24plus[105], C24[105], coeff[104]);
                eval_4_isog_mod(pts[862], pts[874], coeff[103]);
                lock[104][1] = 0;
                while(lock[104][0]) {
                    #pragma omp flush(lock[104][0])
                }

                eval_4_isog_mod(pts[873], pts[876], coeff[104]);
                get_4_isog(pts[876], A24plus[106], C24[106], coeff[105]);
                eval_4_isog_mod(pts[856], pts[878], coeff[103]);
                lock[105][1] = 0;
                while(lock[105][0]) {
                    #pragma omp flush(lock[105][0])
                }

                eval_4_isog_mod(pts[877], pts[880], coeff[105]);
                xDBLe(pts[880], pts[883], A24plus[106], C24[106], 2);
                get_4_isog(pts[883], A24plus[107], C24[107], coeff[106]);
                lock[106][1] = 0;
                while(lock[106][0]) {
                    #pragma omp flush(lock[106][0])
                }

                eval_4_isog_mod(pts[882], pts[885], coeff[103]);
                eval_4_isog_mod(pts[880], pts[886], coeff[106]);
                get_4_isog(pts[886], A24plus[108], C24[108], coeff[107]);
                lock[107][1] = 0;
                while(lock[107][0]) {
                    #pragma omp flush(lock[107][0])
                }

                eval_4_isog_mod(pts[887], pts[889], coeff[107]);
                xDBLe(pts[889], pts[891], A24plus[108], C24[108], 2);
                xDBLe(pts[891], pts[893], A24plus[108], C24[108], 2);
                get_4_isog(pts[893], A24plus[109], C24[109], coeff[108]);
                eval_4_isog_mod(pts[754], pts[895], coeff[90]);
                lock[108][1] = 0;
                while(lock[108][0]) {
                    #pragma omp flush(lock[108][0])
                }

                eval_4_isog_mod(pts[891], pts[896], coeff[108]);
                get_4_isog(pts[896], A24plus[110], C24[110], coeff[109]);
                eval_4_isog_mod(pts[894], pts[898], coeff[108]);
                lock[109][1] = 0;
                while(lock[109][0]) {
                    #pragma omp flush(lock[109][0])
                }

                eval_4_isog_mod(pts[897], pts[900], coeff[109]);
                get_4_isog(pts[900], A24plus[111], C24[111], coeff[110]);
                lock[110][1] = 0;
                while(lock[110][0]) {
                    #pragma omp flush(lock[110][0])
                }

                eval_4_isog_mod(pts[899], pts[902], coeff[92]);
                eval_4_isog_mod(pts[902], pts[904], coeff[93]);
                eval_4_isog_mod(pts[904], pts[906], coeff[94]);
                eval_4_isog_mod(pts[906], pts[908], coeff[95]);
                eval_4_isog_mod(pts[908], pts[910], coeff[96]);
                eval_4_isog_mod(pts[910], pts[912], coeff[97]);
                eval_4_isog_mod(pts[912], pts[914], coeff[98]);
                eval_4_isog_mod(pts[914], pts[916], coeff[99]);
                eval_4_isog_mod(pts[916], pts[918], coeff[100]);
                eval_4_isog_mod(pts[918], pts[920], coeff[101]);
                eval_4_isog_mod(pts[920], pts[922], coeff[102]);
                eval_4_isog_mod(pts[922], pts[924], coeff[103]);
                eval_4_isog_mod(pts[924], pts[926], coeff[104]);
                lock[111][1] = 0;
                while(lock[111][0]) {
                    #pragma omp flush(lock[111][0])
                }

                eval_4_isog_mod(pts[921], pts[928], coeff[111]);
                eval_4_isog_mod(pts[928], pts[931], coeff[112]);
                get_4_isog(pts[931], A24plus[114], C24[114], coeff[113]);
                eval_4_isog_mod(pts[911], pts[933], coeff[111]);
                lock[112][1] = 0;
                while(lock[112][0]) {
                    #pragma omp flush(lock[112][0])
                }

                eval_4_isog_mod(pts[930], pts[934], coeff[106]);
                eval_4_isog_mod(pts[934], pts[937], coeff[107]);
                lock[113][1] = 0;
                while(lock[113][0]) {
                    #pragma omp flush(lock[113][0])
                }

                xDBLe(pts[935], pts[938], A24plus[114], C24[114], 2);
                get_4_isog(pts[938], A24plus[115], C24[115], coeff[114]);
                eval_4_isog_mod(pts[937], pts[941], coeff[108]);
                lock[114][1] = 0;
                while(lock[114][0]) {
                    #pragma omp flush(lock[114][0])
                }

                eval_4_isog_mod(pts[935], pts[942], coeff[114]);
                get_4_isog(pts[942], A24plus[116], C24[116], coeff[115]);
                eval_4_isog_mod(pts[941], pts[945], coeff[109]);
                lock[115][1] = 0;
                while(lock[115][0]) {
                    #pragma omp flush(lock[115][0])
                }

                eval_4_isog_mod(pts[944], pts[947], coeff[113]);
                eval_4_isog_mod(pts[945], pts[948], coeff[110]);
                lock[116][1] = 0;
                while(lock[116][0]) {
                    #pragma omp flush(lock[116][0])
                }

                eval_4_isog_mod(pts[947], pts[950], coeff[114]);
                eval_4_isog_mod(pts[950], pts[953], coeff[115]);
                lock[117][1] = 0;
                while(lock[117][0]) {
                    #pragma omp flush(lock[117][0])
                }

                eval_4_isog_mod(pts[951], pts[954], coeff[112]);
                eval_4_isog_mod(pts[946], pts[956], coeff[116]);
                lock[118][1] = 0;
                while(lock[118][0]) {
                    #pragma omp flush(lock[118][0])
                }

                eval_4_isog_mod(pts[954], pts[958], coeff[113]);
                eval_4_isog_mod(pts[958], pts[961], coeff[114]);
                eval_4_isog_mod(pts[961], pts[963], coeff[115]);
                eval_4_isog_mod(pts[963], pts[965], coeff[116]);
                eval_4_isog_mod(pts[734], pts[966], coeff[90]);
                lock[119][1] = 0;
                while(lock[119][0]) {
                    #pragma omp flush(lock[119][0])
                }

                eval_4_isog_mod(pts[965], pts[968], coeff[117]);
                eval_4_isog_mod(pts[968], pts[971], coeff[118]);
                lock[120][1] = 0;
                while(lock[120][0]) {
                    #pragma omp flush(lock[120][0])
                }

                eval_4_isog_mod(pts[969], pts[972], coeff[92]);
                eval_4_isog_mod(pts[962], pts[975], coeff[119]);
                eval_4_isog_mod(pts[972], pts[977], coeff[93]);
                lock[121][1] = 0;
                while(lock[121][0]) {
                    #pragma omp flush(lock[121][0])
                }

                eval_4_isog_mod(pts[974], pts[978], coeff[120]);
                get_4_isog(pts[978], A24plus[122], C24[122], coeff[121]);
                eval_4_isog_mod(pts[977], pts[981], coeff[94]);
                lock[122][1] = 0;
                while(lock[122][0]) {
                    #pragma omp flush(lock[122][0])
                }

                eval_4_isog_mod(pts[980], pts[983], coeff[121]);
                lock[123][1] = 0;
                while(lock[123][0]) {
                    #pragma omp flush(lock[123][0])
                }

                eval_4_isog_mod(pts[981], pts[984], coeff[95]);
                eval_4_isog_mod(pts[984], pts[986], coeff[96]);
                eval_4_isog_mod(pts[986], pts[988], coeff[97]);
                eval_4_isog_mod(pts[988], pts[990], coeff[98]);
                eval_4_isog_mod(pts[990], pts[992], coeff[99]);
                eval_4_isog_mod(pts[992], pts[994], coeff[100]);
                eval_4_isog_mod(pts[994], pts[996], coeff[101]);
                eval_4_isog_mod(pts[996], pts[998], coeff[102]);
                eval_4_isog_mod(pts[998], pts[1000], coeff[103]);
                eval_4_isog_mod(pts[1000], pts[1002], coeff[104]);
                eval_4_isog_mod(pts[1002], pts[1004], coeff[105]);
                eval_4_isog_mod(pts[1004], pts[1006], coeff[106]);
                eval_4_isog_mod(pts[1006], pts[1008], coeff[107]);
                eval_4_isog_mod(pts[1008], pts[1010], coeff[108]);
                eval_4_isog_mod(pts[1010], pts[1012], coeff[109]);
                eval_4_isog_mod(pts[1012], pts[1014], coeff[110]);
                eval_4_isog_mod(pts[1014], pts[1016], coeff[111]);
                eval_4_isog_mod(pts[1016], pts[1018], coeff[112]);
                lock[124][1] = 0;
                while(lock[124][0]) {
                    #pragma omp flush(lock[124][0])
                }

                eval_4_isog_mod(pts[1009], pts[1021], coeff[123]);
                eval_4_isog_mod(pts[1018], pts[1022], coeff[113]);
                eval_4_isog_mod(pts[1021], pts[1024], coeff[124]);
                lock[125][1] = 0;
                while(lock[125][0]) {
                    #pragma omp flush(lock[125][0])
                }

                eval_4_isog_mod(pts[1022], pts[1026], coeff[114]);
                eval_4_isog_mod(pts[1026], pts[1029], coeff[115]);
                lock[126][1] = 0;
                while(lock[126][0]) {
                    #pragma omp flush(lock[126][0])
                }

                eval_4_isog_mod(pts[1028], pts[1031], coeff[125]);
                eval_4_isog_mod(pts[1029], pts[1033], coeff[116]);
                lock[127][1] = 0;
                while(lock[127][0]) {
                    #pragma omp flush(lock[127][0])
                }

                eval_4_isog_mod(pts[1031], pts[1035], coeff[126]);
                eval_4_isog_mod(pts[1033], pts[1037], coeff[117]);
                lock[128][1] = 0;
                while(lock[128][0]) {
                    #pragma omp flush(lock[128][0])
                }

                eval_4_isog_mod(pts[1035], pts[1038], coeff[127]);
                xDBLe(pts[1038], pts[1041], A24plus[128], C24[128], 2);
                eval_4_isog_mod(pts[985], pts[1043], coeff[123]);
                xDBLe(pts[1041], pts[1045], A24plus[128], C24[128], 2);
                get_4_isog(pts[1045], A24plus[129], C24[129], coeff[128]);
                eval_4_isog_mod(pts[1043], pts[1047], coeff[124]);
                eval_4_isog_mod(pts[1041], pts[1049], coeff[128]);
                get_4_isog(pts[1049], A24plus[130], C24[130], coeff[129]);
                lock[129][1] = 0;
                while(lock[129][0]) {
                    #pragma omp flush(lock[129][0])
                }

                eval_4_isog_mod(pts[1046], pts[1051], coeff[128]);
                eval_4_isog_mod(pts[1048], pts[1053], coeff[121]);
                eval_4_isog_mod(pts[1051], pts[1055], coeff[129]);
                eval_4_isog_mod(pts[1053], pts[1057], coeff[122]);
                lock[130][1] = 0;
                while(lock[130][0]) {
                    #pragma omp flush(lock[130][0])
                }

                eval_4_isog_mod(pts[1055], pts[1059], coeff[130]);
                eval_4_isog_mod(pts[1057], pts[1061], coeff[123]);
                xDBLe(pts[1059], pts[1063], A24plus[131], C24[131], 2);
                eval_4_isog_mod(pts[1061], pts[1065], coeff[124]);
                xDBLe(pts[1063], pts[1067], A24plus[131], C24[131], 2);
                eval_4_isog_mod(pts[1065], pts[1069], coeff[125]);
                xDBLe(pts[1067], pts[1071], A24plus[131], C24[131], 2);
                get_4_isog(pts[1071], A24plus[132], C24[132], coeff[131]);
                eval_4_isog_mod(pts[1069], pts[1073], coeff[126]);
                eval_4_isog_mod(pts[1067], pts[1075], coeff[131]);
                get_4_isog(pts[1075], A24plus[133], C24[133], coeff[132]);
                lock[131][1] = 0;
                while(lock[131][0]) {
                    #pragma omp flush(lock[131][0])
                }

                eval_4_isog_mod(pts[1063], pts[1076], coeff[131]);
                eval_4_isog_mod(pts[1072], pts[1078], coeff[131]);
                eval_4_isog_mod(pts[1076], pts[1081], coeff[132]);
                get_4_isog(pts[1081], A24plus[134], C24[134], coeff[133]);
                eval_4_isog_mod(pts[1078], pts[1083], coeff[132]);
                lock[132][1] = 0;
                while(lock[132][0]) {
                    #pragma omp flush(lock[132][0])
                }

                eval_4_isog_mod(pts[1079], pts[1084], coeff[128]);
                eval_4_isog_mod(pts[1082], pts[1086], coeff[133]);
                get_4_isog(pts[1086], A24plus[135], C24[135], coeff[134]);
                eval_4_isog_mod(pts[1084], pts[1088], coeff[129]);
                lock[133][1] = 0;
                while(lock[133][0]) {
                    #pragma omp flush(lock[133][0])
                }

                eval_4_isog_mod(pts[1087], pts[1090], coeff[134]);
                xDBLe(pts[1090], pts[1093], A24plus[135], C24[135], 2);
                lock[134][1] = 0;
                while(lock[134][0]) {
                    #pragma omp flush(lock[134][0])
                }

                eval_4_isog_mod(pts[1091], pts[1094], coeff[131]);
                eval_4_isog_mod(pts[1094], pts[1097], coeff[132]);
                lock[135][1] = 0;
                while(lock[135][0]) {
                    #pragma omp flush(lock[135][0])
                }

                eval_4_isog_mod(pts[1095], pts[1098], coeff[100]);
                eval_4_isog_mod(pts[1098], pts[1101], coeff[101]);
                lock[136][1] = 0;
                while(lock[136][0]) {
                    #pragma omp flush(lock[136][0])
                }

                eval_4_isog_mod(pts[1100], pts[1103], coeff[134]);
                lock[137][1] = 0;
                while(lock[137][0]) {
                    #pragma omp flush(lock[137][0])
                }

                eval_4_isog_mod(pts[1099], pts[1105], coeff[135]);
                get_4_isog(pts[1105], A24plus[137], C24[137], coeff[136]);
                eval_4_isog_mod(pts[1096], pts[1106], coeff[135]);
                eval_4_isog_mod(pts[1090], pts[1108], coeff[135]);
                eval_4_isog_mod(pts[1106], pts[1111], coeff[136]);
                get_4_isog(pts[1111], A24plus[138], C24[138], coeff[137]);
                lock[138][1] = 0;
                while(lock[138][0]) {
                    #pragma omp flush(lock[138][0])
                }

                eval_4_isog_mod(pts[1107], pts[1112], coeff[136]);
                eval_4_isog_mod(pts[1110], pts[1115], coeff[104]);
                eval_4_isog_mod(pts[1112], pts[1116], coeff[137]);
                get_4_isog(pts[1116], A24plus[139], C24[139], coeff[138]);
                eval_4_isog_mod(pts[1115], pts[1119], coeff[105]);
                lock[139][1] = 0;
                while(lock[139][0]) {
                    #pragma omp flush(lock[139][0])
                }

                eval_4_isog_mod(pts[1118], pts[1121], coeff[138]);
                lock[140][1] = 0;
                while(lock[140][0]) {
                    #pragma omp flush(lock[140][0])
                }

                eval_4_isog_mod(pts[1121], pts[1123], coeff[139]);
                xDBLe(pts[1123], pts[1125], A24plus[140], C24[140], 2);
                xDBLe(pts[1125], pts[1127], A24plus[140], C24[140], 2);
                xDBLe(pts[1127], pts[1129], A24plus[140], C24[140], 2);
                xDBLe(pts[1129], pts[1131], A24plus[140], C24[140], 2);
                xDBLe(pts[1131], pts[1133], A24plus[140], C24[140], 2);
                xDBLe(pts[1133], pts[1135], A24plus[140], C24[140], 2);
                xDBLe(pts[1135], pts[1137], A24plus[140], C24[140], 2);
                xDBLe(pts[1137], pts[1139], A24plus[140], C24[140], 2);
                xDBLe(pts[1139], pts[1141], A24plus[140], C24[140], 2);
                xDBLe(pts[1141], pts[1143], A24plus[140], C24[140], 2);
                xDBLe(pts[1143], pts[1145], A24plus[140], C24[140], 2);
                xDBLe(pts[1145], pts[1147], A24plus[140], C24[140], 2);
                xDBLe(pts[1147], pts[1149], A24plus[140], C24[140], 2);
                xDBLe(pts[1149], pts[1151], A24plus[140], C24[140], 2);
                xDBLe(pts[1151], pts[1153], A24plus[140], C24[140], 2);
                xDBLe(pts[1153], pts[1155], A24plus[140], C24[140], 2);
                xDBLe(pts[1155], pts[1157], A24plus[140], C24[140], 2);
                xDBLe(pts[1157], pts[1159], A24plus[140], C24[140], 2);
                xDBLe(pts[1159], pts[1161], A24plus[140], C24[140], 2);
                get_4_isog(pts[1161], A24plus[141], C24[141], coeff[140]);
                eval_4_isog_mod(pts[1159], pts[1163], coeff[140]);
                get_4_isog(pts[1163], A24plus[142], C24[142], coeff[141]);
                lock[141][1] = 0;
                while(lock[141][0]) {
                    #pragma omp flush(lock[141][0])
                }

                eval_4_isog_mod(pts[1153], pts[1165], coeff[140]);
                eval_4_isog_mod(pts[1162], pts[1166], coeff[127]);
                eval_4_isog_mod(pts[1165], pts[1168], coeff[141]);
                lock[142][1] = 0;
                while(lock[142][0]) {
                    #pragma omp flush(lock[142][0])
                }

                eval_4_isog_mod(pts[1166], pts[1170], coeff[128]);
                eval_4_isog_mod(pts[1143], pts[1173], coeff[140]);
                eval_4_isog_mod(pts[1170], pts[1174], coeff[129]);
                eval_4_isog_mod(pts[1173], pts[1177], coeff[141]);
                eval_4_isog_mod(pts[1174], pts[1178], coeff[130]);
                eval_4_isog_mod(pts[1177], pts[1181], coeff[142]);
                eval_4_isog_mod(pts[1178], pts[1183], coeff[131]);
                lock[143][1] = 0;
                while(lock[143][0]) {
                    #pragma omp flush(lock[143][0])
                }

                eval_4_isog_mod(pts[1180], pts[1184], coeff[144]);
                eval_4_isog_mod(pts[1183], pts[1187], coeff[132]);
                xDBLe(pts[1184], pts[1188], A24plus[145], C24[145], 2);
                get_4_isog(pts[1188], A24plus[146], C24[146], coeff[145]);
                eval_4_isog_mod(pts[1187], pts[1191], coeff[133]);
                lock[144][1] = 0;
                while(lock[144][0]) {
                    #pragma omp flush(lock[144][0])
                }

                eval_4_isog_mod(pts[1189], pts[1193], coeff[145]);
                eval_4_isog_mod(pts[1123], pts[1195], coeff[140]);
                lock[145][1] = 0;
                while(lock[145][0]) {
                    #pragma omp flush(lock[145][0])
                }

                eval_4_isog_mod(pts[1191], pts[1196], coeff[134]);
                eval_4_isog_mod(pts[1195], pts[1199], coeff[141]);
                eval_4_isog_mod(pts[1196], pts[1200], coeff[135]);
                eval_4_isog_mod(pts[1199], pts[1203], coeff[142]);
                eval_4_isog_mod(pts[1200], pts[1204], coeff[136]);
                eval_4_isog_mod(pts[1203], pts[1207], coeff[143]);
                eval_4_isog_mod(pts[1204], pts[1208], coeff[137]);
                lock[146][1] = 0;
                while(lock[146][0]) {
                    #pragma omp flush(lock[146][0])
                }

                eval_4_isog_mod(pts[1206], pts[1211], coeff[147]);
                eval_4_isog_mod(pts[1208], pts[1213], coeff[138]);
                eval_4_isog_mod(pts[1211], pts[1215], coeff[148]);
                eval_4_isog_mod(pts[1213], pts[1217], coeff[139]);
                lock[147][1] = 0;
                while(lock[147][0]) {
                    #pragma omp flush(lock[147][0])
                }

                eval_4_isog_mod(pts[1216], pts[1219], coeff[146]);
                eval_4_isog_mod(pts[1217], pts[1220], coeff[140]);
                lock[148][1] = 0;
                while(lock[148][0]) {
                    #pragma omp flush(lock[148][0])
                }

                eval_4_isog_mod(pts[1219], pts[1222], coeff[147]);
                eval_4_isog_mod(pts[1222], pts[1225], coeff[148]);
                lock[149][1] = 0;
                while(lock[149][0]) {
                    #pragma omp flush(lock[149][0])
                }

                eval_4_isog_mod(pts[1223], pts[1226], coeff[142]);
                eval_4_isog_mod(pts[1226], pts[1229], coeff[143]);
                lock[150][1] = 0;
                while(lock[150][0]) {
                    #pragma omp flush(lock[150][0])
                }

                eval_4_isog_mod(pts[1224], pts[1230], coeff[150]);
                get_4_isog(pts[1230], A24plus[152], C24[152], coeff[151]);
                eval_4_isog_mod(pts[1218], pts[1232], coeff[150]);
                lock[151][1] = 0;
                while(lock[151][0]) {
                    #pragma omp flush(lock[151][0])
                }

                eval_4_isog_mod(pts[1231], pts[1235], coeff[151]);
                get_4_isog(pts[1235], A24plus[153], C24[153], coeff[152]);
                eval_4_isog_mod(pts[1233], pts[1237], coeff[151]);
                lock[152][1] = 0;
                while(lock[152][0]) {
                    #pragma omp flush(lock[152][0])
                }

                eval_4_isog_mod(pts[1234], pts[1238], coeff[145]);
                eval_4_isog_mod(pts[1238], pts[1241], coeff[146]);
                eval_4_isog_mod(pts[1241], pts[1243], coeff[147]);
                eval_4_isog_mod(pts[1243], pts[1245], coeff[148]);
                eval_4_isog_mod(pts[1245], pts[1247], coeff[149]);
                eval_4_isog_mod(pts[1247], pts[1249], coeff[150]);
                eval_4_isog_mod(pts[1249], pts[1251], coeff[151]);
                eval_4_isog_mod(pts[1251], pts[1253], coeff[152]);
                lock[153][1] = 0;
                while(lock[153][0]) {
                    #pragma omp flush(lock[153][0])
                }

                eval_4_isog_mod(pts[1248], pts[1255], coeff[154]);
                eval_4_isog_mod(pts[1246], pts[1256], coeff[154]);
                lock[154][1] = 0;
                while(lock[154][0]) {
                    #pragma omp flush(lock[154][0])
                }

                eval_4_isog_mod(pts[1255], pts[1259], coeff[155]);
                get_4_isog(pts[1259], A24plus[157], C24[157], coeff[156]);
                eval_4_isog_mod(pts[1256], pts[1260], coeff[155]);
                eval_4_isog_mod(pts[1260], pts[1263], coeff[156]);
                get_4_isog(pts[1263], A24plus[158], C24[158], coeff[157]);
                lock[155][1] = 0;
                while(lock[155][0]) {
                    #pragma omp flush(lock[155][0])
                }

                eval_4_isog_mod(pts[1262], pts[1265], coeff[155]);
                eval_4_isog_mod(pts[1265], pts[1267], coeff[156]);
                eval_4_isog_mod(pts[1267], pts[1269], coeff[157]);
                lock[156][1] = 0;
                while(lock[156][0]) {
                    #pragma omp flush(lock[156][0])
                }

                eval_4_isog_mod(pts[1269], pts[1271], coeff[158]);
                lock[157][1] = 0;
                while(lock[157][0]) {
                    #pragma omp flush(lock[157][0])
                }

                lock[158][1] = 0;
                while(lock[158][0]) {
                    #pragma omp flush(lock[158][0])
                }

                eval_4_isog_mod(pts[1295], pts[1299], coeff[160]);
                lock[159][1] = 0;
                while(lock[159][0]) {
                    #pragma omp flush(lock[159][0])
                }

                eval_4_isog_mod(pts[1299], pts[1301], coeff[161]);
                get_4_isog(pts[1301], A24plus[163], C24[163], coeff[162]);
                eval_4_isog_mod(pts[1291], pts[1303], coeff[160]);
                lock[160][1] = 0;
                while(lock[160][0]) {
                    #pragma omp flush(lock[160][0])
                }

                eval_4_isog_mod(pts[1302], pts[1304], coeff[162]);
                xDBLe(pts[1304], pts[1307], A24plus[163], C24[163], 2);
                get_4_isog(pts[1307], A24plus[164], C24[164], coeff[163]);
                lock[161][1] = 0;
                while(lock[161][0]) {
                    #pragma omp flush(lock[161][0])
                }

                eval_4_isog_mod(pts[1306], pts[1309], coeff[161]);
                eval_4_isog_mod(pts[1285], pts[1310], coeff[160]);
                eval_4_isog_mod(pts[1309], pts[1313], coeff[162]);
                eval_4_isog_mod(pts[1310], pts[1314], coeff[161]);
                lock[162][1] = 0;
                while(lock[162][0]) {
                    #pragma omp flush(lock[162][0])
                }

                eval_4_isog_mod(pts[1313], pts[1316], coeff[163]);
                eval_4_isog_mod(pts[1316], pts[1319], coeff[164]);
                eval_4_isog_mod(pts[1280], pts[1321], coeff[160]);
                lock[163][1] = 0;
                while(lock[163][0]) {
                    #pragma omp flush(lock[163][0])
                }

                eval_4_isog_mod(pts[1319], pts[1323], coeff[165]);
                eval_4_isog_mod(pts[1321], pts[1325], coeff[161]);
                lock[164][1] = 0;
                while(lock[164][0]) {
                    #pragma omp flush(lock[164][0])
                }

                eval_4_isog_mod(pts[1323], pts[1326], coeff[166]);
                xDBLe(pts[1326], pts[1329], A24plus[167], C24[167], 2);
                get_4_isog(pts[1329], A24plus[168], C24[168], coeff[167]);
                lock[165][1] = 0;
                while(lock[165][0]) {
                    #pragma omp flush(lock[165][0])
                }

                eval_4_isog_mod(pts[1327], pts[1330], coeff[166]);
                eval_4_isog_mod(pts[1330], pts[1333], coeff[167]);
                lock[166][1] = 0;
                while(lock[166][0]) {
                    #pragma omp flush(lock[166][0])
                }

                eval_4_isog_mod(pts[1331], pts[1334], coeff[164]);
                eval_4_isog_mod(pts[1334], pts[1336], coeff[165]);
                eval_4_isog_mod(pts[1336], pts[1339], coeff[166]);
                lock[167][1] = 0;
                while(lock[167][0]) {
                    #pragma omp flush(lock[167][0])
                }

                xDBLe(pts[1338], pts[1341], A24plus[169], C24[169], 2);
                eval_4_isog_mod(pts[1339], pts[1342], coeff[167]);
                lock[168][1] = 0;
                while(lock[168][0]) {
                    #pragma omp flush(lock[168][0])
                }

                eval_4_isog_mod(pts[1342], pts[1345], coeff[168]);
                lock[169][1] = 0;
                while(lock[169][0]) {
                    #pragma omp flush(lock[169][0])
                }

                eval_4_isog_mod(pts[1341], pts[1347], coeff[169]);
                get_4_isog(pts[1347], A24plus[171], C24[171], coeff[170]);
                eval_4_isog_mod(pts[1338], pts[1348], coeff[169]);
                eval_4_isog_mod(pts[1345], pts[1350], coeff[169]);
                lock[170][1] = 0;
                while(lock[170][0]) {
                    #pragma omp flush(lock[170][0])
                }

                eval_4_isog_mod(pts[1349], pts[1353], coeff[170]);
                eval_4_isog_mod(pts[1350], pts[1354], coeff[170]);
                lock[171][1] = 0;
                while(lock[171][0]) {
                    #pragma omp flush(lock[171][0])
                }

                eval_4_isog_mod(pts[1354], pts[1357], coeff[171]);
                lock[172][1] = 0;
                while(lock[172][0]) {
                    #pragma omp flush(lock[172][0])
                }

                eval_4_isog_mod(pts[1357], pts[1359], coeff[172]);
                xDBLe(pts[1359], pts[1361], A24plus[173], C24[173], 2);
                xDBLe(pts[1361], pts[1363], A24plus[173], C24[173], 2);
                xDBLe(pts[1363], pts[1365], A24plus[173], C24[173], 2);
                xDBLe(pts[1365], pts[1367], A24plus[173], C24[173], 2);
                get_4_isog(pts[1367], A24plus[174], C24[174], coeff[173]);
                eval_4_isog_mod(pts[1365], pts[1369], coeff[173]);
                get_4_isog(pts[1369], A24plus[175], C24[175], coeff[174]);
                lock[173][1] = 0;
                while(lock[173][0]) {
                    #pragma omp flush(lock[173][0])
                }

                eval_4_isog_mod(pts[1363], pts[1370], coeff[173]);
                eval_4_isog_mod(pts[1370], pts[1373], coeff[174]);
                get_4_isog(pts[1373], A24plus[176], C24[176], coeff[175]);
                lock[174][1] = 0;
                while(lock[174][0]) {
                    #pragma omp flush(lock[174][0])
                }

                eval_4_isog_mod(pts[1372], pts[1375], coeff[173]);
                eval_4_isog_mod(pts[1375], pts[1377], coeff[174]);
                eval_4_isog_mod(pts[1377], pts[1379], coeff[175]);
                lock[175][1] = 0;
                while(lock[175][0]) {
                    #pragma omp flush(lock[175][0])
                }

                eval_4_isog_mod(pts[1376], pts[1380], coeff[176]);
                get_4_isog(pts[1380], A24plus[178], C24[178], coeff[177]);
                lock[176][1] = 0;
                while(lock[176][0]) {
                    #pragma omp flush(lock[176][0])
                }

                lock[177][1] = 0;
                while(lock[177][0]) {
                    #pragma omp flush(lock[177][0])
                }

                eval_4_isog_mod(pts[1387], pts[1391], coeff[178]);
                lock[178][1] = 0;
                while(lock[178][0]) {
                    #pragma omp flush(lock[178][0])
                }

                eval_4_isog_mod(pts[1391], pts[1393], coeff[179]);
                get_4_isog(pts[1393], A24plus[181], C24[181], coeff[180]);
                eval_4_isog_mod(pts[1382], pts[1395], coeff[178]);
                lock[179][1] = 0;
                while(lock[179][0]) {
                    #pragma omp flush(lock[179][0])
                }

                eval_4_isog_mod(pts[1395], pts[1397], coeff[179]);
                eval_4_isog_mod(pts[1397], pts[1399], coeff[180]);
                lock[180][1] = 0;
                while(lock[180][0]) {
                    #pragma omp flush(lock[180][0])
                }

                eval_4_isog_mod(pts[1396], pts[1400], coeff[181]);
                get_4_isog(pts[1400], A24plus[183], C24[183], coeff[182]);
                lock[181][1] = 0;
                while(lock[181][0]) {
                    #pragma omp flush(lock[181][0])
                }

                lock[182][1] = 0;
                while(lock[182][0]) {
                    #pragma omp flush(lock[182][0])
                }

                eval_4_isog_mod(pts[1402], pts[1406], coeff[183]);
            }
        }
    }

    eval_4_isog(pts[1406], coeff[184]);
    get_4_isog(pts[1406], A24plus[186], C24[186], coeff[185]);

    fp2div2(C24[186], C24[186]);
    fp2sub(A24plus[186], C24[186], A24plus[186]);
    fp2div2(C24[186], C24[186]);
    j_inv(A24plus[186], C24[186], jinv);
    fp2_encode(jinv, SharedSecretA);

    return 0;
}

 #if ((BOB_PRIMES == 1))
int EphemeralKeyGeneration_B(const unsigned char* PrivateKeyB, unsigned char* PublicKeyB) {
    point_proj_t phiP = {0}, phiQ = {0}, phiR = {0}, pts[2242];
    f2elm_t XPB, XQB, XRB, coeff[MAX_Bob][3], A24minus[MAX_Bob+1] = {0}, A24plus[MAX_Bob+1] = {0}, A = {0};
    char lock[263][2];

    for(int i = 0; i < 263; i++)
        for(int j = 0; j < 2; j++)
            lock[i][j] = 1;

    init_basis((digit_t*)B_gen, XPB, XQB, XRB);
    init_basis((digit_t*)A_gen, phiP->X, phiQ->X, phiR->X);
    fpcopy((digit_t*)&Montgomery_one, (phiP->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, (phiQ->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, (phiR->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, A24plus[0][0]);
    fp2add(A24plus[0], A24plus[0], A24plus[0]);
    fp2copy(A24plus[0], A24minus[0]);
    fp2neg(A24minus[0]);
    LADDER3PT(XPB, XQB, XRB, (digit_t*)PrivateKeyB, BOB, pts[0], A);

    for(int i = 0; i < MAX_Bob-1; i++)
        xTPLe(pts[i], pts[i+1], A24minus[0], A24plus[0], 1);
    get_3_isog(pts[MAX_Bob-1], A24minus[1], A24plus[1], coeff[0]);

    omp_set_num_threads(2);
    #pragma omp parallel
    {
        #pragma omp sections
        {
            #pragma omp section
            {
                eval_3_isog_mod(pts[237], pts[239], coeff[0]);
                get_3_isog(pts[239], A24minus[2], A24plus[2], coeff[1]);
                eval_3_isog_mod(pts[235], pts[241], coeff[0]);
                lock[0][0] = 0;
                while(lock[0][1]) {
                    #pragma omp flush(lock[0][1])
                }

                eval_3_isog_mod(pts[240], pts[244], coeff[1]);
                get_3_isog(pts[244], A24minus[3], A24plus[3], coeff[2]);
                eval_3_isog_mod(pts[242], pts[246], coeff[1]);
                eval_3_isog_mod(pts[229], pts[248], coeff[0]);
                lock[1][0] = 0;
                while(lock[1][1]) {
                    #pragma omp flush(lock[1][1])
                }

                eval_3_isog_mod(pts[246], pts[250], coeff[2]);
                eval_3_isog_mod(pts[247], pts[251], coeff[2]);
                lock[2][0] = 0;
                while(lock[2][1]) {
                    #pragma omp flush(lock[2][1])
                }

                eval_3_isog_mod(pts[250], pts[253], coeff[3]);
                get_3_isog(pts[253], A24minus[5], A24plus[5], coeff[4]);
                eval_3_isog_mod(pts[252], pts[255], coeff[2]);
                lock[3][0] = 0;
                while(lock[3][1]) {
                    #pragma omp flush(lock[3][1])
                }

                eval_3_isog_mod(pts[254], pts[257], coeff[4]);
                xTPLe(pts[257], pts[260], A24minus[5], A24plus[5], 1);
                get_3_isog(pts[260], A24minus[6], A24plus[6], coeff[5]);
                lock[4][0] = 0;
                while(lock[4][1]) {
                    #pragma omp flush(lock[4][1])
                }

                eval_3_isog_mod(pts[258], pts[261], coeff[4]);
                eval_3_isog_mod(pts[261], pts[264], coeff[5]);
                eval_3_isog_mod(pts[220], pts[266], coeff[0]);
                lock[5][0] = 0;
                while(lock[5][1]) {
                    #pragma omp flush(lock[5][1])
                }

                eval_3_isog_mod(pts[265], pts[268], coeff[4]);
                eval_3_isog_mod(pts[266], pts[269], coeff[1]);
                lock[6][0] = 0;
                while(lock[6][1]) {
                    #pragma omp flush(lock[6][1])
                }

                eval_3_isog_mod(pts[269], pts[272], coeff[2]);
                xTPLe(pts[270], pts[273], A24minus[7], A24plus[7], 1);
                get_3_isog(pts[273], A24minus[8], A24plus[8], coeff[7]);
                lock[7][0] = 0;
                while(lock[7][1]) {
                    #pragma omp flush(lock[7][1])
                }

                eval_3_isog_mod(pts[272], pts[275], coeff[3]);
                eval_3_isog_mod(pts[267], pts[277], coeff[7]);
                eval_3_isog_mod(pts[275], pts[279], coeff[4]);
                lock[8][0] = 0;
                while(lock[8][1]) {
                    #pragma omp flush(lock[8][1])
                }

                eval_3_isog_mod(pts[278], pts[282], coeff[8]);
                eval_3_isog_mod(pts[280], pts[284], coeff[1]);
                lock[9][0] = 0;
                while(lock[9][1]) {
                    #pragma omp flush(lock[9][1])
                }

                eval_3_isog_mod(pts[283], pts[286], coeff[6]);
                eval_3_isog_mod(pts[284], pts[287], coeff[2]);
                lock[10][0] = 0;
                while(lock[10][1]) {
                    #pragma omp flush(lock[10][1])
                }

                eval_3_isog_mod(pts[286], pts[289], coeff[7]);
                eval_3_isog_mod(pts[289], pts[292], coeff[8]);
                lock[11][0] = 0;
                while(lock[11][1]) {
                    #pragma omp flush(lock[11][1])
                }

                eval_3_isog_mod(pts[290], pts[293], coeff[4]);
                eval_3_isog_mod(pts[293], pts[296], coeff[5]);
                lock[12][0] = 0;
                while(lock[12][1]) {
                    #pragma omp flush(lock[12][1])
                }

                eval_3_isog_mod(pts[291], pts[297], coeff[10]);
                get_3_isog(pts[297], A24minus[12], A24plus[12], coeff[11]);
                eval_3_isog_mod(pts[295], pts[300], coeff[10]);
                lock[13][0] = 0;
                while(lock[13][1]) {
                    #pragma omp flush(lock[13][1])
                }

                eval_3_isog_mod(pts[296], pts[301], coeff[6]);
                eval_3_isog_mod(pts[300], pts[304], coeff[11]);
                eval_3_isog_mod(pts[301], pts[305], coeff[7]);
                lock[14][0] = 0;
                while(lock[14][1]) {
                    #pragma omp flush(lock[14][1])
                }

                eval_3_isog_mod(pts[304], pts[308], coeff[12]);
                eval_3_isog_mod(pts[305], pts[309], coeff[8]);
                lock[15][0] = 0;
                while(lock[15][1]) {
                    #pragma omp flush(lock[15][1])
                }

                eval_3_isog_mod(pts[309], pts[312], coeff[9]);
                eval_3_isog_mod(pts[310], pts[313], coeff[2]);
                lock[16][0] = 0;
                while(lock[16][1]) {
                    #pragma omp flush(lock[16][1])
                }

                eval_3_isog_mod(pts[313], pts[316], coeff[3]);
                xTPLe(pts[314], pts[317], A24minus[14], A24plus[14], 1);
                lock[17][0] = 0;
                while(lock[17][1]) {
                    #pragma omp flush(lock[17][1])
                }

                eval_3_isog_mod(pts[316], pts[319], coeff[4]);
                eval_3_isog_mod(pts[319], pts[322], coeff[5]);
                lock[18][0] = 0;
                while(lock[18][1]) {
                    #pragma omp flush(lock[18][1])
                }

                eval_3_isog_mod(pts[321], pts[324], coeff[13]);
                eval_3_isog_mod(pts[322], pts[325], coeff[6]);
                lock[19][0] = 0;
                while(lock[19][1]) {
                    #pragma omp flush(lock[19][1])
                }

                eval_3_isog_mod(pts[317], pts[327], coeff[14]);
                eval_3_isog_mod(pts[311], pts[329], coeff[14]);
                eval_3_isog_mod(pts[327], pts[332], coeff[15]);
                get_3_isog(pts[332], A24minus[17], A24plus[17], coeff[16]);
                eval_3_isog_mod(pts[329], pts[334], coeff[15]);
                lock[20][0] = 0;
                while(lock[20][1]) {
                    #pragma omp flush(lock[20][1])
                }

                eval_3_isog_mod(pts[330], pts[335], coeff[15]);
                eval_3_isog_mod(pts[334], pts[338], coeff[16]);
                eval_3_isog_mod(pts[335], pts[339], coeff[16]);
                lock[21][0] = 0;
                while(lock[21][1]) {
                    #pragma omp flush(lock[21][1])
                }

                eval_3_isog_mod(pts[338], pts[341], coeff[17]);
                get_3_isog(pts[341], A24minus[19], A24plus[19], coeff[18]);
                lock[22][0] = 0;
                while(lock[22][1]) {
                    #pragma omp flush(lock[22][1])
                }

                eval_3_isog_mod(pts[342], pts[344], coeff[18]);
                xTPLe(pts[344], pts[346], A24minus[19], A24plus[19], 1);
                eval_3_isog_mod(pts[189], pts[348], coeff[0]);
                xTPLe(pts[346], pts[349], A24minus[19], A24plus[19], 1);
                lock[23][0] = 0;
                while(lock[23][1]) {
                    #pragma omp flush(lock[23][1])
                }

                xTPLe(pts[349], pts[352], A24minus[19], A24plus[19], 1);
                eval_3_isog_mod(pts[350], pts[353], coeff[14]);
                lock[24][0] = 0;
                while(lock[24][1]) {
                    #pragma omp flush(lock[24][1])
                }

                eval_3_isog_mod(pts[353], pts[356], coeff[15]);
                eval_3_isog_mod(pts[354], pts[357], coeff[3]);
                lock[25][0] = 0;
                while(lock[25][1]) {
                    #pragma omp flush(lock[25][1])
                }

                eval_3_isog_mod(pts[357], pts[360], coeff[4]);
                xTPLe(pts[358], pts[361], A24minus[19], A24plus[19], 1);
                get_3_isog(pts[361], A24minus[20], A24plus[20], coeff[19]);
                lock[26][0] = 0;
                while(lock[26][1]) {
                    #pragma omp flush(lock[26][1])
                }

                eval_3_isog_mod(pts[358], pts[364], coeff[19]);
                get_3_isog(pts[364], A24minus[21], A24plus[21], coeff[20]);
                eval_3_isog_mod(pts[355], pts[365], coeff[19]);
                eval_3_isog_mod(pts[344], pts[368], coeff[19]);
                eval_3_isog_mod(pts[362], pts[369], coeff[18]);
                lock[27][0] = 0;
                while(lock[27][1]) {
                    #pragma omp flush(lock[27][1])
                }

                eval_3_isog_mod(pts[365], pts[371], coeff[20]);
                get_3_isog(pts[371], A24minus[22], A24plus[22], coeff[21]);
                eval_3_isog_mod(pts[368], pts[374], coeff[20]);
                eval_3_isog_mod(pts[369], pts[375], coeff[19]);
                lock[28][0] = 0;
                while(lock[28][1]) {
                    #pragma omp flush(lock[28][1])
                }

                eval_3_isog_mod(pts[373], pts[378], coeff[21]);
                eval_3_isog_mod(pts[375], pts[380], coeff[20]);
                lock[29][0] = 0;
                while(lock[29][1]) {
                    #pragma omp flush(lock[29][1])
                }

                eval_3_isog_mod(pts[378], pts[382], coeff[22]);
                get_3_isog(pts[382], A24minus[24], A24plus[24], coeff[23]);
                eval_3_isog_mod(pts[380], pts[384], coeff[21]);
                lock[30][0] = 0;
                while(lock[30][1]) {
                    #pragma omp flush(lock[30][1])
                }

                eval_3_isog_mod(pts[381], pts[385], coeff[9]);
                eval_3_isog_mod(pts[385], pts[388], coeff[10]);
                lock[31][0] = 0;
                while(lock[31][1]) {
                    #pragma omp flush(lock[31][1])
                }

                eval_3_isog_mod(pts[387], pts[390], coeff[23]);
                eval_3_isog_mod(pts[388], pts[391], coeff[11]);
                lock[32][0] = 0;
                while(lock[32][1]) {
                    #pragma omp flush(lock[32][1])
                }

                eval_3_isog_mod(pts[390], pts[393], coeff[24]);
                eval_3_isog_mod(pts[393], pts[395], coeff[25]);
                xTPLe(pts[395], pts[397], A24minus[26], A24plus[26], 1);
                xTPLe(pts[397], pts[399], A24minus[26], A24plus[26], 1);
                xTPLe(pts[399], pts[401], A24minus[26], A24plus[26], 1);
                xTPLe(pts[401], pts[403], A24minus[26], A24plus[26], 1);
                xTPLe(pts[403], pts[405], A24minus[26], A24plus[26], 1);
                xTPLe(pts[405], pts[407], A24minus[26], A24plus[26], 1);
                xTPLe(pts[407], pts[410], A24minus[26], A24plus[26], 1);
                lock[33][0] = 0;
                while(lock[33][1]) {
                    #pragma omp flush(lock[33][1])
                }

                eval_3_isog_mod(pts[409], pts[412], coeff[1]);
                xTPLe(pts[410], pts[413], A24minus[26], A24plus[26], 1);
                lock[34][0] = 0;
                while(lock[34][1]) {
                    #pragma omp flush(lock[34][1])
                }

                xTPLe(pts[413], pts[416], A24minus[26], A24plus[26], 1);
                get_3_isog(pts[416], A24minus[27], A24plus[27], coeff[26]);
                eval_3_isog_mod(pts[414], pts[417], coeff[22]);
                lock[35][0] = 0;
                while(lock[35][1]) {
                    #pragma omp flush(lock[35][1])
                }

                eval_3_isog_mod(pts[413], pts[419], coeff[26]);
                get_3_isog(pts[419], A24minus[28], A24plus[28], coeff[27]);
                eval_3_isog_mod(pts[405], pts[422], coeff[26]);
                eval_3_isog_mod(pts[417], pts[424], coeff[23]);
                lock[36][0] = 0;
                while(lock[36][1]) {
                    #pragma omp flush(lock[36][1])
                }

                eval_3_isog_mod(pts[418], pts[425], coeff[4]);
                eval_3_isog_mod(pts[422], pts[428], coeff[27]);
                eval_3_isog_mod(pts[423], pts[429], coeff[27]);
                eval_3_isog_mod(pts[425], pts[432], coeff[5]);
                lock[37][0] = 0;
                while(lock[37][1]) {
                    #pragma omp flush(lock[37][1])
                }

                eval_3_isog_mod(pts[428], pts[434], coeff[28]);
                eval_3_isog_mod(pts[430], pts[436], coeff[27]);
                eval_3_isog_mod(pts[431], pts[437], coeff[25]);
                lock[38][0] = 0;
                while(lock[38][1]) {
                    #pragma omp flush(lock[38][1])
                }

                eval_3_isog_mod(pts[435], pts[440], coeff[29]);
                eval_3_isog_mod(pts[437], pts[442], coeff[26]);
                lock[39][0] = 0;
                while(lock[39][1]) {
                    #pragma omp flush(lock[39][1])
                }

                eval_3_isog_mod(pts[440], pts[444], coeff[30]);
                eval_3_isog_mod(pts[441], pts[445], coeff[29]);
                xTPLe(pts[444], pts[448], A24minus[31], A24plus[31], 1);
                get_3_isog(pts[448], A24minus[32], A24plus[32], coeff[31]);
                eval_3_isog_mod(pts[445], pts[449], coeff[30]);
                eval_3_isog_mod(pts[444], pts[452], coeff[31]);
                get_3_isog(pts[452], A24minus[33], A24plus[33], coeff[32]);
                eval_3_isog_mod(pts[449], pts[453], coeff[31]);
                eval_3_isog_mod(pts[453], pts[456], coeff[32]);
                lock[40][0] = 0;
                while(lock[40][1]) {
                    #pragma omp flush(lock[40][1])
                }

                eval_3_isog_mod(pts[455], pts[458], coeff[11]);
                xTPLe(pts[456], pts[459], A24minus[33], A24plus[33], 1);
                lock[41][0] = 0;
                while(lock[41][1]) {
                    #pragma omp flush(lock[41][1])
                }

                xTPLe(pts[459], pts[462], A24minus[33], A24plus[33], 1);
                get_3_isog(pts[462], A24minus[34], A24plus[34], coeff[33]);
                eval_3_isog_mod(pts[460], pts[463], coeff[32]);
                lock[42][0] = 0;
                while(lock[42][1]) {
                    #pragma omp flush(lock[42][1])
                }

                eval_3_isog_mod(pts[456], pts[466], coeff[33]);
                eval_3_isog_mod(pts[463], pts[467], coeff[33]);
                lock[43][0] = 0;
                while(lock[43][1]) {
                    #pragma omp flush(lock[43][1])
                }

                eval_3_isog_mod(pts[466], pts[469], coeff[34]);
                get_3_isog(pts[469], A24minus[36], A24plus[36], coeff[35]);
                lock[44][0] = 0;
                while(lock[44][1]) {
                    #pragma omp flush(lock[44][1])
                }

                eval_3_isog_mod(pts[470], pts[472], coeff[35]);
                xTPLe(pts[472], pts[474], A24minus[36], A24plus[36], 1);
                xTPLe(pts[474], pts[476], A24minus[36], A24plus[36], 1);
                xTPLe(pts[476], pts[478], A24minus[36], A24plus[36], 1);
                xTPLe(pts[478], pts[480], A24minus[36], A24plus[36], 1);
                xTPLe(pts[480], pts[482], A24minus[36], A24plus[36], 1);
                xTPLe(pts[482], pts[484], A24minus[36], A24plus[36], 1);
                xTPLe(pts[484], pts[486], A24minus[36], A24plus[36], 1);
                xTPLe(pts[486], pts[488], A24minus[36], A24plus[36], 1);
                xTPLe(pts[488], pts[490], A24minus[36], A24plus[36], 1);
                xTPLe(pts[490], pts[492], A24minus[36], A24plus[36], 1);
                xTPLe(pts[492], pts[494], A24minus[36], A24plus[36], 1);
                xTPLe(pts[494], pts[496], A24minus[36], A24plus[36], 1);
                eval_3_isog_mod(pts[144], pts[498], coeff[0]);
                xTPLe(pts[496], pts[499], A24minus[36], A24plus[36], 1);
                get_3_isog(pts[499], A24minus[37], A24plus[37], coeff[36]);
                lock[45][0] = 0;
                while(lock[45][1]) {
                    #pragma omp flush(lock[45][1])
                }

                eval_3_isog_mod(pts[498], pts[501], coeff[1]);
                eval_3_isog_mod(pts[492], pts[504], coeff[36]);
                eval_3_isog_mod(pts[486], pts[506], coeff[36]);
                eval_3_isog_mod(pts[501], pts[508], coeff[2]);
                lock[46][0] = 0;
                while(lock[46][1]) {
                    #pragma omp flush(lock[46][1])
                }

                eval_3_isog_mod(pts[503], pts[509], coeff[37]);
                get_3_isog(pts[509], A24minus[39], A24plus[39], coeff[38]);
                eval_3_isog_mod(pts[506], pts[512], coeff[37]);
                eval_3_isog_mod(pts[480], pts[513], coeff[36]);
                lock[47][0] = 0;
                while(lock[47][1]) {
                    #pragma omp flush(lock[47][1])
                }

                eval_3_isog_mod(pts[508], pts[515], coeff[3]);
                eval_3_isog_mod(pts[512], pts[518], coeff[38]);
                eval_3_isog_mod(pts[513], pts[519], coeff[37]);
                eval_3_isog_mod(pts[515], pts[521], coeff[4]);
                lock[48][0] = 0;
                while(lock[48][1]) {
                    #pragma omp flush(lock[48][1])
                }

                eval_3_isog_mod(pts[518], pts[523], coeff[39]);
                eval_3_isog_mod(pts[520], pts[526], coeff[33]);
                eval_3_isog_mod(pts[523], pts[528], coeff[40]);
                lock[49][0] = 0;
                while(lock[49][1]) {
                    #pragma omp flush(lock[49][1])
                }

                eval_3_isog_mod(pts[524], pts[529], coeff[39]);
                eval_3_isog_mod(pts[526], pts[531], coeff[34]);
                eval_3_isog_mod(pts[529], pts[534], coeff[40]);
                eval_3_isog_mod(pts[531], pts[536], coeff[35]);
                lock[50][0] = 0;
                while(lock[50][1]) {
                    #pragma omp flush(lock[50][1])
                }

                eval_3_isog_mod(pts[532], pts[537], coeff[7]);
                eval_3_isog_mod(pts[535], pts[540], coeff[39]);
                eval_3_isog_mod(pts[537], pts[542], coeff[8]);
                eval_3_isog_mod(pts[540], pts[544], coeff[40]);
                eval_3_isog_mod(pts[542], pts[546], coeff[9]);
                eval_3_isog_mod(pts[544], pts[548], coeff[41]);
                eval_3_isog_mod(pts[546], pts[550], coeff[10]);
                lock[51][0] = 0;
                while(lock[51][1]) {
                    #pragma omp flush(lock[51][1])
                }

                eval_3_isog_mod(pts[548], pts[552], coeff[42]);
                eval_3_isog_mod(pts[549], pts[553], coeff[39]);
                lock[52][0] = 0;
                while(lock[52][1]) {
                    #pragma omp flush(lock[52][1])
                }

                eval_3_isog_mod(pts[543], pts[556], coeff[43]);
                eval_3_isog_mod(pts[553], pts[558], coeff[40]);
                lock[53][0] = 0;
                while(lock[53][1]) {
                    #pragma omp flush(lock[53][1])
                }

                eval_3_isog_mod(pts[556], pts[560], coeff[44]);
                get_3_isog(pts[560], A24minus[46], A24plus[46], coeff[45]);
                eval_3_isog_mod(pts[558], pts[562], coeff[41]);
                lock[54][0] = 0;
                while(lock[54][1]) {
                    #pragma omp flush(lock[54][1])
                }

                eval_3_isog_mod(pts[561], pts[564], coeff[45]);
                eval_3_isog_mod(pts[562], pts[565], coeff[42]);
                lock[55][0] = 0;
                while(lock[55][1]) {
                    #pragma omp flush(lock[55][1])
                }

                eval_3_isog_mod(pts[565], pts[568], coeff[43]);
                eval_3_isog_mod(pts[566], pts[569], coeff[15]);
                lock[56][0] = 0;
                while(lock[56][1]) {
                    #pragma omp flush(lock[56][1])
                }

                eval_3_isog_mod(pts[568], pts[571], coeff[44]);
                eval_3_isog_mod(pts[571], pts[574], coeff[45]);
                lock[57][0] = 0;
                while(lock[57][1]) {
                    #pragma omp flush(lock[57][1])
                }

                eval_3_isog_mod(pts[570], pts[576], coeff[46]);
                get_3_isog(pts[576], A24minus[48], A24plus[48], coeff[47]);
                eval_3_isog_mod(pts[564], pts[578], coeff[46]);
                eval_3_isog_mod(pts[574], pts[579], coeff[46]);
                lock[58][0] = 0;
                while(lock[58][1]) {
                    #pragma omp flush(lock[58][1])
                }

                eval_3_isog_mod(pts[578], pts[582], coeff[47]);
                eval_3_isog_mod(pts[580], pts[584], coeff[19]);
                lock[59][0] = 0;
                while(lock[59][1]) {
                    #pragma omp flush(lock[59][1])
                }

                eval_3_isog_mod(pts[582], pts[585], coeff[48]);
                get_3_isog(pts[585], A24minus[50], A24plus[50], coeff[49]);
                lock[60][0] = 0;
                while(lock[60][1]) {
                    #pragma omp flush(lock[60][1])
                }

                eval_3_isog_mod(pts[586], pts[588], coeff[49]);
                xTPLe(pts[588], pts[590], A24minus[50], A24plus[50], 1);
                xTPLe(pts[590], pts[592], A24minus[50], A24plus[50], 1);
                xTPLe(pts[592], pts[594], A24minus[50], A24plus[50], 1);
                xTPLe(pts[594], pts[596], A24minus[50], A24plus[50], 1);
                xTPLe(pts[596], pts[598], A24minus[50], A24plus[50], 1);
                xTPLe(pts[598], pts[600], A24minus[50], A24plus[50], 1);
                xTPLe(pts[600], pts[602], A24minus[50], A24plus[50], 1);
                xTPLe(pts[602], pts[604], A24minus[50], A24plus[50], 1);
                xTPLe(pts[604], pts[606], A24minus[50], A24plus[50], 1);
                xTPLe(pts[606], pts[608], A24minus[50], A24plus[50], 1);
                xTPLe(pts[608], pts[610], A24minus[50], A24plus[50], 1);
                xTPLe(pts[610], pts[612], A24minus[50], A24plus[50], 1);
                xTPLe(pts[612], pts[614], A24minus[50], A24plus[50], 1);
                xTPLe(pts[614], pts[616], A24minus[50], A24plus[50], 1);
                xTPLe(pts[616], pts[618], A24minus[50], A24plus[50], 1);
                xTPLe(pts[618], pts[620], A24minus[50], A24plus[50], 1);
                xTPLe(pts[620], pts[622], A24minus[50], A24plus[50], 1);
                xTPLe(pts[622], pts[624], A24minus[50], A24plus[50], 1);
                get_3_isog(pts[624], A24minus[51], A24plus[51], coeff[50]);
                eval_3_isog_mod(pts[622], pts[626], coeff[50]);
                get_3_isog(pts[626], A24minus[52], A24plus[52], coeff[51]);
                lock[61][0] = 0;
                while(lock[61][1]) {
                    #pragma omp flush(lock[61][1])
                }

                eval_3_isog_mod(pts[620], pts[627], coeff[50]);
                eval_3_isog_mod(pts[612], pts[630], coeff[50]);
                eval_3_isog_mod(pts[627], pts[632], coeff[51]);
                get_3_isog(pts[632], A24minus[53], A24plus[53], coeff[52]);
                lock[62][0] = 0;
                while(lock[62][1]) {
                    #pragma omp flush(lock[62][1])
                }

                eval_3_isog_mod(pts[628], pts[633], coeff[51]);
                eval_3_isog_mod(pts[606], pts[636], coeff[50]);
                eval_3_isog_mod(pts[633], pts[638], coeff[52]);
                get_3_isog(pts[638], A24minus[54], A24plus[54], coeff[53]);
                lock[63][0] = 0;
                while(lock[63][1]) {
                    #pragma omp flush(lock[63][1])
                }

                eval_3_isog_mod(pts[634], pts[639], coeff[52]);
                eval_3_isog_mod(pts[636], pts[641], coeff[51]);
                eval_3_isog_mod(pts[639], pts[644], coeff[53]);
                get_3_isog(pts[644], A24minus[55], A24plus[55], coeff[54]);
                eval_3_isog_mod(pts[641], pts[646], coeff[52]);
                eval_3_isog_mod(pts[598], pts[647], coeff[50]);
                lock[64][0] = 0;
                while(lock[64][1]) {
                    #pragma omp flush(lock[64][1])
                }

                eval_3_isog_mod(pts[645], pts[650], coeff[54]);
                eval_3_isog_mod(pts[647], pts[652], coeff[51]);
                eval_3_isog_mod(pts[648], pts[653], coeff[44]);
                xTPLe(pts[650], pts[655], A24minus[55], A24plus[55], 1);
                get_3_isog(pts[655], A24minus[56], A24plus[56], coeff[55]);
                lock[65][0] = 0;
                while(lock[65][1]) {
                    #pragma omp flush(lock[65][1])
                }

                eval_3_isog_mod(pts[653], pts[658], coeff[45]);
                eval_3_isog_mod(pts[654], pts[659], coeff[3]);
                eval_3_isog_mod(pts[656], pts[661], coeff[55]);
                eval_3_isog_mod(pts[658], pts[664], coeff[46]);
                lock[66][0] = 0;
                while(lock[66][1]) {
                    #pragma omp flush(lock[66][1])
                }

                eval_3_isog_mod(pts[659], pts[665], coeff[4]);
                eval_3_isog_mod(pts[662], pts[667], coeff[54]);
                eval_3_isog_mod(pts[665], pts[670], coeff[5]);
                eval_3_isog_mod(pts[667], pts[672], coeff[55]);
                lock[67][0] = 0;
                while(lock[67][1]) {
                    #pragma omp flush(lock[67][1])
                }

                eval_3_isog_mod(pts[669], pts[674], coeff[48]);
                xTPLe(pts[671], pts[676], A24minus[57], A24plus[57], 1);
                get_3_isog(pts[676], A24minus[58], A24plus[58], coeff[57]);
                eval_3_isog_mod(pts[672], pts[677], coeff[56]);
                eval_3_isog_mod(pts[674], pts[679], coeff[49]);
                lock[68][0] = 0;
                while(lock[68][1]) {
                    #pragma omp flush(lock[68][1])
                }

                eval_3_isog_mod(pts[671], pts[681], coeff[57]);
                get_3_isog(pts[681], A24minus[59], A24plus[59], coeff[58]);
                eval_3_isog_mod(pts[677], pts[683], coeff[57]);
                eval_3_isog_mod(pts[680], pts[686], coeff[8]);
                lock[69][0] = 0;
                while(lock[69][1]) {
                    #pragma omp flush(lock[69][1])
                }

                eval_3_isog_mod(pts[683], pts[688], coeff[58]);
                eval_3_isog_mod(pts[685], pts[690], coeff[51]);
                lock[70][0] = 0;
                while(lock[70][1]) {
                    #pragma omp flush(lock[70][1])
                }

                eval_3_isog_mod(pts[688], pts[692], coeff[59]);
                eval_3_isog_mod(pts[689], pts[693], coeff[56]);
                xTPLe(pts[692], pts[696], A24minus[60], A24plus[60], 1);
                eval_3_isog_mod(pts[693], pts[697], coeff[57]);
                xTPLe(pts[696], pts[700], A24minus[60], A24plus[60], 1);
                eval_3_isog_mod(pts[697], pts[701], coeff[58]);
                xTPLe(pts[700], pts[704], A24minus[60], A24plus[60], 1);
                get_3_isog(pts[704], A24minus[61], A24plus[61], coeff[60]);
                eval_3_isog_mod(pts[701], pts[705], coeff[59]);
                eval_3_isog_mod(pts[700], pts[708], coeff[60]);
                get_3_isog(pts[708], A24minus[62], A24plus[62], coeff[61]);
                lock[71][0] = 0;
                while(lock[71][1]) {
                    #pragma omp flush(lock[71][1])
                }

                eval_3_isog_mod(pts[696], pts[709], coeff[60]);
                eval_3_isog_mod(pts[706], pts[712], coeff[56]);
                eval_3_isog_mod(pts[709], pts[714], coeff[61]);
                get_3_isog(pts[714], A24minus[63], A24plus[63], coeff[62]);
                lock[72][0] = 0;
                while(lock[72][1]) {
                    #pragma omp flush(lock[72][1])
                }

                eval_3_isog_mod(pts[710], pts[715], coeff[61]);
                eval_3_isog_mod(pts[713], pts[718], coeff[15]);
                eval_3_isog_mod(pts[715], pts[719], coeff[62]);
                get_3_isog(pts[719], A24minus[64], A24plus[64], coeff[63]);
                eval_3_isog_mod(pts[718], pts[722], coeff[16]);
                lock[73][0] = 0;
                while(lock[73][1]) {
                    #pragma omp flush(lock[73][1])
                }

                eval_3_isog_mod(pts[721], pts[724], coeff[59]);
                eval_3_isog_mod(pts[722], pts[725], coeff[17]);
                lock[74][0] = 0;
                while(lock[74][1]) {
                    #pragma omp flush(lock[74][1])
                }

                eval_3_isog_mod(pts[725], pts[728], coeff[18]);
                xTPLe(pts[726], pts[729], A24minus[64], A24plus[64], 1);
                lock[75][0] = 0;
                while(lock[75][1]) {
                    #pragma omp flush(lock[75][1])
                }

                xTPLe(pts[729], pts[732], A24minus[64], A24plus[64], 1);
                eval_3_isog_mod(pts[730], pts[733], coeff[62]);
                lock[76][0] = 0;
                while(lock[76][1]) {
                    #pragma omp flush(lock[76][1])
                }

                eval_3_isog_mod(pts[733], pts[736], coeff[63]);
                eval_3_isog_mod(pts[734], pts[737], coeff[21]);
                lock[77][0] = 0;
                while(lock[77][1]) {
                    #pragma omp flush(lock[77][1])
                }

                eval_3_isog_mod(pts[726], pts[740], coeff[64]);
                eval_3_isog_mod(pts[736], pts[742], coeff[64]);
                eval_3_isog_mod(pts[737], pts[743], coeff[22]);
                eval_3_isog_mod(pts[740], pts[745], coeff[65]);
                lock[78][0] = 0;
                while(lock[78][1]) {
                    #pragma omp flush(lock[78][1])
                }

                eval_3_isog_mod(pts[742], pts[747], coeff[65]);
                eval_3_isog_mod(pts[745], pts[749], coeff[66]);
                get_3_isog(pts[749], A24minus[68], A24plus[68], coeff[67]);
                eval_3_isog_mod(pts[747], pts[751], coeff[66]);
                lock[79][0] = 0;
                while(lock[79][1]) {
                    #pragma omp flush(lock[79][1])
                }

                eval_3_isog_mod(pts[750], pts[753], coeff[67]);
                get_3_isog(pts[753], A24minus[69], A24plus[69], coeff[68]);
                lock[80][0] = 0;
                while(lock[80][1]) {
                    #pragma omp flush(lock[80][1])
                }

                eval_3_isog_mod(pts[752], pts[755], coeff[25]);
                eval_3_isog_mod(pts[755], pts[757], coeff[26]);
                eval_3_isog_mod(pts[757], pts[759], coeff[27]);
                eval_3_isog_mod(pts[759], pts[761], coeff[28]);
                eval_3_isog_mod(pts[761], pts[763], coeff[29]);
                eval_3_isog_mod(pts[763], pts[765], coeff[30]);
                eval_3_isog_mod(pts[765], pts[767], coeff[31]);
                eval_3_isog_mod(pts[767], pts[769], coeff[32]);
                eval_3_isog_mod(pts[769], pts[771], coeff[33]);
                eval_3_isog_mod(pts[771], pts[773], coeff[34]);
                eval_3_isog_mod(pts[773], pts[775], coeff[35]);
                eval_3_isog_mod(pts[775], pts[777], coeff[36]);
                eval_3_isog_mod(pts[777], pts[779], coeff[37]);
                eval_3_isog_mod(pts[779], pts[781], coeff[38]);
                eval_3_isog_mod(pts[781], pts[783], coeff[39]);
                eval_3_isog_mod(pts[783], pts[785], coeff[40]);
                eval_3_isog_mod(pts[785], pts[787], coeff[41]);
                eval_3_isog_mod(pts[787], pts[789], coeff[42]);
                eval_3_isog_mod(pts[789], pts[791], coeff[43]);
                eval_3_isog_mod(pts[791], pts[793], coeff[44]);
                eval_3_isog_mod(pts[793], pts[795], coeff[45]);
                eval_3_isog_mod(pts[795], pts[797], coeff[46]);
                eval_3_isog_mod(pts[797], pts[799], coeff[47]);
                eval_3_isog_mod(pts[799], pts[801], coeff[48]);
                eval_3_isog_mod(pts[801], pts[803], coeff[49]);
                eval_3_isog_mod(pts[803], pts[805], coeff[50]);
                eval_3_isog_mod(pts[805], pts[807], coeff[51]);
                lock[81][0] = 0;
                while(lock[81][1]) {
                    #pragma omp flush(lock[81][1])
                }

                eval_3_isog_mod(pts[800], pts[810], coeff[69]);
                eval_3_isog_mod(pts[798], pts[811], coeff[69]);
                eval_3_isog_mod(pts[807], pts[813], coeff[52]);
                lock[82][0] = 0;
                while(lock[82][1]) {
                    #pragma omp flush(lock[82][1])
                }

                eval_3_isog_mod(pts[810], pts[815], coeff[70]);
                eval_3_isog_mod(pts[788], pts[818], coeff[69]);
                eval_3_isog_mod(pts[815], pts[820], coeff[71]);
                get_3_isog(pts[820], A24minus[73], A24plus[73], coeff[72]);
                lock[83][0] = 0;
                while(lock[83][1]) {
                    #pragma omp flush(lock[83][1])
                }

                eval_3_isog_mod(pts[817], pts[822], coeff[71]);
                eval_3_isog_mod(pts[819], pts[824], coeff[54]);
                eval_3_isog_mod(pts[822], pts[826], coeff[72]);
                eval_3_isog_mod(pts[780], pts[828], coeff[69]);
                lock[84][0] = 0;
                while(lock[84][1]) {
                    #pragma omp flush(lock[84][1])
                }

                eval_3_isog_mod(pts[826], pts[830], coeff[73]);
                eval_3_isog_mod(pts[827], pts[831], coeff[72]);
                xTPLe(pts[830], pts[834], A24minus[74], A24plus[74], 1);
                get_3_isog(pts[834], A24minus[75], A24plus[75], coeff[74]);
                eval_3_isog_mod(pts[831], pts[835], coeff[73]);
                eval_3_isog_mod(pts[830], pts[838], coeff[74]);
                get_3_isog(pts[838], A24minus[76], A24plus[76], coeff[75]);
                eval_3_isog_mod(pts[835], pts[839], coeff[74]);
                eval_3_isog_mod(pts[770], pts[841], coeff[69]);
                eval_3_isog_mod(pts[839], pts[843], coeff[75]);
                eval_3_isog_mod(pts[841], pts[845], coeff[70]);
                lock[85][0] = 0;
                while(lock[85][1]) {
                    #pragma omp flush(lock[85][1])
                }

                xTPLe(pts[843], pts[847], A24minus[76], A24plus[76], 1);
                eval_3_isog_mod(pts[845], pts[849], coeff[71]);
                xTPLe(pts[847], pts[851], A24minus[76], A24plus[76], 1);
                get_3_isog(pts[851], A24minus[77], A24plus[77], coeff[76]);
                eval_3_isog_mod(pts[849], pts[853], coeff[72]);
                lock[86][0] = 0;
                while(lock[86][1]) {
                    #pragma omp flush(lock[86][1])
                }

                eval_3_isog_mod(pts[843], pts[856], coeff[76]);
                eval_3_isog_mod(pts[852], pts[857], coeff[76]);
                eval_3_isog_mod(pts[854], pts[860], coeff[62]);
                lock[87][0] = 0;
                while(lock[87][1]) {
                    #pragma omp flush(lock[87][1])
                }

                eval_3_isog_mod(pts[856], pts[861], coeff[77]);
                get_3_isog(pts[861], A24minus[79], A24plus[79], coeff[78]);
                eval_3_isog_mod(pts[858], pts[863], coeff[74]);
                lock[88][0] = 0;
                while(lock[88][1]) {
                    #pragma omp flush(lock[88][1])
                }

                eval_3_isog_mod(pts[860], pts[865], coeff[63]);
                eval_3_isog_mod(pts[863], pts[867], coeff[75]);
                eval_3_isog_mod(pts[865], pts[869], coeff[64]);
                eval_3_isog_mod(pts[867], pts[872], coeff[76]);
                eval_3_isog_mod(pts[869], pts[874], coeff[65]);
                lock[89][0] = 0;
                while(lock[89][1]) {
                    #pragma omp flush(lock[89][1])
                }

                xTPLe(pts[871], pts[876], A24minus[79], A24plus[79], 1);
                eval_3_isog_mod(pts[873], pts[878], coeff[73]);
                eval_3_isog_mod(pts[874], pts[879], coeff[66]);
                xTPLe(pts[876], pts[881], A24minus[79], A24plus[79], 1);
                get_3_isog(pts[881], A24minus[80], A24plus[80], coeff[79]);
                lock[90][0] = 0;
                while(lock[90][1]) {
                    #pragma omp flush(lock[90][1])
                }

                eval_3_isog_mod(pts[879], pts[884], coeff[67]);
                eval_3_isog_mod(pts[876], pts[886], coeff[79]);
                get_3_isog(pts[886], A24minus[81], A24plus[81], coeff[80]);
                eval_3_isog_mod(pts[871], pts[887], coeff[79]);
                eval_3_isog_mod(pts[882], pts[889], coeff[79]);
                eval_3_isog_mod(pts[884], pts[891], coeff[68]);
                lock[91][0] = 0;
                while(lock[91][1]) {
                    #pragma omp flush(lock[91][1])
                }

                eval_3_isog_mod(pts[888], pts[894], coeff[80]);
                eval_3_isog_mod(pts[889], pts[895], coeff[80]);
                eval_3_isog_mod(pts[892], pts[898], coeff[5]);
                lock[92][0] = 0;
                while(lock[92][1]) {
                    #pragma omp flush(lock[92][1])
                }

                eval_3_isog_mod(pts[895], pts[900], coeff[81]);
                eval_3_isog_mod(pts[896], pts[901], coeff[77]);
                lock[93][0] = 0;
                while(lock[93][1]) {
                    #pragma omp flush(lock[93][1])
                }

                eval_3_isog_mod(pts[898], pts[903], coeff[6]);
                eval_3_isog_mod(pts[902], pts[906], coeff[71]);
                eval_3_isog_mod(pts[903], pts[907], coeff[7]);
                eval_3_isog_mod(pts[906], pts[910], coeff[72]);
                eval_3_isog_mod(pts[907], pts[911], coeff[8]);
                eval_3_isog_mod(pts[910], pts[914], coeff[73]);
                eval_3_isog_mod(pts[911], pts[915], coeff[9]);
                eval_3_isog_mod(pts[914], pts[918], coeff[74]);
                eval_3_isog_mod(pts[915], pts[919], coeff[10]);
                eval_3_isog_mod(pts[918], pts[922], coeff[75]);
                eval_3_isog_mod(pts[919], pts[923], coeff[11]);
                lock[94][0] = 0;
                while(lock[94][1]) {
                    #pragma omp flush(lock[94][1])
                }

                eval_3_isog_mod(pts[912], pts[925], coeff[83]);
                eval_3_isog_mod(pts[904], pts[927], coeff[83]);
                eval_3_isog_mod(pts[922], pts[929], coeff[76]);
                eval_3_isog_mod(pts[925], pts[931], coeff[84]);
                get_3_isog(pts[931], A24minus[86], A24plus[86], coeff[85]);
                eval_3_isog_mod(pts[927], pts[933], coeff[84]);
                eval_3_isog_mod(pts[929], pts[935], coeff[77]);
                lock[95][0] = 0;
                while(lock[95][1]) {
                    #pragma omp flush(lock[95][1])
                }

                eval_3_isog_mod(pts[932], pts[937], coeff[85]);
                get_3_isog(pts[937], A24minus[87], A24plus[87], coeff[86]);
                eval_3_isog_mod(pts[934], pts[939], coeff[85]);
                lock[96][0] = 0;
                while(lock[96][1]) {
                    #pragma omp flush(lock[96][1])
                }

                eval_3_isog_mod(pts[936], pts[941], coeff[14]);
                eval_3_isog_mod(pts[939], pts[943], coeff[86]);
                lock[97][0] = 0;
                while(lock[97][1]) {
                    #pragma omp flush(lock[97][1])
                }

                eval_3_isog_mod(pts[943], pts[946], coeff[87]);
                eval_3_isog_mod(pts[944], pts[947], coeff[80]);
                lock[98][0] = 0;
                while(lock[98][1]) {
                    #pragma omp flush(lock[98][1])
                }

                xTPLe(pts[946], pts[949], A24minus[88], A24plus[88], 1);
                xTPLe(pts[949], pts[952], A24minus[88], A24plus[88], 1);
                lock[99][0] = 0;
                while(lock[99][1]) {
                    #pragma omp flush(lock[99][1])
                }

                eval_3_isog_mod(pts[950], pts[953], coeff[82]);
                eval_3_isog_mod(pts[953], pts[956], coeff[83]);
                lock[100][0] = 0;
                while(lock[100][1]) {
                    #pragma omp flush(lock[100][1])
                }

                xTPLe(pts[955], pts[958], A24minus[88], A24plus[88], 1);
                eval_3_isog_mod(pts[956], pts[959], coeff[84]);
                lock[101][0] = 0;
                while(lock[101][1]) {
                    #pragma omp flush(lock[101][1])
                }

                eval_3_isog_mod(pts[959], pts[962], coeff[85]);
                eval_3_isog_mod(pts[960], pts[963], coeff[21]);
                lock[102][0] = 0;
                while(lock[102][1]) {
                    #pragma omp flush(lock[102][1])
                }

                eval_3_isog_mod(pts[963], pts[966], coeff[22]);
                eval_3_isog_mod(pts[958], pts[968], coeff[88]);
                eval_3_isog_mod(pts[952], pts[970], coeff[88]);
                eval_3_isog_mod(pts[946], pts[971], coeff[88]);
                lock[103][0] = 0;
                while(lock[103][1]) {
                    #pragma omp flush(lock[103][1])
                }

                eval_3_isog_mod(pts[968], pts[974], coeff[89]);
                get_3_isog(pts[974], A24minus[91], A24plus[91], coeff[90]);
                eval_3_isog_mod(pts[969], pts[975], coeff[89]);
                eval_3_isog_mod(pts[971], pts[977], coeff[89]);
                eval_3_isog_mod(pts[975], pts[980], coeff[90]);
                get_3_isog(pts[980], A24minus[92], A24plus[92], coeff[91]);
                lock[104][0] = 0;
                while(lock[104][1]) {
                    #pragma omp flush(lock[104][1])
                }

                eval_3_isog_mod(pts[977], pts[982], coeff[90]);
                eval_3_isog_mod(pts[978], pts[983], coeff[89]);
                eval_3_isog_mod(pts[982], pts[986], coeff[91]);
                eval_3_isog_mod(pts[983], pts[987], coeff[90]);
                lock[105][0] = 0;
                while(lock[105][1]) {
                    #pragma omp flush(lock[105][1])
                }

                eval_3_isog_mod(pts[987], pts[990], coeff[91]);
                eval_3_isog_mod(pts[988], pts[991], coeff[27]);
                lock[106][0] = 0;
                while(lock[106][1]) {
                    #pragma omp flush(lock[106][1])
                }

                eval_3_isog_mod(pts[990], pts[993], coeff[92]);
                eval_3_isog_mod(pts[993], pts[996], coeff[93]);
                lock[107][0] = 0;
                while(lock[107][1]) {
                    #pragma omp flush(lock[107][1])
                }

                eval_3_isog_mod(pts[996], pts[998], coeff[94]);
                xTPLe(pts[998], pts[1000], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1000], pts[1002], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1002], pts[1004], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1004], pts[1006], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1006], pts[1008], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1008], pts[1010], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1010], pts[1012], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1012], pts[1014], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1014], pts[1016], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1016], pts[1018], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1018], pts[1020], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1020], pts[1022], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1022], pts[1024], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1024], pts[1026], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1026], pts[1028], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1028], pts[1030], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1030], pts[1032], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1032], pts[1034], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1034], pts[1036], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1036], pts[1038], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1038], pts[1040], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1040], pts[1042], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1042], pts[1044], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1044], pts[1046], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1046], pts[1048], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1048], pts[1050], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1050], pts[1052], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1052], pts[1054], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1054], pts[1056], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1056], pts[1058], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1058], pts[1060], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1060], pts[1062], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1062], pts[1064], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1064], pts[1066], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1066], pts[1068], A24minus[95], A24plus[95], 1);
                get_3_isog(pts[1068], A24minus[96], A24plus[96], coeff[95]);
                eval_3_isog_mod(pts[1066], pts[1070], coeff[95]);
                get_3_isog(pts[1070], A24minus[97], A24plus[97], coeff[96]);
                lock[108][0] = 0;
                while(lock[108][1]) {
                    #pragma omp flush(lock[108][1])
                }

                eval_3_isog_mod(pts[1064], pts[1071], coeff[95]);
                eval_3_isog_mod(pts[1056], pts[1074], coeff[95]);
                eval_3_isog_mod(pts[1071], pts[1076], coeff[96]);
                get_3_isog(pts[1076], A24minus[98], A24plus[98], coeff[97]);
                lock[109][0] = 0;
                while(lock[109][1]) {
                    #pragma omp flush(lock[109][1])
                }

                eval_3_isog_mod(pts[1073], pts[1078], coeff[96]);
                eval_3_isog_mod(pts[1074], pts[1079], coeff[96]);
                eval_3_isog_mod(pts[1075], pts[1081], coeff[67]);
                lock[110][0] = 0;
                while(lock[110][1]) {
                    #pragma omp flush(lock[110][1])
                }

                eval_3_isog_mod(pts[1078], pts[1083], coeff[97]);
                eval_3_isog_mod(pts[1080], pts[1085], coeff[96]);
                eval_3_isog_mod(pts[1083], pts[1087], coeff[98]);
                get_3_isog(pts[1087], A24minus[100], A24plus[100], coeff[99]);
                eval_3_isog_mod(pts[1085], pts[1089], coeff[97]);
                lock[111][0] = 0;
                while(lock[111][1]) {
                    #pragma omp flush(lock[111][1])
                }

                eval_3_isog_mod(pts[1088], pts[1092], coeff[99]);
                eval_3_isog_mod(pts[1089], pts[1093], coeff[98]);
                xTPLe(pts[1092], pts[1096], A24minus[100], A24plus[100], 1);
                get_3_isog(pts[1096], A24minus[101], A24plus[101], coeff[100]);
                eval_3_isog_mod(pts[1093], pts[1097], coeff[99]);
                eval_3_isog_mod(pts[1092], pts[1100], coeff[100]);
                get_3_isog(pts[1100], A24minus[102], A24plus[102], coeff[101]);
                eval_3_isog_mod(pts[1097], pts[1101], coeff[100]);
                eval_3_isog_mod(pts[1032], pts[1103], coeff[95]);
                eval_3_isog_mod(pts[1101], pts[1105], coeff[101]);
                eval_3_isog_mod(pts[1103], pts[1107], coeff[96]);
                lock[112][0] = 0;
                while(lock[112][1]) {
                    #pragma omp flush(lock[112][1])
                }

                eval_3_isog_mod(pts[1106], pts[1110], coeff[100]);
                eval_3_isog_mod(pts[1108], pts[1112], coeff[74]);
                eval_3_isog_mod(pts[1110], pts[1114], coeff[101]);
                eval_3_isog_mod(pts[1112], pts[1116], coeff[75]);
                lock[113][0] = 0;
                while(lock[113][1]) {
                    #pragma omp flush(lock[113][1])
                }

                eval_3_isog_mod(pts[1105], pts[1118], coeff[102]);
                eval_3_isog_mod(pts[1115], pts[1120], coeff[99]);
                eval_3_isog_mod(pts[1116], pts[1122], coeff[76]);
                lock[114][0] = 0;
                while(lock[114][1]) {
                    #pragma omp flush(lock[114][1])
                }

                eval_3_isog_mod(pts[1119], pts[1124], coeff[103]);
                eval_3_isog_mod(pts[1121], pts[1126], coeff[96]);
                lock[115][0] = 0;
                while(lock[115][1]) {
                    #pragma omp flush(lock[115][1])
                }

                eval_3_isog_mod(pts[1124], pts[1128], coeff[104]);
                eval_3_isog_mod(pts[1125], pts[1129], coeff[101]);
                xTPLe(pts[1128], pts[1132], A24minus[105], A24plus[105], 1);
                eval_3_isog_mod(pts[1129], pts[1133], coeff[102]);
                xTPLe(pts[1132], pts[1136], A24minus[105], A24plus[105], 1);
                eval_3_isog_mod(pts[1133], pts[1137], coeff[103]);
                xTPLe(pts[1136], pts[1140], A24minus[105], A24plus[105], 1);
                get_3_isog(pts[1140], A24minus[106], A24plus[106], coeff[105]);
                eval_3_isog_mod(pts[1137], pts[1141], coeff[104]);
                eval_3_isog_mod(pts[1136], pts[1144], coeff[105]);
                get_3_isog(pts[1144], A24minus[107], A24plus[107], coeff[106]);
                lock[116][0] = 0;
                while(lock[116][1]) {
                    #pragma omp flush(lock[116][1])
                }

                eval_3_isog_mod(pts[1132], pts[1145], coeff[105]);
                eval_3_isog_mod(pts[1142], pts[1148], coeff[101]);
                eval_3_isog_mod(pts[1145], pts[1150], coeff[106]);
                get_3_isog(pts[1150], A24minus[108], A24plus[108], coeff[107]);
                lock[117][0] = 0;
                while(lock[117][1]) {
                    #pragma omp flush(lock[117][1])
                }

                eval_3_isog_mod(pts[1146], pts[1151], coeff[106]);
                eval_3_isog_mod(pts[1148], pts[1153], coeff[102]);
                eval_3_isog_mod(pts[1151], pts[1156], coeff[107]);
                get_3_isog(pts[1156], A24minus[109], A24plus[109], coeff[108]);
                eval_3_isog_mod(pts[1153], pts[1158], coeff[103]);
                lock[118][0] = 0;
                while(lock[118][1]) {
                    #pragma omp flush(lock[118][1])
                }

                eval_3_isog_mod(pts[1155], pts[1160], coeff[84]);
                eval_3_isog_mod(pts[1157], pts[1161], coeff[108]);
                eval_3_isog_mod(pts[1160], pts[1164], coeff[85]);
                xTPLe(pts[1161], pts[1165], A24minus[109], A24plus[109], 1);
                eval_3_isog_mod(pts[1164], pts[1168], coeff[86]);
                xTPLe(pts[1165], pts[1169], A24minus[109], A24plus[109], 1);
                eval_3_isog_mod(pts[1168], pts[1172], coeff[87]);
                xTPLe(pts[1169], pts[1173], A24minus[109], A24plus[109], 1);
                eval_3_isog_mod(pts[1172], pts[1176], coeff[88]);
                xTPLe(pts[1173], pts[1177], A24minus[109], A24plus[109], 1);
                get_3_isog(pts[1177], A24minus[110], A24plus[110], coeff[109]);
                eval_3_isog_mod(pts[1176], pts[1180], coeff[89]);
                lock[119][0] = 0;
                while(lock[119][1]) {
                    #pragma omp flush(lock[119][1])
                }

                eval_3_isog_mod(pts[1169], pts[1182], coeff[109]);
                eval_3_isog_mod(pts[1161], pts[1184], coeff[109]);
                eval_3_isog_mod(pts[1179], pts[1186], coeff[102]);
                lock[120][0] = 0;
                while(lock[120][1]) {
                    #pragma omp flush(lock[120][1])
                }

                eval_3_isog_mod(pts[1182], pts[1188], coeff[110]);
                get_3_isog(pts[1188], A24minus[112], A24plus[112], coeff[111]);
                eval_3_isog_mod(pts[1184], pts[1190], coeff[110]);
                eval_3_isog_mod(pts[1186], pts[1192], coeff[103]);
                lock[121][0] = 0;
                while(lock[121][1]) {
                    #pragma omp flush(lock[121][1])
                }

                eval_3_isog_mod(pts[1187], pts[1193], coeff[91]);
                eval_3_isog_mod(pts[1191], pts[1196], coeff[111]);
                eval_3_isog_mod(pts[1193], pts[1198], coeff[92]);
                lock[122][0] = 0;
                while(lock[122][1]) {
                    #pragma omp flush(lock[122][1])
                }

                eval_3_isog_mod(pts[1195], pts[1199], coeff[112]);
                get_3_isog(pts[1199], A24minus[114], A24plus[114], coeff[113]);
                eval_3_isog_mod(pts[1197], pts[1201], coeff[105]);
                lock[123][0] = 0;
                while(lock[123][1]) {
                    #pragma omp flush(lock[123][1])
                }

                eval_3_isog_mod(pts[1200], pts[1203], coeff[113]);
                xTPLe(pts[1203], pts[1206], A24minus[114], A24plus[114], 1);
                lock[124][0] = 0;
                while(lock[124][1]) {
                    #pragma omp flush(lock[124][1])
                }

                eval_3_isog_mod(pts[1205], pts[1208], coeff[95]);
                xTPLe(pts[1206], pts[1209], A24minus[114], A24plus[114], 1);
                lock[125][0] = 0;
                while(lock[125][1]) {
                    #pragma omp flush(lock[125][1])
                }

                xTPLe(pts[1209], pts[1212], A24minus[114], A24plus[114], 1);
                eval_3_isog_mod(pts[1210], pts[1213], coeff[109]);
                xTPLe(pts[1212], pts[1216], A24minus[114], A24plus[114], 1);
                eval_3_isog_mod(pts[1213], pts[1217], coeff[110]);
                xTPLe(pts[1216], pts[1220], A24minus[114], A24plus[114], 1);
                eval_3_isog_mod(pts[1217], pts[1221], coeff[111]);
                xTPLe(pts[1220], pts[1224], A24minus[114], A24plus[114], 1);
                get_3_isog(pts[1224], A24minus[115], A24plus[115], coeff[114]);
                eval_3_isog_mod(pts[1221], pts[1225], coeff[112]);
                eval_3_isog_mod(pts[1220], pts[1228], coeff[114]);
                get_3_isog(pts[1228], A24minus[116], A24plus[116], coeff[115]);
                lock[126][0] = 0;
                while(lock[126][1]) {
                    #pragma omp flush(lock[126][1])
                }

                eval_3_isog_mod(pts[1212], pts[1230], coeff[114]);
                eval_3_isog_mod(pts[1209], pts[1231], coeff[114]);
                eval_3_isog_mod(pts[1226], pts[1234], coeff[101]);
                eval_3_isog_mod(pts[1227], pts[1235], coeff[4]);
                lock[127][0] = 0;
                while(lock[127][1]) {
                    #pragma omp flush(lock[127][1])
                }

                eval_3_isog_mod(pts[1231], pts[1238], coeff[115]);
                eval_3_isog_mod(pts[1233], pts[1240], coeff[114]);
                eval_3_isog_mod(pts[1234], pts[1241], coeff[102]);
                eval_3_isog_mod(pts[1238], pts[1244], coeff[116]);
                eval_3_isog_mod(pts[1240], pts[1246], coeff[115]);
                eval_3_isog_mod(pts[1241], pts[1247], coeff[103]);
                lock[128][0] = 0;
                while(lock[128][1]) {
                    #pragma omp flush(lock[128][1])
                }

                eval_3_isog_mod(pts[1244], pts[1249], coeff[117]);
                get_3_isog(pts[1249], A24minus[119], A24plus[119], coeff[118]);
                eval_3_isog_mod(pts[1247], pts[1252], coeff[104]);
                lock[129][0] = 0;
                while(lock[129][1]) {
                    #pragma omp flush(lock[129][1])
                }

                eval_3_isog_mod(pts[1248], pts[1253], coeff[7]);
                eval_3_isog_mod(pts[1251], pts[1255], coeff[117]);
                eval_3_isog_mod(pts[1253], pts[1257], coeff[8]);
                eval_3_isog_mod(pts[1255], pts[1259], coeff[118]);
                eval_3_isog_mod(pts[1257], pts[1261], coeff[9]);
                lock[130][0] = 0;
                while(lock[130][1]) {
                    #pragma omp flush(lock[130][1])
                }

                eval_3_isog_mod(pts[1260], pts[1264], coeff[107]);
                eval_3_isog_mod(pts[1261], pts[1265], coeff[10]);
                lock[131][0] = 0;
                while(lock[131][1]) {
                    #pragma omp flush(lock[131][1])
                }

                eval_3_isog_mod(pts[1265], pts[1268], coeff[11]);
                xTPLe(pts[1266], pts[1269], A24minus[121], A24plus[121], 1);
                lock[132][0] = 0;
                while(lock[132][1]) {
                    #pragma omp flush(lock[132][1])
                }

                eval_3_isog_mod(pts[1268], pts[1271], coeff[12]);
                eval_3_isog_mod(pts[1271], pts[1274], coeff[13]);
                lock[133][0] = 0;
                while(lock[133][1]) {
                    #pragma omp flush(lock[133][1])
                }

                eval_3_isog_mod(pts[1273], pts[1276], coeff[111]);
                eval_3_isog_mod(pts[1274], pts[1277], coeff[14]);
                lock[134][0] = 0;
                while(lock[134][1]) {
                    #pragma omp flush(lock[134][1])
                }

                eval_3_isog_mod(pts[1277], pts[1280], coeff[15]);
                xTPLe(pts[1278], pts[1281], A24minus[121], A24plus[121], 1);
                lock[135][0] = 0;
                while(lock[135][1]) {
                    #pragma omp flush(lock[135][1])
                }

                eval_3_isog_mod(pts[1280], pts[1283], coeff[16]);
                eval_3_isog_mod(pts[1283], pts[1286], coeff[17]);
                lock[136][0] = 0;
                while(lock[136][1]) {
                    #pragma omp flush(lock[136][1])
                }

                eval_3_isog_mod(pts[1285], pts[1288], coeff[115]);
                eval_3_isog_mod(pts[1286], pts[1289], coeff[18]);
                lock[137][0] = 0;
                while(lock[137][1]) {
                    #pragma omp flush(lock[137][1])
                }

                eval_3_isog_mod(pts[1288], pts[1291], coeff[116]);
                eval_3_isog_mod(pts[1291], pts[1294], coeff[117]);
                lock[138][0] = 0;
                while(lock[138][1]) {
                    #pragma omp flush(lock[138][1])
                }

                eval_3_isog_mod(pts[1290], pts[1296], coeff[121]);
                get_3_isog(pts[1296], A24minus[123], A24plus[123], coeff[122]);
                eval_3_isog_mod(pts[1287], pts[1297], coeff[121]);
                eval_3_isog_mod(pts[1275], pts[1300], coeff[121]);
                eval_3_isog_mod(pts[1294], pts[1301], coeff[118]);
                lock[139][0] = 0;
                while(lock[139][1]) {
                    #pragma omp flush(lock[139][1])
                }

                eval_3_isog_mod(pts[1297], pts[1303], coeff[122]);
                get_3_isog(pts[1303], A24minus[124], A24plus[124], coeff[123]);
                eval_3_isog_mod(pts[1300], pts[1306], coeff[122]);
                eval_3_isog_mod(pts[1301], pts[1308], coeff[119]);
                lock[140][0] = 0;
                while(lock[140][1]) {
                    #pragma omp flush(lock[140][1])
                }

                eval_3_isog_mod(pts[1302], pts[1309], coeff[22]);
                eval_3_isog_mod(pts[1305], pts[1311], coeff[123]);
                eval_3_isog_mod(pts[1307], pts[1313], coeff[122]);
                lock[141][0] = 0;
                while(lock[141][1]) {
                    #pragma omp flush(lock[141][1])
                }

                eval_3_isog_mod(pts[1311], pts[1316], coeff[124]);
                get_3_isog(pts[1316], A24minus[126], A24plus[126], coeff[125]);
                eval_3_isog_mod(pts[1312], pts[1317], coeff[124]);
                eval_3_isog_mod(pts[1314], pts[1319], coeff[121]);
                eval_3_isog_mod(pts[1317], pts[1321], coeff[125]);
                eval_3_isog_mod(pts[1319], pts[1323], coeff[122]);
                lock[142][0] = 0;
                while(lock[142][1]) {
                    #pragma omp flush(lock[142][1])
                }

                eval_3_isog_mod(pts[1322], pts[1326], coeff[125]);
                eval_3_isog_mod(pts[1324], pts[1328], coeff[26]);
                lock[143][0] = 0;
                while(lock[143][1]) {
                    #pragma omp flush(lock[143][1])
                }

                eval_3_isog_mod(pts[1326], pts[1330], coeff[126]);
                eval_3_isog_mod(pts[1328], pts[1332], coeff[27]);
                lock[144][0] = 0;
                while(lock[144][1]) {
                    #pragma omp flush(lock[144][1])
                }

                eval_3_isog_mod(pts[1330], pts[1333], coeff[127]);
                xTPLe(pts[1333], pts[1336], A24minus[128], A24plus[128], 1);
                lock[145][0] = 0;
                while(lock[145][1]) {
                    #pragma omp flush(lock[145][1])
                }

                eval_3_isog_mod(pts[1334], pts[1337], coeff[126]);
                eval_3_isog_mod(pts[1337], pts[1340], coeff[127]);
                lock[146][0] = 0;
                while(lock[146][1]) {
                    #pragma omp flush(lock[146][1])
                }

                eval_3_isog_mod(pts[1336], pts[1342], coeff[128]);
                get_3_isog(pts[1342], A24minus[130], A24plus[130], coeff[129]);
                eval_3_isog_mod(pts[1340], pts[1344], coeff[128]);
                lock[147][0] = 0;
                while(lock[147][1]) {
                    #pragma omp flush(lock[147][1])
                }

                eval_3_isog_mod(pts[1341], pts[1345], coeff[31]);
                eval_3_isog_mod(pts[1345], pts[1348], coeff[32]);
                eval_3_isog_mod(pts[1348], pts[1350], coeff[33]);
                eval_3_isog_mod(pts[1350], pts[1352], coeff[34]);
                eval_3_isog_mod(pts[1352], pts[1354], coeff[35]);
                eval_3_isog_mod(pts[1354], pts[1356], coeff[36]);
                eval_3_isog_mod(pts[1356], pts[1358], coeff[37]);
                eval_3_isog_mod(pts[1358], pts[1360], coeff[38]);
                eval_3_isog_mod(pts[1360], pts[1362], coeff[39]);
                eval_3_isog_mod(pts[1362], pts[1364], coeff[40]);
                eval_3_isog_mod(pts[1364], pts[1366], coeff[41]);
                eval_3_isog_mod(pts[1366], pts[1368], coeff[42]);
                eval_3_isog_mod(pts[1368], pts[1370], coeff[43]);
                eval_3_isog_mod(pts[1370], pts[1372], coeff[44]);
                eval_3_isog_mod(pts[1372], pts[1374], coeff[45]);
                eval_3_isog_mod(pts[1374], pts[1376], coeff[46]);
                eval_3_isog_mod(pts[1376], pts[1378], coeff[47]);
                eval_3_isog_mod(pts[1378], pts[1380], coeff[48]);
                eval_3_isog_mod(pts[1380], pts[1382], coeff[49]);
                eval_3_isog_mod(pts[1382], pts[1384], coeff[50]);
                eval_3_isog_mod(pts[1384], pts[1386], coeff[51]);
                eval_3_isog_mod(pts[1386], pts[1388], coeff[52]);
                eval_3_isog_mod(pts[1388], pts[1390], coeff[53]);
                eval_3_isog_mod(pts[1390], pts[1392], coeff[54]);
                eval_3_isog_mod(pts[1392], pts[1394], coeff[55]);
                eval_3_isog_mod(pts[1394], pts[1396], coeff[56]);
                eval_3_isog_mod(pts[1396], pts[1398], coeff[57]);
                eval_3_isog_mod(pts[1398], pts[1400], coeff[58]);
                eval_3_isog_mod(pts[1400], pts[1402], coeff[59]);
                eval_3_isog_mod(pts[1402], pts[1404], coeff[60]);
                eval_3_isog_mod(pts[1404], pts[1406], coeff[61]);
                eval_3_isog_mod(pts[1406], pts[1408], coeff[62]);
                eval_3_isog_mod(pts[1408], pts[1410], coeff[63]);
                eval_3_isog_mod(pts[1410], pts[1412], coeff[64]);
                eval_3_isog_mod(pts[1412], pts[1414], coeff[65]);
                eval_3_isog_mod(pts[1414], pts[1416], coeff[66]);
                eval_3_isog_mod(pts[1416], pts[1418], coeff[67]);
                eval_3_isog_mod(pts[1418], pts[1420], coeff[68]);
                eval_3_isog_mod(pts[1420], pts[1422], coeff[69]);
                eval_3_isog_mod(pts[1422], pts[1424], coeff[70]);
                eval_3_isog_mod(pts[1424], pts[1426], coeff[71]);
                eval_3_isog_mod(pts[1426], pts[1428], coeff[72]);
                eval_3_isog_mod(pts[1428], pts[1430], coeff[73]);
                eval_3_isog_mod(pts[1430], pts[1432], coeff[74]);
                eval_3_isog_mod(pts[1432], pts[1434], coeff[75]);
                eval_3_isog_mod(pts[1434], pts[1436], coeff[76]);
                eval_3_isog_mod(pts[1436], pts[1438], coeff[77]);
                eval_3_isog_mod(pts[1438], pts[1440], coeff[78]);
                eval_3_isog_mod(pts[1440], pts[1442], coeff[79]);
                eval_3_isog_mod(pts[1442], pts[1444], coeff[80]);
                eval_3_isog_mod(pts[1444], pts[1446], coeff[81]);
                eval_3_isog_mod(pts[1446], pts[1448], coeff[82]);
                lock[148][0] = 0;
                while(lock[148][1]) {
                    #pragma omp flush(lock[148][1])
                }

                eval_3_isog_mod(pts[1443], pts[1450], coeff[131]);
                eval_3_isog_mod(pts[1441], pts[1451], coeff[131]);
                eval_3_isog_mod(pts[1435], pts[1453], coeff[131]);
                lock[149][0] = 0;
                while(lock[149][1]) {
                    #pragma omp flush(lock[149][1])
                }

                eval_3_isog_mod(pts[1450], pts[1455], coeff[132]);
                get_3_isog(pts[1455], A24minus[134], A24plus[134], coeff[133]);
                eval_3_isog_mod(pts[1453], pts[1458], coeff[132]);
                eval_3_isog_mod(pts[1429], pts[1459], coeff[131]);
                lock[150][0] = 0;
                while(lock[150][1]) {
                    #pragma omp flush(lock[150][1])
                }

                eval_3_isog_mod(pts[1457], pts[1462], coeff[133]);
                eval_3_isog_mod(pts[1458], pts[1463], coeff[133]);
                lock[151][0] = 0;
                while(lock[151][1]) {
                    #pragma omp flush(lock[151][1])
                }

                eval_3_isog_mod(pts[1460], pts[1465], coeff[85]);
                eval_3_isog_mod(pts[1463], pts[1467], coeff[134]);
                eval_3_isog_mod(pts[1465], pts[1470], coeff[86]);
                lock[152][0] = 0;
                while(lock[152][1]) {
                    #pragma omp flush(lock[152][1])
                }

                eval_3_isog_mod(pts[1467], pts[1471], coeff[135]);
                eval_3_isog_mod(pts[1470], pts[1474], coeff[87]);
                xTPLe(pts[1471], pts[1475], A24minus[136], A24plus[136], 1);
                get_3_isog(pts[1475], A24minus[137], A24plus[137], coeff[136]);
                eval_3_isog_mod(pts[1474], pts[1478], coeff[88]);
                lock[153][0] = 0;
                while(lock[153][1]) {
                    #pragma omp flush(lock[153][1])
                }

                eval_3_isog_mod(pts[1476], pts[1480], coeff[136]);
                eval_3_isog_mod(pts[1477], pts[1481], coeff[134]);
                lock[154][0] = 0;
                while(lock[154][1]) {
                    #pragma omp flush(lock[154][1])
                }

                eval_3_isog_mod(pts[1478], pts[1483], coeff[89]);
                eval_3_isog_mod(pts[1482], pts[1486], coeff[132]);
                eval_3_isog_mod(pts[1483], pts[1487], coeff[90]);
                eval_3_isog_mod(pts[1486], pts[1490], coeff[133]);
                eval_3_isog_mod(pts[1487], pts[1491], coeff[91]);
                eval_3_isog_mod(pts[1490], pts[1494], coeff[134]);
                eval_3_isog_mod(pts[1491], pts[1495], coeff[92]);
                lock[155][0] = 0;
                while(lock[155][1]) {
                    #pragma omp flush(lock[155][1])
                }

                eval_3_isog_mod(pts[1484], pts[1497], coeff[138]);
                eval_3_isog_mod(pts[1494], pts[1499], coeff[135]);
                eval_3_isog_mod(pts[1497], pts[1502], coeff[139]);
                get_3_isog(pts[1502], A24minus[141], A24plus[141], coeff[140]);
                eval_3_isog_mod(pts[1499], pts[1504], coeff[136]);
                lock[156][0] = 0;
                while(lock[156][1]) {
                    #pragma omp flush(lock[156][1])
                }

                eval_3_isog_mod(pts[1500], pts[1505], coeff[132]);
                eval_3_isog_mod(pts[1503], pts[1507], coeff[140]);
                eval_3_isog_mod(pts[1505], pts[1509], coeff[133]);
                xTPLe(pts[1507], pts[1511], A24minus[141], A24plus[141], 1);
                eval_3_isog_mod(pts[1509], pts[1513], coeff[134]);
                xTPLe(pts[1511], pts[1515], A24minus[141], A24plus[141], 1);
                eval_3_isog_mod(pts[1513], pts[1517], coeff[135]);
                xTPLe(pts[1515], pts[1519], A24minus[141], A24plus[141], 1);
                get_3_isog(pts[1519], A24minus[142], A24plus[142], coeff[141]);
                eval_3_isog_mod(pts[1517], pts[1521], coeff[136]);
                lock[157][0] = 0;
                while(lock[157][1]) {
                    #pragma omp flush(lock[157][1])
                }

                eval_3_isog_mod(pts[1511], pts[1524], coeff[141]);
                eval_3_isog_mod(pts[1507], pts[1525], coeff[141]);
                eval_3_isog_mod(pts[1522], pts[1528], coeff[99]);
                lock[158][0] = 0;
                while(lock[158][1]) {
                    #pragma omp flush(lock[158][1])
                }

                eval_3_isog_mod(pts[1524], pts[1529], coeff[142]);
                get_3_isog(pts[1529], A24minus[144], A24plus[144], coeff[143]);
                eval_3_isog_mod(pts[1526], pts[1531], coeff[142]);
                eval_3_isog_mod(pts[1528], pts[1534], coeff[100]);
                lock[159][0] = 0;
                while(lock[159][1]) {
                    #pragma omp flush(lock[159][1])
                }

                eval_3_isog_mod(pts[1531], pts[1536], coeff[143]);
                eval_3_isog_mod(pts[1533], pts[1538], coeff[132]);
                lock[160][0] = 0;
                while(lock[160][1]) {
                    #pragma omp flush(lock[160][1])
                }

                eval_3_isog_mod(pts[1534], pts[1539], coeff[101]);
                eval_3_isog_mod(pts[1538], pts[1542], coeff[133]);
                eval_3_isog_mod(pts[1539], pts[1543], coeff[102]);
                eval_3_isog_mod(pts[1542], pts[1546], coeff[134]);
                eval_3_isog_mod(pts[1543], pts[1547], coeff[103]);
                eval_3_isog_mod(pts[1546], pts[1550], coeff[135]);
                eval_3_isog_mod(pts[1547], pts[1551], coeff[104]);
                eval_3_isog_mod(pts[1550], pts[1554], coeff[136]);
                eval_3_isog_mod(pts[1551], pts[1555], coeff[105]);
                eval_3_isog_mod(pts[1554], pts[1558], coeff[137]);
                eval_3_isog_mod(pts[1555], pts[1559], coeff[106]);
                lock[161][0] = 0;
                while(lock[161][1]) {
                    #pragma omp flush(lock[161][1])
                }

                eval_3_isog_mod(pts[1544], pts[1562], coeff[145]);
                eval_3_isog_mod(pts[1557], pts[1564], coeff[145]);
                eval_3_isog_mod(pts[1559], pts[1566], coeff[107]);
                eval_3_isog_mod(pts[1562], pts[1568], coeff[146]);
                eval_3_isog_mod(pts[1564], pts[1570], coeff[146]);
                eval_3_isog_mod(pts[1566], pts[1572], coeff[108]);
                lock[162][0] = 0;
                while(lock[162][1]) {
                    #pragma omp flush(lock[162][1])
                }

                eval_3_isog_mod(pts[1569], pts[1574], coeff[147]);
                eval_3_isog_mod(pts[1571], pts[1576], coeff[140]);
                lock[163][0] = 0;
                while(lock[163][1]) {
                    #pragma omp flush(lock[163][1])
                }

                eval_3_isog_mod(pts[1574], pts[1578], coeff[148]);
                get_3_isog(pts[1578], A24minus[150], A24plus[150], coeff[149]);
                eval_3_isog_mod(pts[1575], pts[1579], coeff[148]);
                eval_3_isog_mod(pts[1579], pts[1582], coeff[149]);
                lock[164][0] = 0;
                while(lock[164][1]) {
                    #pragma omp flush(lock[164][1])
                }

                eval_3_isog_mod(pts[1581], pts[1584], coeff[111]);
                xTPLe(pts[1582], pts[1585], A24minus[150], A24plus[150], 1);
                eval_3_isog_mod(pts[1584], pts[1588], coeff[112]);
                xTPLe(pts[1585], pts[1589], A24minus[150], A24plus[150], 1);
                eval_3_isog_mod(pts[1588], pts[1592], coeff[113]);
                xTPLe(pts[1589], pts[1593], A24minus[150], A24plus[150], 1);
                eval_3_isog_mod(pts[1592], pts[1596], coeff[114]);
                xTPLe(pts[1593], pts[1597], A24minus[150], A24plus[150], 1);
                eval_3_isog_mod(pts[1596], pts[1600], coeff[115]);
                xTPLe(pts[1597], pts[1601], A24minus[150], A24plus[150], 1);
                eval_3_isog_mod(pts[1600], pts[1604], coeff[116]);
                xTPLe(pts[1601], pts[1605], A24minus[150], A24plus[150], 1);
                get_3_isog(pts[1605], A24minus[151], A24plus[151], coeff[150]);
                eval_3_isog_mod(pts[1604], pts[1608], coeff[117]);
                lock[165][0] = 0;
                while(lock[165][1]) {
                    #pragma omp flush(lock[165][1])
                }

                eval_3_isog_mod(pts[1601], pts[1609], coeff[150]);
                get_3_isog(pts[1609], A24minus[152], A24plus[152], coeff[151]);
                eval_3_isog_mod(pts[1593], pts[1611], coeff[150]);
                eval_3_isog_mod(pts[1606], pts[1614], coeff[149]);
                eval_3_isog_mod(pts[1608], pts[1616], coeff[118]);
                lock[166][0] = 0;
                while(lock[166][1]) {
                    #pragma omp flush(lock[166][1])
                }

                eval_3_isog_mod(pts[1611], pts[1618], coeff[151]);
                eval_3_isog_mod(pts[1612], pts[1619], coeff[151]);
                eval_3_isog_mod(pts[1615], pts[1622], coeff[138]);
                lock[167][0] = 0;
                while(lock[167][1]) {
                    #pragma omp flush(lock[167][1])
                }

                eval_3_isog_mod(pts[1618], pts[1624], coeff[152]);
                get_3_isog(pts[1624], A24minus[154], A24plus[154], coeff[153]);
                eval_3_isog_mod(pts[1619], pts[1625], coeff[152]);
                eval_3_isog_mod(pts[1622], pts[1628], coeff[139]);
                eval_3_isog_mod(pts[1625], pts[1630], coeff[153]);
                get_3_isog(pts[1630], A24minus[155], A24plus[155], coeff[154]);
                lock[168][0] = 0;
                while(lock[168][1]) {
                    #pragma omp flush(lock[168][1])
                }

                eval_3_isog_mod(pts[1627], pts[1632], coeff[152]);
                eval_3_isog_mod(pts[1628], pts[1633], coeff[140]);
                eval_3_isog_mod(pts[1632], pts[1636], coeff[153]);
                eval_3_isog_mod(pts[1633], pts[1637], coeff[141]);
                eval_3_isog_mod(pts[1636], pts[1640], coeff[154]);
                eval_3_isog_mod(pts[1637], pts[1641], coeff[142]);
                lock[169][0] = 0;
                while(lock[169][1]) {
                    #pragma omp flush(lock[169][1])
                }

                eval_3_isog_mod(pts[1635], pts[1643], coeff[155]);
                get_3_isog(pts[1643], A24minus[157], A24plus[157], coeff[156]);
                eval_3_isog_mod(pts[1641], pts[1645], coeff[143]);
                lock[170][0] = 0;
                while(lock[170][1]) {
                    #pragma omp flush(lock[170][1])
                }

                eval_3_isog_mod(pts[1644], pts[1647], coeff[156]);
                xTPLe(pts[1647], pts[1650], A24minus[157], A24plus[157], 1);
                lock[171][0] = 0;
                while(lock[171][1]) {
                    #pragma omp flush(lock[171][1])
                }

                eval_3_isog_mod(pts[1649], pts[1652], coeff[126]);
                xTPLe(pts[1650], pts[1653], A24minus[157], A24plus[157], 1);
                lock[172][0] = 0;
                while(lock[172][1]) {
                    #pragma omp flush(lock[172][1])
                }

                eval_3_isog_mod(pts[1652], pts[1655], coeff[127]);
                eval_3_isog_mod(pts[1655], pts[1658], coeff[128]);
                lock[173][0] = 0;
                while(lock[173][1]) {
                    #pragma omp flush(lock[173][1])
                }

                xTPLe(pts[1656], pts[1659], A24minus[157], A24plus[157], 1);
                xTPLe(pts[1659], pts[1662], A24minus[157], A24plus[157], 1);
                lock[174][0] = 0;
                while(lock[174][1]) {
                    #pragma omp flush(lock[174][1])
                }

                eval_3_isog_mod(pts[1661], pts[1664], coeff[130]);
                xTPLe(pts[1662], pts[1665], A24minus[157], A24plus[157], 1);
                lock[175][0] = 0;
                while(lock[175][1]) {
                    #pragma omp flush(lock[175][1])
                }

                xTPLe(pts[1665], pts[1668], A24minus[157], A24plus[157], 1);
                eval_3_isog_mod(pts[1666], pts[1669], coeff[151]);
                lock[176][0] = 0;
                while(lock[176][1]) {
                    #pragma omp flush(lock[176][1])
                }

                xTPLe(pts[1668], pts[1671], A24minus[157], A24plus[157], 1);
                xTPLe(pts[1671], pts[1674], A24minus[157], A24plus[157], 1);
                get_3_isog(pts[1674], A24minus[158], A24plus[158], coeff[157]);
                lock[177][0] = 0;
                while(lock[177][1]) {
                    #pragma omp flush(lock[177][1])
                }

                eval_3_isog_mod(pts[1673], pts[1676], coeff[134]);
                eval_3_isog_mod(pts[1668], pts[1678], coeff[157]);
                eval_3_isog_mod(pts[1662], pts[1680], coeff[157]);
                eval_3_isog_mod(pts[1656], pts[1681], coeff[157]);
                lock[178][0] = 0;
                while(lock[178][1]) {
                    #pragma omp flush(lock[178][1])
                }

                eval_3_isog_mod(pts[1676], pts[1683], coeff[135]);
                eval_3_isog_mod(pts[1680], pts[1686], coeff[158]);
                eval_3_isog_mod(pts[1647], pts[1688], coeff[157]);
                eval_3_isog_mod(pts[1683], pts[1690], coeff[136]);
                lock[179][0] = 0;
                while(lock[179][1]) {
                    #pragma omp flush(lock[179][1])
                }

                eval_3_isog_mod(pts[1685], pts[1691], coeff[159]);
                get_3_isog(pts[1691], A24minus[161], A24plus[161], coeff[160]);
                eval_3_isog_mod(pts[1688], pts[1694], coeff[158]);
                eval_3_isog_mod(pts[1690], pts[1696], coeff[137]);
                lock[180][0] = 0;
                while(lock[180][1]) {
                    #pragma omp flush(lock[180][1])
                }

                eval_3_isog_mod(pts[1692], pts[1697], coeff[160]);
                get_3_isog(pts[1697], A24minus[162], A24plus[162], coeff[161]);
                eval_3_isog_mod(pts[1695], pts[1700], coeff[157]);
                lock[181][0] = 0;
                while(lock[181][1]) {
                    #pragma omp flush(lock[181][1])
                }

                eval_3_isog_mod(pts[1696], pts[1701], coeff[138]);
                eval_3_isog_mod(pts[1700], pts[1704], coeff[158]);
                eval_3_isog_mod(pts[1701], pts[1705], coeff[139]);
                eval_3_isog_mod(pts[1704], pts[1708], coeff[159]);
                eval_3_isog_mod(pts[1705], pts[1709], coeff[140]);
                eval_3_isog_mod(pts[1708], pts[1712], coeff[160]);
                eval_3_isog_mod(pts[1709], pts[1713], coeff[141]);
                lock[182][0] = 0;
                while(lock[182][1]) {
                    #pragma omp flush(lock[182][1])
                }

                eval_3_isog_mod(pts[1713], pts[1716], coeff[142]);
                xTPLe(pts[1714], pts[1717], A24minus[164], A24plus[164], 1);
                lock[183][0] = 0;
                while(lock[183][1]) {
                    #pragma omp flush(lock[183][1])
                }

                xTPLe(pts[1717], pts[1720], A24minus[164], A24plus[164], 1);
                get_3_isog(pts[1720], A24minus[165], A24plus[165], coeff[164]);
                eval_3_isog_mod(pts[1718], pts[1721], coeff[163]);
                lock[184][0] = 0;
                while(lock[184][1]) {
                    #pragma omp flush(lock[184][1])
                }

                eval_3_isog_mod(pts[1717], pts[1723], coeff[164]);
                get_3_isog(pts[1723], A24minus[166], A24plus[166], coeff[165]);
                eval_3_isog_mod(pts[1722], pts[1726], coeff[145]);
                lock[185][0] = 0;
                while(lock[185][1]) {
                    #pragma omp flush(lock[185][1])
                }

                eval_3_isog_mod(pts[1725], pts[1728], coeff[165]);
                lock[186][0] = 0;
                while(lock[186][1]) {
                    #pragma omp flush(lock[186][1])
                }

                eval_3_isog_mod(pts[1728], pts[1730], coeff[166]);
                xTPLe(pts[1730], pts[1732], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1732], pts[1734], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1734], pts[1736], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1736], pts[1738], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1738], pts[1740], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1740], pts[1742], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1742], pts[1744], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1744], pts[1746], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1746], pts[1748], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1748], pts[1750], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1750], pts[1752], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1752], pts[1754], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1754], pts[1756], A24minus[167], A24plus[167], 1);
                get_3_isog(pts[1756], A24minus[168], A24plus[168], coeff[167]);
                eval_3_isog_mod(pts[1754], pts[1758], coeff[167]);
                get_3_isog(pts[1758], A24minus[169], A24plus[169], coeff[168]);
                lock[187][0] = 0;
                while(lock[187][1]) {
                    #pragma omp flush(lock[187][1])
                }

                eval_3_isog_mod(pts[1750], pts[1760], coeff[167]);
                eval_3_isog_mod(pts[1748], pts[1761], coeff[167]);
                eval_3_isog_mod(pts[1757], pts[1763], coeff[161]);
                lock[188][0] = 0;
                while(lock[188][1]) {
                    #pragma omp flush(lock[188][1])
                }

                eval_3_isog_mod(pts[1760], pts[1765], coeff[168]);
                eval_3_isog_mod(pts[1762], pts[1767], coeff[168]);
                eval_3_isog_mod(pts[1765], pts[1770], coeff[169]);
                get_3_isog(pts[1770], A24minus[171], A24plus[171], coeff[170]);
                eval_3_isog_mod(pts[1767], pts[1772], coeff[169]);
                lock[189][0] = 0;
                while(lock[189][1]) {
                    #pragma omp flush(lock[189][1])
                }

                eval_3_isog_mod(pts[1768], pts[1773], coeff[168]);
                eval_3_isog_mod(pts[1772], pts[1776], coeff[170]);
                eval_3_isog_mod(pts[1773], pts[1777], coeff[169]);
                lock[190][0] = 0;
                while(lock[190][1]) {
                    #pragma omp flush(lock[190][1])
                }

                eval_3_isog_mod(pts[1774], pts[1779], coeff[164]);
                eval_3_isog_mod(pts[1778], pts[1782], coeff[168]);
                eval_3_isog_mod(pts[1779], pts[1783], coeff[165]);
                eval_3_isog_mod(pts[1782], pts[1786], coeff[169]);
                eval_3_isog_mod(pts[1783], pts[1787], coeff[166]);
                eval_3_isog_mod(pts[1786], pts[1790], coeff[170]);
                eval_3_isog_mod(pts[1787], pts[1791], coeff[167]);
                lock[191][0] = 0;
                while(lock[191][1]) {
                    #pragma omp flush(lock[191][1])
                }

                eval_3_isog_mod(pts[1791], pts[1794], coeff[168]);
                xTPLe(pts[1792], pts[1795], A24minus[174], A24plus[174], 1);
                lock[192][0] = 0;
                while(lock[192][1]) {
                    #pragma omp flush(lock[192][1])
                }

                xTPLe(pts[1795], pts[1798], A24minus[174], A24plus[174], 1);
                get_3_isog(pts[1798], A24minus[175], A24plus[175], coeff[174]);
                eval_3_isog_mod(pts[1796], pts[1799], coeff[173]);
                lock[193][0] = 0;
                while(lock[193][1]) {
                    #pragma omp flush(lock[193][1])
                }

                eval_3_isog_mod(pts[1795], pts[1801], coeff[174]);
                get_3_isog(pts[1801], A24minus[176], A24plus[176], coeff[175]);
                eval_3_isog_mod(pts[1799], pts[1803], coeff[174]);
                lock[194][0] = 0;
                while(lock[194][1]) {
                    #pragma omp flush(lock[194][1])
                }

                eval_3_isog_mod(pts[1803], pts[1806], coeff[175]);
                lock[195][0] = 0;
                while(lock[195][1]) {
                    #pragma omp flush(lock[195][1])
                }

                eval_3_isog_mod(pts[1806], pts[1808], coeff[176]);
                xTPLe(pts[1808], pts[1810], A24minus[177], A24plus[177], 1);
                xTPLe(pts[1810], pts[1812], A24minus[177], A24plus[177], 1);
                xTPLe(pts[1812], pts[1814], A24minus[177], A24plus[177], 1);
                get_3_isog(pts[1814], A24minus[178], A24plus[178], coeff[177]);
                eval_3_isog_mod(pts[1812], pts[1816], coeff[177]);
                get_3_isog(pts[1816], A24minus[179], A24plus[179], coeff[178]);
                lock[196][0] = 0;
                while(lock[196][1]) {
                    #pragma omp flush(lock[196][1])
                }

                eval_3_isog_mod(pts[1810], pts[1817], coeff[177]);
                eval_3_isog_mod(pts[1817], pts[1820], coeff[178]);
                get_3_isog(pts[1820], A24minus[180], A24plus[180], coeff[179]);
                lock[197][0] = 0;
                while(lock[197][1]) {
                    #pragma omp flush(lock[197][1])
                }

                eval_3_isog_mod(pts[1819], pts[1822], coeff[178]);
                eval_3_isog_mod(pts[1822], pts[1824], coeff[179]);
                lock[198][0] = 0;
                while(lock[198][1]) {
                    #pragma omp flush(lock[198][1])
                }

                eval_3_isog_mod(pts[1824], pts[1825], coeff[180]);
                xTPLe(pts[1825], pts[1826], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1826], pts[1827], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1827], pts[1828], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1828], pts[1829], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1829], pts[1830], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1830], pts[1831], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1831], pts[1832], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1832], pts[1833], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1833], pts[1834], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1834], pts[1835], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1835], pts[1836], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1836], pts[1837], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1837], pts[1838], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1838], pts[1839], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1839], pts[1840], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1840], pts[1841], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1841], pts[1842], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1842], pts[1843], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1843], pts[1844], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1844], pts[1845], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1845], pts[1846], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1846], pts[1847], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1847], pts[1848], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1848], pts[1849], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1849], pts[1850], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1850], pts[1851], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1851], pts[1852], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1852], pts[1853], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1853], pts[1854], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1854], pts[1855], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1855], pts[1856], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1856], pts[1857], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1857], pts[1858], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1858], pts[1859], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1859], pts[1860], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1860], pts[1861], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1861], pts[1862], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1862], pts[1863], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1863], pts[1864], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1864], pts[1865], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1865], pts[1866], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1866], pts[1867], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1867], pts[1868], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1868], pts[1869], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1869], pts[1870], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1870], pts[1871], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1871], pts[1872], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1872], pts[1873], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1873], pts[1874], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1874], pts[1875], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1875], pts[1876], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1876], pts[1877], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1877], pts[1878], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1878], pts[1879], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1879], pts[1880], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1880], pts[1881], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1881], pts[1882], A24minus[181], A24plus[181], 1);
                get_3_isog(pts[1882], A24minus[182], A24plus[182], coeff[181]);
                lock[199][0] = 0;
                while(lock[199][1]) {
                    #pragma omp flush(lock[199][1])
                }

                eval_3_isog_mod(pts[1880], pts[1884], coeff[181]);
                eval_3_isog_mod(pts[1878], pts[1886], coeff[181]);
                lock[200][0] = 0;
                while(lock[200][1]) {
                    #pragma omp flush(lock[200][1])
                }

                eval_3_isog_mod(pts[1876], pts[1887], coeff[181]);
                eval_3_isog_mod(pts[1885], pts[1889], coeff[182]);
                eval_3_isog_mod(pts[1887], pts[1891], coeff[182]);
                lock[201][0] = 0;
                while(lock[201][1]) {
                    #pragma omp flush(lock[201][1])
                }

                eval_3_isog_mod(pts[1889], pts[1893], coeff[183]);
                get_3_isog(pts[1893], A24minus[185], A24plus[185], coeff[184]);
                eval_3_isog_mod(pts[1891], pts[1895], coeff[183]);
                lock[202][0] = 0;
                while(lock[202][1]) {
                    #pragma omp flush(lock[202][1])
                }

                eval_3_isog_mod(pts[1895], pts[1898], coeff[184]);
                eval_3_isog_mod(pts[1896], pts[1899], coeff[183]);
                lock[203][0] = 0;
                while(lock[203][1]) {
                    #pragma omp flush(lock[203][1])
                }

                eval_3_isog_mod(pts[1898], pts[1901], coeff[185]);
                xTPLe(pts[1901], pts[1904], A24minus[186], A24plus[186], 1);
                get_3_isog(pts[1904], A24minus[187], A24plus[187], coeff[186]);
                lock[204][0] = 0;
                while(lock[204][1]) {
                    #pragma omp flush(lock[204][1])
                }

                eval_3_isog_mod(pts[1902], pts[1905], coeff[185]);
                eval_3_isog_mod(pts[1905], pts[1908], coeff[186]);
                eval_3_isog_mod(pts[1864], pts[1910], coeff[181]);
                lock[205][0] = 0;
                while(lock[205][1]) {
                    #pragma omp flush(lock[205][1])
                }

                eval_3_isog_mod(pts[1909], pts[1912], coeff[185]);
                eval_3_isog_mod(pts[1910], pts[1913], coeff[182]);
                lock[206][0] = 0;
                while(lock[206][1]) {
                    #pragma omp flush(lock[206][1])
                }

                eval_3_isog_mod(pts[1912], pts[1915], coeff[186]);
                eval_3_isog_mod(pts[1915], pts[1918], coeff[187]);
                lock[207][0] = 0;
                while(lock[207][1]) {
                    #pragma omp flush(lock[207][1])
                }

                eval_3_isog_mod(pts[1916], pts[1919], coeff[184]);
                eval_3_isog_mod(pts[1911], pts[1921], coeff[188]);
                eval_3_isog_mod(pts[1919], pts[1923], coeff[185]);
                lock[208][0] = 0;
                while(lock[208][1]) {
                    #pragma omp flush(lock[208][1])
                }

                eval_3_isog_mod(pts[1921], pts[1925], coeff[189]);
                get_3_isog(pts[1925], A24minus[191], A24plus[191], coeff[190]);
                eval_3_isog_mod(pts[1923], pts[1927], coeff[186]);
                lock[209][0] = 0;
                while(lock[209][1]) {
                    #pragma omp flush(lock[209][1])
                }

                eval_3_isog_mod(pts[1927], pts[1930], coeff[187]);
                eval_3_isog_mod(pts[1928], pts[1931], coeff[183]);
                lock[210][0] = 0;
                while(lock[210][1]) {
                    #pragma omp flush(lock[210][1])
                }

                eval_3_isog_mod(pts[1931], pts[1934], coeff[184]);
                xTPLe(pts[1932], pts[1935], A24minus[191], A24plus[191], 1);
                lock[211][0] = 0;
                while(lock[211][1]) {
                    #pragma omp flush(lock[211][1])
                }

                eval_3_isog_mod(pts[1934], pts[1937], coeff[185]);
                eval_3_isog_mod(pts[1937], pts[1940], coeff[186]);
                eval_3_isog_mod(pts[1848], pts[1941], coeff[181]);
                lock[212][0] = 0;
                while(lock[212][1]) {
                    #pragma omp flush(lock[212][1])
                }

                eval_3_isog_mod(pts[1929], pts[1944], coeff[191]);
                eval_3_isog_mod(pts[1940], pts[1946], coeff[187]);
                eval_3_isog_mod(pts[1941], pts[1947], coeff[182]);
                eval_3_isog_mod(pts[1944], pts[1949], coeff[192]);
                lock[213][0] = 0;
                while(lock[213][1]) {
                    #pragma omp flush(lock[213][1])
                }

                eval_3_isog_mod(pts[1946], pts[1951], coeff[188]);
                eval_3_isog_mod(pts[1950], pts[1954], coeff[193]);
                eval_3_isog_mod(pts[1951], pts[1955], coeff[189]);
                lock[214][0] = 0;
                while(lock[214][1]) {
                    #pragma omp flush(lock[214][1])
                }

                eval_3_isog_mod(pts[1954], pts[1957], coeff[194]);
                xTPLe(pts[1957], pts[1960], A24minus[195], A24plus[195], 1);
                lock[215][0] = 0;
                while(lock[215][1]) {
                    #pragma omp flush(lock[215][1])
                }

                eval_3_isog_mod(pts[1959], pts[1962], coeff[186]);
                xTPLe(pts[1960], pts[1963], A24minus[195], A24plus[195], 1);
                lock[216][0] = 0;
                while(lock[216][1]) {
                    #pragma omp flush(lock[216][1])
                }

                eval_3_isog_mod(pts[1962], pts[1965], coeff[187]);
                eval_3_isog_mod(pts[1965], pts[1968], coeff[188]);
                lock[217][0] = 0;
                while(lock[217][1]) {
                    #pragma omp flush(lock[217][1])
                }

                xTPLe(pts[1966], pts[1969], A24minus[195], A24plus[195], 1);
                get_3_isog(pts[1969], A24minus[196], A24plus[196], coeff[195]);
                lock[218][0] = 0;
                while(lock[218][1]) {
                    #pragma omp flush(lock[218][1])
                }

                eval_3_isog_mod(pts[1968], pts[1971], coeff[189]);
                eval_3_isog_mod(pts[1960], pts[1974], coeff[195]);
                eval_3_isog_mod(pts[1970], pts[1976], coeff[195]);
                eval_3_isog_mod(pts[1971], pts[1977], coeff[190]);
                lock[219][0] = 0;
                while(lock[219][1]) {
                    #pragma omp flush(lock[219][1])
                }

                eval_3_isog_mod(pts[1974], pts[1979], coeff[196]);
                eval_3_isog_mod(pts[1976], pts[1981], coeff[196]);
                eval_3_isog_mod(pts[1979], pts[1983], coeff[197]);
                get_3_isog(pts[1983], A24minus[199], A24plus[199], coeff[198]);
                eval_3_isog_mod(pts[1981], pts[1985], coeff[197]);
                lock[220][0] = 0;
                while(lock[220][1]) {
                    #pragma omp flush(lock[220][1])
                }

                eval_3_isog_mod(pts[1984], pts[1987], coeff[198]);
                get_3_isog(pts[1987], A24minus[200], A24plus[200], coeff[199]);
                eval_3_isog_mod(pts[1837], pts[1990], coeff[181]);
                lock[221][0] = 0;
                while(lock[221][1]) {
                    #pragma omp flush(lock[221][1])
                }

                eval_3_isog_mod(pts[1989], pts[1992], coeff[194]);
                eval_3_isog_mod(pts[1990], pts[1993], coeff[182]);
                lock[222][0] = 0;
                while(lock[222][1]) {
                    #pragma omp flush(lock[222][1])
                }

                eval_3_isog_mod(pts[1992], pts[1995], coeff[195]);
                eval_3_isog_mod(pts[1995], pts[1998], coeff[196]);
                lock[223][0] = 0;
                while(lock[223][1]) {
                    #pragma omp flush(lock[223][1])
                }

                eval_3_isog_mod(pts[1996], pts[1999], coeff[184]);
                eval_3_isog_mod(pts[1999], pts[2002], coeff[185]);
                lock[224][0] = 0;
                while(lock[224][1]) {
                    #pragma omp flush(lock[224][1])
                }

                eval_3_isog_mod(pts[2001], pts[2004], coeff[198]);
                eval_3_isog_mod(pts[2002], pts[2005], coeff[186]);
                lock[225][0] = 0;
                while(lock[225][1]) {
                    #pragma omp flush(lock[225][1])
                }

                eval_3_isog_mod(pts[2005], pts[2008], coeff[187]);
                eval_3_isog_mod(pts[2003], pts[2009], coeff[200]);
                get_3_isog(pts[2009], A24minus[202], A24plus[202], coeff[201]);
                eval_3_isog_mod(pts[1994], pts[2012], coeff[200]);
                eval_3_isog_mod(pts[1991], pts[2013], coeff[200]);
                lock[226][0] = 0;
                while(lock[226][1]) {
                    #pragma omp flush(lock[226][1])
                }

                eval_3_isog_mod(pts[2008], pts[2015], coeff[188]);
                eval_3_isog_mod(pts[2012], pts[2018], coeff[201]);
                eval_3_isog_mod(pts[2014], pts[2020], coeff[201]);
                eval_3_isog_mod(pts[2015], pts[2021], coeff[189]);
                lock[227][0] = 0;
                while(lock[227][1]) {
                    #pragma omp flush(lock[227][1])
                }

                eval_3_isog_mod(pts[2019], pts[2024], coeff[202]);
                eval_3_isog_mod(pts[2021], pts[2026], coeff[190]);
                eval_3_isog_mod(pts[2024], pts[2028], coeff[203]);
                eval_3_isog_mod(pts[2026], pts[2030], coeff[191]);
                lock[228][0] = 0;
                while(lock[228][1]) {
                    #pragma omp flush(lock[228][1])
                }

                eval_3_isog_mod(pts[2029], pts[2032], coeff[204]);
                lock[229][0] = 0;
                while(lock[229][1]) {
                    #pragma omp flush(lock[229][1])
                }

                eval_3_isog_mod(pts[2030], pts[2033], coeff[192]);
                eval_3_isog_mod(pts[2033], pts[2035], coeff[193]);
                eval_3_isog_mod(pts[2035], pts[2037], coeff[194]);
                eval_3_isog_mod(pts[2037], pts[2040], coeff[195]);
                lock[230][0] = 0;
                while(lock[230][1]) {
                    #pragma omp flush(lock[230][1])
                }

                eval_3_isog_mod(pts[2038], pts[2041], coeff[182]);
                eval_3_isog_mod(pts[2041], pts[2044], coeff[183]);
                lock[231][0] = 0;
                while(lock[231][1]) {
                    #pragma omp flush(lock[231][1])
                }

                eval_3_isog_mod(pts[2043], pts[2046], coeff[197]);
                eval_3_isog_mod(pts[2044], pts[2047], coeff[184]);
                lock[232][0] = 0;
                while(lock[232][1]) {
                    #pragma omp flush(lock[232][1])
                }

                eval_3_isog_mod(pts[2047], pts[2050], coeff[185]);
                xTPLe(pts[2048], pts[2051], A24minus[206], A24plus[206], 1);
                lock[233][0] = 0;
                while(lock[233][1]) {
                    #pragma omp flush(lock[233][1])
                }

                eval_3_isog_mod(pts[2050], pts[2053], coeff[186]);
                eval_3_isog_mod(pts[2053], pts[2056], coeff[187]);
                lock[234][0] = 0;
                while(lock[234][1]) {
                    #pragma omp flush(lock[234][1])
                }

                xTPLe(pts[2054], pts[2057], A24minus[206], A24plus[206], 1);
                xTPLe(pts[2057], pts[2060], A24minus[206], A24plus[206], 1);
                get_3_isog(pts[2060], A24minus[207], A24plus[207], coeff[206]);
                lock[235][0] = 0;
                while(lock[235][1]) {
                    #pragma omp flush(lock[235][1])
                }

                eval_3_isog_mod(pts[2058], pts[2061], coeff[202]);
                eval_3_isog_mod(pts[2057], pts[2063], coeff[206]);
                get_3_isog(pts[2063], A24minus[208], A24plus[208], coeff[207]);
                eval_3_isog_mod(pts[2048], pts[2066], coeff[206]);
                eval_3_isog_mod(pts[2061], pts[2068], coeff[203]);
                lock[236][0] = 0;
                while(lock[236][1]) {
                    #pragma omp flush(lock[236][1])
                }

                eval_3_isog_mod(pts[2062], pts[2069], coeff[190]);
                eval_3_isog_mod(pts[2065], pts[2071], coeff[207]);
                eval_3_isog_mod(pts[2034], pts[2074], coeff[206]);
                eval_3_isog_mod(pts[2069], pts[2076], coeff[191]);
                lock[237][0] = 0;
                while(lock[237][1]) {
                    #pragma omp flush(lock[237][1])
                }

                eval_3_isog_mod(pts[2072], pts[2078], coeff[208]);
                eval_3_isog_mod(pts[2073], pts[2079], coeff[208]);
                eval_3_isog_mod(pts[2076], pts[2082], coeff[192]);
                lock[238][0] = 0;
                while(lock[238][1]) {
                    #pragma omp flush(lock[238][1])
                }

                eval_3_isog_mod(pts[2079], pts[2084], coeff[209]);
                eval_3_isog_mod(pts[2080], pts[2085], coeff[208]);
                lock[239][0] = 0;
                while(lock[239][1]) {
                    #pragma omp flush(lock[239][1])
                }

                eval_3_isog_mod(pts[2084], pts[2088], coeff[210]);
                eval_3_isog_mod(pts[2085], pts[2089], coeff[209]);
                xTPLe(pts[2088], pts[2092], A24minus[211], A24plus[211], 1);
                get_3_isog(pts[2092], A24minus[212], A24plus[212], coeff[211]);
                eval_3_isog_mod(pts[2089], pts[2093], coeff[210]);
                eval_3_isog_mod(pts[2088], pts[2096], coeff[211]);
                get_3_isog(pts[2096], A24minus[213], A24plus[213], coeff[212]);
                eval_3_isog_mod(pts[2093], pts[2097], coeff[211]);
                eval_3_isog_mod(pts[2097], pts[2100], coeff[212]);
                lock[240][0] = 0;
                while(lock[240][1]) {
                    #pragma omp flush(lock[240][1])
                }

                eval_3_isog_mod(pts[2098], pts[2101], coeff[210]);
                eval_3_isog_mod(pts[2101], pts[2104], coeff[211]);
                lock[241][0] = 0;
                while(lock[241][1]) {
                    #pragma omp flush(lock[241][1])
                }

                xTPLe(pts[2103], pts[2106], A24minus[213], A24plus[213], 1);
                get_3_isog(pts[2106], A24minus[214], A24plus[214], coeff[213]);
                eval_3_isog_mod(pts[2104], pts[2107], coeff[212]);
                lock[242][0] = 0;
                while(lock[242][1]) {
                    #pragma omp flush(lock[242][1])
                }

                eval_3_isog_mod(pts[2100], pts[2110], coeff[213]);
                eval_3_isog_mod(pts[2107], pts[2111], coeff[213]);
                lock[243][0] = 0;
                while(lock[243][1]) {
                    #pragma omp flush(lock[243][1])
                }

                eval_3_isog_mod(pts[2110], pts[2113], coeff[214]);
                get_3_isog(pts[2113], A24minus[216], A24plus[216], coeff[215]);
                lock[244][0] = 0;
                while(lock[244][1]) {
                    #pragma omp flush(lock[244][1])
                }

                eval_3_isog_mod(pts[2114], pts[2116], coeff[215]);
                xTPLe(pts[2116], pts[2118], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2118], pts[2120], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2120], pts[2122], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2122], pts[2124], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2124], pts[2126], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2126], pts[2128], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2128], pts[2130], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2130], pts[2132], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2132], pts[2134], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2134], pts[2136], A24minus[216], A24plus[216], 1);
                get_3_isog(pts[2136], A24minus[217], A24plus[217], coeff[216]);
                eval_3_isog_mod(pts[2134], pts[2138], coeff[216]);
                get_3_isog(pts[2138], A24minus[218], A24plus[218], coeff[217]);
                lock[245][0] = 0;
                while(lock[245][1]) {
                    #pragma omp flush(lock[245][1])
                }

                eval_3_isog_mod(pts[2132], pts[2139], coeff[216]);
                eval_3_isog_mod(pts[2126], pts[2142], coeff[216]);
                eval_3_isog_mod(pts[2137], pts[2144], coeff[213]);
                eval_3_isog_mod(pts[2139], pts[2145], coeff[217]);
                get_3_isog(pts[2145], A24minus[219], A24plus[219], coeff[218]);
                eval_3_isog_mod(pts[2142], pts[2148], coeff[217]);
                eval_3_isog_mod(pts[2116], pts[2150], coeff[216]);
                lock[246][0] = 0;
                while(lock[246][1]) {
                    #pragma omp flush(lock[246][1])
                }

                eval_3_isog_mod(pts[2146], pts[2152], coeff[218]);
                get_3_isog(pts[2152], A24minus[220], A24plus[220], coeff[219]);
                eval_3_isog_mod(pts[2148], pts[2154], coeff[218]);
                eval_3_isog_mod(pts[2150], pts[2156], coeff[217]);
                lock[247][0] = 0;
                while(lock[247][1]) {
                    #pragma omp flush(lock[247][1])
                }

                eval_3_isog_mod(pts[2151], pts[2157], coeff[215]);
                eval_3_isog_mod(pts[2155], pts[2160], coeff[219]);
                eval_3_isog_mod(pts[2157], pts[2162], coeff[216]);
                lock[248][0] = 0;
                while(lock[248][1]) {
                    #pragma omp flush(lock[248][1])
                }

                eval_3_isog_mod(pts[2159], pts[2163], coeff[220]);
                get_3_isog(pts[2163], A24minus[222], A24plus[222], coeff[221]);
                eval_3_isog_mod(pts[2161], pts[2165], coeff[219]);
                lock[249][0] = 0;
                while(lock[249][1]) {
                    #pragma omp flush(lock[249][1])
                }

                eval_3_isog_mod(pts[2164], pts[2167], coeff[221]);
                xTPLe(pts[2167], pts[2170], A24minus[222], A24plus[222], 1);
                get_3_isog(pts[2170], A24minus[223], A24plus[223], coeff[222]);
                lock[250][0] = 0;
                while(lock[250][1]) {
                    #pragma omp flush(lock[250][1])
                }

                eval_3_isog_mod(pts[2169], pts[2172], coeff[219]);
                eval_3_isog_mod(pts[2167], pts[2173], coeff[222]);
                get_3_isog(pts[2173], A24minus[224], A24plus[224], coeff[223]);
                lock[251][0] = 0;
                while(lock[251][1]) {
                    #pragma omp flush(lock[251][1])
                }

                eval_3_isog_mod(pts[2172], pts[2175], coeff[220]);
                eval_3_isog_mod(pts[2175], pts[2177], coeff[221]);
                eval_3_isog_mod(pts[2177], pts[2179], coeff[222]);
                eval_3_isog_mod(pts[2179], pts[2181], coeff[223]);
                lock[252][0] = 0;
                while(lock[252][1]) {
                    #pragma omp flush(lock[252][1])
                }

                eval_3_isog_mod(pts[2181], pts[2184], coeff[224]);
                eval_3_isog_mod(pts[2184], pts[2186], coeff[225]);
                lock[253][0] = 0;
                while(lock[253][1]) {
                    #pragma omp flush(lock[253][1])
                }

                eval_3_isog_mod(pts[2186], pts[2187], coeff[226]);
                xTPLe(pts[2187], pts[2188], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2188], pts[2189], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2189], pts[2190], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2190], pts[2191], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2191], pts[2192], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2192], pts[2193], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2193], pts[2194], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2194], pts[2195], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2195], pts[2196], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2196], pts[2197], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2197], pts[2198], A24minus[227], A24plus[227], 1);
                get_3_isog(pts[2198], A24minus[228], A24plus[228], coeff[227]);
                lock[254][0] = 0;
                while(lock[254][1]) {
                    #pragma omp flush(lock[254][1])
                }

                eval_3_isog_mod(pts[2197], pts[2199], coeff[227]);
                get_3_isog(pts[2199], A24minus[229], A24plus[229], coeff[228]);
                eval_3_isog_mod(pts[2194], pts[2202], coeff[227]);
                eval_3_isog_mod(pts[2193], pts[2203], coeff[227]);
                lock[255][0] = 0;
                while(lock[255][1]) {
                    #pragma omp flush(lock[255][1])
                }

                eval_3_isog_mod(pts[2200], pts[2206], coeff[228]);
                get_3_isog(pts[2206], A24minus[230], A24plus[230], coeff[229]);
                eval_3_isog_mod(pts[2201], pts[2207], coeff[228]);
                eval_3_isog_mod(pts[2204], pts[2210], coeff[228]);
                eval_3_isog_mod(pts[2187], pts[2212], coeff[227]);
                lock[256][0] = 0;
                while(lock[256][1]) {
                    #pragma omp flush(lock[256][1])
                }

                eval_3_isog_mod(pts[2207], pts[2213], coeff[229]);
                get_3_isog(pts[2213], A24minus[231], A24plus[231], coeff[230]);
                eval_3_isog_mod(pts[2209], pts[2215], coeff[229]);
                eval_3_isog_mod(pts[2212], pts[2218], coeff[228]);
                lock[257][0] = 0;
                while(lock[257][1]) {
                    #pragma omp flush(lock[257][1])
                }

                eval_3_isog_mod(pts[2214], pts[2219], coeff[230]);
                get_3_isog(pts[2219], A24minus[232], A24plus[232], coeff[231]);
                eval_3_isog_mod(pts[2216], pts[2221], coeff[230]);
                lock[258][0] = 0;
                while(lock[258][1]) {
                    #pragma omp flush(lock[258][1])
                }

                eval_3_isog_mod(pts[2218], pts[2223], coeff[229]);
                eval_3_isog_mod(pts[2222], pts[2226], coeff[231]);
                eval_3_isog_mod(pts[2223], pts[2227], coeff[230]);
                lock[259][0] = 0;
                while(lock[259][1]) {
                    #pragma omp flush(lock[259][1])
                }

                eval_3_isog_mod(pts[2226], pts[2229], coeff[232]);
                eval_3_isog_mod(pts[2229], pts[2231], coeff[233]);
                xTPLe(pts[2231], pts[2233], A24minus[234], A24plus[234], 1);
                get_3_isog(pts[2233], A24minus[235], A24plus[235], coeff[234]);
                lock[260][0] = 0;
                while(lock[260][1]) {
                    #pragma omp flush(lock[260][1])
                }

                eval_3_isog_mod(pts[2234], pts[2236], coeff[234]);
                lock[261][0] = 0;
                while(lock[261][1]) {
                    #pragma omp flush(lock[261][1])
                }

                eval_3_isog_mod(pts[2236], pts[2237], coeff[235]);
                xTPLe(pts[2237], pts[2238], A24minus[236], A24plus[236], 1);
                xTPLe(pts[2238], pts[2239], A24minus[236], A24plus[236], 1);
                get_3_isog(pts[2239], A24minus[237], A24plus[237], coeff[236]);
                lock[262][0] = 0;
                while(lock[262][1]) {
                    #pragma omp flush(lock[262][1])
                }

                eval_3_isog_mod(pts[2238], pts[2240], coeff[236]);
                get_3_isog(pts[2240], A24minus[238], A24plus[238], coeff[237]);
            }
            #pragma omp section
            {
                eval_3_isog_mod(pts[236], pts[240], coeff[0]);
                eval_3_isog_mod(pts[234], pts[242], coeff[0]);
                lock[0][1] = 0;
                while(lock[0][0]) {
                    #pragma omp flush(lock[0][0])
                }

                eval_3_isog_mod(pts[232], pts[243], coeff[0]);
                eval_3_isog_mod(pts[241], pts[245], coeff[1]);
                eval_3_isog_mod(pts[243], pts[247], coeff[1]);
                lock[1][1] = 0;
                while(lock[1][0]) {
                    #pragma omp flush(lock[1][0])
                }

                eval_3_isog_mod(pts[245], pts[249], coeff[2]);
                get_3_isog(pts[249], A24minus[4], A24plus[4], coeff[3]);
                eval_3_isog_mod(pts[248], pts[252], coeff[1]);
                lock[2][1] = 0;
                while(lock[2][0]) {
                    #pragma omp flush(lock[2][0])
                }

                eval_3_isog_mod(pts[251], pts[254], coeff[3]);
                eval_3_isog_mod(pts[225], pts[256], coeff[0]);
                lock[3][1] = 0;
                while(lock[3][0]) {
                    #pragma omp flush(lock[3][0])
                }

                eval_3_isog_mod(pts[255], pts[258], coeff[3]);
                eval_3_isog_mod(pts[256], pts[259], coeff[1]);
                lock[4][1] = 0;
                while(lock[4][0]) {
                    #pragma omp flush(lock[4][0])
                }

                eval_3_isog_mod(pts[259], pts[262], coeff[2]);
                eval_3_isog_mod(pts[257], pts[263], coeff[5]);
                get_3_isog(pts[263], A24minus[7], A24plus[7], coeff[6]);
                eval_3_isog_mod(pts[262], pts[265], coeff[3]);
                lock[5][1] = 0;
                while(lock[5][0]) {
                    #pragma omp flush(lock[5][0])
                }

                eval_3_isog_mod(pts[264], pts[267], coeff[6]);
                xTPLe(pts[267], pts[270], A24minus[7], A24plus[7], 1);
                lock[6][1] = 0;
                while(lock[6][0]) {
                    #pragma omp flush(lock[6][0])
                }

                eval_3_isog_mod(pts[268], pts[271], coeff[5]);
                eval_3_isog_mod(pts[271], pts[274], coeff[6]);
                lock[7][1] = 0;
                while(lock[7][0]) {
                    #pragma omp flush(lock[7][0])
                }

                eval_3_isog_mod(pts[270], pts[276], coeff[7]);
                get_3_isog(pts[276], A24minus[9], A24plus[9], coeff[8]);
                eval_3_isog_mod(pts[274], pts[278], coeff[7]);
                eval_3_isog_mod(pts[213], pts[280], coeff[0]);
                lock[8][1] = 0;
                while(lock[8][0]) {
                    #pragma omp flush(lock[8][0])
                }

                eval_3_isog_mod(pts[277], pts[281], coeff[8]);
                get_3_isog(pts[281], A24minus[10], A24plus[10], coeff[9]);
                eval_3_isog_mod(pts[279], pts[283], coeff[5]);
                lock[9][1] = 0;
                while(lock[9][0]) {
                    #pragma omp flush(lock[9][0])
                }

                eval_3_isog_mod(pts[282], pts[285], coeff[9]);
                xTPLe(pts[285], pts[288], A24minus[10], A24plus[10], 1);
                lock[10][1] = 0;
                while(lock[10][0]) {
                    #pragma omp flush(lock[10][0])
                }

                eval_3_isog_mod(pts[287], pts[290], coeff[3]);
                xTPLe(pts[288], pts[291], A24minus[10], A24plus[10], 1);
                lock[11][1] = 0;
                while(lock[11][0]) {
                    #pragma omp flush(lock[11][0])
                }

                xTPLe(pts[291], pts[294], A24minus[10], A24plus[10], 1);
                get_3_isog(pts[294], A24minus[11], A24plus[11], coeff[10]);
                eval_3_isog_mod(pts[292], pts[295], coeff[9]);
                lock[12][1] = 0;
                while(lock[12][0]) {
                    #pragma omp flush(lock[12][0])
                }

                eval_3_isog_mod(pts[288], pts[298], coeff[10]);
                eval_3_isog_mod(pts[285], pts[299], coeff[10]);
                lock[13][1] = 0;
                while(lock[13][0]) {
                    #pragma omp flush(lock[13][0])
                }

                eval_3_isog_mod(pts[298], pts[302], coeff[11]);
                get_3_isog(pts[302], A24minus[13], A24plus[13], coeff[12]);
                eval_3_isog_mod(pts[299], pts[303], coeff[11]);
                eval_3_isog_mod(pts[203], pts[306], coeff[0]);
                lock[14][1] = 0;
                while(lock[14][0]) {
                    #pragma omp flush(lock[14][0])
                }

                eval_3_isog_mod(pts[303], pts[307], coeff[12]);
                get_3_isog(pts[307], A24minus[14], A24plus[14], coeff[13]);
                eval_3_isog_mod(pts[306], pts[310], coeff[1]);
                lock[15][1] = 0;
                while(lock[15][0]) {
                    #pragma omp flush(lock[15][0])
                }

                eval_3_isog_mod(pts[308], pts[311], coeff[13]);
                xTPLe(pts[311], pts[314], A24minus[14], A24plus[14], 1);
                lock[16][1] = 0;
                while(lock[16][0]) {
                    #pragma omp flush(lock[16][0])
                }

                eval_3_isog_mod(pts[312], pts[315], coeff[10]);
                eval_3_isog_mod(pts[315], pts[318], coeff[11]);
                lock[17][1] = 0;
                while(lock[17][0]) {
                    #pragma omp flush(lock[17][0])
                }

                xTPLe(pts[317], pts[320], A24minus[14], A24plus[14], 1);
                eval_3_isog_mod(pts[318], pts[321], coeff[12]);
                lock[18][1] = 0;
                while(lock[18][0]) {
                    #pragma omp flush(lock[18][0])
                }

                xTPLe(pts[320], pts[323], A24minus[14], A24plus[14], 1);
                get_3_isog(pts[323], A24minus[15], A24plus[15], coeff[14]);
                eval_3_isog_mod(pts[320], pts[326], coeff[14]);
                get_3_isog(pts[326], A24minus[16], A24plus[16], coeff[15]);
                lock[19][1] = 0;
                while(lock[19][0]) {
                    #pragma omp flush(lock[19][0])
                }

                eval_3_isog_mod(pts[314], pts[328], coeff[14]);
                eval_3_isog_mod(pts[324], pts[330], coeff[14]);
                eval_3_isog_mod(pts[325], pts[331], coeff[7]);
                eval_3_isog_mod(pts[328], pts[333], coeff[15]);
                lock[20][1] = 0;
                while(lock[20][0]) {
                    #pragma omp flush(lock[20][0])
                }

                eval_3_isog_mod(pts[331], pts[336], coeff[8]);
                eval_3_isog_mod(pts[333], pts[337], coeff[16]);
                get_3_isog(pts[337], A24minus[18], A24plus[18], coeff[17]);
                eval_3_isog_mod(pts[336], pts[340], coeff[9]);
                lock[21][1] = 0;
                while(lock[21][0]) {
                    #pragma omp flush(lock[21][0])
                }

                eval_3_isog_mod(pts[339], pts[342], coeff[17]);
                lock[22][1] = 0;
                while(lock[22][0]) {
                    #pragma omp flush(lock[22][0])
                }

                eval_3_isog_mod(pts[340], pts[343], coeff[10]);
                eval_3_isog_mod(pts[343], pts[345], coeff[11]);
                eval_3_isog_mod(pts[345], pts[347], coeff[12]);
                eval_3_isog_mod(pts[347], pts[350], coeff[13]);
                lock[23][1] = 0;
                while(lock[23][0]) {
                    #pragma omp flush(lock[23][0])
                }

                eval_3_isog_mod(pts[348], pts[351], coeff[1]);
                eval_3_isog_mod(pts[351], pts[354], coeff[2]);
                lock[24][1] = 0;
                while(lock[24][0]) {
                    #pragma omp flush(lock[24][0])
                }

                xTPLe(pts[352], pts[355], A24minus[19], A24plus[19], 1);
                xTPLe(pts[355], pts[358], A24minus[19], A24plus[19], 1);
                lock[25][1] = 0;
                while(lock[25][0]) {
                    #pragma omp flush(lock[25][0])
                }

                eval_3_isog_mod(pts[356], pts[359], coeff[16]);
                eval_3_isog_mod(pts[359], pts[362], coeff[17]);
                lock[26][1] = 0;
                while(lock[26][0]) {
                    #pragma omp flush(lock[26][0])
                }

                eval_3_isog_mod(pts[360], pts[363], coeff[5]);
                eval_3_isog_mod(pts[352], pts[366], coeff[19]);
                eval_3_isog_mod(pts[349], pts[367], coeff[19]);
                eval_3_isog_mod(pts[363], pts[370], coeff[6]);
                lock[27][1] = 0;
                while(lock[27][0]) {
                    #pragma omp flush(lock[27][0])
                }

                eval_3_isog_mod(pts[366], pts[372], coeff[20]);
                eval_3_isog_mod(pts[367], pts[373], coeff[20]);
                eval_3_isog_mod(pts[370], pts[376], coeff[7]);
                lock[28][1] = 0;
                while(lock[28][0]) {
                    #pragma omp flush(lock[28][0])
                }

                eval_3_isog_mod(pts[372], pts[377], coeff[21]);
                get_3_isog(pts[377], A24minus[23], A24plus[23], coeff[22]);
                eval_3_isog_mod(pts[374], pts[379], coeff[21]);
                lock[29][1] = 0;
                while(lock[29][0]) {
                    #pragma omp flush(lock[29][0])
                }

                eval_3_isog_mod(pts[376], pts[381], coeff[8]);
                eval_3_isog_mod(pts[379], pts[383], coeff[22]);
                lock[30][1] = 0;
                while(lock[30][0]) {
                    #pragma omp flush(lock[30][0])
                }

                eval_3_isog_mod(pts[383], pts[386], coeff[23]);
                eval_3_isog_mod(pts[384], pts[387], coeff[22]);
                lock[31][1] = 0;
                while(lock[31][0]) {
                    #pragma omp flush(lock[31][0])
                }

                xTPLe(pts[386], pts[389], A24minus[24], A24plus[24], 1);
                get_3_isog(pts[389], A24minus[25], A24plus[25], coeff[24]);
                eval_3_isog_mod(pts[386], pts[392], coeff[24]);
                get_3_isog(pts[392], A24minus[26], A24plus[26], coeff[25]);
                lock[32][1] = 0;
                while(lock[32][0]) {
                    #pragma omp flush(lock[32][0])
                }

                eval_3_isog_mod(pts[391], pts[394], coeff[12]);
                eval_3_isog_mod(pts[394], pts[396], coeff[13]);
                eval_3_isog_mod(pts[396], pts[398], coeff[14]);
                eval_3_isog_mod(pts[398], pts[400], coeff[15]);
                eval_3_isog_mod(pts[400], pts[402], coeff[16]);
                eval_3_isog_mod(pts[402], pts[404], coeff[17]);
                eval_3_isog_mod(pts[404], pts[406], coeff[18]);
                eval_3_isog_mod(pts[406], pts[408], coeff[19]);
                eval_3_isog_mod(pts[170], pts[409], coeff[0]);
                lock[33][1] = 0;
                while(lock[33][0]) {
                    #pragma omp flush(lock[33][0])
                }

                eval_3_isog_mod(pts[408], pts[411], coeff[20]);
                eval_3_isog_mod(pts[411], pts[414], coeff[21]);
                lock[34][1] = 0;
                while(lock[34][0]) {
                    #pragma omp flush(lock[34][0])
                }

                eval_3_isog_mod(pts[412], pts[415], coeff[2]);
                eval_3_isog_mod(pts[415], pts[418], coeff[3]);
                lock[35][1] = 0;
                while(lock[35][0]) {
                    #pragma omp flush(lock[35][0])
                }

                eval_3_isog_mod(pts[410], pts[420], coeff[26]);
                eval_3_isog_mod(pts[407], pts[421], coeff[26]);
                eval_3_isog_mod(pts[401], pts[423], coeff[26]);
                lock[36][1] = 0;
                while(lock[36][0]) {
                    #pragma omp flush(lock[36][0])
                }

                eval_3_isog_mod(pts[420], pts[426], coeff[27]);
                get_3_isog(pts[426], A24minus[29], A24plus[29], coeff[28]);
                eval_3_isog_mod(pts[421], pts[427], coeff[27]);
                eval_3_isog_mod(pts[395], pts[430], coeff[26]);
                eval_3_isog_mod(pts[424], pts[431], coeff[24]);
                lock[37][1] = 0;
                while(lock[37][0]) {
                    #pragma omp flush(lock[37][0])
                }

                eval_3_isog_mod(pts[427], pts[433], coeff[28]);
                get_3_isog(pts[433], A24minus[30], A24plus[30], coeff[29]);
                eval_3_isog_mod(pts[429], pts[435], coeff[28]);
                eval_3_isog_mod(pts[432], pts[438], coeff[6]);
                lock[38][1] = 0;
                while(lock[38][0]) {
                    #pragma omp flush(lock[38][0])
                }

                eval_3_isog_mod(pts[434], pts[439], coeff[29]);
                get_3_isog(pts[439], A24minus[31], A24plus[31], coeff[30]);
                eval_3_isog_mod(pts[436], pts[441], coeff[28]);
                lock[39][1] = 0;
                while(lock[39][0]) {
                    #pragma omp flush(lock[39][0])
                }

                eval_3_isog_mod(pts[438], pts[443], coeff[7]);
                eval_3_isog_mod(pts[442], pts[446], coeff[27]);
                eval_3_isog_mod(pts[443], pts[447], coeff[8]);
                eval_3_isog_mod(pts[446], pts[450], coeff[28]);
                eval_3_isog_mod(pts[447], pts[451], coeff[9]);
                eval_3_isog_mod(pts[450], pts[454], coeff[29]);
                eval_3_isog_mod(pts[451], pts[455], coeff[10]);
                lock[40][1] = 0;
                while(lock[40][0]) {
                    #pragma omp flush(lock[40][0])
                }

                eval_3_isog_mod(pts[454], pts[457], coeff[30]);
                eval_3_isog_mod(pts[457], pts[460], coeff[31]);
                lock[41][1] = 0;
                while(lock[41][0]) {
                    #pragma omp flush(lock[41][0])
                }

                eval_3_isog_mod(pts[458], pts[461], coeff[12]);
                eval_3_isog_mod(pts[461], pts[464], coeff[13]);
                lock[42][1] = 0;
                while(lock[42][0]) {
                    #pragma omp flush(lock[42][0])
                }

                eval_3_isog_mod(pts[459], pts[465], coeff[33]);
                get_3_isog(pts[465], A24minus[35], A24plus[35], coeff[34]);
                eval_3_isog_mod(pts[464], pts[468], coeff[14]);
                lock[43][1] = 0;
                while(lock[43][0]) {
                    #pragma omp flush(lock[43][0])
                }

                eval_3_isog_mod(pts[467], pts[470], coeff[34]);
                lock[44][1] = 0;
                while(lock[44][0]) {
                    #pragma omp flush(lock[44][0])
                }

                eval_3_isog_mod(pts[468], pts[471], coeff[15]);
                eval_3_isog_mod(pts[471], pts[473], coeff[16]);
                eval_3_isog_mod(pts[473], pts[475], coeff[17]);
                eval_3_isog_mod(pts[475], pts[477], coeff[18]);
                eval_3_isog_mod(pts[477], pts[479], coeff[19]);
                eval_3_isog_mod(pts[479], pts[481], coeff[20]);
                eval_3_isog_mod(pts[481], pts[483], coeff[21]);
                eval_3_isog_mod(pts[483], pts[485], coeff[22]);
                eval_3_isog_mod(pts[485], pts[487], coeff[23]);
                eval_3_isog_mod(pts[487], pts[489], coeff[24]);
                eval_3_isog_mod(pts[489], pts[491], coeff[25]);
                eval_3_isog_mod(pts[491], pts[493], coeff[26]);
                eval_3_isog_mod(pts[493], pts[495], coeff[27]);
                eval_3_isog_mod(pts[495], pts[497], coeff[28]);
                eval_3_isog_mod(pts[497], pts[500], coeff[29]);
                lock[45][1] = 0;
                while(lock[45][0]) {
                    #pragma omp flush(lock[45][0])
                }

                eval_3_isog_mod(pts[496], pts[502], coeff[36]);
                get_3_isog(pts[502], A24minus[38], A24plus[38], coeff[37]);
                eval_3_isog_mod(pts[494], pts[503], coeff[36]);
                eval_3_isog_mod(pts[490], pts[505], coeff[36]);
                eval_3_isog_mod(pts[500], pts[507], coeff[30]);
                lock[46][1] = 0;
                while(lock[46][0]) {
                    #pragma omp flush(lock[46][0])
                }

                eval_3_isog_mod(pts[504], pts[510], coeff[37]);
                eval_3_isog_mod(pts[505], pts[511], coeff[37]);
                eval_3_isog_mod(pts[507], pts[514], coeff[31]);
                lock[47][1] = 0;
                while(lock[47][0]) {
                    #pragma omp flush(lock[47][0])
                }

                eval_3_isog_mod(pts[510], pts[516], coeff[38]);
                get_3_isog(pts[516], A24minus[40], A24plus[40], coeff[39]);
                eval_3_isog_mod(pts[511], pts[517], coeff[38]);
                eval_3_isog_mod(pts[514], pts[520], coeff[32]);
                eval_3_isog_mod(pts[517], pts[522], coeff[39]);
                get_3_isog(pts[522], A24minus[41], A24plus[41], coeff[40]);
                lock[48][1] = 0;
                while(lock[48][0]) {
                    #pragma omp flush(lock[48][0])
                }

                eval_3_isog_mod(pts[519], pts[524], coeff[38]);
                eval_3_isog_mod(pts[472], pts[525], coeff[36]);
                eval_3_isog_mod(pts[521], pts[527], coeff[5]);
                lock[49][1] = 0;
                while(lock[49][0]) {
                    #pragma omp flush(lock[49][0])
                }

                eval_3_isog_mod(pts[525], pts[530], coeff[37]);
                eval_3_isog_mod(pts[527], pts[532], coeff[6]);
                xTPLe(pts[528], pts[533], A24minus[41], A24plus[41], 1);
                get_3_isog(pts[533], A24minus[42], A24plus[42], coeff[41]);
                eval_3_isog_mod(pts[530], pts[535], coeff[38]);
                lock[50][1] = 0;
                while(lock[50][0]) {
                    #pragma omp flush(lock[50][0])
                }

                eval_3_isog_mod(pts[528], pts[538], coeff[41]);
                get_3_isog(pts[538], A24minus[43], A24plus[43], coeff[42]);
                eval_3_isog_mod(pts[534], pts[539], coeff[41]);
                eval_3_isog_mod(pts[536], pts[541], coeff[36]);
                eval_3_isog_mod(pts[539], pts[543], coeff[42]);
                eval_3_isog_mod(pts[541], pts[545], coeff[37]);
                xTPLe(pts[543], pts[547], A24minus[43], A24plus[43], 1);
                eval_3_isog_mod(pts[545], pts[549], coeff[38]);
                lock[51][1] = 0;
                while(lock[51][0]) {
                    #pragma omp flush(lock[51][0])
                }

                xTPLe(pts[547], pts[551], A24minus[43], A24plus[43], 1);
                get_3_isog(pts[551], A24minus[44], A24plus[44], coeff[43]);
                eval_3_isog_mod(pts[550], pts[554], coeff[11]);
                lock[52][1] = 0;
                while(lock[52][0]) {
                    #pragma omp flush(lock[52][0])
                }

                eval_3_isog_mod(pts[547], pts[555], coeff[43]);
                get_3_isog(pts[555], A24minus[45], A24plus[45], coeff[44]);
                eval_3_isog_mod(pts[552], pts[557], coeff[43]);
                lock[53][1] = 0;
                while(lock[53][0]) {
                    #pragma omp flush(lock[53][0])
                }

                eval_3_isog_mod(pts[554], pts[559], coeff[12]);
                eval_3_isog_mod(pts[557], pts[561], coeff[44]);
                lock[54][1] = 0;
                while(lock[54][0]) {
                    #pragma omp flush(lock[54][0])
                }

                eval_3_isog_mod(pts[559], pts[563], coeff[13]);
                eval_3_isog_mod(pts[563], pts[566], coeff[14]);
                lock[55][1] = 0;
                while(lock[55][0]) {
                    #pragma omp flush(lock[55][0])
                }

                xTPLe(pts[564], pts[567], A24minus[46], A24plus[46], 1);
                xTPLe(pts[567], pts[570], A24minus[46], A24plus[46], 1);
                lock[56][1] = 0;
                while(lock[56][0]) {
                    #pragma omp flush(lock[56][0])
                }

                eval_3_isog_mod(pts[569], pts[572], coeff[16]);
                xTPLe(pts[570], pts[573], A24minus[46], A24plus[46], 1);
                get_3_isog(pts[573], A24minus[47], A24plus[47], coeff[46]);
                lock[57][1] = 0;
                while(lock[57][0]) {
                    #pragma omp flush(lock[57][0])
                }

                eval_3_isog_mod(pts[572], pts[575], coeff[17]);
                eval_3_isog_mod(pts[567], pts[577], coeff[46]);
                eval_3_isog_mod(pts[575], pts[580], coeff[18]);
                lock[58][1] = 0;
                while(lock[58][0]) {
                    #pragma omp flush(lock[58][0])
                }

                eval_3_isog_mod(pts[577], pts[581], coeff[47]);
                get_3_isog(pts[581], A24minus[49], A24plus[49], coeff[48]);
                eval_3_isog_mod(pts[579], pts[583], coeff[47]);
                lock[59][1] = 0;
                while(lock[59][0]) {
                    #pragma omp flush(lock[59][0])
                }

                eval_3_isog_mod(pts[583], pts[586], coeff[48]);
                lock[60][1] = 0;
                while(lock[60][0]) {
                    #pragma omp flush(lock[60][0])
                }

                eval_3_isog_mod(pts[584], pts[587], coeff[20]);
                eval_3_isog_mod(pts[587], pts[589], coeff[21]);
                eval_3_isog_mod(pts[589], pts[591], coeff[22]);
                eval_3_isog_mod(pts[591], pts[593], coeff[23]);
                eval_3_isog_mod(pts[593], pts[595], coeff[24]);
                eval_3_isog_mod(pts[595], pts[597], coeff[25]);
                eval_3_isog_mod(pts[597], pts[599], coeff[26]);
                eval_3_isog_mod(pts[599], pts[601], coeff[27]);
                eval_3_isog_mod(pts[601], pts[603], coeff[28]);
                eval_3_isog_mod(pts[603], pts[605], coeff[29]);
                eval_3_isog_mod(pts[605], pts[607], coeff[30]);
                eval_3_isog_mod(pts[607], pts[609], coeff[31]);
                eval_3_isog_mod(pts[609], pts[611], coeff[32]);
                eval_3_isog_mod(pts[611], pts[613], coeff[33]);
                eval_3_isog_mod(pts[613], pts[615], coeff[34]);
                eval_3_isog_mod(pts[615], pts[617], coeff[35]);
                eval_3_isog_mod(pts[617], pts[619], coeff[36]);
                eval_3_isog_mod(pts[619], pts[621], coeff[37]);
                eval_3_isog_mod(pts[621], pts[623], coeff[38]);
                eval_3_isog_mod(pts[623], pts[625], coeff[39]);
                lock[61][1] = 0;
                while(lock[61][0]) {
                    #pragma omp flush(lock[61][0])
                }

                eval_3_isog_mod(pts[618], pts[628], coeff[50]);
                eval_3_isog_mod(pts[616], pts[629], coeff[50]);
                eval_3_isog_mod(pts[625], pts[631], coeff[40]);
                lock[62][1] = 0;
                while(lock[62][0]) {
                    #pragma omp flush(lock[62][0])
                }

                eval_3_isog_mod(pts[629], pts[634], coeff[51]);
                eval_3_isog_mod(pts[630], pts[635], coeff[51]);
                eval_3_isog_mod(pts[631], pts[637], coeff[41]);
                lock[63][1] = 0;
                while(lock[63][0]) {
                    #pragma omp flush(lock[63][0])
                }

                eval_3_isog_mod(pts[635], pts[640], coeff[52]);
                eval_3_isog_mod(pts[637], pts[642], coeff[42]);
                eval_3_isog_mod(pts[108], pts[643], coeff[0]);
                eval_3_isog_mod(pts[640], pts[645], coeff[53]);
                eval_3_isog_mod(pts[642], pts[648], coeff[43]);
                lock[64][1] = 0;
                while(lock[64][0]) {
                    #pragma omp flush(lock[64][0])
                }

                eval_3_isog_mod(pts[643], pts[649], coeff[1]);
                eval_3_isog_mod(pts[646], pts[651], coeff[53]);
                eval_3_isog_mod(pts[649], pts[654], coeff[2]);
                eval_3_isog_mod(pts[651], pts[656], coeff[54]);
                lock[65][1] = 0;
                while(lock[65][0]) {
                    #pragma omp flush(lock[65][0])
                }

                eval_3_isog_mod(pts[652], pts[657], coeff[52]);
                eval_3_isog_mod(pts[650], pts[660], coeff[55]);
                get_3_isog(pts[660], A24minus[57], A24plus[57], coeff[56]);
                eval_3_isog_mod(pts[657], pts[662], coeff[53]);
                eval_3_isog_mod(pts[588], pts[663], coeff[50]);
                lock[66][1] = 0;
                while(lock[66][0]) {
                    #pragma omp flush(lock[66][0])
                }

                eval_3_isog_mod(pts[661], pts[666], coeff[56]);
                eval_3_isog_mod(pts[663], pts[668], coeff[51]);
                eval_3_isog_mod(pts[664], pts[669], coeff[47]);
                xTPLe(pts[666], pts[671], A24minus[57], A24plus[57], 1);
                lock[67][1] = 0;
                while(lock[67][0]) {
                    #pragma omp flush(lock[67][0])
                }

                eval_3_isog_mod(pts[668], pts[673], coeff[52]);
                eval_3_isog_mod(pts[670], pts[675], coeff[6]);
                eval_3_isog_mod(pts[673], pts[678], coeff[53]);
                eval_3_isog_mod(pts[675], pts[680], coeff[7]);
                lock[68][1] = 0;
                while(lock[68][0]) {
                    #pragma omp flush(lock[68][0])
                }

                eval_3_isog_mod(pts[666], pts[682], coeff[57]);
                eval_3_isog_mod(pts[678], pts[684], coeff[54]);
                eval_3_isog_mod(pts[679], pts[685], coeff[50]);
                lock[69][1] = 0;
                while(lock[69][0]) {
                    #pragma omp flush(lock[69][0])
                }

                eval_3_isog_mod(pts[682], pts[687], coeff[58]);
                get_3_isog(pts[687], A24minus[60], A24plus[60], coeff[59]);
                eval_3_isog_mod(pts[684], pts[689], coeff[55]);
                lock[70][1] = 0;
                while(lock[70][0]) {
                    #pragma omp flush(lock[70][0])
                }

                eval_3_isog_mod(pts[686], pts[691], coeff[9]);
                eval_3_isog_mod(pts[690], pts[694], coeff[52]);
                eval_3_isog_mod(pts[691], pts[695], coeff[10]);
                eval_3_isog_mod(pts[694], pts[698], coeff[53]);
                eval_3_isog_mod(pts[695], pts[699], coeff[11]);
                eval_3_isog_mod(pts[698], pts[702], coeff[54]);
                eval_3_isog_mod(pts[699], pts[703], coeff[12]);
                eval_3_isog_mod(pts[702], pts[706], coeff[55]);
                eval_3_isog_mod(pts[703], pts[707], coeff[13]);
                lock[71][1] = 0;
                while(lock[71][0]) {
                    #pragma omp flush(lock[71][0])
                }

                eval_3_isog_mod(pts[692], pts[710], coeff[60]);
                eval_3_isog_mod(pts[705], pts[711], coeff[60]);
                eval_3_isog_mod(pts[707], pts[713], coeff[14]);
                lock[72][1] = 0;
                while(lock[72][0]) {
                    #pragma omp flush(lock[72][0])
                }

                eval_3_isog_mod(pts[711], pts[716], coeff[61]);
                eval_3_isog_mod(pts[712], pts[717], coeff[57]);
                eval_3_isog_mod(pts[716], pts[720], coeff[62]);
                eval_3_isog_mod(pts[717], pts[721], coeff[58]);
                lock[73][1] = 0;
                while(lock[73][0]) {
                    #pragma omp flush(lock[73][0])
                }

                eval_3_isog_mod(pts[720], pts[723], coeff[63]);
                xTPLe(pts[723], pts[726], A24minus[64], A24plus[64], 1);
                lock[74][1] = 0;
                while(lock[74][0]) {
                    #pragma omp flush(lock[74][0])
                }

                eval_3_isog_mod(pts[724], pts[727], coeff[60]);
                eval_3_isog_mod(pts[727], pts[730], coeff[61]);
                lock[75][1] = 0;
                while(lock[75][0]) {
                    #pragma omp flush(lock[75][0])
                }

                eval_3_isog_mod(pts[728], pts[731], coeff[19]);
                eval_3_isog_mod(pts[731], pts[734], coeff[20]);
                lock[76][1] = 0;
                while(lock[76][0]) {
                    #pragma omp flush(lock[76][0])
                }

                xTPLe(pts[732], pts[735], A24minus[64], A24plus[64], 1);
                get_3_isog(pts[735], A24minus[65], A24plus[65], coeff[64]);
                eval_3_isog_mod(pts[732], pts[738], coeff[64]);
                get_3_isog(pts[738], A24minus[66], A24plus[66], coeff[65]);
                lock[77][1] = 0;
                while(lock[77][0]) {
                    #pragma omp flush(lock[77][0])
                }

                eval_3_isog_mod(pts[729], pts[739], coeff[64]);
                eval_3_isog_mod(pts[723], pts[741], coeff[64]);
                eval_3_isog_mod(pts[739], pts[744], coeff[65]);
                get_3_isog(pts[744], A24minus[67], A24plus[67], coeff[66]);
                eval_3_isog_mod(pts[741], pts[746], coeff[65]);
                lock[78][1] = 0;
                while(lock[78][0]) {
                    #pragma omp flush(lock[78][0])
                }

                eval_3_isog_mod(pts[743], pts[748], coeff[23]);
                eval_3_isog_mod(pts[746], pts[750], coeff[66]);
                eval_3_isog_mod(pts[748], pts[752], coeff[24]);
                lock[79][1] = 0;
                while(lock[79][0]) {
                    #pragma omp flush(lock[79][0])
                }

                eval_3_isog_mod(pts[751], pts[754], coeff[67]);
                lock[80][1] = 0;
                while(lock[80][0]) {
                    #pragma omp flush(lock[80][0])
                }

                eval_3_isog_mod(pts[754], pts[756], coeff[68]);
                xTPLe(pts[756], pts[758], A24minus[69], A24plus[69], 1);
                xTPLe(pts[758], pts[760], A24minus[69], A24plus[69], 1);
                xTPLe(pts[760], pts[762], A24minus[69], A24plus[69], 1);
                xTPLe(pts[762], pts[764], A24minus[69], A24plus[69], 1);
                xTPLe(pts[764], pts[766], A24minus[69], A24plus[69], 1);
                xTPLe(pts[766], pts[768], A24minus[69], A24plus[69], 1);
                xTPLe(pts[768], pts[770], A24minus[69], A24plus[69], 1);
                xTPLe(pts[770], pts[772], A24minus[69], A24plus[69], 1);
                xTPLe(pts[772], pts[774], A24minus[69], A24plus[69], 1);
                xTPLe(pts[774], pts[776], A24minus[69], A24plus[69], 1);
                xTPLe(pts[776], pts[778], A24minus[69], A24plus[69], 1);
                xTPLe(pts[778], pts[780], A24minus[69], A24plus[69], 1);
                xTPLe(pts[780], pts[782], A24minus[69], A24plus[69], 1);
                xTPLe(pts[782], pts[784], A24minus[69], A24plus[69], 1);
                xTPLe(pts[784], pts[786], A24minus[69], A24plus[69], 1);
                xTPLe(pts[786], pts[788], A24minus[69], A24plus[69], 1);
                xTPLe(pts[788], pts[790], A24minus[69], A24plus[69], 1);
                xTPLe(pts[790], pts[792], A24minus[69], A24plus[69], 1);
                xTPLe(pts[792], pts[794], A24minus[69], A24plus[69], 1);
                xTPLe(pts[794], pts[796], A24minus[69], A24plus[69], 1);
                xTPLe(pts[796], pts[798], A24minus[69], A24plus[69], 1);
                xTPLe(pts[798], pts[800], A24minus[69], A24plus[69], 1);
                xTPLe(pts[800], pts[802], A24minus[69], A24plus[69], 1);
                xTPLe(pts[802], pts[804], A24minus[69], A24plus[69], 1);
                xTPLe(pts[804], pts[806], A24minus[69], A24plus[69], 1);
                get_3_isog(pts[806], A24minus[70], A24plus[70], coeff[69]);
                eval_3_isog_mod(pts[804], pts[808], coeff[69]);
                get_3_isog(pts[808], A24minus[71], A24plus[71], coeff[70]);
                lock[81][1] = 0;
                while(lock[81][0]) {
                    #pragma omp flush(lock[81][0])
                }

                eval_3_isog_mod(pts[802], pts[809], coeff[69]);
                eval_3_isog_mod(pts[794], pts[812], coeff[69]);
                eval_3_isog_mod(pts[809], pts[814], coeff[70]);
                get_3_isog(pts[814], A24minus[72], A24plus[72], coeff[71]);
                lock[82][1] = 0;
                while(lock[82][0]) {
                    #pragma omp flush(lock[82][0])
                }

                eval_3_isog_mod(pts[811], pts[816], coeff[70]);
                eval_3_isog_mod(pts[812], pts[817], coeff[70]);
                eval_3_isog_mod(pts[813], pts[819], coeff[53]);
                lock[83][1] = 0;
                while(lock[83][0]) {
                    #pragma omp flush(lock[83][0])
                }

                eval_3_isog_mod(pts[816], pts[821], coeff[71]);
                eval_3_isog_mod(pts[818], pts[823], coeff[70]);
                eval_3_isog_mod(pts[821], pts[825], coeff[72]);
                get_3_isog(pts[825], A24minus[74], A24plus[74], coeff[73]);
                eval_3_isog_mod(pts[823], pts[827], coeff[71]);
                lock[84][1] = 0;
                while(lock[84][0]) {
                    #pragma omp flush(lock[84][0])
                }

                eval_3_isog_mod(pts[824], pts[829], coeff[55]);
                eval_3_isog_mod(pts[828], pts[832], coeff[70]);
                eval_3_isog_mod(pts[829], pts[833], coeff[56]);
                eval_3_isog_mod(pts[832], pts[836], coeff[71]);
                eval_3_isog_mod(pts[833], pts[837], coeff[57]);
                eval_3_isog_mod(pts[836], pts[840], coeff[72]);
                eval_3_isog_mod(pts[837], pts[842], coeff[58]);
                eval_3_isog_mod(pts[840], pts[844], coeff[73]);
                eval_3_isog_mod(pts[842], pts[846], coeff[59]);
                lock[85][1] = 0;
                while(lock[85][0]) {
                    #pragma omp flush(lock[85][0])
                }

                eval_3_isog_mod(pts[844], pts[848], coeff[74]);
                eval_3_isog_mod(pts[846], pts[850], coeff[60]);
                eval_3_isog_mod(pts[848], pts[852], coeff[75]);
                eval_3_isog_mod(pts[850], pts[854], coeff[61]);
                lock[86][1] = 0;
                while(lock[86][0]) {
                    #pragma omp flush(lock[86][0])
                }

                eval_3_isog_mod(pts[847], pts[855], coeff[76]);
                get_3_isog(pts[855], A24minus[78], A24plus[78], coeff[77]);
                eval_3_isog_mod(pts[853], pts[858], coeff[73]);
                eval_3_isog_mod(pts[756], pts[859], coeff[69]);
                lock[87][1] = 0;
                while(lock[87][0]) {
                    #pragma omp flush(lock[87][0])
                }

                eval_3_isog_mod(pts[857], pts[862], coeff[77]);
                eval_3_isog_mod(pts[859], pts[864], coeff[70]);
                lock[88][1] = 0;
                while(lock[88][0]) {
                    #pragma omp flush(lock[88][0])
                }

                eval_3_isog_mod(pts[862], pts[866], coeff[78]);
                eval_3_isog_mod(pts[864], pts[868], coeff[71]);
                eval_3_isog_mod(pts[58], pts[870], coeff[0]);
                xTPLe(pts[866], pts[871], A24minus[79], A24plus[79], 1);
                eval_3_isog_mod(pts[868], pts[873], coeff[72]);
                lock[89][1] = 0;
                while(lock[89][0]) {
                    #pragma omp flush(lock[89][0])
                }

                eval_3_isog_mod(pts[870], pts[875], coeff[1]);
                eval_3_isog_mod(pts[872], pts[877], coeff[77]);
                eval_3_isog_mod(pts[875], pts[880], coeff[2]);
                eval_3_isog_mod(pts[877], pts[882], coeff[78]);
                lock[90][1] = 0;
                while(lock[90][0]) {
                    #pragma omp flush(lock[90][0])
                }

                eval_3_isog_mod(pts[878], pts[883], coeff[74]);
                eval_3_isog_mod(pts[880], pts[885], coeff[3]);
                eval_3_isog_mod(pts[866], pts[888], coeff[79]);
                eval_3_isog_mod(pts[883], pts[890], coeff[75]);
                eval_3_isog_mod(pts[885], pts[892], coeff[4]);
                lock[91][1] = 0;
                while(lock[91][0]) {
                    #pragma omp flush(lock[91][0])
                }

                eval_3_isog_mod(pts[887], pts[893], coeff[80]);
                get_3_isog(pts[893], A24minus[82], A24plus[82], coeff[81]);
                eval_3_isog_mod(pts[890], pts[896], coeff[76]);
                eval_3_isog_mod(pts[891], pts[897], coeff[69]);
                lock[92][1] = 0;
                while(lock[92][0]) {
                    #pragma omp flush(lock[92][0])
                }

                eval_3_isog_mod(pts[894], pts[899], coeff[81]);
                get_3_isog(pts[899], A24minus[83], A24plus[83], coeff[82]);
                eval_3_isog_mod(pts[897], pts[902], coeff[70]);
                lock[93][1] = 0;
                while(lock[93][0]) {
                    #pragma omp flush(lock[93][0])
                }

                eval_3_isog_mod(pts[900], pts[904], coeff[82]);
                eval_3_isog_mod(pts[901], pts[905], coeff[78]);
                xTPLe(pts[904], pts[908], A24minus[83], A24plus[83], 1);
                eval_3_isog_mod(pts[905], pts[909], coeff[79]);
                xTPLe(pts[908], pts[912], A24minus[83], A24plus[83], 1);
                eval_3_isog_mod(pts[909], pts[913], coeff[80]);
                xTPLe(pts[912], pts[916], A24minus[83], A24plus[83], 1);
                eval_3_isog_mod(pts[913], pts[917], coeff[81]);
                xTPLe(pts[916], pts[920], A24minus[83], A24plus[83], 1);
                get_3_isog(pts[920], A24minus[84], A24plus[84], coeff[83]);
                eval_3_isog_mod(pts[917], pts[921], coeff[82]);
                eval_3_isog_mod(pts[916], pts[924], coeff[83]);
                get_3_isog(pts[924], A24minus[85], A24plus[85], coeff[84]);
                lock[94][1] = 0;
                while(lock[94][0]) {
                    #pragma omp flush(lock[94][0])
                }

                eval_3_isog_mod(pts[908], pts[926], coeff[83]);
                eval_3_isog_mod(pts[921], pts[928], coeff[83]);
                eval_3_isog_mod(pts[923], pts[930], coeff[12]);
                eval_3_isog_mod(pts[926], pts[932], coeff[84]);
                eval_3_isog_mod(pts[928], pts[934], coeff[84]);
                eval_3_isog_mod(pts[930], pts[936], coeff[13]);
                lock[95][1] = 0;
                while(lock[95][0]) {
                    #pragma omp flush(lock[95][0])
                }

                eval_3_isog_mod(pts[933], pts[938], coeff[85]);
                eval_3_isog_mod(pts[935], pts[940], coeff[78]);
                lock[96][1] = 0;
                while(lock[96][0]) {
                    #pragma omp flush(lock[96][0])
                }

                eval_3_isog_mod(pts[938], pts[942], coeff[86]);
                get_3_isog(pts[942], A24minus[88], A24plus[88], coeff[87]);
                eval_3_isog_mod(pts[940], pts[944], coeff[79]);
                lock[97][1] = 0;
                while(lock[97][0]) {
                    #pragma omp flush(lock[97][0])
                }

                eval_3_isog_mod(pts[941], pts[945], coeff[15]);
                eval_3_isog_mod(pts[945], pts[948], coeff[16]);
                lock[98][1] = 0;
                while(lock[98][0]) {
                    #pragma omp flush(lock[98][0])
                }

                eval_3_isog_mod(pts[947], pts[950], coeff[81]);
                eval_3_isog_mod(pts[948], pts[951], coeff[17]);
                lock[99][1] = 0;
                while(lock[99][0]) {
                    #pragma omp flush(lock[99][0])
                }

                eval_3_isog_mod(pts[951], pts[954], coeff[18]);
                xTPLe(pts[952], pts[955], A24minus[88], A24plus[88], 1);
                lock[100][1] = 0;
                while(lock[100][0]) {
                    #pragma omp flush(lock[100][0])
                }

                eval_3_isog_mod(pts[954], pts[957], coeff[19]);
                eval_3_isog_mod(pts[957], pts[960], coeff[20]);
                lock[101][1] = 0;
                while(lock[101][0]) {
                    #pragma omp flush(lock[101][0])
                }

                xTPLe(pts[958], pts[961], A24minus[88], A24plus[88], 1);
                xTPLe(pts[961], pts[964], A24minus[88], A24plus[88], 1);
                get_3_isog(pts[964], A24minus[89], A24plus[89], coeff[88]);
                lock[102][1] = 0;
                while(lock[102][0]) {
                    #pragma omp flush(lock[102][0])
                }

                eval_3_isog_mod(pts[962], pts[965], coeff[86]);
                eval_3_isog_mod(pts[961], pts[967], coeff[88]);
                get_3_isog(pts[967], A24minus[90], A24plus[90], coeff[89]);
                eval_3_isog_mod(pts[955], pts[969], coeff[88]);
                eval_3_isog_mod(pts[965], pts[972], coeff[87]);
                lock[103][1] = 0;
                while(lock[103][0]) {
                    #pragma omp flush(lock[103][0])
                }

                eval_3_isog_mod(pts[966], pts[973], coeff[23]);
                eval_3_isog_mod(pts[970], pts[976], coeff[89]);
                eval_3_isog_mod(pts[972], pts[978], coeff[88]);
                eval_3_isog_mod(pts[973], pts[979], coeff[24]);
                lock[104][1] = 0;
                while(lock[104][0]) {
                    #pragma omp flush(lock[104][0])
                }

                eval_3_isog_mod(pts[976], pts[981], coeff[90]);
                eval_3_isog_mod(pts[979], pts[984], coeff[25]);
                eval_3_isog_mod(pts[981], pts[985], coeff[91]);
                get_3_isog(pts[985], A24minus[93], A24plus[93], coeff[92]);
                eval_3_isog_mod(pts[984], pts[988], coeff[26]);
                lock[105][1] = 0;
                while(lock[105][0]) {
                    #pragma omp flush(lock[105][0])
                }

                eval_3_isog_mod(pts[986], pts[989], coeff[92]);
                xTPLe(pts[989], pts[992], A24minus[93], A24plus[93], 1);
                get_3_isog(pts[992], A24minus[94], A24plus[94], coeff[93]);
                lock[106][1] = 0;
                while(lock[106][0]) {
                    #pragma omp flush(lock[106][0])
                }

                eval_3_isog_mod(pts[991], pts[994], coeff[28]);
                eval_3_isog_mod(pts[989], pts[995], coeff[93]);
                get_3_isog(pts[995], A24minus[95], A24plus[95], coeff[94]);
                lock[107][1] = 0;
                while(lock[107][0]) {
                    #pragma omp flush(lock[107][0])
                }

                eval_3_isog_mod(pts[994], pts[997], coeff[29]);
                eval_3_isog_mod(pts[997], pts[999], coeff[30]);
                eval_3_isog_mod(pts[999], pts[1001], coeff[31]);
                eval_3_isog_mod(pts[1001], pts[1003], coeff[32]);
                eval_3_isog_mod(pts[1003], pts[1005], coeff[33]);
                eval_3_isog_mod(pts[1005], pts[1007], coeff[34]);
                eval_3_isog_mod(pts[1007], pts[1009], coeff[35]);
                eval_3_isog_mod(pts[1009], pts[1011], coeff[36]);
                eval_3_isog_mod(pts[1011], pts[1013], coeff[37]);
                eval_3_isog_mod(pts[1013], pts[1015], coeff[38]);
                eval_3_isog_mod(pts[1015], pts[1017], coeff[39]);
                eval_3_isog_mod(pts[1017], pts[1019], coeff[40]);
                eval_3_isog_mod(pts[1019], pts[1021], coeff[41]);
                eval_3_isog_mod(pts[1021], pts[1023], coeff[42]);
                eval_3_isog_mod(pts[1023], pts[1025], coeff[43]);
                eval_3_isog_mod(pts[1025], pts[1027], coeff[44]);
                eval_3_isog_mod(pts[1027], pts[1029], coeff[45]);
                eval_3_isog_mod(pts[1029], pts[1031], coeff[46]);
                eval_3_isog_mod(pts[1031], pts[1033], coeff[47]);
                eval_3_isog_mod(pts[1033], pts[1035], coeff[48]);
                eval_3_isog_mod(pts[1035], pts[1037], coeff[49]);
                eval_3_isog_mod(pts[1037], pts[1039], coeff[50]);
                eval_3_isog_mod(pts[1039], pts[1041], coeff[51]);
                eval_3_isog_mod(pts[1041], pts[1043], coeff[52]);
                eval_3_isog_mod(pts[1043], pts[1045], coeff[53]);
                eval_3_isog_mod(pts[1045], pts[1047], coeff[54]);
                eval_3_isog_mod(pts[1047], pts[1049], coeff[55]);
                eval_3_isog_mod(pts[1049], pts[1051], coeff[56]);
                eval_3_isog_mod(pts[1051], pts[1053], coeff[57]);
                eval_3_isog_mod(pts[1053], pts[1055], coeff[58]);
                eval_3_isog_mod(pts[1055], pts[1057], coeff[59]);
                eval_3_isog_mod(pts[1057], pts[1059], coeff[60]);
                eval_3_isog_mod(pts[1059], pts[1061], coeff[61]);
                eval_3_isog_mod(pts[1061], pts[1063], coeff[62]);
                eval_3_isog_mod(pts[1063], pts[1065], coeff[63]);
                eval_3_isog_mod(pts[1065], pts[1067], coeff[64]);
                eval_3_isog_mod(pts[1067], pts[1069], coeff[65]);
                lock[108][1] = 0;
                while(lock[108][0]) {
                    #pragma omp flush(lock[108][0])
                }

                eval_3_isog_mod(pts[1062], pts[1072], coeff[95]);
                eval_3_isog_mod(pts[1060], pts[1073], coeff[95]);
                eval_3_isog_mod(pts[1069], pts[1075], coeff[66]);
                lock[109][1] = 0;
                while(lock[109][0]) {
                    #pragma omp flush(lock[109][0])
                }

                eval_3_isog_mod(pts[1072], pts[1077], coeff[96]);
                eval_3_isog_mod(pts[1050], pts[1080], coeff[95]);
                eval_3_isog_mod(pts[1077], pts[1082], coeff[97]);
                get_3_isog(pts[1082], A24minus[99], A24plus[99], coeff[98]);
                lock[110][1] = 0;
                while(lock[110][0]) {
                    #pragma omp flush(lock[110][0])
                }

                eval_3_isog_mod(pts[1079], pts[1084], coeff[97]);
                eval_3_isog_mod(pts[1081], pts[1086], coeff[68]);
                eval_3_isog_mod(pts[1084], pts[1088], coeff[98]);
                eval_3_isog_mod(pts[1042], pts[1090], coeff[95]);
                lock[111][1] = 0;
                while(lock[111][0]) {
                    #pragma omp flush(lock[111][0])
                }

                eval_3_isog_mod(pts[1086], pts[1091], coeff[69]);
                eval_3_isog_mod(pts[1090], pts[1094], coeff[96]);
                eval_3_isog_mod(pts[1091], pts[1095], coeff[70]);
                eval_3_isog_mod(pts[1094], pts[1098], coeff[97]);
                eval_3_isog_mod(pts[1095], pts[1099], coeff[71]);
                eval_3_isog_mod(pts[1098], pts[1102], coeff[98]);
                eval_3_isog_mod(pts[1099], pts[1104], coeff[72]);
                eval_3_isog_mod(pts[1102], pts[1106], coeff[99]);
                eval_3_isog_mod(pts[1104], pts[1108], coeff[73]);
                lock[112][1] = 0;
                while(lock[112][0]) {
                    #pragma omp flush(lock[112][0])
                }

                xTPLe(pts[1105], pts[1109], A24minus[102], A24plus[102], 1);
                eval_3_isog_mod(pts[1107], pts[1111], coeff[97]);
                xTPLe(pts[1109], pts[1113], A24minus[102], A24plus[102], 1);
                get_3_isog(pts[1113], A24minus[103], A24plus[103], coeff[102]);
                eval_3_isog_mod(pts[1111], pts[1115], coeff[98]);
                lock[113][1] = 0;
                while(lock[113][0]) {
                    #pragma omp flush(lock[113][0])
                }

                eval_3_isog_mod(pts[1109], pts[1117], coeff[102]);
                get_3_isog(pts[1117], A24minus[104], A24plus[104], coeff[103]);
                eval_3_isog_mod(pts[1114], pts[1119], coeff[102]);
                eval_3_isog_mod(pts[1018], pts[1121], coeff[95]);
                lock[114][1] = 0;
                while(lock[114][0]) {
                    #pragma omp flush(lock[114][0])
                }

                eval_3_isog_mod(pts[1118], pts[1123], coeff[103]);
                get_3_isog(pts[1123], A24minus[105], A24plus[105], coeff[104]);
                eval_3_isog_mod(pts[1120], pts[1125], coeff[100]);
                lock[115][1] = 0;
                while(lock[115][0]) {
                    #pragma omp flush(lock[115][0])
                }

                eval_3_isog_mod(pts[1122], pts[1127], coeff[77]);
                eval_3_isog_mod(pts[1126], pts[1130], coeff[97]);
                eval_3_isog_mod(pts[1127], pts[1131], coeff[78]);
                eval_3_isog_mod(pts[1130], pts[1134], coeff[98]);
                eval_3_isog_mod(pts[1131], pts[1135], coeff[79]);
                eval_3_isog_mod(pts[1134], pts[1138], coeff[99]);
                eval_3_isog_mod(pts[1135], pts[1139], coeff[80]);
                eval_3_isog_mod(pts[1138], pts[1142], coeff[100]);
                eval_3_isog_mod(pts[1139], pts[1143], coeff[81]);
                lock[116][1] = 0;
                while(lock[116][0]) {
                    #pragma omp flush(lock[116][0])
                }

                eval_3_isog_mod(pts[1128], pts[1146], coeff[105]);
                eval_3_isog_mod(pts[1141], pts[1147], coeff[105]);
                eval_3_isog_mod(pts[1143], pts[1149], coeff[82]);
                lock[117][1] = 0;
                while(lock[117][0]) {
                    #pragma omp flush(lock[117][0])
                }

                eval_3_isog_mod(pts[1147], pts[1152], coeff[106]);
                eval_3_isog_mod(pts[998], pts[1154], coeff[95]);
                eval_3_isog_mod(pts[1149], pts[1155], coeff[83]);
                eval_3_isog_mod(pts[1152], pts[1157], coeff[107]);
                lock[118][1] = 0;
                while(lock[118][0]) {
                    #pragma omp flush(lock[118][0])
                }

                eval_3_isog_mod(pts[1154], pts[1159], coeff[96]);
                eval_3_isog_mod(pts[1158], pts[1162], coeff[104]);
                eval_3_isog_mod(pts[1159], pts[1163], coeff[97]);
                eval_3_isog_mod(pts[1162], pts[1166], coeff[105]);
                eval_3_isog_mod(pts[1163], pts[1167], coeff[98]);
                eval_3_isog_mod(pts[1166], pts[1170], coeff[106]);
                eval_3_isog_mod(pts[1167], pts[1171], coeff[99]);
                eval_3_isog_mod(pts[1170], pts[1174], coeff[107]);
                eval_3_isog_mod(pts[1171], pts[1175], coeff[100]);
                eval_3_isog_mod(pts[1174], pts[1178], coeff[108]);
                eval_3_isog_mod(pts[1175], pts[1179], coeff[101]);
                lock[119][1] = 0;
                while(lock[119][0]) {
                    #pragma omp flush(lock[119][0])
                }

                eval_3_isog_mod(pts[1173], pts[1181], coeff[109]);
                get_3_isog(pts[1181], A24minus[111], A24plus[111], coeff[110]);
                eval_3_isog_mod(pts[1165], pts[1183], coeff[109]);
                eval_3_isog_mod(pts[1178], pts[1185], coeff[109]);
                lock[120][1] = 0;
                while(lock[120][0]) {
                    #pragma omp flush(lock[120][0])
                }

                eval_3_isog_mod(pts[1180], pts[1187], coeff[90]);
                eval_3_isog_mod(pts[1183], pts[1189], coeff[110]);
                eval_3_isog_mod(pts[1185], pts[1191], coeff[110]);
                lock[121][1] = 0;
                while(lock[121][0]) {
                    #pragma omp flush(lock[121][0])
                }

                eval_3_isog_mod(pts[1189], pts[1194], coeff[111]);
                get_3_isog(pts[1194], A24minus[113], A24plus[113], coeff[112]);
                eval_3_isog_mod(pts[1190], pts[1195], coeff[111]);
                eval_3_isog_mod(pts[1192], pts[1197], coeff[104]);
                lock[122][1] = 0;
                while(lock[122][0]) {
                    #pragma omp flush(lock[122][0])
                }

                eval_3_isog_mod(pts[1196], pts[1200], coeff[112]);
                eval_3_isog_mod(pts[1198], pts[1202], coeff[93]);
                lock[123][1] = 0;
                while(lock[123][0]) {
                    #pragma omp flush(lock[123][0])
                }

                eval_3_isog_mod(pts[1201], pts[1204], coeff[106]);
                eval_3_isog_mod(pts[1202], pts[1205], coeff[94]);
                lock[124][1] = 0;
                while(lock[124][0]) {
                    #pragma omp flush(lock[124][0])
                }

                eval_3_isog_mod(pts[1204], pts[1207], coeff[107]);
                eval_3_isog_mod(pts[1207], pts[1210], coeff[108]);
                lock[125][1] = 0;
                while(lock[125][0]) {
                    #pragma omp flush(lock[125][0])
                }

                eval_3_isog_mod(pts[1208], pts[1211], coeff[96]);
                eval_3_isog_mod(pts[1211], pts[1214], coeff[97]);
                eval_3_isog_mod(pts[0], pts[1215], coeff[0]);
                eval_3_isog_mod(pts[1214], pts[1218], coeff[98]);
                eval_3_isog_mod(pts[1215], pts[1219], coeff[1]);
                eval_3_isog_mod(pts[1218], pts[1222], coeff[99]);
                eval_3_isog_mod(pts[1219], pts[1223], coeff[2]);
                eval_3_isog_mod(pts[1222], pts[1226], coeff[100]);
                eval_3_isog_mod(pts[1223], pts[1227], coeff[3]);
                lock[126][1] = 0;
                while(lock[126][0]) {
                    #pragma omp flush(lock[126][0])
                }

                eval_3_isog_mod(pts[1216], pts[1229], coeff[114]);
                eval_3_isog_mod(pts[1203], pts[1232], coeff[114]);
                eval_3_isog_mod(pts[1225], pts[1233], coeff[113]);
                eval_3_isog_mod(pts[1229], pts[1236], coeff[115]);
                get_3_isog(pts[1236], A24minus[117], A24plus[117], coeff[116]);
                lock[127][1] = 0;
                while(lock[127][0]) {
                    #pragma omp flush(lock[127][0])
                }

                eval_3_isog_mod(pts[1230], pts[1237], coeff[115]);
                eval_3_isog_mod(pts[1232], pts[1239], coeff[115]);
                eval_3_isog_mod(pts[1235], pts[1242], coeff[5]);
                eval_3_isog_mod(pts[1237], pts[1243], coeff[116]);
                get_3_isog(pts[1243], A24minus[118], A24plus[118], coeff[117]);
                eval_3_isog_mod(pts[1239], pts[1245], coeff[116]);
                eval_3_isog_mod(pts[1242], pts[1248], coeff[6]);
                lock[128][1] = 0;
                while(lock[128][0]) {
                    #pragma omp flush(lock[128][0])
                }

                eval_3_isog_mod(pts[1245], pts[1250], coeff[117]);
                eval_3_isog_mod(pts[1246], pts[1251], coeff[116]);
                lock[129][1] = 0;
                while(lock[129][0]) {
                    #pragma omp flush(lock[129][0])
                }

                eval_3_isog_mod(pts[1250], pts[1254], coeff[118]);
                eval_3_isog_mod(pts[1252], pts[1256], coeff[105]);
                xTPLe(pts[1254], pts[1258], A24minus[119], A24plus[119], 1);
                get_3_isog(pts[1258], A24minus[120], A24plus[120], coeff[119]);
                eval_3_isog_mod(pts[1256], pts[1260], coeff[106]);
                eval_3_isog_mod(pts[1254], pts[1262], coeff[119]);
                get_3_isog(pts[1262], A24minus[121], A24plus[121], coeff[120]);
                lock[130][1] = 0;
                while(lock[130][0]) {
                    #pragma omp flush(lock[130][0])
                }

                eval_3_isog_mod(pts[1259], pts[1263], coeff[119]);
                eval_3_isog_mod(pts[1263], pts[1266], coeff[120]);
                lock[131][1] = 0;
                while(lock[131][0]) {
                    #pragma omp flush(lock[131][0])
                }

                eval_3_isog_mod(pts[1264], pts[1267], coeff[108]);
                eval_3_isog_mod(pts[1267], pts[1270], coeff[109]);
                lock[132][1] = 0;
                while(lock[132][0]) {
                    #pragma omp flush(lock[132][0])
                }

                xTPLe(pts[1269], pts[1272], A24minus[121], A24plus[121], 1);
                eval_3_isog_mod(pts[1270], pts[1273], coeff[110]);
                lock[133][1] = 0;
                while(lock[133][0]) {
                    #pragma omp flush(lock[133][0])
                }

                xTPLe(pts[1272], pts[1275], A24minus[121], A24plus[121], 1);
                xTPLe(pts[1275], pts[1278], A24minus[121], A24plus[121], 1);
                lock[134][1] = 0;
                while(lock[134][0]) {
                    #pragma omp flush(lock[134][0])
                }

                eval_3_isog_mod(pts[1276], pts[1279], coeff[112]);
                eval_3_isog_mod(pts[1279], pts[1282], coeff[113]);
                lock[135][1] = 0;
                while(lock[135][0]) {
                    #pragma omp flush(lock[135][0])
                }

                xTPLe(pts[1281], pts[1284], A24minus[121], A24plus[121], 1);
                eval_3_isog_mod(pts[1282], pts[1285], coeff[114]);
                lock[136][1] = 0;
                while(lock[136][0]) {
                    #pragma omp flush(lock[136][0])
                }

                xTPLe(pts[1284], pts[1287], A24minus[121], A24plus[121], 1);
                xTPLe(pts[1287], pts[1290], A24minus[121], A24plus[121], 1);
                lock[137][1] = 0;
                while(lock[137][0]) {
                    #pragma omp flush(lock[137][0])
                }

                eval_3_isog_mod(pts[1289], pts[1292], coeff[19]);
                xTPLe(pts[1290], pts[1293], A24minus[121], A24plus[121], 1);
                get_3_isog(pts[1293], A24minus[122], A24plus[122], coeff[121]);
                lock[138][1] = 0;
                while(lock[138][0]) {
                    #pragma omp flush(lock[138][0])
                }

                eval_3_isog_mod(pts[1292], pts[1295], coeff[20]);
                eval_3_isog_mod(pts[1284], pts[1298], coeff[121]);
                eval_3_isog_mod(pts[1281], pts[1299], coeff[121]);
                eval_3_isog_mod(pts[1295], pts[1302], coeff[21]);
                lock[139][1] = 0;
                while(lock[139][0]) {
                    #pragma omp flush(lock[139][0])
                }

                eval_3_isog_mod(pts[1298], pts[1304], coeff[122]);
                eval_3_isog_mod(pts[1299], pts[1305], coeff[122]);
                eval_3_isog_mod(pts[1266], pts[1307], coeff[121]);
                lock[140][1] = 0;
                while(lock[140][0]) {
                    #pragma omp flush(lock[140][0])
                }

                eval_3_isog_mod(pts[1304], pts[1310], coeff[123]);
                get_3_isog(pts[1310], A24minus[125], A24plus[125], coeff[124]);
                eval_3_isog_mod(pts[1306], pts[1312], coeff[123]);
                eval_3_isog_mod(pts[1308], pts[1314], coeff[120]);
                lock[141][1] = 0;
                while(lock[141][0]) {
                    #pragma omp flush(lock[141][0])
                }

                eval_3_isog_mod(pts[1309], pts[1315], coeff[23]);
                eval_3_isog_mod(pts[1313], pts[1318], coeff[123]);
                eval_3_isog_mod(pts[1315], pts[1320], coeff[24]);
                eval_3_isog_mod(pts[1318], pts[1322], coeff[124]);
                eval_3_isog_mod(pts[1320], pts[1324], coeff[25]);
                lock[142][1] = 0;
                while(lock[142][0]) {
                    #pragma omp flush(lock[142][0])
                }

                xTPLe(pts[1321], pts[1325], A24minus[126], A24plus[126], 1);
                get_3_isog(pts[1325], A24minus[127], A24plus[127], coeff[126]);
                eval_3_isog_mod(pts[1323], pts[1327], coeff[123]);
                lock[143][1] = 0;
                while(lock[143][0]) {
                    #pragma omp flush(lock[143][0])
                }

                eval_3_isog_mod(pts[1321], pts[1329], coeff[126]);
                get_3_isog(pts[1329], A24minus[128], A24plus[128], coeff[127]);
                eval_3_isog_mod(pts[1327], pts[1331], coeff[124]);
                lock[144][1] = 0;
                while(lock[144][0]) {
                    #pragma omp flush(lock[144][0])
                }

                eval_3_isog_mod(pts[1331], pts[1334], coeff[125]);
                eval_3_isog_mod(pts[1332], pts[1335], coeff[28]);
                lock[145][1] = 0;
                while(lock[145][0]) {
                    #pragma omp flush(lock[145][0])
                }

                eval_3_isog_mod(pts[1335], pts[1338], coeff[29]);
                xTPLe(pts[1336], pts[1339], A24minus[128], A24plus[128], 1);
                get_3_isog(pts[1339], A24minus[129], A24plus[129], coeff[128]);
                lock[146][1] = 0;
                while(lock[146][0]) {
                    #pragma omp flush(lock[146][0])
                }

                eval_3_isog_mod(pts[1338], pts[1341], coeff[30]);
                eval_3_isog_mod(pts[1333], pts[1343], coeff[128]);
                lock[147][1] = 0;
                while(lock[147][0]) {
                    #pragma omp flush(lock[147][0])
                }

                eval_3_isog_mod(pts[1343], pts[1346], coeff[129]);
                get_3_isog(pts[1346], A24minus[131], A24plus[131], coeff[130]);
                eval_3_isog_mod(pts[1344], pts[1347], coeff[129]);
                eval_3_isog_mod(pts[1347], pts[1349], coeff[130]);
                xTPLe(pts[1349], pts[1351], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1351], pts[1353], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1353], pts[1355], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1355], pts[1357], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1357], pts[1359], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1359], pts[1361], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1361], pts[1363], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1363], pts[1365], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1365], pts[1367], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1367], pts[1369], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1369], pts[1371], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1371], pts[1373], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1373], pts[1375], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1375], pts[1377], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1377], pts[1379], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1379], pts[1381], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1381], pts[1383], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1383], pts[1385], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1385], pts[1387], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1387], pts[1389], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1389], pts[1391], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1391], pts[1393], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1393], pts[1395], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1395], pts[1397], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1397], pts[1399], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1399], pts[1401], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1401], pts[1403], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1403], pts[1405], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1405], pts[1407], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1407], pts[1409], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1409], pts[1411], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1411], pts[1413], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1413], pts[1415], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1415], pts[1417], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1417], pts[1419], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1419], pts[1421], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1421], pts[1423], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1423], pts[1425], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1425], pts[1427], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1427], pts[1429], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1429], pts[1431], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1431], pts[1433], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1433], pts[1435], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1435], pts[1437], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1437], pts[1439], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1439], pts[1441], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1441], pts[1443], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1443], pts[1445], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1445], pts[1447], A24minus[131], A24plus[131], 1);
                get_3_isog(pts[1447], A24minus[132], A24plus[132], coeff[131]);
                lock[148][1] = 0;
                while(lock[148][0]) {
                    #pragma omp flush(lock[148][0])
                }

                eval_3_isog_mod(pts[1445], pts[1449], coeff[131]);
                get_3_isog(pts[1449], A24minus[133], A24plus[133], coeff[132]);
                eval_3_isog_mod(pts[1439], pts[1452], coeff[131]);
                eval_3_isog_mod(pts[1448], pts[1454], coeff[83]);
                lock[149][1] = 0;
                while(lock[149][0]) {
                    #pragma omp flush(lock[149][0])
                }

                eval_3_isog_mod(pts[1451], pts[1456], coeff[132]);
                eval_3_isog_mod(pts[1452], pts[1457], coeff[132]);
                eval_3_isog_mod(pts[1454], pts[1460], coeff[84]);
                lock[150][1] = 0;
                while(lock[150][0]) {
                    #pragma omp flush(lock[150][0])
                }

                eval_3_isog_mod(pts[1456], pts[1461], coeff[133]);
                get_3_isog(pts[1461], A24minus[135], A24plus[135], coeff[134]);
                eval_3_isog_mod(pts[1459], pts[1464], coeff[132]);
                lock[151][1] = 0;
                while(lock[151][0]) {
                    #pragma omp flush(lock[151][0])
                }

                eval_3_isog_mod(pts[1462], pts[1466], coeff[134]);
                get_3_isog(pts[1466], A24minus[136], A24plus[136], coeff[135]);
                eval_3_isog_mod(pts[1464], pts[1468], coeff[133]);
                eval_3_isog_mod(pts[1421], pts[1469], coeff[131]);
                lock[152][1] = 0;
                while(lock[152][0]) {
                    #pragma omp flush(lock[152][0])
                }

                eval_3_isog_mod(pts[1468], pts[1472], coeff[134]);
                eval_3_isog_mod(pts[1469], pts[1473], coeff[132]);
                eval_3_isog_mod(pts[1472], pts[1476], coeff[135]);
                eval_3_isog_mod(pts[1473], pts[1477], coeff[133]);
                lock[153][1] = 0;
                while(lock[153][0]) {
                    #pragma omp flush(lock[153][0])
                }

                eval_3_isog_mod(pts[1471], pts[1479], coeff[136]);
                get_3_isog(pts[1479], A24minus[138], A24plus[138], coeff[137]);
                eval_3_isog_mod(pts[1411], pts[1482], coeff[131]);
                lock[154][1] = 0;
                while(lock[154][0]) {
                    #pragma omp flush(lock[154][0])
                }

                eval_3_isog_mod(pts[1480], pts[1484], coeff[137]);
                eval_3_isog_mod(pts[1481], pts[1485], coeff[135]);
                xTPLe(pts[1484], pts[1488], A24minus[138], A24plus[138], 1);
                eval_3_isog_mod(pts[1485], pts[1489], coeff[136]);
                xTPLe(pts[1488], pts[1492], A24minus[138], A24plus[138], 1);
                get_3_isog(pts[1492], A24minus[139], A24plus[139], coeff[138]);
                eval_3_isog_mod(pts[1489], pts[1493], coeff[137]);
                eval_3_isog_mod(pts[1488], pts[1496], coeff[138]);
                get_3_isog(pts[1496], A24minus[140], A24plus[140], coeff[139]);
                lock[155][1] = 0;
                while(lock[155][0]) {
                    #pragma omp flush(lock[155][0])
                }

                eval_3_isog_mod(pts[1493], pts[1498], coeff[138]);
                eval_3_isog_mod(pts[1397], pts[1500], coeff[131]);
                eval_3_isog_mod(pts[1495], pts[1501], coeff[93]);
                eval_3_isog_mod(pts[1498], pts[1503], coeff[139]);
                lock[156][1] = 0;
                while(lock[156][0]) {
                    #pragma omp flush(lock[156][0])
                }

                eval_3_isog_mod(pts[1501], pts[1506], coeff[94]);
                eval_3_isog_mod(pts[1504], pts[1508], coeff[137]);
                eval_3_isog_mod(pts[1506], pts[1510], coeff[95]);
                eval_3_isog_mod(pts[1508], pts[1512], coeff[138]);
                eval_3_isog_mod(pts[1510], pts[1514], coeff[96]);
                eval_3_isog_mod(pts[1512], pts[1516], coeff[139]);
                eval_3_isog_mod(pts[1514], pts[1518], coeff[97]);
                eval_3_isog_mod(pts[1516], pts[1520], coeff[140]);
                eval_3_isog_mod(pts[1518], pts[1522], coeff[98]);
                lock[157][1] = 0;
                while(lock[157][0]) {
                    #pragma omp flush(lock[157][0])
                }

                eval_3_isog_mod(pts[1515], pts[1523], coeff[141]);
                get_3_isog(pts[1523], A24minus[143], A24plus[143], coeff[142]);
                eval_3_isog_mod(pts[1520], pts[1526], coeff[141]);
                eval_3_isog_mod(pts[1521], pts[1527], coeff[137]);
                lock[158][1] = 0;
                while(lock[158][0]) {
                    #pragma omp flush(lock[158][0])
                }

                eval_3_isog_mod(pts[1525], pts[1530], coeff[142]);
                eval_3_isog_mod(pts[1527], pts[1532], coeff[138]);
                eval_3_isog_mod(pts[1377], pts[1533], coeff[131]);
                lock[159][1] = 0;
                while(lock[159][0]) {
                    #pragma omp flush(lock[159][0])
                }

                eval_3_isog_mod(pts[1530], pts[1535], coeff[143]);
                get_3_isog(pts[1535], A24minus[145], A24plus[145], coeff[144]);
                eval_3_isog_mod(pts[1532], pts[1537], coeff[139]);
                lock[160][1] = 0;
                while(lock[160][0]) {
                    #pragma omp flush(lock[160][0])
                }

                eval_3_isog_mod(pts[1536], pts[1540], coeff[144]);
                eval_3_isog_mod(pts[1537], pts[1541], coeff[140]);
                xTPLe(pts[1540], pts[1544], A24minus[145], A24plus[145], 1);
                eval_3_isog_mod(pts[1541], pts[1545], coeff[141]);
                xTPLe(pts[1544], pts[1548], A24minus[145], A24plus[145], 1);
                eval_3_isog_mod(pts[1545], pts[1549], coeff[142]);
                xTPLe(pts[1548], pts[1552], A24minus[145], A24plus[145], 1);
                eval_3_isog_mod(pts[1549], pts[1553], coeff[143]);
                xTPLe(pts[1552], pts[1556], A24minus[145], A24plus[145], 1);
                get_3_isog(pts[1556], A24minus[146], A24plus[146], coeff[145]);
                eval_3_isog_mod(pts[1553], pts[1557], coeff[144]);
                eval_3_isog_mod(pts[1552], pts[1560], coeff[145]);
                get_3_isog(pts[1560], A24minus[147], A24plus[147], coeff[146]);
                lock[161][1] = 0;
                while(lock[161][0]) {
                    #pragma omp flush(lock[161][0])
                }

                eval_3_isog_mod(pts[1548], pts[1561], coeff[145]);
                eval_3_isog_mod(pts[1540], pts[1563], coeff[145]);
                eval_3_isog_mod(pts[1558], pts[1565], coeff[138]);
                eval_3_isog_mod(pts[1561], pts[1567], coeff[146]);
                get_3_isog(pts[1567], A24minus[148], A24plus[148], coeff[147]);
                eval_3_isog_mod(pts[1563], pts[1569], coeff[146]);
                eval_3_isog_mod(pts[1565], pts[1571], coeff[139]);
                lock[162][1] = 0;
                while(lock[162][0]) {
                    #pragma omp flush(lock[162][0])
                }

                eval_3_isog_mod(pts[1568], pts[1573], coeff[147]);
                get_3_isog(pts[1573], A24minus[149], A24plus[149], coeff[148]);
                eval_3_isog_mod(pts[1570], pts[1575], coeff[147]);
                lock[163][1] = 0;
                while(lock[163][0]) {
                    #pragma omp flush(lock[163][0])
                }

                eval_3_isog_mod(pts[1572], pts[1577], coeff[109]);
                eval_3_isog_mod(pts[1576], pts[1580], coeff[141]);
                eval_3_isog_mod(pts[1577], pts[1581], coeff[110]);
                lock[164][1] = 0;
                while(lock[164][0]) {
                    #pragma omp flush(lock[164][0])
                }

                eval_3_isog_mod(pts[1580], pts[1583], coeff[142]);
                eval_3_isog_mod(pts[1583], pts[1586], coeff[143]);
                eval_3_isog_mod(pts[1349], pts[1587], coeff[131]);
                eval_3_isog_mod(pts[1586], pts[1590], coeff[144]);
                eval_3_isog_mod(pts[1587], pts[1591], coeff[132]);
                eval_3_isog_mod(pts[1590], pts[1594], coeff[145]);
                eval_3_isog_mod(pts[1591], pts[1595], coeff[133]);
                eval_3_isog_mod(pts[1594], pts[1598], coeff[146]);
                eval_3_isog_mod(pts[1595], pts[1599], coeff[134]);
                eval_3_isog_mod(pts[1598], pts[1602], coeff[147]);
                eval_3_isog_mod(pts[1599], pts[1603], coeff[135]);
                eval_3_isog_mod(pts[1602], pts[1606], coeff[148]);
                eval_3_isog_mod(pts[1603], pts[1607], coeff[136]);
                lock[165][1] = 0;
                while(lock[165][0]) {
                    #pragma omp flush(lock[165][0])
                }

                eval_3_isog_mod(pts[1597], pts[1610], coeff[150]);
                eval_3_isog_mod(pts[1589], pts[1612], coeff[150]);
                eval_3_isog_mod(pts[1582], pts[1613], coeff[150]);
                eval_3_isog_mod(pts[1607], pts[1615], coeff[137]);
                lock[166][1] = 0;
                while(lock[166][0]) {
                    #pragma omp flush(lock[166][0])
                }

                eval_3_isog_mod(pts[1610], pts[1617], coeff[151]);
                get_3_isog(pts[1617], A24minus[153], A24plus[153], coeff[152]);
                eval_3_isog_mod(pts[1613], pts[1620], coeff[151]);
                eval_3_isog_mod(pts[1614], pts[1621], coeff[150]);
                lock[167][1] = 0;
                while(lock[167][0]) {
                    #pragma omp flush(lock[167][0])
                }

                eval_3_isog_mod(pts[1616], pts[1623], coeff[119]);
                eval_3_isog_mod(pts[1620], pts[1626], coeff[152]);
                eval_3_isog_mod(pts[1621], pts[1627], coeff[151]);
                eval_3_isog_mod(pts[1623], pts[1629], coeff[120]);
                lock[168][1] = 0;
                while(lock[168][0]) {
                    #pragma omp flush(lock[168][0])
                }

                eval_3_isog_mod(pts[1626], pts[1631], coeff[153]);
                eval_3_isog_mod(pts[1629], pts[1634], coeff[121]);
                eval_3_isog_mod(pts[1631], pts[1635], coeff[154]);
                eval_3_isog_mod(pts[1634], pts[1638], coeff[122]);
                xTPLe(pts[1635], pts[1639], A24minus[155], A24plus[155], 1);
                get_3_isog(pts[1639], A24minus[156], A24plus[156], coeff[155]);
                eval_3_isog_mod(pts[1638], pts[1642], coeff[123]);
                lock[169][1] = 0;
                while(lock[169][0]) {
                    #pragma omp flush(lock[169][0])
                }

                eval_3_isog_mod(pts[1640], pts[1644], coeff[155]);
                eval_3_isog_mod(pts[1642], pts[1646], coeff[124]);
                lock[170][1] = 0;
                while(lock[170][0]) {
                    #pragma omp flush(lock[170][0])
                }

                eval_3_isog_mod(pts[1645], pts[1648], coeff[144]);
                eval_3_isog_mod(pts[1646], pts[1649], coeff[125]);
                lock[171][1] = 0;
                while(lock[171][0]) {
                    #pragma omp flush(lock[171][0])
                }

                eval_3_isog_mod(pts[1648], pts[1651], coeff[145]);
                eval_3_isog_mod(pts[1651], pts[1654], coeff[146]);
                lock[172][1] = 0;
                while(lock[172][0]) {
                    #pragma omp flush(lock[172][0])
                }

                xTPLe(pts[1653], pts[1656], A24minus[157], A24plus[157], 1);
                eval_3_isog_mod(pts[1654], pts[1657], coeff[147]);
                lock[173][1] = 0;
                while(lock[173][0]) {
                    #pragma omp flush(lock[173][0])
                }

                eval_3_isog_mod(pts[1657], pts[1660], coeff[148]);
                eval_3_isog_mod(pts[1658], pts[1661], coeff[129]);
                lock[174][1] = 0;
                while(lock[174][0]) {
                    #pragma omp flush(lock[174][0])
                }

                eval_3_isog_mod(pts[1660], pts[1663], coeff[149]);
                eval_3_isog_mod(pts[1663], pts[1666], coeff[150]);
                lock[175][1] = 0;
                while(lock[175][0]) {
                    #pragma omp flush(lock[175][0])
                }

                eval_3_isog_mod(pts[1664], pts[1667], coeff[131]);
                eval_3_isog_mod(pts[1667], pts[1670], coeff[132]);
                lock[176][1] = 0;
                while(lock[176][0]) {
                    #pragma omp flush(lock[176][0])
                }

                eval_3_isog_mod(pts[1669], pts[1672], coeff[152]);
                eval_3_isog_mod(pts[1670], pts[1673], coeff[133]);
                lock[177][1] = 0;
                while(lock[177][0]) {
                    #pragma omp flush(lock[177][0])
                }

                eval_3_isog_mod(pts[1672], pts[1675], coeff[153]);
                eval_3_isog_mod(pts[1671], pts[1677], coeff[157]);
                get_3_isog(pts[1677], A24minus[159], A24plus[159], coeff[158]);
                eval_3_isog_mod(pts[1665], pts[1679], coeff[157]);
                eval_3_isog_mod(pts[1675], pts[1682], coeff[154]);
                lock[178][1] = 0;
                while(lock[178][0]) {
                    #pragma omp flush(lock[178][0])
                }

                eval_3_isog_mod(pts[1678], pts[1684], coeff[158]);
                get_3_isog(pts[1684], A24minus[160], A24plus[160], coeff[159]);
                eval_3_isog_mod(pts[1679], pts[1685], coeff[158]);
                eval_3_isog_mod(pts[1681], pts[1687], coeff[158]);
                eval_3_isog_mod(pts[1682], pts[1689], coeff[155]);
                lock[179][1] = 0;
                while(lock[179][0]) {
                    #pragma omp flush(lock[179][0])
                }

                eval_3_isog_mod(pts[1686], pts[1692], coeff[159]);
                eval_3_isog_mod(pts[1687], pts[1693], coeff[159]);
                eval_3_isog_mod(pts[1689], pts[1695], coeff[156]);
                lock[180][1] = 0;
                while(lock[180][0]) {
                    #pragma omp flush(lock[180][0])
                }

                eval_3_isog_mod(pts[1693], pts[1698], coeff[160]);
                eval_3_isog_mod(pts[1694], pts[1699], coeff[159]);
                lock[181][1] = 0;
                while(lock[181][0]) {
                    #pragma omp flush(lock[181][0])
                }

                eval_3_isog_mod(pts[1698], pts[1702], coeff[161]);
                eval_3_isog_mod(pts[1699], pts[1703], coeff[160]);
                xTPLe(pts[1702], pts[1706], A24minus[162], A24plus[162], 1);
                get_3_isog(pts[1706], A24minus[163], A24plus[163], coeff[162]);
                eval_3_isog_mod(pts[1703], pts[1707], coeff[161]);
                eval_3_isog_mod(pts[1702], pts[1710], coeff[162]);
                get_3_isog(pts[1710], A24minus[164], A24plus[164], coeff[163]);
                eval_3_isog_mod(pts[1707], pts[1711], coeff[162]);
                eval_3_isog_mod(pts[1711], pts[1714], coeff[163]);
                lock[182][1] = 0;
                while(lock[182][0]) {
                    #pragma omp flush(lock[182][0])
                }

                eval_3_isog_mod(pts[1712], pts[1715], coeff[161]);
                eval_3_isog_mod(pts[1715], pts[1718], coeff[162]);
                lock[183][1] = 0;
                while(lock[183][0]) {
                    #pragma omp flush(lock[183][0])
                }

                eval_3_isog_mod(pts[1716], pts[1719], coeff[143]);
                eval_3_isog_mod(pts[1719], pts[1722], coeff[144]);
                lock[184][1] = 0;
                while(lock[184][0]) {
                    #pragma omp flush(lock[184][0])
                }

                eval_3_isog_mod(pts[1714], pts[1724], coeff[164]);
                eval_3_isog_mod(pts[1721], pts[1725], coeff[164]);
                lock[185][1] = 0;
                while(lock[185][0]) {
                    #pragma omp flush(lock[185][0])
                }

                eval_3_isog_mod(pts[1724], pts[1727], coeff[165]);
                get_3_isog(pts[1727], A24minus[167], A24plus[167], coeff[166]);
                lock[186][1] = 0;
                while(lock[186][0]) {
                    #pragma omp flush(lock[186][0])
                }

                eval_3_isog_mod(pts[1726], pts[1729], coeff[146]);
                eval_3_isog_mod(pts[1729], pts[1731], coeff[147]);
                eval_3_isog_mod(pts[1731], pts[1733], coeff[148]);
                eval_3_isog_mod(pts[1733], pts[1735], coeff[149]);
                eval_3_isog_mod(pts[1735], pts[1737], coeff[150]);
                eval_3_isog_mod(pts[1737], pts[1739], coeff[151]);
                eval_3_isog_mod(pts[1739], pts[1741], coeff[152]);
                eval_3_isog_mod(pts[1741], pts[1743], coeff[153]);
                eval_3_isog_mod(pts[1743], pts[1745], coeff[154]);
                eval_3_isog_mod(pts[1745], pts[1747], coeff[155]);
                eval_3_isog_mod(pts[1747], pts[1749], coeff[156]);
                eval_3_isog_mod(pts[1749], pts[1751], coeff[157]);
                eval_3_isog_mod(pts[1751], pts[1753], coeff[158]);
                eval_3_isog_mod(pts[1753], pts[1755], coeff[159]);
                eval_3_isog_mod(pts[1755], pts[1757], coeff[160]);
                lock[187][1] = 0;
                while(lock[187][0]) {
                    #pragma omp flush(lock[187][0])
                }

                eval_3_isog_mod(pts[1752], pts[1759], coeff[167]);
                eval_3_isog_mod(pts[1744], pts[1762], coeff[167]);
                eval_3_isog_mod(pts[1759], pts[1764], coeff[168]);
                get_3_isog(pts[1764], A24minus[170], A24plus[170], coeff[169]);
                lock[188][1] = 0;
                while(lock[188][0]) {
                    #pragma omp flush(lock[188][0])
                }

                eval_3_isog_mod(pts[1761], pts[1766], coeff[168]);
                eval_3_isog_mod(pts[1738], pts[1768], coeff[167]);
                eval_3_isog_mod(pts[1763], pts[1769], coeff[162]);
                eval_3_isog_mod(pts[1766], pts[1771], coeff[169]);
                lock[189][1] = 0;
                while(lock[189][0]) {
                    #pragma omp flush(lock[189][0])
                }

                eval_3_isog_mod(pts[1769], pts[1774], coeff[163]);
                eval_3_isog_mod(pts[1771], pts[1775], coeff[170]);
                get_3_isog(pts[1775], A24minus[172], A24plus[172], coeff[171]);
                eval_3_isog_mod(pts[1730], pts[1778], coeff[167]);
                lock[190][1] = 0;
                while(lock[190][0]) {
                    #pragma omp flush(lock[190][0])
                }

                eval_3_isog_mod(pts[1776], pts[1780], coeff[171]);
                eval_3_isog_mod(pts[1777], pts[1781], coeff[170]);
                xTPLe(pts[1780], pts[1784], A24minus[172], A24plus[172], 1);
                get_3_isog(pts[1784], A24minus[173], A24plus[173], coeff[172]);
                eval_3_isog_mod(pts[1781], pts[1785], coeff[171]);
                eval_3_isog_mod(pts[1780], pts[1788], coeff[172]);
                get_3_isog(pts[1788], A24minus[174], A24plus[174], coeff[173]);
                eval_3_isog_mod(pts[1785], pts[1789], coeff[172]);
                eval_3_isog_mod(pts[1789], pts[1792], coeff[173]);
                lock[191][1] = 0;
                while(lock[191][0]) {
                    #pragma omp flush(lock[191][0])
                }

                eval_3_isog_mod(pts[1790], pts[1793], coeff[171]);
                eval_3_isog_mod(pts[1793], pts[1796], coeff[172]);
                lock[192][1] = 0;
                while(lock[192][0]) {
                    #pragma omp flush(lock[192][0])
                }

                eval_3_isog_mod(pts[1794], pts[1797], coeff[169]);
                eval_3_isog_mod(pts[1797], pts[1800], coeff[170]);
                lock[193][1] = 0;
                while(lock[193][0]) {
                    #pragma omp flush(lock[193][0])
                }

                eval_3_isog_mod(pts[1792], pts[1802], coeff[174]);
                eval_3_isog_mod(pts[1800], pts[1804], coeff[171]);
                lock[194][1] = 0;
                while(lock[194][0]) {
                    #pragma omp flush(lock[194][0])
                }

                eval_3_isog_mod(pts[1802], pts[1805], coeff[175]);
                get_3_isog(pts[1805], A24minus[177], A24plus[177], coeff[176]);
                lock[195][1] = 0;
                while(lock[195][0]) {
                    #pragma omp flush(lock[195][0])
                }

                eval_3_isog_mod(pts[1804], pts[1807], coeff[172]);
                eval_3_isog_mod(pts[1807], pts[1809], coeff[173]);
                eval_3_isog_mod(pts[1809], pts[1811], coeff[174]);
                eval_3_isog_mod(pts[1811], pts[1813], coeff[175]);
                eval_3_isog_mod(pts[1813], pts[1815], coeff[176]);
                lock[196][1] = 0;
                while(lock[196][0]) {
                    #pragma omp flush(lock[196][0])
                }

                eval_3_isog_mod(pts[1808], pts[1818], coeff[177]);
                eval_3_isog_mod(pts[1815], pts[1819], coeff[177]);
                lock[197][1] = 0;
                while(lock[197][0]) {
                    #pragma omp flush(lock[197][0])
                }

                eval_3_isog_mod(pts[1818], pts[1821], coeff[178]);
                eval_3_isog_mod(pts[1821], pts[1823], coeff[179]);
                get_3_isog(pts[1823], A24minus[181], A24plus[181], coeff[180]);
                lock[198][1] = 0;
                while(lock[198][0]) {
                    #pragma omp flush(lock[198][0])
                }

                lock[199][1] = 0;
                while(lock[199][0]) {
                    #pragma omp flush(lock[199][0])
                }

                eval_3_isog_mod(pts[1881], pts[1883], coeff[181]);
                get_3_isog(pts[1883], A24minus[183], A24plus[183], coeff[182]);
                eval_3_isog_mod(pts[1879], pts[1885], coeff[181]);
                lock[200][1] = 0;
                while(lock[200][0]) {
                    #pragma omp flush(lock[200][0])
                }

                eval_3_isog_mod(pts[1884], pts[1888], coeff[182]);
                get_3_isog(pts[1888], A24minus[184], A24plus[184], coeff[183]);
                eval_3_isog_mod(pts[1886], pts[1890], coeff[182]);
                eval_3_isog_mod(pts[1873], pts[1892], coeff[181]);
                lock[201][1] = 0;
                while(lock[201][0]) {
                    #pragma omp flush(lock[201][0])
                }

                eval_3_isog_mod(pts[1890], pts[1894], coeff[183]);
                eval_3_isog_mod(pts[1892], pts[1896], coeff[182]);
                lock[202][1] = 0;
                while(lock[202][0]) {
                    #pragma omp flush(lock[202][0])
                }

                eval_3_isog_mod(pts[1894], pts[1897], coeff[184]);
                get_3_isog(pts[1897], A24minus[186], A24plus[186], coeff[185]);
                eval_3_isog_mod(pts[1869], pts[1900], coeff[181]);
                lock[203][1] = 0;
                while(lock[203][0]) {
                    #pragma omp flush(lock[203][0])
                }

                eval_3_isog_mod(pts[1899], pts[1902], coeff[184]);
                eval_3_isog_mod(pts[1900], pts[1903], coeff[182]);
                lock[204][1] = 0;
                while(lock[204][0]) {
                    #pragma omp flush(lock[204][0])
                }

                eval_3_isog_mod(pts[1903], pts[1906], coeff[183]);
                eval_3_isog_mod(pts[1901], pts[1907], coeff[186]);
                get_3_isog(pts[1907], A24minus[188], A24plus[188], coeff[187]);
                eval_3_isog_mod(pts[1906], pts[1909], coeff[184]);
                lock[205][1] = 0;
                while(lock[205][0]) {
                    #pragma omp flush(lock[205][0])
                }

                eval_3_isog_mod(pts[1908], pts[1911], coeff[187]);
                xTPLe(pts[1911], pts[1914], A24minus[188], A24plus[188], 1);
                lock[206][1] = 0;
                while(lock[206][0]) {
                    #pragma omp flush(lock[206][0])
                }

                eval_3_isog_mod(pts[1913], pts[1916], coeff[183]);
                xTPLe(pts[1914], pts[1917], A24minus[188], A24plus[188], 1);
                get_3_isog(pts[1917], A24minus[189], A24plus[189], coeff[188]);
                lock[207][1] = 0;
                while(lock[207][0]) {
                    #pragma omp flush(lock[207][0])
                }

                eval_3_isog_mod(pts[1914], pts[1920], coeff[188]);
                get_3_isog(pts[1920], A24minus[190], A24plus[190], coeff[189]);
                eval_3_isog_mod(pts[1918], pts[1922], coeff[188]);
                eval_3_isog_mod(pts[1858], pts[1924], coeff[181]);
                lock[208][1] = 0;
                while(lock[208][0]) {
                    #pragma omp flush(lock[208][0])
                }

                eval_3_isog_mod(pts[1922], pts[1926], coeff[189]);
                eval_3_isog_mod(pts[1924], pts[1928], coeff[182]);
                lock[209][1] = 0;
                while(lock[209][0]) {
                    #pragma omp flush(lock[209][0])
                }

                eval_3_isog_mod(pts[1926], pts[1929], coeff[190]);
                xTPLe(pts[1929], pts[1932], A24minus[191], A24plus[191], 1);
                lock[210][1] = 0;
                while(lock[210][0]) {
                    #pragma omp flush(lock[210][0])
                }

                eval_3_isog_mod(pts[1930], pts[1933], coeff[188]);
                eval_3_isog_mod(pts[1933], pts[1936], coeff[189]);
                lock[211][1] = 0;
                while(lock[211][0]) {
                    #pragma omp flush(lock[211][0])
                }

                xTPLe(pts[1935], pts[1938], A24minus[191], A24plus[191], 1);
                get_3_isog(pts[1938], A24minus[192], A24plus[192], coeff[191]);
                eval_3_isog_mod(pts[1936], pts[1939], coeff[190]);
                eval_3_isog_mod(pts[1935], pts[1942], coeff[191]);
                get_3_isog(pts[1942], A24minus[193], A24plus[193], coeff[192]);
                lock[212][1] = 0;
                while(lock[212][0]) {
                    #pragma omp flush(lock[212][0])
                }

                eval_3_isog_mod(pts[1932], pts[1943], coeff[191]);
                eval_3_isog_mod(pts[1939], pts[1945], coeff[191]);
                eval_3_isog_mod(pts[1943], pts[1948], coeff[192]);
                get_3_isog(pts[1948], A24minus[194], A24plus[194], coeff[193]);
                eval_3_isog_mod(pts[1945], pts[1950], coeff[192]);
                lock[213][1] = 0;
                while(lock[213][0]) {
                    #pragma omp flush(lock[213][0])
                }

                eval_3_isog_mod(pts[1947], pts[1952], coeff[183]);
                eval_3_isog_mod(pts[1949], pts[1953], coeff[193]);
                get_3_isog(pts[1953], A24minus[195], A24plus[195], coeff[194]);
                eval_3_isog_mod(pts[1952], pts[1956], coeff[184]);
                lock[214][1] = 0;
                while(lock[214][0]) {
                    #pragma omp flush(lock[214][0])
                }

                eval_3_isog_mod(pts[1955], pts[1958], coeff[190]);
                eval_3_isog_mod(pts[1956], pts[1959], coeff[185]);
                lock[215][1] = 0;
                while(lock[215][0]) {
                    #pragma omp flush(lock[215][0])
                }

                eval_3_isog_mod(pts[1958], pts[1961], coeff[191]);
                eval_3_isog_mod(pts[1961], pts[1964], coeff[192]);
                lock[216][1] = 0;
                while(lock[216][0]) {
                    #pragma omp flush(lock[216][0])
                }

                xTPLe(pts[1963], pts[1966], A24minus[195], A24plus[195], 1);
                eval_3_isog_mod(pts[1964], pts[1967], coeff[193]);
                lock[217][1] = 0;
                while(lock[217][0]) {
                    #pragma omp flush(lock[217][0])
                }

                eval_3_isog_mod(pts[1967], pts[1970], coeff[194]);
                lock[218][1] = 0;
                while(lock[218][0]) {
                    #pragma omp flush(lock[218][0])
                }

                eval_3_isog_mod(pts[1966], pts[1972], coeff[195]);
                get_3_isog(pts[1972], A24minus[197], A24plus[197], coeff[196]);
                eval_3_isog_mod(pts[1963], pts[1973], coeff[195]);
                eval_3_isog_mod(pts[1957], pts[1975], coeff[195]);
                eval_3_isog_mod(pts[1973], pts[1978], coeff[196]);
                get_3_isog(pts[1978], A24minus[198], A24plus[198], coeff[197]);
                lock[219][1] = 0;
                while(lock[219][0]) {
                    #pragma omp flush(lock[219][0])
                }

                eval_3_isog_mod(pts[1975], pts[1980], coeff[196]);
                eval_3_isog_mod(pts[1977], pts[1982], coeff[191]);
                eval_3_isog_mod(pts[1980], pts[1984], coeff[197]);
                eval_3_isog_mod(pts[1982], pts[1986], coeff[192]);
                lock[220][1] = 0;
                while(lock[220][0]) {
                    #pragma omp flush(lock[220][0])
                }

                eval_3_isog_mod(pts[1985], pts[1988], coeff[198]);
                eval_3_isog_mod(pts[1986], pts[1989], coeff[193]);
                lock[221][1] = 0;
                while(lock[221][0]) {
                    #pragma omp flush(lock[221][0])
                }

                eval_3_isog_mod(pts[1988], pts[1991], coeff[199]);
                xTPLe(pts[1991], pts[1994], A24minus[200], A24plus[200], 1);
                lock[222][1] = 0;
                while(lock[222][0]) {
                    #pragma omp flush(lock[222][0])
                }

                eval_3_isog_mod(pts[1993], pts[1996], coeff[183]);
                xTPLe(pts[1994], pts[1997], A24minus[200], A24plus[200], 1);
                lock[223][1] = 0;
                while(lock[223][0]) {
                    #pragma omp flush(lock[223][0])
                }

                xTPLe(pts[1997], pts[2000], A24minus[200], A24plus[200], 1);
                eval_3_isog_mod(pts[1998], pts[2001], coeff[197]);
                lock[224][1] = 0;
                while(lock[224][0]) {
                    #pragma omp flush(lock[224][0])
                }

                xTPLe(pts[2000], pts[2003], A24minus[200], A24plus[200], 1);
                xTPLe(pts[2003], pts[2006], A24minus[200], A24plus[200], 1);
                get_3_isog(pts[2006], A24minus[201], A24plus[201], coeff[200]);
                lock[225][1] = 0;
                while(lock[225][0]) {
                    #pragma omp flush(lock[225][0])
                }

                eval_3_isog_mod(pts[2004], pts[2007], coeff[199]);
                eval_3_isog_mod(pts[2000], pts[2010], coeff[200]);
                eval_3_isog_mod(pts[1997], pts[2011], coeff[200]);
                eval_3_isog_mod(pts[2007], pts[2014], coeff[200]);
                lock[226][1] = 0;
                while(lock[226][0]) {
                    #pragma omp flush(lock[226][0])
                }

                eval_3_isog_mod(pts[2010], pts[2016], coeff[201]);
                get_3_isog(pts[2016], A24minus[203], A24plus[203], coeff[202]);
                eval_3_isog_mod(pts[2011], pts[2017], coeff[201]);
                eval_3_isog_mod(pts[2013], pts[2019], coeff[201]);
                eval_3_isog_mod(pts[2017], pts[2022], coeff[202]);
                get_3_isog(pts[2022], A24minus[204], A24plus[204], coeff[203]);
                lock[227][1] = 0;
                while(lock[227][0]) {
                    #pragma omp flush(lock[227][0])
                }

                eval_3_isog_mod(pts[2018], pts[2023], coeff[202]);
                eval_3_isog_mod(pts[2020], pts[2025], coeff[202]);
                eval_3_isog_mod(pts[2023], pts[2027], coeff[203]);
                get_3_isog(pts[2027], A24minus[205], A24plus[205], coeff[204]);
                eval_3_isog_mod(pts[2025], pts[2029], coeff[203]);
                lock[228][1] = 0;
                while(lock[228][0]) {
                    #pragma omp flush(lock[228][0])
                }

                eval_3_isog_mod(pts[2028], pts[2031], coeff[204]);
                get_3_isog(pts[2031], A24minus[206], A24plus[206], coeff[205]);
                lock[229][1] = 0;
                while(lock[229][0]) {
                    #pragma omp flush(lock[229][0])
                }

                eval_3_isog_mod(pts[2032], pts[2034], coeff[205]);
                xTPLe(pts[2034], pts[2036], A24minus[206], A24plus[206], 1);
                eval_3_isog_mod(pts[1825], pts[2038], coeff[181]);
                xTPLe(pts[2036], pts[2039], A24minus[206], A24plus[206], 1);
                lock[230][1] = 0;
                while(lock[230][0]) {
                    #pragma omp flush(lock[230][0])
                }

                xTPLe(pts[2039], pts[2042], A24minus[206], A24plus[206], 1);
                eval_3_isog_mod(pts[2040], pts[2043], coeff[196]);
                lock[231][1] = 0;
                while(lock[231][0]) {
                    #pragma omp flush(lock[231][0])
                }

                xTPLe(pts[2042], pts[2045], A24minus[206], A24plus[206], 1);
                xTPLe(pts[2045], pts[2048], A24minus[206], A24plus[206], 1);
                lock[232][1] = 0;
                while(lock[232][0]) {
                    #pragma omp flush(lock[232][0])
                }

                eval_3_isog_mod(pts[2046], pts[2049], coeff[198]);
                eval_3_isog_mod(pts[2049], pts[2052], coeff[199]);
                lock[233][1] = 0;
                while(lock[233][0]) {
                    #pragma omp flush(lock[233][0])
                }

                xTPLe(pts[2051], pts[2054], A24minus[206], A24plus[206], 1);
                eval_3_isog_mod(pts[2052], pts[2055], coeff[200]);
                lock[234][1] = 0;
                while(lock[234][0]) {
                    #pragma omp flush(lock[234][0])
                }

                eval_3_isog_mod(pts[2055], pts[2058], coeff[201]);
                eval_3_isog_mod(pts[2056], pts[2059], coeff[188]);
                lock[235][1] = 0;
                while(lock[235][0]) {
                    #pragma omp flush(lock[235][0])
                }

                eval_3_isog_mod(pts[2059], pts[2062], coeff[189]);
                eval_3_isog_mod(pts[2054], pts[2064], coeff[206]);
                eval_3_isog_mod(pts[2051], pts[2065], coeff[206]);
                eval_3_isog_mod(pts[2042], pts[2067], coeff[206]);
                lock[236][1] = 0;
                while(lock[236][0]) {
                    #pragma omp flush(lock[236][0])
                }

                eval_3_isog_mod(pts[2064], pts[2070], coeff[207]);
                get_3_isog(pts[2070], A24minus[209], A24plus[209], coeff[208]);
                eval_3_isog_mod(pts[2066], pts[2072], coeff[207]);
                eval_3_isog_mod(pts[2067], pts[2073], coeff[207]);
                eval_3_isog_mod(pts[2068], pts[2075], coeff[204]);
                lock[237][1] = 0;
                while(lock[237][0]) {
                    #pragma omp flush(lock[237][0])
                }

                eval_3_isog_mod(pts[2071], pts[2077], coeff[208]);
                get_3_isog(pts[2077], A24minus[210], A24plus[210], coeff[209]);
                eval_3_isog_mod(pts[2074], pts[2080], coeff[207]);
                eval_3_isog_mod(pts[2075], pts[2081], coeff[205]);
                lock[238][1] = 0;
                while(lock[238][0]) {
                    #pragma omp flush(lock[238][0])
                }

                eval_3_isog_mod(pts[2078], pts[2083], coeff[209]);
                get_3_isog(pts[2083], A24minus[211], A24plus[211], coeff[210]);
                eval_3_isog_mod(pts[2081], pts[2086], coeff[206]);
                lock[239][1] = 0;
                while(lock[239][0]) {
                    #pragma omp flush(lock[239][0])
                }

                eval_3_isog_mod(pts[2082], pts[2087], coeff[193]);
                eval_3_isog_mod(pts[2086], pts[2090], coeff[207]);
                eval_3_isog_mod(pts[2087], pts[2091], coeff[194]);
                eval_3_isog_mod(pts[2090], pts[2094], coeff[208]);
                eval_3_isog_mod(pts[2091], pts[2095], coeff[195]);
                eval_3_isog_mod(pts[2094], pts[2098], coeff[209]);
                eval_3_isog_mod(pts[2095], pts[2099], coeff[196]);
                lock[240][1] = 0;
                while(lock[240][0]) {
                    #pragma omp flush(lock[240][0])
                }

                eval_3_isog_mod(pts[2099], pts[2102], coeff[197]);
                xTPLe(pts[2100], pts[2103], A24minus[213], A24plus[213], 1);
                lock[241][1] = 0;
                while(lock[241][0]) {
                    #pragma omp flush(lock[241][0])
                }

                eval_3_isog_mod(pts[2102], pts[2105], coeff[198]);
                eval_3_isog_mod(pts[2105], pts[2108], coeff[199]);
                lock[242][1] = 0;
                while(lock[242][0]) {
                    #pragma omp flush(lock[242][0])
                }

                eval_3_isog_mod(pts[2103], pts[2109], coeff[213]);
                get_3_isog(pts[2109], A24minus[215], A24plus[215], coeff[214]);
                eval_3_isog_mod(pts[2108], pts[2112], coeff[200]);
                lock[243][1] = 0;
                while(lock[243][0]) {
                    #pragma omp flush(lock[243][0])
                }

                eval_3_isog_mod(pts[2111], pts[2114], coeff[214]);
                lock[244][1] = 0;
                while(lock[244][0]) {
                    #pragma omp flush(lock[244][0])
                }

                eval_3_isog_mod(pts[2112], pts[2115], coeff[201]);
                eval_3_isog_mod(pts[2115], pts[2117], coeff[202]);
                eval_3_isog_mod(pts[2117], pts[2119], coeff[203]);
                eval_3_isog_mod(pts[2119], pts[2121], coeff[204]);
                eval_3_isog_mod(pts[2121], pts[2123], coeff[205]);
                eval_3_isog_mod(pts[2123], pts[2125], coeff[206]);
                eval_3_isog_mod(pts[2125], pts[2127], coeff[207]);
                eval_3_isog_mod(pts[2127], pts[2129], coeff[208]);
                eval_3_isog_mod(pts[2129], pts[2131], coeff[209]);
                eval_3_isog_mod(pts[2131], pts[2133], coeff[210]);
                eval_3_isog_mod(pts[2133], pts[2135], coeff[211]);
                eval_3_isog_mod(pts[2135], pts[2137], coeff[212]);
                lock[245][1] = 0;
                while(lock[245][0]) {
                    #pragma omp flush(lock[245][0])
                }

                eval_3_isog_mod(pts[2130], pts[2140], coeff[216]);
                eval_3_isog_mod(pts[2128], pts[2141], coeff[216]);
                eval_3_isog_mod(pts[2122], pts[2143], coeff[216]);
                eval_3_isog_mod(pts[2140], pts[2146], coeff[217]);
                eval_3_isog_mod(pts[2141], pts[2147], coeff[217]);
                eval_3_isog_mod(pts[2143], pts[2149], coeff[217]);
                lock[246][1] = 0;
                while(lock[246][0]) {
                    #pragma omp flush(lock[246][0])
                }

                eval_3_isog_mod(pts[2144], pts[2151], coeff[214]);
                eval_3_isog_mod(pts[2147], pts[2153], coeff[218]);
                eval_3_isog_mod(pts[2149], pts[2155], coeff[218]);
                lock[247][1] = 0;
                while(lock[247][0]) {
                    #pragma omp flush(lock[247][0])
                }

                eval_3_isog_mod(pts[2153], pts[2158], coeff[219]);
                get_3_isog(pts[2158], A24minus[221], A24plus[221], coeff[220]);
                eval_3_isog_mod(pts[2154], pts[2159], coeff[219]);
                eval_3_isog_mod(pts[2156], pts[2161], coeff[218]);
                lock[248][1] = 0;
                while(lock[248][0]) {
                    #pragma omp flush(lock[248][0])
                }

                eval_3_isog_mod(pts[2160], pts[2164], coeff[220]);
                eval_3_isog_mod(pts[2162], pts[2166], coeff[217]);
                lock[249][1] = 0;
                while(lock[249][0]) {
                    #pragma omp flush(lock[249][0])
                }

                eval_3_isog_mod(pts[2165], pts[2168], coeff[220]);
                eval_3_isog_mod(pts[2166], pts[2169], coeff[218]);
                lock[250][1] = 0;
                while(lock[250][0]) {
                    #pragma omp flush(lock[250][0])
                }

                eval_3_isog_mod(pts[2168], pts[2171], coeff[221]);
                eval_3_isog_mod(pts[2171], pts[2174], coeff[222]);
                lock[251][1] = 0;
                while(lock[251][0]) {
                    #pragma omp flush(lock[251][0])
                }

                eval_3_isog_mod(pts[2174], pts[2176], coeff[223]);
                xTPLe(pts[2176], pts[2178], A24minus[224], A24plus[224], 1);
                xTPLe(pts[2178], pts[2180], A24minus[224], A24plus[224], 1);
                get_3_isog(pts[2180], A24minus[225], A24plus[225], coeff[224]);
                eval_3_isog_mod(pts[2178], pts[2182], coeff[224]);
                get_3_isog(pts[2182], A24minus[226], A24plus[226], coeff[225]);
                lock[252][1] = 0;
                while(lock[252][0]) {
                    #pragma omp flush(lock[252][0])
                }

                eval_3_isog_mod(pts[2176], pts[2183], coeff[224]);
                eval_3_isog_mod(pts[2183], pts[2185], coeff[225]);
                get_3_isog(pts[2185], A24minus[227], A24plus[227], coeff[226]);
                lock[253][1] = 0;
                while(lock[253][0]) {
                    #pragma omp flush(lock[253][0])
                }

                lock[254][1] = 0;
                while(lock[254][0]) {
                    #pragma omp flush(lock[254][0])
                }

                eval_3_isog_mod(pts[2196], pts[2200], coeff[227]);
                eval_3_isog_mod(pts[2195], pts[2201], coeff[227]);
                eval_3_isog_mod(pts[2192], pts[2204], coeff[227]);
                lock[255][1] = 0;
                while(lock[255][0]) {
                    #pragma omp flush(lock[255][0])
                }

                eval_3_isog_mod(pts[2190], pts[2205], coeff[227]);
                eval_3_isog_mod(pts[2202], pts[2208], coeff[228]);
                eval_3_isog_mod(pts[2203], pts[2209], coeff[228]);
                eval_3_isog_mod(pts[2205], pts[2211], coeff[228]);
                lock[256][1] = 0;
                while(lock[256][0]) {
                    #pragma omp flush(lock[256][0])
                }

                eval_3_isog_mod(pts[2208], pts[2214], coeff[229]);
                eval_3_isog_mod(pts[2210], pts[2216], coeff[229]);
                eval_3_isog_mod(pts[2211], pts[2217], coeff[229]);
                lock[257][1] = 0;
                while(lock[257][0]) {
                    #pragma omp flush(lock[257][0])
                }

                eval_3_isog_mod(pts[2215], pts[2220], coeff[230]);
                eval_3_isog_mod(pts[2217], pts[2222], coeff[230]);
                lock[258][1] = 0;
                while(lock[258][0]) {
                    #pragma omp flush(lock[258][0])
                }

                eval_3_isog_mod(pts[2220], pts[2224], coeff[231]);
                get_3_isog(pts[2224], A24minus[233], A24plus[233], coeff[232]);
                eval_3_isog_mod(pts[2221], pts[2225], coeff[231]);
                eval_3_isog_mod(pts[2225], pts[2228], coeff[232]);
                get_3_isog(pts[2228], A24minus[234], A24plus[234], coeff[233]);
                lock[259][1] = 0;
                while(lock[259][0]) {
                    #pragma omp flush(lock[259][0])
                }

                eval_3_isog_mod(pts[2227], pts[2230], coeff[231]);
                eval_3_isog_mod(pts[2230], pts[2232], coeff[232]);
                eval_3_isog_mod(pts[2232], pts[2234], coeff[233]);
                lock[260][1] = 0;
                while(lock[260][0]) {
                    #pragma omp flush(lock[260][0])
                }

                eval_3_isog_mod(pts[2231], pts[2235], coeff[234]);
                get_3_isog(pts[2235], A24minus[236], A24plus[236], coeff[235]);
                lock[261][1] = 0;
                while(lock[261][0]) {
                    #pragma omp flush(lock[261][0])
                }

                lock[262][1] = 0;
                while(lock[262][0]) {
                    #pragma omp flush(lock[262][0])
                }

                eval_3_isog_mod(pts[2237], pts[2241], coeff[236]);
            }
        }
    }

    eval_3_isog(pts[2241], coeff[237]);
    get_3_isog(pts[2241], A24minus[239], A24plus[239], coeff[238]);

    for(int i = 0; i < MAX_Bob; i++) {
        eval_3_isog(phiP, coeff[i]);
        eval_3_isog(phiQ, coeff[i]);
        eval_3_isog(phiR, coeff[i]);
    }

    inv_3_way(phiP->Z, phiQ->Z, phiR->Z);
    fp2mul_mont(phiP->X, phiP->Z, phiP->X);
    fp2mul_mont(phiQ->X, phiQ->Z, phiQ->X);
    fp2mul_mont(phiR->X, phiR->Z, phiR->X);

    fp2_encode(phiP->X, PublicKeyB);
    fp2_encode(phiQ->X, PublicKeyB + FP2_ENCODED_BYTES);
    fp2_encode(phiR->X, PublicKeyB + 2*FP2_ENCODED_BYTES);

    return 0;
}

int EphemeralSecretAgreement_B(const unsigned char* PrivateKeyB, const unsigned char* PublicKeyA, unsigned char* SharedSecretB) {
    point_proj_t pts[2242];
    f2elm_t coeff[MAX_Bob][3], A24minus[MAX_Bob+1] = {0}, A24plus[MAX_Bob+1] = {0}, A = {0}, PKB[3], jinv;
    char lock[265][2];

    for(int i = 0; i < 265; i++)
        for(int j = 0; j < 2; j++)
            lock[i][j] = 1;

    fp2_decode(PublicKeyA, PKB[0]);
    fp2_decode(PublicKeyA + FP2_ENCODED_BYTES, PKB[1]);
    fp2_decode(PublicKeyA + 2*FP2_ENCODED_BYTES, PKB[2]);
    get_A(PKB[0], PKB[1], PKB[2], A);
    fpadd((digit_t*)&Montgomery_one, (digit_t*)&Montgomery_one, A24minus[0][0]);
    fp2add(A, A24minus[0], A24plus[0]);
    fp2sub(A, A24minus[0], A24minus[0]);
    LADDER3PT(PKB[0], PKB[1], PKB[2], (digit_t*)PrivateKeyB, BOB, pts[0], A);

    for(int i = 0; i < MAX_Bob-1; i++)
        xTPLe(pts[i], pts[i+1], A24minus[0], A24plus[0], 1);
    get_3_isog(pts[MAX_Bob-1], A24minus[1], A24plus[1], coeff[0]);

    omp_set_num_threads(2);
    #pragma omp parallel
    {
        #pragma omp sections
        {
            #pragma omp section
            {
                eval_3_isog_mod(pts[236], pts[240], coeff[0]);
                eval_3_isog_mod(pts[234], pts[242], coeff[0]);
                lock[0][0] = 0;
                while(lock[0][1]) {
                    #pragma omp flush(lock[0][1])
                }

                eval_3_isog_mod(pts[240], pts[244], coeff[1]);
                get_3_isog(pts[244], A24minus[3], A24plus[3], coeff[2]);
                eval_3_isog_mod(pts[241], pts[245], coeff[1]);
                eval_3_isog_mod(pts[229], pts[248], coeff[0]);
                lock[1][0] = 0;
                while(lock[1][1]) {
                    #pragma omp flush(lock[1][1])
                }

                eval_3_isog_mod(pts[245], pts[249], coeff[2]);
                get_3_isog(pts[249], A24minus[4], A24plus[4], coeff[3]);
                eval_3_isog_mod(pts[247], pts[251], coeff[2]);
                lock[2][0] = 0;
                while(lock[2][1]) {
                    #pragma omp flush(lock[2][1])
                }

                eval_3_isog_mod(pts[250], pts[253], coeff[3]);
                get_3_isog(pts[253], A24minus[5], A24plus[5], coeff[4]);
                eval_3_isog_mod(pts[252], pts[255], coeff[2]);
                lock[3][0] = 0;
                while(lock[3][1]) {
                    #pragma omp flush(lock[3][1])
                }

                eval_3_isog_mod(pts[255], pts[258], coeff[3]);
                eval_3_isog_mod(pts[256], pts[259], coeff[1]);
                lock[4][0] = 0;
                while(lock[4][1]) {
                    #pragma omp flush(lock[4][1])
                }

                eval_3_isog_mod(pts[259], pts[262], coeff[2]);
                eval_3_isog_mod(pts[257], pts[263], coeff[5]);
                get_3_isog(pts[263], A24minus[7], A24plus[7], coeff[6]);
                eval_3_isog_mod(pts[262], pts[265], coeff[3]);
                lock[5][0] = 0;
                while(lock[5][1]) {
                    #pragma omp flush(lock[5][1])
                }

                eval_3_isog_mod(pts[265], pts[268], coeff[4]);
                eval_3_isog_mod(pts[266], pts[269], coeff[1]);
                lock[6][0] = 0;
                while(lock[6][1]) {
                    #pragma omp flush(lock[6][1])
                }

                eval_3_isog_mod(pts[269], pts[272], coeff[2]);
                xTPLe(pts[270], pts[273], A24minus[7], A24plus[7], 1);
                get_3_isog(pts[273], A24minus[8], A24plus[8], coeff[7]);
                lock[7][0] = 0;
                while(lock[7][1]) {
                    #pragma omp flush(lock[7][1])
                }

                eval_3_isog_mod(pts[272], pts[275], coeff[3]);
                eval_3_isog_mod(pts[274], pts[278], coeff[7]);
                eval_3_isog_mod(pts[275], pts[279], coeff[4]);
                lock[8][0] = 0;
                while(lock[8][1]) {
                    #pragma omp flush(lock[8][1])
                }

                eval_3_isog_mod(pts[277], pts[281], coeff[8]);
                get_3_isog(pts[281], A24minus[10], A24plus[10], coeff[9]);
                eval_3_isog_mod(pts[280], pts[284], coeff[1]);
                lock[9][0] = 0;
                while(lock[9][1]) {
                    #pragma omp flush(lock[9][1])
                }

                eval_3_isog_mod(pts[282], pts[285], coeff[9]);
                xTPLe(pts[285], pts[288], A24minus[10], A24plus[10], 1);
                lock[10][0] = 0;
                while(lock[10][1]) {
                    #pragma omp flush(lock[10][1])
                }

                eval_3_isog_mod(pts[286], pts[289], coeff[7]);
                eval_3_isog_mod(pts[289], pts[292], coeff[8]);
                lock[11][0] = 0;
                while(lock[11][1]) {
                    #pragma omp flush(lock[11][1])
                }

                eval_3_isog_mod(pts[290], pts[293], coeff[4]);
                eval_3_isog_mod(pts[293], pts[296], coeff[5]);
                lock[12][0] = 0;
                while(lock[12][1]) {
                    #pragma omp flush(lock[12][1])
                }

                eval_3_isog_mod(pts[291], pts[297], coeff[10]);
                get_3_isog(pts[297], A24minus[12], A24plus[12], coeff[11]);
                eval_3_isog_mod(pts[285], pts[299], coeff[10]);
                lock[13][0] = 0;
                while(lock[13][1]) {
                    #pragma omp flush(lock[13][1])
                }

                eval_3_isog_mod(pts[296], pts[301], coeff[6]);
                eval_3_isog_mod(pts[299], pts[303], coeff[11]);
                eval_3_isog_mod(pts[301], pts[305], coeff[7]);
                lock[14][0] = 0;
                while(lock[14][1]) {
                    #pragma omp flush(lock[14][1])
                }

                eval_3_isog_mod(pts[303], pts[307], coeff[12]);
                get_3_isog(pts[307], A24minus[14], A24plus[14], coeff[13]);
                eval_3_isog_mod(pts[306], pts[310], coeff[1]);
                lock[15][0] = 0;
                while(lock[15][1]) {
                    #pragma omp flush(lock[15][1])
                }

                eval_3_isog_mod(pts[308], pts[311], coeff[13]);
                xTPLe(pts[311], pts[314], A24minus[14], A24plus[14], 1);
                lock[16][0] = 0;
                while(lock[16][1]) {
                    #pragma omp flush(lock[16][1])
                }

                eval_3_isog_mod(pts[312], pts[315], coeff[10]);
                eval_3_isog_mod(pts[315], pts[318], coeff[11]);
                lock[17][0] = 0;
                while(lock[17][1]) {
                    #pragma omp flush(lock[17][1])
                }

                eval_3_isog_mod(pts[316], pts[319], coeff[4]);
                eval_3_isog_mod(pts[319], pts[322], coeff[5]);
                lock[18][0] = 0;
                while(lock[18][1]) {
                    #pragma omp flush(lock[18][1])
                }

                eval_3_isog_mod(pts[321], pts[324], coeff[13]);
                eval_3_isog_mod(pts[322], pts[325], coeff[6]);
                lock[19][0] = 0;
                while(lock[19][1]) {
                    #pragma omp flush(lock[19][1])
                }

                eval_3_isog_mod(pts[317], pts[327], coeff[14]);
                eval_3_isog_mod(pts[324], pts[330], coeff[14]);
                eval_3_isog_mod(pts[327], pts[332], coeff[15]);
                get_3_isog(pts[332], A24minus[17], A24plus[17], coeff[16]);
                lock[20][0] = 0;
                while(lock[20][1]) {
                    #pragma omp flush(lock[20][1])
                }

                eval_3_isog_mod(pts[328], pts[333], coeff[15]);
                eval_3_isog_mod(pts[330], pts[335], coeff[15]);
                eval_3_isog_mod(pts[333], pts[337], coeff[16]);
                get_3_isog(pts[337], A24minus[18], A24plus[18], coeff[17]);
                eval_3_isog_mod(pts[335], pts[339], coeff[16]);
                lock[21][0] = 0;
                while(lock[21][1]) {
                    #pragma omp flush(lock[21][1])
                }

                eval_3_isog_mod(pts[339], pts[342], coeff[17]);
                lock[22][0] = 0;
                while(lock[22][1]) {
                    #pragma omp flush(lock[22][1])
                }

                eval_3_isog_mod(pts[342], pts[344], coeff[18]);
                xTPLe(pts[344], pts[346], A24minus[19], A24plus[19], 1);
                eval_3_isog_mod(pts[189], pts[348], coeff[0]);
                xTPLe(pts[346], pts[349], A24minus[19], A24plus[19], 1);
                lock[23][0] = 0;
                while(lock[23][1]) {
                    #pragma omp flush(lock[23][1])
                }

                xTPLe(pts[349], pts[352], A24minus[19], A24plus[19], 1);
                eval_3_isog_mod(pts[350], pts[353], coeff[14]);
                lock[24][0] = 0;
                while(lock[24][1]) {
                    #pragma omp flush(lock[24][1])
                }

                xTPLe(pts[352], pts[355], A24minus[19], A24plus[19], 1);
                xTPLe(pts[355], pts[358], A24minus[19], A24plus[19], 1);
                lock[25][0] = 0;
                while(lock[25][1]) {
                    #pragma omp flush(lock[25][1])
                }

                eval_3_isog_mod(pts[357], pts[360], coeff[4]);
                xTPLe(pts[358], pts[361], A24minus[19], A24plus[19], 1);
                get_3_isog(pts[361], A24minus[20], A24plus[20], coeff[19]);
                lock[26][0] = 0;
                while(lock[26][1]) {
                    #pragma omp flush(lock[26][1])
                }

                eval_3_isog_mod(pts[360], pts[363], coeff[5]);
                eval_3_isog_mod(pts[355], pts[365], coeff[19]);
                eval_3_isog_mod(pts[344], pts[368], coeff[19]);
                eval_3_isog_mod(pts[363], pts[370], coeff[6]);
                lock[27][0] = 0;
                while(lock[27][1]) {
                    #pragma omp flush(lock[27][1])
                }

                eval_3_isog_mod(pts[365], pts[371], coeff[20]);
                get_3_isog(pts[371], A24minus[22], A24plus[22], coeff[21]);
                eval_3_isog_mod(pts[368], pts[374], coeff[20]);
                eval_3_isog_mod(pts[370], pts[376], coeff[7]);
                lock[28][0] = 0;
                while(lock[28][1]) {
                    #pragma omp flush(lock[28][1])
                }

                eval_3_isog_mod(pts[372], pts[377], coeff[21]);
                get_3_isog(pts[377], A24minus[23], A24plus[23], coeff[22]);
                eval_3_isog_mod(pts[375], pts[380], coeff[20]);
                lock[29][0] = 0;
                while(lock[29][1]) {
                    #pragma omp flush(lock[29][1])
                }

                eval_3_isog_mod(pts[376], pts[381], coeff[8]);
                eval_3_isog_mod(pts[380], pts[384], coeff[21]);
                eval_3_isog_mod(pts[381], pts[385], coeff[9]);
                lock[30][0] = 0;
                while(lock[30][1]) {
                    #pragma omp flush(lock[30][1])
                }

                eval_3_isog_mod(pts[384], pts[387], coeff[22]);
                eval_3_isog_mod(pts[387], pts[390], coeff[23]);
                lock[31][0] = 0;
                while(lock[31][1]) {
                    #pragma omp flush(lock[31][1])
                }

                eval_3_isog_mod(pts[388], pts[391], coeff[11]);
                eval_3_isog_mod(pts[391], pts[394], coeff[12]);
                eval_3_isog_mod(pts[394], pts[396], coeff[13]);
                eval_3_isog_mod(pts[396], pts[398], coeff[14]);
                eval_3_isog_mod(pts[398], pts[400], coeff[15]);
                eval_3_isog_mod(pts[400], pts[402], coeff[16]);
                eval_3_isog_mod(pts[402], pts[404], coeff[17]);
                eval_3_isog_mod(pts[404], pts[406], coeff[18]);
                eval_3_isog_mod(pts[406], pts[408], coeff[19]);
                eval_3_isog_mod(pts[170], pts[409], coeff[0]);
                lock[32][0] = 0;
                while(lock[32][1]) {
                    #pragma omp flush(lock[32][1])
                }

                eval_3_isog_mod(pts[409], pts[412], coeff[1]);
                xTPLe(pts[410], pts[413], A24minus[26], A24plus[26], 1);
                lock[33][0] = 0;
                while(lock[33][1]) {
                    #pragma omp flush(lock[33][1])
                }

                xTPLe(pts[413], pts[416], A24minus[26], A24plus[26], 1);
                get_3_isog(pts[416], A24minus[27], A24plus[27], coeff[26]);
                eval_3_isog_mod(pts[414], pts[417], coeff[22]);
                lock[34][0] = 0;
                while(lock[34][1]) {
                    #pragma omp flush(lock[34][1])
                }

                eval_3_isog_mod(pts[410], pts[420], coeff[26]);
                eval_3_isog_mod(pts[407], pts[421], coeff[26]);
                eval_3_isog_mod(pts[401], pts[423], coeff[26]);
                lock[35][0] = 0;
                while(lock[35][1]) {
                    #pragma omp flush(lock[35][1])
                }

                eval_3_isog_mod(pts[418], pts[425], coeff[4]);
                eval_3_isog_mod(pts[421], pts[427], coeff[27]);
                eval_3_isog_mod(pts[395], pts[430], coeff[26]);
                eval_3_isog_mod(pts[425], pts[432], coeff[5]);
                lock[36][0] = 0;
                while(lock[36][1]) {
                    #pragma omp flush(lock[36][1])
                }

                eval_3_isog_mod(pts[428], pts[434], coeff[28]);
                eval_3_isog_mod(pts[430], pts[436], coeff[27]);
                eval_3_isog_mod(pts[432], pts[438], coeff[6]);
                lock[37][0] = 0;
                while(lock[37][1]) {
                    #pragma omp flush(lock[37][1])
                }

                eval_3_isog_mod(pts[435], pts[440], coeff[29]);
                eval_3_isog_mod(pts[436], pts[441], coeff[28]);
                lock[38][0] = 0;
                while(lock[38][1]) {
                    #pragma omp flush(lock[38][1])
                }

                eval_3_isog_mod(pts[438], pts[443], coeff[7]);
                eval_3_isog_mod(pts[442], pts[446], coeff[27]);
                eval_3_isog_mod(pts[443], pts[447], coeff[8]);
                eval_3_isog_mod(pts[446], pts[450], coeff[28]);
                eval_3_isog_mod(pts[447], pts[451], coeff[9]);
                eval_3_isog_mod(pts[450], pts[454], coeff[29]);
                eval_3_isog_mod(pts[451], pts[455], coeff[10]);
                lock[39][0] = 0;
                while(lock[39][1]) {
                    #pragma omp flush(lock[39][1])
                }

                eval_3_isog_mod(pts[454], pts[457], coeff[30]);
                eval_3_isog_mod(pts[457], pts[460], coeff[31]);
                lock[40][0] = 0;
                while(lock[40][1]) {
                    #pragma omp flush(lock[40][1])
                }

                xTPLe(pts[459], pts[462], A24minus[33], A24plus[33], 1);
                get_3_isog(pts[462], A24minus[34], A24plus[34], coeff[33]);
                eval_3_isog_mod(pts[460], pts[463], coeff[32]);
                lock[41][0] = 0;
                while(lock[41][1]) {
                    #pragma omp flush(lock[41][1])
                }

                eval_3_isog_mod(pts[456], pts[466], coeff[33]);
                eval_3_isog_mod(pts[464], pts[468], coeff[14]);
                lock[42][0] = 0;
                while(lock[42][1]) {
                    #pragma omp flush(lock[42][1])
                }

                eval_3_isog_mod(pts[466], pts[469], coeff[34]);
                get_3_isog(pts[469], A24minus[36], A24plus[36], coeff[35]);
                lock[43][0] = 0;
                while(lock[43][1]) {
                    #pragma omp flush(lock[43][1])
                }

                eval_3_isog_mod(pts[470], pts[472], coeff[35]);
                xTPLe(pts[472], pts[474], A24minus[36], A24plus[36], 1);
                xTPLe(pts[474], pts[476], A24minus[36], A24plus[36], 1);
                xTPLe(pts[476], pts[478], A24minus[36], A24plus[36], 1);
                xTPLe(pts[478], pts[480], A24minus[36], A24plus[36], 1);
                xTPLe(pts[480], pts[482], A24minus[36], A24plus[36], 1);
                xTPLe(pts[482], pts[484], A24minus[36], A24plus[36], 1);
                xTPLe(pts[484], pts[486], A24minus[36], A24plus[36], 1);
                xTPLe(pts[486], pts[488], A24minus[36], A24plus[36], 1);
                xTPLe(pts[488], pts[490], A24minus[36], A24plus[36], 1);
                xTPLe(pts[490], pts[492], A24minus[36], A24plus[36], 1);
                xTPLe(pts[492], pts[494], A24minus[36], A24plus[36], 1);
                xTPLe(pts[494], pts[496], A24minus[36], A24plus[36], 1);
                eval_3_isog_mod(pts[144], pts[498], coeff[0]);
                xTPLe(pts[496], pts[499], A24minus[36], A24plus[36], 1);
                get_3_isog(pts[499], A24minus[37], A24plus[37], coeff[36]);
                lock[44][0] = 0;
                while(lock[44][1]) {
                    #pragma omp flush(lock[44][1])
                }

                eval_3_isog_mod(pts[498], pts[501], coeff[1]);
                eval_3_isog_mod(pts[494], pts[503], coeff[36]);
                eval_3_isog_mod(pts[486], pts[506], coeff[36]);
                eval_3_isog_mod(pts[501], pts[508], coeff[2]);
                lock[45][0] = 0;
                while(lock[45][1]) {
                    #pragma omp flush(lock[45][1])
                }

                eval_3_isog_mod(pts[504], pts[510], coeff[37]);
                eval_3_isog_mod(pts[506], pts[512], coeff[37]);
                eval_3_isog_mod(pts[480], pts[513], coeff[36]);
                lock[46][0] = 0;
                while(lock[46][1]) {
                    #pragma omp flush(lock[46][1])
                }

                eval_3_isog_mod(pts[510], pts[516], coeff[38]);
                get_3_isog(pts[516], A24minus[40], A24plus[40], coeff[39]);
                eval_3_isog_mod(pts[512], pts[518], coeff[38]);
                eval_3_isog_mod(pts[513], pts[519], coeff[37]);
                lock[47][0] = 0;
                while(lock[47][1]) {
                    #pragma omp flush(lock[47][1])
                }

                eval_3_isog_mod(pts[515], pts[521], coeff[4]);
                eval_3_isog_mod(pts[518], pts[523], coeff[39]);
                eval_3_isog_mod(pts[472], pts[525], coeff[36]);
                lock[48][0] = 0;
                while(lock[48][1]) {
                    #pragma omp flush(lock[48][1])
                }

                eval_3_isog_mod(pts[521], pts[527], coeff[5]);
                eval_3_isog_mod(pts[525], pts[530], coeff[37]);
                eval_3_isog_mod(pts[527], pts[532], coeff[6]);
                lock[49][0] = 0;
                while(lock[49][1]) {
                    #pragma omp flush(lock[49][1])
                }

                xTPLe(pts[528], pts[533], A24minus[41], A24plus[41], 1);
                get_3_isog(pts[533], A24minus[42], A24plus[42], coeff[41]);
                eval_3_isog_mod(pts[530], pts[535], coeff[38]);
                eval_3_isog_mod(pts[528], pts[538], coeff[41]);
                get_3_isog(pts[538], A24minus[43], A24plus[43], coeff[42]);
                lock[50][0] = 0;
                while(lock[50][1]) {
                    #pragma omp flush(lock[50][1])
                }

                eval_3_isog_mod(pts[534], pts[539], coeff[41]);
                eval_3_isog_mod(pts[536], pts[541], coeff[36]);
                eval_3_isog_mod(pts[539], pts[543], coeff[42]);
                eval_3_isog_mod(pts[541], pts[545], coeff[37]);
                xTPLe(pts[543], pts[547], A24minus[43], A24plus[43], 1);
                eval_3_isog_mod(pts[545], pts[549], coeff[38]);
                xTPLe(pts[547], pts[551], A24minus[43], A24plus[43], 1);
                get_3_isog(pts[551], A24minus[44], A24plus[44], coeff[43]);
                eval_3_isog_mod(pts[549], pts[553], coeff[39]);
                lock[51][0] = 0;
                while(lock[51][1]) {
                    #pragma omp flush(lock[51][1])
                }

                eval_3_isog_mod(pts[543], pts[556], coeff[43]);
                eval_3_isog_mod(pts[553], pts[558], coeff[40]);
                lock[52][0] = 0;
                while(lock[52][1]) {
                    #pragma omp flush(lock[52][1])
                }

                eval_3_isog_mod(pts[556], pts[560], coeff[44]);
                get_3_isog(pts[560], A24minus[46], A24plus[46], coeff[45]);
                eval_3_isog_mod(pts[558], pts[562], coeff[41]);
                lock[53][0] = 0;
                while(lock[53][1]) {
                    #pragma omp flush(lock[53][1])
                }

                eval_3_isog_mod(pts[561], pts[564], coeff[45]);
                eval_3_isog_mod(pts[562], pts[565], coeff[42]);
                lock[54][0] = 0;
                while(lock[54][1]) {
                    #pragma omp flush(lock[54][1])
                }

                xTPLe(pts[564], pts[567], A24minus[46], A24plus[46], 1);
                xTPLe(pts[567], pts[570], A24minus[46], A24plus[46], 1);
                lock[55][0] = 0;
                while(lock[55][1]) {
                    #pragma omp flush(lock[55][1])
                }

                eval_3_isog_mod(pts[569], pts[572], coeff[16]);
                xTPLe(pts[570], pts[573], A24minus[46], A24plus[46], 1);
                get_3_isog(pts[573], A24minus[47], A24plus[47], coeff[46]);
                lock[56][0] = 0;
                while(lock[56][1]) {
                    #pragma omp flush(lock[56][1])
                }

                eval_3_isog_mod(pts[570], pts[576], coeff[46]);
                get_3_isog(pts[576], A24minus[48], A24plus[48], coeff[47]);
                eval_3_isog_mod(pts[564], pts[578], coeff[46]);
                eval_3_isog_mod(pts[574], pts[579], coeff[46]);
                lock[57][0] = 0;
                while(lock[57][1]) {
                    #pragma omp flush(lock[57][1])
                }

                eval_3_isog_mod(pts[577], pts[581], coeff[47]);
                get_3_isog(pts[581], A24minus[49], A24plus[49], coeff[48]);
                eval_3_isog_mod(pts[579], pts[583], coeff[47]);
                lock[58][0] = 0;
                while(lock[58][1]) {
                    #pragma omp flush(lock[58][1])
                }

                eval_3_isog_mod(pts[582], pts[585], coeff[48]);
                get_3_isog(pts[585], A24minus[50], A24plus[50], coeff[49]);
                lock[59][0] = 0;
                while(lock[59][1]) {
                    #pragma omp flush(lock[59][1])
                }

                eval_3_isog_mod(pts[584], pts[587], coeff[20]);
                eval_3_isog_mod(pts[587], pts[589], coeff[21]);
                eval_3_isog_mod(pts[589], pts[591], coeff[22]);
                eval_3_isog_mod(pts[591], pts[593], coeff[23]);
                eval_3_isog_mod(pts[593], pts[595], coeff[24]);
                eval_3_isog_mod(pts[595], pts[597], coeff[25]);
                eval_3_isog_mod(pts[597], pts[599], coeff[26]);
                eval_3_isog_mod(pts[599], pts[601], coeff[27]);
                eval_3_isog_mod(pts[601], pts[603], coeff[28]);
                eval_3_isog_mod(pts[603], pts[605], coeff[29]);
                eval_3_isog_mod(pts[605], pts[607], coeff[30]);
                eval_3_isog_mod(pts[607], pts[609], coeff[31]);
                eval_3_isog_mod(pts[609], pts[611], coeff[32]);
                eval_3_isog_mod(pts[611], pts[613], coeff[33]);
                eval_3_isog_mod(pts[613], pts[615], coeff[34]);
                eval_3_isog_mod(pts[615], pts[617], coeff[35]);
                eval_3_isog_mod(pts[617], pts[619], coeff[36]);
                eval_3_isog_mod(pts[619], pts[621], coeff[37]);
                eval_3_isog_mod(pts[621], pts[623], coeff[38]);
                eval_3_isog_mod(pts[623], pts[625], coeff[39]);
                lock[60][0] = 0;
                while(lock[60][1]) {
                    #pragma omp flush(lock[60][1])
                }

                eval_3_isog_mod(pts[618], pts[628], coeff[50]);
                eval_3_isog_mod(pts[612], pts[630], coeff[50]);
                eval_3_isog_mod(pts[625], pts[631], coeff[40]);
                eval_3_isog_mod(pts[628], pts[633], coeff[51]);
                eval_3_isog_mod(pts[630], pts[635], coeff[51]);
                lock[61][0] = 0;
                while(lock[61][1]) {
                    #pragma omp flush(lock[61][1])
                }

                eval_3_isog_mod(pts[633], pts[638], coeff[52]);
                get_3_isog(pts[638], A24minus[54], A24plus[54], coeff[53]);
                eval_3_isog_mod(pts[634], pts[639], coeff[52]);
                eval_3_isog_mod(pts[636], pts[641], coeff[51]);
                eval_3_isog_mod(pts[639], pts[644], coeff[53]);
                get_3_isog(pts[644], A24minus[55], A24plus[55], coeff[54]);
                lock[62][0] = 0;
                while(lock[62][1]) {
                    #pragma omp flush(lock[62][1])
                }

                eval_3_isog_mod(pts[640], pts[645], coeff[53]);
                eval_3_isog_mod(pts[642], pts[648], coeff[43]);
                eval_3_isog_mod(pts[645], pts[650], coeff[54]);
                lock[63][0] = 0;
                while(lock[63][1]) {
                    #pragma omp flush(lock[63][1])
                }

                eval_3_isog_mod(pts[646], pts[651], coeff[53]);
                eval_3_isog_mod(pts[648], pts[653], coeff[44]);
                eval_3_isog_mod(pts[651], pts[656], coeff[54]);
                eval_3_isog_mod(pts[653], pts[658], coeff[45]);
                lock[64][0] = 0;
                while(lock[64][1]) {
                    #pragma omp flush(lock[64][1])
                }

                eval_3_isog_mod(pts[650], pts[660], coeff[55]);
                get_3_isog(pts[660], A24minus[57], A24plus[57], coeff[56]);
                eval_3_isog_mod(pts[657], pts[662], coeff[53]);
                eval_3_isog_mod(pts[588], pts[663], coeff[50]);
                lock[65][0] = 0;
                while(lock[65][1]) {
                    #pragma omp flush(lock[65][1])
                }

                eval_3_isog_mod(pts[659], pts[665], coeff[4]);
                eval_3_isog_mod(pts[662], pts[667], coeff[54]);
                eval_3_isog_mod(pts[665], pts[670], coeff[5]);
                eval_3_isog_mod(pts[667], pts[672], coeff[55]);
                lock[66][0] = 0;
                while(lock[66][1]) {
                    #pragma omp flush(lock[66][1])
                }

                eval_3_isog_mod(pts[668], pts[673], coeff[52]);
                eval_3_isog_mod(pts[670], pts[675], coeff[6]);
                eval_3_isog_mod(pts[673], pts[678], coeff[53]);
                eval_3_isog_mod(pts[675], pts[680], coeff[7]);
                lock[67][0] = 0;
                while(lock[67][1]) {
                    #pragma omp flush(lock[67][1])
                }

                eval_3_isog_mod(pts[671], pts[681], coeff[57]);
                get_3_isog(pts[681], A24minus[59], A24plus[59], coeff[58]);
                eval_3_isog_mod(pts[678], pts[684], coeff[54]);
                eval_3_isog_mod(pts[679], pts[685], coeff[50]);
                lock[68][0] = 0;
                while(lock[68][1]) {
                    #pragma omp flush(lock[68][1])
                }

                eval_3_isog_mod(pts[683], pts[688], coeff[58]);
                eval_3_isog_mod(pts[684], pts[689], coeff[55]);
                lock[69][0] = 0;
                while(lock[69][1]) {
                    #pragma omp flush(lock[69][1])
                }

                eval_3_isog_mod(pts[688], pts[692], coeff[59]);
                eval_3_isog_mod(pts[690], pts[694], coeff[52]);
                xTPLe(pts[692], pts[696], A24minus[60], A24plus[60], 1);
                eval_3_isog_mod(pts[694], pts[698], coeff[53]);
                xTPLe(pts[696], pts[700], A24minus[60], A24plus[60], 1);
                eval_3_isog_mod(pts[698], pts[702], coeff[54]);
                xTPLe(pts[700], pts[704], A24minus[60], A24plus[60], 1);
                get_3_isog(pts[704], A24minus[61], A24plus[61], coeff[60]);
                eval_3_isog_mod(pts[702], pts[706], coeff[55]);
                eval_3_isog_mod(pts[700], pts[708], coeff[60]);
                get_3_isog(pts[708], A24minus[62], A24plus[62], coeff[61]);
                lock[70][0] = 0;
                while(lock[70][1]) {
                    #pragma omp flush(lock[70][1])
                }

                eval_3_isog_mod(pts[692], pts[710], coeff[60]);
                eval_3_isog_mod(pts[705], pts[711], coeff[60]);
                eval_3_isog_mod(pts[707], pts[713], coeff[14]);
                lock[71][0] = 0;
                while(lock[71][1]) {
                    #pragma omp flush(lock[71][1])
                }

                eval_3_isog_mod(pts[711], pts[716], coeff[61]);
                eval_3_isog_mod(pts[713], pts[718], coeff[15]);
                eval_3_isog_mod(pts[716], pts[720], coeff[62]);
                eval_3_isog_mod(pts[718], pts[722], coeff[16]);
                lock[72][0] = 0;
                while(lock[72][1]) {
                    #pragma omp flush(lock[72][1])
                }

                eval_3_isog_mod(pts[720], pts[723], coeff[63]);
                xTPLe(pts[723], pts[726], A24minus[64], A24plus[64], 1);
                lock[73][0] = 0;
                while(lock[73][1]) {
                    #pragma omp flush(lock[73][1])
                }

                eval_3_isog_mod(pts[724], pts[727], coeff[60]);
                eval_3_isog_mod(pts[727], pts[730], coeff[61]);
                lock[74][0] = 0;
                while(lock[74][1]) {
                    #pragma omp flush(lock[74][1])
                }

                eval_3_isog_mod(pts[728], pts[731], coeff[19]);
                eval_3_isog_mod(pts[731], pts[734], coeff[20]);
                lock[75][0] = 0;
                while(lock[75][1]) {
                    #pragma omp flush(lock[75][1])
                }

                eval_3_isog_mod(pts[733], pts[736], coeff[63]);
                eval_3_isog_mod(pts[734], pts[737], coeff[21]);
                lock[76][0] = 0;
                while(lock[76][1]) {
                    #pragma omp flush(lock[76][1])
                }

                eval_3_isog_mod(pts[726], pts[740], coeff[64]);
                eval_3_isog_mod(pts[736], pts[742], coeff[64]);
                eval_3_isog_mod(pts[737], pts[743], coeff[22]);
                eval_3_isog_mod(pts[740], pts[745], coeff[65]);
                lock[77][0] = 0;
                while(lock[77][1]) {
                    #pragma omp flush(lock[77][1])
                }

                eval_3_isog_mod(pts[742], pts[747], coeff[65]);
                eval_3_isog_mod(pts[746], pts[750], coeff[66]);
                eval_3_isog_mod(pts[747], pts[751], coeff[66]);
                lock[78][0] = 0;
                while(lock[78][1]) {
                    #pragma omp flush(lock[78][1])
                }

                eval_3_isog_mod(pts[750], pts[753], coeff[67]);
                get_3_isog(pts[753], A24minus[69], A24plus[69], coeff[68]);
                lock[79][0] = 0;
                while(lock[79][1]) {
                    #pragma omp flush(lock[79][1])
                }

                eval_3_isog_mod(pts[752], pts[755], coeff[25]);
                eval_3_isog_mod(pts[755], pts[757], coeff[26]);
                eval_3_isog_mod(pts[757], pts[759], coeff[27]);
                eval_3_isog_mod(pts[759], pts[761], coeff[28]);
                eval_3_isog_mod(pts[761], pts[763], coeff[29]);
                eval_3_isog_mod(pts[763], pts[765], coeff[30]);
                eval_3_isog_mod(pts[765], pts[767], coeff[31]);
                eval_3_isog_mod(pts[767], pts[769], coeff[32]);
                eval_3_isog_mod(pts[769], pts[771], coeff[33]);
                eval_3_isog_mod(pts[771], pts[773], coeff[34]);
                eval_3_isog_mod(pts[773], pts[775], coeff[35]);
                eval_3_isog_mod(pts[775], pts[777], coeff[36]);
                eval_3_isog_mod(pts[777], pts[779], coeff[37]);
                eval_3_isog_mod(pts[779], pts[781], coeff[38]);
                eval_3_isog_mod(pts[781], pts[783], coeff[39]);
                eval_3_isog_mod(pts[783], pts[785], coeff[40]);
                eval_3_isog_mod(pts[785], pts[787], coeff[41]);
                eval_3_isog_mod(pts[787], pts[789], coeff[42]);
                eval_3_isog_mod(pts[789], pts[791], coeff[43]);
                eval_3_isog_mod(pts[791], pts[793], coeff[44]);
                eval_3_isog_mod(pts[793], pts[795], coeff[45]);
                eval_3_isog_mod(pts[795], pts[797], coeff[46]);
                eval_3_isog_mod(pts[797], pts[799], coeff[47]);
                eval_3_isog_mod(pts[799], pts[801], coeff[48]);
                eval_3_isog_mod(pts[801], pts[803], coeff[49]);
                eval_3_isog_mod(pts[803], pts[805], coeff[50]);
                eval_3_isog_mod(pts[805], pts[807], coeff[51]);
                lock[80][0] = 0;
                while(lock[80][1]) {
                    #pragma omp flush(lock[80][1])
                }

                eval_3_isog_mod(pts[802], pts[809], coeff[69]);
                eval_3_isog_mod(pts[798], pts[811], coeff[69]);
                eval_3_isog_mod(pts[809], pts[814], coeff[70]);
                get_3_isog(pts[814], A24minus[72], A24plus[72], coeff[71]);
                eval_3_isog_mod(pts[811], pts[816], coeff[70]);
                eval_3_isog_mod(pts[788], pts[818], coeff[69]);
                lock[81][0] = 0;
                while(lock[81][1]) {
                    #pragma omp flush(lock[81][1])
                }

                eval_3_isog_mod(pts[813], pts[819], coeff[53]);
                eval_3_isog_mod(pts[816], pts[821], coeff[71]);
                eval_3_isog_mod(pts[819], pts[824], coeff[54]);
                lock[82][0] = 0;
                while(lock[82][1]) {
                    #pragma omp flush(lock[82][1])
                }

                eval_3_isog_mod(pts[822], pts[826], coeff[72]);
                eval_3_isog_mod(pts[823], pts[827], coeff[71]);
                lock[83][0] = 0;
                while(lock[83][1]) {
                    #pragma omp flush(lock[83][1])
                }

                eval_3_isog_mod(pts[824], pts[829], coeff[55]);
                eval_3_isog_mod(pts[827], pts[831], coeff[72]);
                eval_3_isog_mod(pts[829], pts[833], coeff[56]);
                eval_3_isog_mod(pts[831], pts[835], coeff[73]);
                eval_3_isog_mod(pts[833], pts[837], coeff[57]);
                lock[84][0] = 0;
                while(lock[84][1]) {
                    #pragma omp flush(lock[84][1])
                }

                eval_3_isog_mod(pts[836], pts[840], coeff[72]);
                eval_3_isog_mod(pts[837], pts[842], coeff[58]);
                eval_3_isog_mod(pts[840], pts[844], coeff[73]);
                eval_3_isog_mod(pts[842], pts[846], coeff[59]);
                eval_3_isog_mod(pts[844], pts[848], coeff[74]);
                eval_3_isog_mod(pts[846], pts[850], coeff[60]);
                eval_3_isog_mod(pts[848], pts[852], coeff[75]);
                eval_3_isog_mod(pts[850], pts[854], coeff[61]);
                lock[85][0] = 0;
                while(lock[85][1]) {
                    #pragma omp flush(lock[85][1])
                }

                eval_3_isog_mod(pts[843], pts[856], coeff[76]);
                eval_3_isog_mod(pts[853], pts[858], coeff[73]);
                eval_3_isog_mod(pts[854], pts[860], coeff[62]);
                lock[86][0] = 0;
                while(lock[86][1]) {
                    #pragma omp flush(lock[86][1])
                }

                eval_3_isog_mod(pts[856], pts[861], coeff[77]);
                get_3_isog(pts[861], A24minus[79], A24plus[79], coeff[78]);
                eval_3_isog_mod(pts[858], pts[863], coeff[74]);
                lock[87][0] = 0;
                while(lock[87][1]) {
                    #pragma omp flush(lock[87][1])
                }

                eval_3_isog_mod(pts[860], pts[865], coeff[63]);
                eval_3_isog_mod(pts[864], pts[868], coeff[71]);
                eval_3_isog_mod(pts[865], pts[869], coeff[64]);
                lock[88][0] = 0;
                while(lock[88][1]) {
                    #pragma omp flush(lock[88][1])
                }

                eval_3_isog_mod(pts[867], pts[872], coeff[76]);
                eval_3_isog_mod(pts[869], pts[874], coeff[65]);
                eval_3_isog_mod(pts[870], pts[875], coeff[1]);
                eval_3_isog_mod(pts[872], pts[877], coeff[77]);
                lock[89][0] = 0;
                while(lock[89][1]) {
                    #pragma omp flush(lock[89][1])
                }

                eval_3_isog_mod(pts[874], pts[879], coeff[66]);
                xTPLe(pts[876], pts[881], A24minus[79], A24plus[79], 1);
                get_3_isog(pts[881], A24minus[80], A24plus[80], coeff[79]);
                eval_3_isog_mod(pts[879], pts[884], coeff[67]);
                eval_3_isog_mod(pts[876], pts[886], coeff[79]);
                get_3_isog(pts[886], A24minus[81], A24plus[81], coeff[80]);
                lock[90][0] = 0;
                while(lock[90][1]) {
                    #pragma omp flush(lock[90][1])
                }

                eval_3_isog_mod(pts[866], pts[888], coeff[79]);
                eval_3_isog_mod(pts[882], pts[889], coeff[79]);
                eval_3_isog_mod(pts[884], pts[891], coeff[68]);
                eval_3_isog_mod(pts[888], pts[894], coeff[80]);
                eval_3_isog_mod(pts[889], pts[895], coeff[80]);
                eval_3_isog_mod(pts[891], pts[897], coeff[69]);
                lock[91][0] = 0;
                while(lock[91][1]) {
                    #pragma omp flush(lock[91][1])
                }

                eval_3_isog_mod(pts[894], pts[899], coeff[81]);
                get_3_isog(pts[899], A24minus[83], A24plus[83], coeff[82]);
                eval_3_isog_mod(pts[896], pts[901], coeff[77]);
                lock[92][0] = 0;
                while(lock[92][1]) {
                    #pragma omp flush(lock[92][1])
                }

                eval_3_isog_mod(pts[900], pts[904], coeff[82]);
                eval_3_isog_mod(pts[902], pts[906], coeff[71]);
                xTPLe(pts[904], pts[908], A24minus[83], A24plus[83], 1);
                eval_3_isog_mod(pts[906], pts[910], coeff[72]);
                xTPLe(pts[908], pts[912], A24minus[83], A24plus[83], 1);
                eval_3_isog_mod(pts[910], pts[914], coeff[73]);
                xTPLe(pts[912], pts[916], A24minus[83], A24plus[83], 1);
                eval_3_isog_mod(pts[914], pts[918], coeff[74]);
                xTPLe(pts[916], pts[920], A24minus[83], A24plus[83], 1);
                get_3_isog(pts[920], A24minus[84], A24plus[84], coeff[83]);
                eval_3_isog_mod(pts[918], pts[922], coeff[75]);
                eval_3_isog_mod(pts[916], pts[924], coeff[83]);
                get_3_isog(pts[924], A24minus[85], A24plus[85], coeff[84]);
                lock[93][0] = 0;
                while(lock[93][1]) {
                    #pragma omp flush(lock[93][1])
                }

                eval_3_isog_mod(pts[912], pts[925], coeff[83]);
                eval_3_isog_mod(pts[904], pts[927], coeff[83]);
                eval_3_isog_mod(pts[922], pts[929], coeff[76]);
                eval_3_isog_mod(pts[925], pts[931], coeff[84]);
                get_3_isog(pts[931], A24minus[86], A24plus[86], coeff[85]);
                eval_3_isog_mod(pts[927], pts[933], coeff[84]);
                eval_3_isog_mod(pts[929], pts[935], coeff[77]);
                lock[94][0] = 0;
                while(lock[94][1]) {
                    #pragma omp flush(lock[94][1])
                }

                eval_3_isog_mod(pts[933], pts[938], coeff[85]);
                eval_3_isog_mod(pts[935], pts[940], coeff[78]);
                lock[95][0] = 0;
                while(lock[95][1]) {
                    #pragma omp flush(lock[95][1])
                }

                eval_3_isog_mod(pts[938], pts[942], coeff[86]);
                get_3_isog(pts[942], A24minus[88], A24plus[88], coeff[87]);
                eval_3_isog_mod(pts[940], pts[944], coeff[79]);
                lock[96][0] = 0;
                while(lock[96][1]) {
                    #pragma omp flush(lock[96][1])
                }

                eval_3_isog_mod(pts[941], pts[945], coeff[15]);
                eval_3_isog_mod(pts[945], pts[948], coeff[16]);
                lock[97][0] = 0;
                while(lock[97][1]) {
                    #pragma omp flush(lock[97][1])
                }

                xTPLe(pts[946], pts[949], A24minus[88], A24plus[88], 1);
                xTPLe(pts[949], pts[952], A24minus[88], A24plus[88], 1);
                lock[98][0] = 0;
                while(lock[98][1]) {
                    #pragma omp flush(lock[98][1])
                }

                eval_3_isog_mod(pts[951], pts[954], coeff[18]);
                xTPLe(pts[952], pts[955], A24minus[88], A24plus[88], 1);
                lock[99][0] = 0;
                while(lock[99][1]) {
                    #pragma omp flush(lock[99][1])
                }

                xTPLe(pts[955], pts[958], A24minus[88], A24plus[88], 1);
                eval_3_isog_mod(pts[956], pts[959], coeff[84]);
                lock[100][0] = 0;
                while(lock[100][1]) {
                    #pragma omp flush(lock[100][1])
                }

                eval_3_isog_mod(pts[959], pts[962], coeff[85]);
                eval_3_isog_mod(pts[960], pts[963], coeff[21]);
                lock[101][0] = 0;
                while(lock[101][1]) {
                    #pragma omp flush(lock[101][1])
                }

                eval_3_isog_mod(pts[963], pts[966], coeff[22]);
                eval_3_isog_mod(pts[958], pts[968], coeff[88]);
                eval_3_isog_mod(pts[952], pts[970], coeff[88]);
                eval_3_isog_mod(pts[946], pts[971], coeff[88]);
                lock[102][0] = 0;
                while(lock[102][1]) {
                    #pragma omp flush(lock[102][1])
                }

                eval_3_isog_mod(pts[968], pts[974], coeff[89]);
                get_3_isog(pts[974], A24minus[91], A24plus[91], coeff[90]);
                eval_3_isog_mod(pts[969], pts[975], coeff[89]);
                eval_3_isog_mod(pts[972], pts[978], coeff[88]);
                eval_3_isog_mod(pts[975], pts[980], coeff[90]);
                get_3_isog(pts[980], A24minus[92], A24plus[92], coeff[91]);
                lock[103][0] = 0;
                while(lock[103][1]) {
                    #pragma omp flush(lock[103][1])
                }

                eval_3_isog_mod(pts[976], pts[981], coeff[90]);
                eval_3_isog_mod(pts[979], pts[984], coeff[25]);
                eval_3_isog_mod(pts[981], pts[985], coeff[91]);
                get_3_isog(pts[985], A24minus[93], A24plus[93], coeff[92]);
                eval_3_isog_mod(pts[984], pts[988], coeff[26]);
                lock[104][0] = 0;
                while(lock[104][1]) {
                    #pragma omp flush(lock[104][1])
                }

                eval_3_isog_mod(pts[987], pts[990], coeff[91]);
                eval_3_isog_mod(pts[988], pts[991], coeff[27]);
                lock[105][0] = 0;
                while(lock[105][1]) {
                    #pragma omp flush(lock[105][1])
                }

                eval_3_isog_mod(pts[990], pts[993], coeff[92]);
                eval_3_isog_mod(pts[993], pts[996], coeff[93]);
                lock[106][0] = 0;
                while(lock[106][1]) {
                    #pragma omp flush(lock[106][1])
                }

                eval_3_isog_mod(pts[996], pts[998], coeff[94]);
                xTPLe(pts[998], pts[1000], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1000], pts[1002], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1002], pts[1004], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1004], pts[1006], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1006], pts[1008], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1008], pts[1010], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1010], pts[1012], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1012], pts[1014], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1014], pts[1016], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1016], pts[1018], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1018], pts[1020], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1020], pts[1022], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1022], pts[1024], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1024], pts[1026], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1026], pts[1028], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1028], pts[1030], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1030], pts[1032], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1032], pts[1034], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1034], pts[1036], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1036], pts[1038], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1038], pts[1040], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1040], pts[1042], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1042], pts[1044], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1044], pts[1046], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1046], pts[1048], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1048], pts[1050], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1050], pts[1052], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1052], pts[1054], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1054], pts[1056], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1056], pts[1058], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1058], pts[1060], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1060], pts[1062], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1062], pts[1064], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1064], pts[1066], A24minus[95], A24plus[95], 1);
                xTPLe(pts[1066], pts[1068], A24minus[95], A24plus[95], 1);
                get_3_isog(pts[1068], A24minus[96], A24plus[96], coeff[95]);
                eval_3_isog_mod(pts[1066], pts[1070], coeff[95]);
                get_3_isog(pts[1070], A24minus[97], A24plus[97], coeff[96]);
                lock[107][0] = 0;
                while(lock[107][1]) {
                    #pragma omp flush(lock[107][1])
                }

                eval_3_isog_mod(pts[1062], pts[1072], coeff[95]);
                eval_3_isog_mod(pts[1056], pts[1074], coeff[95]);
                eval_3_isog_mod(pts[1069], pts[1075], coeff[66]);
                eval_3_isog_mod(pts[1072], pts[1077], coeff[96]);
                eval_3_isog_mod(pts[1074], pts[1079], coeff[96]);
                lock[108][0] = 0;
                while(lock[108][1]) {
                    #pragma omp flush(lock[108][1])
                }

                eval_3_isog_mod(pts[1075], pts[1081], coeff[67]);
                eval_3_isog_mod(pts[1079], pts[1084], coeff[97]);
                eval_3_isog_mod(pts[1081], pts[1086], coeff[68]);
                lock[109][0] = 0;
                while(lock[109][1]) {
                    #pragma omp flush(lock[109][1])
                }

                eval_3_isog_mod(pts[1083], pts[1087], coeff[98]);
                get_3_isog(pts[1087], A24minus[100], A24plus[100], coeff[99]);
                eval_3_isog_mod(pts[1042], pts[1090], coeff[95]);
                lock[110][0] = 0;
                while(lock[110][1]) {
                    #pragma omp flush(lock[110][1])
                }

                eval_3_isog_mod(pts[1086], pts[1091], coeff[69]);
                eval_3_isog_mod(pts[1089], pts[1093], coeff[98]);
                eval_3_isog_mod(pts[1091], pts[1095], coeff[70]);
                eval_3_isog_mod(pts[1093], pts[1097], coeff[99]);
                eval_3_isog_mod(pts[1095], pts[1099], coeff[71]);
                lock[111][0] = 0;
                while(lock[111][1]) {
                    #pragma omp flush(lock[111][1])
                }

                eval_3_isog_mod(pts[1097], pts[1101], coeff[100]);
                eval_3_isog_mod(pts[1099], pts[1104], coeff[72]);
                eval_3_isog_mod(pts[1101], pts[1105], coeff[101]);
                eval_3_isog_mod(pts[1104], pts[1108], coeff[73]);
                xTPLe(pts[1105], pts[1109], A24minus[102], A24plus[102], 1);
                eval_3_isog_mod(pts[1108], pts[1112], coeff[74]);
                xTPLe(pts[1109], pts[1113], A24minus[102], A24plus[102], 1);
                get_3_isog(pts[1113], A24minus[103], A24plus[103], coeff[102]);
                eval_3_isog_mod(pts[1112], pts[1116], coeff[75]);
                lock[112][0] = 0;
                while(lock[112][1]) {
                    #pragma omp flush(lock[112][1])
                }

                eval_3_isog_mod(pts[1105], pts[1118], coeff[102]);
                eval_3_isog_mod(pts[1115], pts[1120], coeff[99]);
                eval_3_isog_mod(pts[1018], pts[1121], coeff[95]);
                lock[113][0] = 0;
                while(lock[113][1]) {
                    #pragma omp flush(lock[113][1])
                }

                eval_3_isog_mod(pts[1118], pts[1123], coeff[103]);
                get_3_isog(pts[1123], A24minus[105], A24plus[105], coeff[104]);
                eval_3_isog_mod(pts[1121], pts[1126], coeff[96]);
                lock[114][0] = 0;
                while(lock[114][1]) {
                    #pragma omp flush(lock[114][1])
                }

                eval_3_isog_mod(pts[1124], pts[1128], coeff[104]);
                eval_3_isog_mod(pts[1125], pts[1129], coeff[101]);
                xTPLe(pts[1128], pts[1132], A24minus[105], A24plus[105], 1);
                eval_3_isog_mod(pts[1129], pts[1133], coeff[102]);
                xTPLe(pts[1132], pts[1136], A24minus[105], A24plus[105], 1);
                eval_3_isog_mod(pts[1133], pts[1137], coeff[103]);
                xTPLe(pts[1136], pts[1140], A24minus[105], A24plus[105], 1);
                get_3_isog(pts[1140], A24minus[106], A24plus[106], coeff[105]);
                eval_3_isog_mod(pts[1137], pts[1141], coeff[104]);
                eval_3_isog_mod(pts[1136], pts[1144], coeff[105]);
                get_3_isog(pts[1144], A24minus[107], A24plus[107], coeff[106]);
                lock[115][0] = 0;
                while(lock[115][1]) {
                    #pragma omp flush(lock[115][1])
                }

                eval_3_isog_mod(pts[1132], pts[1145], coeff[105]);
                eval_3_isog_mod(pts[1142], pts[1148], coeff[101]);
                eval_3_isog_mod(pts[1145], pts[1150], coeff[106]);
                get_3_isog(pts[1150], A24minus[108], A24plus[108], coeff[107]);
                lock[116][0] = 0;
                while(lock[116][1]) {
                    #pragma omp flush(lock[116][1])
                }

                eval_3_isog_mod(pts[1146], pts[1151], coeff[106]);
                eval_3_isog_mod(pts[1148], pts[1153], coeff[102]);
                eval_3_isog_mod(pts[1151], pts[1156], coeff[107]);
                get_3_isog(pts[1156], A24minus[109], A24plus[109], coeff[108]);
                eval_3_isog_mod(pts[1153], pts[1158], coeff[103]);
                lock[117][0] = 0;
                while(lock[117][1]) {
                    #pragma omp flush(lock[117][1])
                }

                eval_3_isog_mod(pts[1154], pts[1159], coeff[96]);
                eval_3_isog_mod(pts[1158], pts[1162], coeff[104]);
                eval_3_isog_mod(pts[1159], pts[1163], coeff[97]);
                eval_3_isog_mod(pts[1162], pts[1166], coeff[105]);
                eval_3_isog_mod(pts[1163], pts[1167], coeff[98]);
                eval_3_isog_mod(pts[1166], pts[1170], coeff[106]);
                eval_3_isog_mod(pts[1167], pts[1171], coeff[99]);
                eval_3_isog_mod(pts[1170], pts[1174], coeff[107]);
                eval_3_isog_mod(pts[1171], pts[1175], coeff[100]);
                eval_3_isog_mod(pts[1174], pts[1178], coeff[108]);
                eval_3_isog_mod(pts[1175], pts[1179], coeff[101]);
                lock[118][0] = 0;
                while(lock[118][1]) {
                    #pragma omp flush(lock[118][1])
                }

                eval_3_isog_mod(pts[1173], pts[1181], coeff[109]);
                get_3_isog(pts[1181], A24minus[111], A24plus[111], coeff[110]);
                eval_3_isog_mod(pts[1161], pts[1184], coeff[109]);
                eval_3_isog_mod(pts[1178], pts[1185], coeff[109]);
                lock[119][0] = 0;
                while(lock[119][1]) {
                    #pragma omp flush(lock[119][1])
                }

                eval_3_isog_mod(pts[1182], pts[1188], coeff[110]);
                get_3_isog(pts[1188], A24minus[112], A24plus[112], coeff[111]);
                eval_3_isog_mod(pts[1183], pts[1189], coeff[110]);
                eval_3_isog_mod(pts[1186], pts[1192], coeff[103]);
                eval_3_isog_mod(pts[1189], pts[1194], coeff[111]);
                get_3_isog(pts[1194], A24minus[113], A24plus[113], coeff[112]);
                lock[120][0] = 0;
                while(lock[120][1]) {
                    #pragma omp flush(lock[120][1])
                }

                eval_3_isog_mod(pts[1190], pts[1195], coeff[111]);
                eval_3_isog_mod(pts[1192], pts[1197], coeff[104]);
                eval_3_isog_mod(pts[1195], pts[1199], coeff[112]);
                get_3_isog(pts[1199], A24minus[114], A24plus[114], coeff[113]);
                eval_3_isog_mod(pts[1197], pts[1201], coeff[105]);
                lock[121][0] = 0;
                while(lock[121][1]) {
                    #pragma omp flush(lock[121][1])
                }

                eval_3_isog_mod(pts[1201], pts[1204], coeff[106]);
                eval_3_isog_mod(pts[1202], pts[1205], coeff[94]);
                lock[122][0] = 0;
                while(lock[122][1]) {
                    #pragma omp flush(lock[122][1])
                }

                eval_3_isog_mod(pts[1205], pts[1208], coeff[95]);
                xTPLe(pts[1206], pts[1209], A24minus[114], A24plus[114], 1);
                lock[123][0] = 0;
                while(lock[123][1]) {
                    #pragma omp flush(lock[123][1])
                }

                xTPLe(pts[1209], pts[1212], A24minus[114], A24plus[114], 1);
                eval_3_isog_mod(pts[1210], pts[1213], coeff[109]);
                xTPLe(pts[1212], pts[1216], A24minus[114], A24plus[114], 1);
                eval_3_isog_mod(pts[1213], pts[1217], coeff[110]);
                xTPLe(pts[1216], pts[1220], A24minus[114], A24plus[114], 1);
                eval_3_isog_mod(pts[1217], pts[1221], coeff[111]);
                xTPLe(pts[1220], pts[1224], A24minus[114], A24plus[114], 1);
                get_3_isog(pts[1224], A24minus[115], A24plus[115], coeff[114]);
                eval_3_isog_mod(pts[1221], pts[1225], coeff[112]);
                eval_3_isog_mod(pts[1220], pts[1228], coeff[114]);
                get_3_isog(pts[1228], A24minus[116], A24plus[116], coeff[115]);
                lock[124][0] = 0;
                while(lock[124][1]) {
                    #pragma omp flush(lock[124][1])
                }

                eval_3_isog_mod(pts[1216], pts[1229], coeff[114]);
                eval_3_isog_mod(pts[1203], pts[1232], coeff[114]);
                eval_3_isog_mod(pts[1226], pts[1234], coeff[101]);
                eval_3_isog_mod(pts[1229], pts[1236], coeff[115]);
                get_3_isog(pts[1236], A24minus[117], A24plus[117], coeff[116]);
                lock[125][0] = 0;
                while(lock[125][1]) {
                    #pragma omp flush(lock[125][1])
                }

                eval_3_isog_mod(pts[1231], pts[1238], coeff[115]);
                eval_3_isog_mod(pts[1233], pts[1240], coeff[114]);
                eval_3_isog_mod(pts[1234], pts[1241], coeff[102]);
                eval_3_isog_mod(pts[1238], pts[1244], coeff[116]);
                eval_3_isog_mod(pts[1240], pts[1246], coeff[115]);
                eval_3_isog_mod(pts[1241], pts[1247], coeff[103]);
                lock[126][0] = 0;
                while(lock[126][1]) {
                    #pragma omp flush(lock[126][1])
                }

                eval_3_isog_mod(pts[1244], pts[1249], coeff[117]);
                get_3_isog(pts[1249], A24minus[119], A24plus[119], coeff[118]);
                eval_3_isog_mod(pts[1247], pts[1252], coeff[104]);
                lock[127][0] = 0;
                while(lock[127][1]) {
                    #pragma omp flush(lock[127][1])
                }

                eval_3_isog_mod(pts[1250], pts[1254], coeff[118]);
                eval_3_isog_mod(pts[1251], pts[1255], coeff[117]);
                xTPLe(pts[1254], pts[1258], A24minus[119], A24plus[119], 1);
                get_3_isog(pts[1258], A24minus[120], A24plus[120], coeff[119]);
                eval_3_isog_mod(pts[1255], pts[1259], coeff[118]);
                eval_3_isog_mod(pts[1254], pts[1262], coeff[119]);
                get_3_isog(pts[1262], A24minus[121], A24plus[121], coeff[120]);
                eval_3_isog_mod(pts[1259], pts[1263], coeff[119]);
                eval_3_isog_mod(pts[1263], pts[1266], coeff[120]);
                lock[128][0] = 0;
                while(lock[128][1]) {
                    #pragma omp flush(lock[128][1])
                }

                eval_3_isog_mod(pts[1264], pts[1267], coeff[108]);
                eval_3_isog_mod(pts[1267], pts[1270], coeff[109]);
                lock[129][0] = 0;
                while(lock[129][1]) {
                    #pragma omp flush(lock[129][1])
                }

                eval_3_isog_mod(pts[1268], pts[1271], coeff[12]);
                eval_3_isog_mod(pts[1271], pts[1274], coeff[13]);
                lock[130][0] = 0;
                while(lock[130][1]) {
                    #pragma omp flush(lock[130][1])
                }

                eval_3_isog_mod(pts[1273], pts[1276], coeff[111]);
                eval_3_isog_mod(pts[1274], pts[1277], coeff[14]);
                lock[131][0] = 0;
                while(lock[131][1]) {
                    #pragma omp flush(lock[131][1])
                }

                eval_3_isog_mod(pts[1276], pts[1279], coeff[112]);
                eval_3_isog_mod(pts[1279], pts[1282], coeff[113]);
                lock[132][0] = 0;
                while(lock[132][1]) {
                    #pragma omp flush(lock[132][1])
                }

                xTPLe(pts[1281], pts[1284], A24minus[121], A24plus[121], 1);
                eval_3_isog_mod(pts[1282], pts[1285], coeff[114]);
                lock[133][0] = 0;
                while(lock[133][1]) {
                    #pragma omp flush(lock[133][1])
                }

                xTPLe(pts[1284], pts[1287], A24minus[121], A24plus[121], 1);
                xTPLe(pts[1287], pts[1290], A24minus[121], A24plus[121], 1);
                lock[134][0] = 0;
                while(lock[134][1]) {
                    #pragma omp flush(lock[134][1])
                }

                eval_3_isog_mod(pts[1289], pts[1292], coeff[19]);
                xTPLe(pts[1290], pts[1293], A24minus[121], A24plus[121], 1);
                get_3_isog(pts[1293], A24minus[122], A24plus[122], coeff[121]);
                lock[135][0] = 0;
                while(lock[135][1]) {
                    #pragma omp flush(lock[135][1])
                }

                eval_3_isog_mod(pts[1292], pts[1295], coeff[20]);
                eval_3_isog_mod(pts[1284], pts[1298], coeff[121]);
                eval_3_isog_mod(pts[1275], pts[1300], coeff[121]);
                eval_3_isog_mod(pts[1295], pts[1302], coeff[21]);
                lock[136][0] = 0;
                while(lock[136][1]) {
                    #pragma omp flush(lock[136][1])
                }

                eval_3_isog_mod(pts[1297], pts[1303], coeff[122]);
                get_3_isog(pts[1303], A24minus[124], A24plus[124], coeff[123]);
                eval_3_isog_mod(pts[1300], pts[1306], coeff[122]);
                eval_3_isog_mod(pts[1301], pts[1308], coeff[119]);
                lock[137][0] = 0;
                while(lock[137][1]) {
                    #pragma omp flush(lock[137][1])
                }

                eval_3_isog_mod(pts[1304], pts[1310], coeff[123]);
                get_3_isog(pts[1310], A24minus[125], A24plus[125], coeff[124]);
                eval_3_isog_mod(pts[1306], pts[1312], coeff[123]);
                eval_3_isog_mod(pts[1307], pts[1313], coeff[122]);
                lock[138][0] = 0;
                while(lock[138][1]) {
                    #pragma omp flush(lock[138][1])
                }

                eval_3_isog_mod(pts[1309], pts[1315], coeff[23]);
                eval_3_isog_mod(pts[1313], pts[1318], coeff[123]);
                eval_3_isog_mod(pts[1315], pts[1320], coeff[24]);
                eval_3_isog_mod(pts[1318], pts[1322], coeff[124]);
                eval_3_isog_mod(pts[1320], pts[1324], coeff[25]);
                lock[139][0] = 0;
                while(lock[139][1]) {
                    #pragma omp flush(lock[139][1])
                }

                xTPLe(pts[1321], pts[1325], A24minus[126], A24plus[126], 1);
                get_3_isog(pts[1325], A24minus[127], A24plus[127], coeff[126]);
                eval_3_isog_mod(pts[1323], pts[1327], coeff[123]);
                lock[140][0] = 0;
                while(lock[140][1]) {
                    #pragma omp flush(lock[140][1])
                }

                eval_3_isog_mod(pts[1321], pts[1329], coeff[126]);
                get_3_isog(pts[1329], A24minus[128], A24plus[128], coeff[127]);
                eval_3_isog_mod(pts[1327], pts[1331], coeff[124]);
                lock[141][0] = 0;
                while(lock[141][1]) {
                    #pragma omp flush(lock[141][1])
                }

                eval_3_isog_mod(pts[1330], pts[1333], coeff[127]);
                xTPLe(pts[1333], pts[1336], A24minus[128], A24plus[128], 1);
                lock[142][0] = 0;
                while(lock[142][1]) {
                    #pragma omp flush(lock[142][1])
                }

                eval_3_isog_mod(pts[1335], pts[1338], coeff[29]);
                xTPLe(pts[1336], pts[1339], A24minus[128], A24plus[128], 1);
                get_3_isog(pts[1339], A24minus[129], A24plus[129], coeff[128]);
                lock[143][0] = 0;
                while(lock[143][1]) {
                    #pragma omp flush(lock[143][1])
                }

                eval_3_isog_mod(pts[1338], pts[1341], coeff[30]);
                eval_3_isog_mod(pts[1333], pts[1343], coeff[128]);
                lock[144][0] = 0;
                while(lock[144][1]) {
                    #pragma omp flush(lock[144][1])
                }

                eval_3_isog_mod(pts[1341], pts[1345], coeff[31]);
                eval_3_isog_mod(pts[1345], pts[1348], coeff[32]);
                eval_3_isog_mod(pts[1348], pts[1350], coeff[33]);
                eval_3_isog_mod(pts[1350], pts[1352], coeff[34]);
                eval_3_isog_mod(pts[1352], pts[1354], coeff[35]);
                eval_3_isog_mod(pts[1354], pts[1356], coeff[36]);
                eval_3_isog_mod(pts[1356], pts[1358], coeff[37]);
                eval_3_isog_mod(pts[1358], pts[1360], coeff[38]);
                eval_3_isog_mod(pts[1360], pts[1362], coeff[39]);
                eval_3_isog_mod(pts[1362], pts[1364], coeff[40]);
                eval_3_isog_mod(pts[1364], pts[1366], coeff[41]);
                eval_3_isog_mod(pts[1366], pts[1368], coeff[42]);
                eval_3_isog_mod(pts[1368], pts[1370], coeff[43]);
                eval_3_isog_mod(pts[1370], pts[1372], coeff[44]);
                eval_3_isog_mod(pts[1372], pts[1374], coeff[45]);
                eval_3_isog_mod(pts[1374], pts[1376], coeff[46]);
                eval_3_isog_mod(pts[1376], pts[1378], coeff[47]);
                eval_3_isog_mod(pts[1378], pts[1380], coeff[48]);
                eval_3_isog_mod(pts[1380], pts[1382], coeff[49]);
                eval_3_isog_mod(pts[1382], pts[1384], coeff[50]);
                eval_3_isog_mod(pts[1384], pts[1386], coeff[51]);
                eval_3_isog_mod(pts[1386], pts[1388], coeff[52]);
                eval_3_isog_mod(pts[1388], pts[1390], coeff[53]);
                eval_3_isog_mod(pts[1390], pts[1392], coeff[54]);
                eval_3_isog_mod(pts[1392], pts[1394], coeff[55]);
                eval_3_isog_mod(pts[1394], pts[1396], coeff[56]);
                eval_3_isog_mod(pts[1396], pts[1398], coeff[57]);
                eval_3_isog_mod(pts[1398], pts[1400], coeff[58]);
                eval_3_isog_mod(pts[1400], pts[1402], coeff[59]);
                eval_3_isog_mod(pts[1402], pts[1404], coeff[60]);
                eval_3_isog_mod(pts[1404], pts[1406], coeff[61]);
                eval_3_isog_mod(pts[1406], pts[1408], coeff[62]);
                eval_3_isog_mod(pts[1408], pts[1410], coeff[63]);
                eval_3_isog_mod(pts[1410], pts[1412], coeff[64]);
                eval_3_isog_mod(pts[1412], pts[1414], coeff[65]);
                eval_3_isog_mod(pts[1414], pts[1416], coeff[66]);
                eval_3_isog_mod(pts[1416], pts[1418], coeff[67]);
                eval_3_isog_mod(pts[1418], pts[1420], coeff[68]);
                eval_3_isog_mod(pts[1420], pts[1422], coeff[69]);
                eval_3_isog_mod(pts[1422], pts[1424], coeff[70]);
                eval_3_isog_mod(pts[1424], pts[1426], coeff[71]);
                eval_3_isog_mod(pts[1426], pts[1428], coeff[72]);
                eval_3_isog_mod(pts[1428], pts[1430], coeff[73]);
                eval_3_isog_mod(pts[1430], pts[1432], coeff[74]);
                eval_3_isog_mod(pts[1432], pts[1434], coeff[75]);
                eval_3_isog_mod(pts[1434], pts[1436], coeff[76]);
                eval_3_isog_mod(pts[1436], pts[1438], coeff[77]);
                eval_3_isog_mod(pts[1438], pts[1440], coeff[78]);
                eval_3_isog_mod(pts[1440], pts[1442], coeff[79]);
                eval_3_isog_mod(pts[1442], pts[1444], coeff[80]);
                eval_3_isog_mod(pts[1444], pts[1446], coeff[81]);
                eval_3_isog_mod(pts[1446], pts[1448], coeff[82]);
                lock[145][0] = 0;
                while(lock[145][1]) {
                    #pragma omp flush(lock[145][1])
                }

                eval_3_isog_mod(pts[1443], pts[1450], coeff[131]);
                eval_3_isog_mod(pts[1441], pts[1451], coeff[131]);
                eval_3_isog_mod(pts[1448], pts[1454], coeff[83]);
                lock[146][0] = 0;
                while(lock[146][1]) {
                    #pragma omp flush(lock[146][1])
                }

                eval_3_isog_mod(pts[1451], pts[1456], coeff[132]);
                eval_3_isog_mod(pts[1452], pts[1457], coeff[132]);
                eval_3_isog_mod(pts[1429], pts[1459], coeff[131]);
                lock[147][0] = 0;
                while(lock[147][1]) {
                    #pragma omp flush(lock[147][1])
                }

                eval_3_isog_mod(pts[1456], pts[1461], coeff[133]);
                get_3_isog(pts[1461], A24minus[135], A24plus[135], coeff[134]);
                eval_3_isog_mod(pts[1459], pts[1464], coeff[132]);
                lock[148][0] = 0;
                while(lock[148][1]) {
                    #pragma omp flush(lock[148][1])
                }

                eval_3_isog_mod(pts[1462], pts[1466], coeff[134]);
                get_3_isog(pts[1466], A24minus[136], A24plus[136], coeff[135]);
                eval_3_isog_mod(pts[1463], pts[1467], coeff[134]);
                eval_3_isog_mod(pts[1421], pts[1469], coeff[131]);
                eval_3_isog_mod(pts[1467], pts[1471], coeff[135]);
                eval_3_isog_mod(pts[1469], pts[1473], coeff[132]);
                lock[149][0] = 0;
                while(lock[149][1]) {
                    #pragma omp flush(lock[149][1])
                }

                xTPLe(pts[1471], pts[1475], A24minus[136], A24plus[136], 1);
                get_3_isog(pts[1475], A24minus[137], A24plus[137], coeff[136]);
                eval_3_isog_mod(pts[1474], pts[1478], coeff[88]);
                lock[150][0] = 0;
                while(lock[150][1]) {
                    #pragma omp flush(lock[150][1])
                }

                eval_3_isog_mod(pts[1476], pts[1480], coeff[136]);
                eval_3_isog_mod(pts[1411], pts[1482], coeff[131]);
                lock[151][0] = 0;
                while(lock[151][1]) {
                    #pragma omp flush(lock[151][1])
                }

                eval_3_isog_mod(pts[1480], pts[1484], coeff[137]);
                eval_3_isog_mod(pts[1481], pts[1485], coeff[135]);
                xTPLe(pts[1484], pts[1488], A24minus[138], A24plus[138], 1);
                eval_3_isog_mod(pts[1485], pts[1489], coeff[136]);
                xTPLe(pts[1488], pts[1492], A24minus[138], A24plus[138], 1);
                get_3_isog(pts[1492], A24minus[139], A24plus[139], coeff[138]);
                eval_3_isog_mod(pts[1489], pts[1493], coeff[137]);
                eval_3_isog_mod(pts[1488], pts[1496], coeff[138]);
                get_3_isog(pts[1496], A24minus[140], A24plus[140], coeff[139]);
                lock[152][0] = 0;
                while(lock[152][1]) {
                    #pragma omp flush(lock[152][1])
                }

                eval_3_isog_mod(pts[1493], pts[1498], coeff[138]);
                eval_3_isog_mod(pts[1397], pts[1500], coeff[131]);
                eval_3_isog_mod(pts[1495], pts[1501], coeff[93]);
                eval_3_isog_mod(pts[1498], pts[1503], coeff[139]);
                lock[153][0] = 0;
                while(lock[153][1]) {
                    #pragma omp flush(lock[153][1])
                }

                eval_3_isog_mod(pts[1501], pts[1506], coeff[94]);
                eval_3_isog_mod(pts[1504], pts[1508], coeff[137]);
                eval_3_isog_mod(pts[1506], pts[1510], coeff[95]);
                eval_3_isog_mod(pts[1508], pts[1512], coeff[138]);
                eval_3_isog_mod(pts[1510], pts[1514], coeff[96]);
                eval_3_isog_mod(pts[1512], pts[1516], coeff[139]);
                eval_3_isog_mod(pts[1514], pts[1518], coeff[97]);
                eval_3_isog_mod(pts[1516], pts[1520], coeff[140]);
                eval_3_isog_mod(pts[1518], pts[1522], coeff[98]);
                lock[154][0] = 0;
                while(lock[154][1]) {
                    #pragma omp flush(lock[154][1])
                }

                eval_3_isog_mod(pts[1511], pts[1524], coeff[141]);
                eval_3_isog_mod(pts[1507], pts[1525], coeff[141]);
                eval_3_isog_mod(pts[1521], pts[1527], coeff[137]);
                lock[155][0] = 0;
                while(lock[155][1]) {
                    #pragma omp flush(lock[155][1])
                }

                eval_3_isog_mod(pts[1524], pts[1529], coeff[142]);
                get_3_isog(pts[1529], A24minus[144], A24plus[144], coeff[143]);
                eval_3_isog_mod(pts[1527], pts[1532], coeff[138]);
                eval_3_isog_mod(pts[1377], pts[1533], coeff[131]);
                lock[156][0] = 0;
                while(lock[156][1]) {
                    #pragma omp flush(lock[156][1])
                }

                eval_3_isog_mod(pts[1531], pts[1536], coeff[143]);
                eval_3_isog_mod(pts[1533], pts[1538], coeff[132]);
                lock[157][0] = 0;
                while(lock[157][1]) {
                    #pragma omp flush(lock[157][1])
                }

                eval_3_isog_mod(pts[1536], pts[1540], coeff[144]);
                eval_3_isog_mod(pts[1538], pts[1542], coeff[133]);
                xTPLe(pts[1540], pts[1544], A24minus[145], A24plus[145], 1);
                eval_3_isog_mod(pts[1542], pts[1546], coeff[134]);
                xTPLe(pts[1544], pts[1548], A24minus[145], A24plus[145], 1);
                eval_3_isog_mod(pts[1546], pts[1550], coeff[135]);
                xTPLe(pts[1548], pts[1552], A24minus[145], A24plus[145], 1);
                eval_3_isog_mod(pts[1550], pts[1554], coeff[136]);
                xTPLe(pts[1552], pts[1556], A24minus[145], A24plus[145], 1);
                get_3_isog(pts[1556], A24minus[146], A24plus[146], coeff[145]);
                eval_3_isog_mod(pts[1554], pts[1558], coeff[137]);
                eval_3_isog_mod(pts[1552], pts[1560], coeff[145]);
                get_3_isog(pts[1560], A24minus[147], A24plus[147], coeff[146]);
                lock[158][0] = 0;
                while(lock[158][1]) {
                    #pragma omp flush(lock[158][1])
                }

                eval_3_isog_mod(pts[1548], pts[1561], coeff[145]);
                eval_3_isog_mod(pts[1557], pts[1564], coeff[145]);
                eval_3_isog_mod(pts[1559], pts[1566], coeff[107]);
                eval_3_isog_mod(pts[1561], pts[1567], coeff[146]);
                get_3_isog(pts[1567], A24minus[148], A24plus[148], coeff[147]);
                eval_3_isog_mod(pts[1564], pts[1570], coeff[146]);
                eval_3_isog_mod(pts[1566], pts[1572], coeff[108]);
                lock[159][0] = 0;
                while(lock[159][1]) {
                    #pragma omp flush(lock[159][1])
                }

                eval_3_isog_mod(pts[1568], pts[1573], coeff[147]);
                get_3_isog(pts[1573], A24minus[149], A24plus[149], coeff[148]);
                eval_3_isog_mod(pts[1571], pts[1576], coeff[140]);
                lock[160][0] = 0;
                while(lock[160][1]) {
                    #pragma omp flush(lock[160][1])
                }

                eval_3_isog_mod(pts[1572], pts[1577], coeff[109]);
                eval_3_isog_mod(pts[1575], pts[1579], coeff[148]);
                lock[161][0] = 0;
                while(lock[161][1]) {
                    #pragma omp flush(lock[161][1])
                }

                eval_3_isog_mod(pts[1577], pts[1581], coeff[110]);
                eval_3_isog_mod(pts[1581], pts[1584], coeff[111]);
                lock[162][0] = 0;
                while(lock[162][1]) {
                    #pragma omp flush(lock[162][1])
                }

                eval_3_isog_mod(pts[1583], pts[1586], coeff[143]);
                eval_3_isog_mod(pts[1349], pts[1587], coeff[131]);
                eval_3_isog_mod(pts[1586], pts[1590], coeff[144]);
                eval_3_isog_mod(pts[1587], pts[1591], coeff[132]);
                eval_3_isog_mod(pts[1590], pts[1594], coeff[145]);
                eval_3_isog_mod(pts[1591], pts[1595], coeff[133]);
                eval_3_isog_mod(pts[1594], pts[1598], coeff[146]);
                eval_3_isog_mod(pts[1595], pts[1599], coeff[134]);
                eval_3_isog_mod(pts[1598], pts[1602], coeff[147]);
                eval_3_isog_mod(pts[1599], pts[1603], coeff[135]);
                eval_3_isog_mod(pts[1602], pts[1606], coeff[148]);
                eval_3_isog_mod(pts[1603], pts[1607], coeff[136]);
                lock[163][0] = 0;
                while(lock[163][1]) {
                    #pragma omp flush(lock[163][1])
                }

                eval_3_isog_mod(pts[1601], pts[1609], coeff[150]);
                get_3_isog(pts[1609], A24minus[152], A24plus[152], coeff[151]);
                eval_3_isog_mod(pts[1593], pts[1611], coeff[150]);
                eval_3_isog_mod(pts[1582], pts[1613], coeff[150]);
                eval_3_isog_mod(pts[1607], pts[1615], coeff[137]);
                lock[164][0] = 0;
                while(lock[164][1]) {
                    #pragma omp flush(lock[164][1])
                }

                eval_3_isog_mod(pts[1611], pts[1618], coeff[151]);
                eval_3_isog_mod(pts[1612], pts[1619], coeff[151]);
                eval_3_isog_mod(pts[1615], pts[1622], coeff[138]);
                lock[165][0] = 0;
                while(lock[165][1]) {
                    #pragma omp flush(lock[165][1])
                }

                eval_3_isog_mod(pts[1616], pts[1623], coeff[119]);
                eval_3_isog_mod(pts[1619], pts[1625], coeff[152]);
                eval_3_isog_mod(pts[1622], pts[1628], coeff[139]);
                lock[166][0] = 0;
                while(lock[166][1]) {
                    #pragma omp flush(lock[166][1])
                }

                eval_3_isog_mod(pts[1625], pts[1630], coeff[153]);
                get_3_isog(pts[1630], A24minus[155], A24plus[155], coeff[154]);
                eval_3_isog_mod(pts[1627], pts[1632], coeff[152]);
                eval_3_isog_mod(pts[1628], pts[1633], coeff[140]);
                lock[167][0] = 0;
                while(lock[167][1]) {
                    #pragma omp flush(lock[167][1])
                }

                eval_3_isog_mod(pts[1631], pts[1635], coeff[154]);
                eval_3_isog_mod(pts[1633], pts[1637], coeff[141]);
                xTPLe(pts[1635], pts[1639], A24minus[155], A24plus[155], 1);
                get_3_isog(pts[1639], A24minus[156], A24plus[156], coeff[155]);
                eval_3_isog_mod(pts[1637], pts[1641], coeff[142]);
                lock[168][0] = 0;
                while(lock[168][1]) {
                    #pragma omp flush(lock[168][1])
                }

                eval_3_isog_mod(pts[1635], pts[1643], coeff[155]);
                get_3_isog(pts[1643], A24minus[157], A24plus[157], coeff[156]);
                eval_3_isog_mod(pts[1642], pts[1646], coeff[124]);
                lock[169][0] = 0;
                while(lock[169][1]) {
                    #pragma omp flush(lock[169][1])
                }

                eval_3_isog_mod(pts[1645], pts[1648], coeff[144]);
                eval_3_isog_mod(pts[1646], pts[1649], coeff[125]);
                lock[170][0] = 0;
                while(lock[170][1]) {
                    #pragma omp flush(lock[170][1])
                }

                eval_3_isog_mod(pts[1649], pts[1652], coeff[126]);
                xTPLe(pts[1650], pts[1653], A24minus[157], A24plus[157], 1);
                lock[171][0] = 0;
                while(lock[171][1]) {
                    #pragma omp flush(lock[171][1])
                }

                eval_3_isog_mod(pts[1652], pts[1655], coeff[127]);
                eval_3_isog_mod(pts[1655], pts[1658], coeff[128]);
                lock[172][0] = 0;
                while(lock[172][1]) {
                    #pragma omp flush(lock[172][1])
                }

                xTPLe(pts[1656], pts[1659], A24minus[157], A24plus[157], 1);
                xTPLe(pts[1659], pts[1662], A24minus[157], A24plus[157], 1);
                lock[173][0] = 0;
                while(lock[173][1]) {
                    #pragma omp flush(lock[173][1])
                }

                eval_3_isog_mod(pts[1660], pts[1663], coeff[149]);
                eval_3_isog_mod(pts[1663], pts[1666], coeff[150]);
                lock[174][0] = 0;
                while(lock[174][1]) {
                    #pragma omp flush(lock[174][1])
                }

                eval_3_isog_mod(pts[1664], pts[1667], coeff[131]);
                eval_3_isog_mod(pts[1667], pts[1670], coeff[132]);
                lock[175][0] = 0;
                while(lock[175][1]) {
                    #pragma omp flush(lock[175][1])
                }

                xTPLe(pts[1668], pts[1671], A24minus[157], A24plus[157], 1);
                xTPLe(pts[1671], pts[1674], A24minus[157], A24plus[157], 1);
                get_3_isog(pts[1674], A24minus[158], A24plus[158], coeff[157]);
                lock[176][0] = 0;
                while(lock[176][1]) {
                    #pragma omp flush(lock[176][1])
                }

                eval_3_isog_mod(pts[1672], pts[1675], coeff[153]);
                eval_3_isog_mod(pts[1668], pts[1678], coeff[157]);
                eval_3_isog_mod(pts[1665], pts[1679], coeff[157]);
                eval_3_isog_mod(pts[1675], pts[1682], coeff[154]);
                lock[177][0] = 0;
                while(lock[177][1]) {
                    #pragma omp flush(lock[177][1])
                }

                eval_3_isog_mod(pts[1678], pts[1684], coeff[158]);
                get_3_isog(pts[1684], A24minus[160], A24plus[160], coeff[159]);
                eval_3_isog_mod(pts[1679], pts[1685], coeff[158]);
                eval_3_isog_mod(pts[1681], pts[1687], coeff[158]);
                eval_3_isog_mod(pts[1682], pts[1689], coeff[155]);
                lock[178][0] = 0;
                while(lock[178][1]) {
                    #pragma omp flush(lock[178][1])
                }

                eval_3_isog_mod(pts[1686], pts[1692], coeff[159]);
                eval_3_isog_mod(pts[1687], pts[1693], coeff[159]);
                eval_3_isog_mod(pts[1689], pts[1695], coeff[156]);
                lock[179][0] = 0;
                while(lock[179][1]) {
                    #pragma omp flush(lock[179][1])
                }

                eval_3_isog_mod(pts[1693], pts[1698], coeff[160]);
                eval_3_isog_mod(pts[1695], pts[1700], coeff[157]);
                lock[180][0] = 0;
                while(lock[180][1]) {
                    #pragma omp flush(lock[180][1])
                }

                eval_3_isog_mod(pts[1698], pts[1702], coeff[161]);
                eval_3_isog_mod(pts[1700], pts[1704], coeff[158]);
                xTPLe(pts[1702], pts[1706], A24minus[162], A24plus[162], 1);
                get_3_isog(pts[1706], A24minus[163], A24plus[163], coeff[162]);
                eval_3_isog_mod(pts[1704], pts[1708], coeff[159]);
                eval_3_isog_mod(pts[1702], pts[1710], coeff[162]);
                get_3_isog(pts[1710], A24minus[164], A24plus[164], coeff[163]);
                lock[181][0] = 0;
                while(lock[181][1]) {
                    #pragma omp flush(lock[181][1])
                }

                eval_3_isog_mod(pts[1707], pts[1711], coeff[162]);
                eval_3_isog_mod(pts[1711], pts[1714], coeff[163]);
                lock[182][0] = 0;
                while(lock[182][1]) {
                    #pragma omp flush(lock[182][1])
                }

                eval_3_isog_mod(pts[1713], pts[1716], coeff[142]);
                xTPLe(pts[1714], pts[1717], A24minus[164], A24plus[164], 1);
                lock[183][0] = 0;
                while(lock[183][1]) {
                    #pragma omp flush(lock[183][1])
                }

                eval_3_isog_mod(pts[1716], pts[1719], coeff[143]);
                eval_3_isog_mod(pts[1719], pts[1722], coeff[144]);
                lock[184][0] = 0;
                while(lock[184][1]) {
                    #pragma omp flush(lock[184][1])
                }

                eval_3_isog_mod(pts[1714], pts[1724], coeff[164]);
                eval_3_isog_mod(pts[1722], pts[1726], coeff[145]);
                lock[185][0] = 0;
                while(lock[185][1]) {
                    #pragma omp flush(lock[185][1])
                }

                eval_3_isog_mod(pts[1725], pts[1728], coeff[165]);
                lock[186][0] = 0;
                while(lock[186][1]) {
                    #pragma omp flush(lock[186][1])
                }

                eval_3_isog_mod(pts[1728], pts[1730], coeff[166]);
                xTPLe(pts[1730], pts[1732], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1732], pts[1734], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1734], pts[1736], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1736], pts[1738], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1738], pts[1740], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1740], pts[1742], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1742], pts[1744], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1744], pts[1746], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1746], pts[1748], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1748], pts[1750], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1750], pts[1752], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1752], pts[1754], A24minus[167], A24plus[167], 1);
                xTPLe(pts[1754], pts[1756], A24minus[167], A24plus[167], 1);
                get_3_isog(pts[1756], A24minus[168], A24plus[168], coeff[167]);
                eval_3_isog_mod(pts[1754], pts[1758], coeff[167]);
                get_3_isog(pts[1758], A24minus[169], A24plus[169], coeff[168]);
                lock[187][0] = 0;
                while(lock[187][1]) {
                    #pragma omp flush(lock[187][1])
                }

                eval_3_isog_mod(pts[1750], pts[1760], coeff[167]);
                eval_3_isog_mod(pts[1744], pts[1762], coeff[167]);
                eval_3_isog_mod(pts[1757], pts[1763], coeff[161]);
                eval_3_isog_mod(pts[1760], pts[1765], coeff[168]);
                eval_3_isog_mod(pts[1762], pts[1767], coeff[168]);
                lock[188][0] = 0;
                while(lock[188][1]) {
                    #pragma omp flush(lock[188][1])
                }

                eval_3_isog_mod(pts[1763], pts[1769], coeff[162]);
                eval_3_isog_mod(pts[1767], pts[1772], coeff[169]);
                eval_3_isog_mod(pts[1769], pts[1774], coeff[163]);
                lock[189][0] = 0;
                while(lock[189][1]) {
                    #pragma omp flush(lock[189][1])
                }

                eval_3_isog_mod(pts[1771], pts[1775], coeff[170]);
                get_3_isog(pts[1775], A24minus[172], A24plus[172], coeff[171]);
                eval_3_isog_mod(pts[1773], pts[1777], coeff[169]);
                lock[190][0] = 0;
                while(lock[190][1]) {
                    #pragma omp flush(lock[190][1])
                }

                eval_3_isog_mod(pts[1774], pts[1779], coeff[164]);
                eval_3_isog_mod(pts[1778], pts[1782], coeff[168]);
                eval_3_isog_mod(pts[1779], pts[1783], coeff[165]);
                eval_3_isog_mod(pts[1782], pts[1786], coeff[169]);
                eval_3_isog_mod(pts[1783], pts[1787], coeff[166]);
                eval_3_isog_mod(pts[1786], pts[1790], coeff[170]);
                eval_3_isog_mod(pts[1787], pts[1791], coeff[167]);
                lock[191][0] = 0;
                while(lock[191][1]) {
                    #pragma omp flush(lock[191][1])
                }

                eval_3_isog_mod(pts[1791], pts[1794], coeff[168]);
                xTPLe(pts[1792], pts[1795], A24minus[174], A24plus[174], 1);
                lock[192][0] = 0;
                while(lock[192][1]) {
                    #pragma omp flush(lock[192][1])
                }

                xTPLe(pts[1795], pts[1798], A24minus[174], A24plus[174], 1);
                get_3_isog(pts[1798], A24minus[175], A24plus[175], coeff[174]);
                eval_3_isog_mod(pts[1796], pts[1799], coeff[173]);
                lock[193][0] = 0;
                while(lock[193][1]) {
                    #pragma omp flush(lock[193][1])
                }

                eval_3_isog_mod(pts[1795], pts[1801], coeff[174]);
                get_3_isog(pts[1801], A24minus[176], A24plus[176], coeff[175]);
                eval_3_isog_mod(pts[1799], pts[1803], coeff[174]);
                lock[194][0] = 0;
                while(lock[194][1]) {
                    #pragma omp flush(lock[194][1])
                }

                eval_3_isog_mod(pts[1802], pts[1805], coeff[175]);
                get_3_isog(pts[1805], A24minus[177], A24plus[177], coeff[176]);
                lock[195][0] = 0;
                while(lock[195][1]) {
                    #pragma omp flush(lock[195][1])
                }

                eval_3_isog_mod(pts[1806], pts[1808], coeff[176]);
                xTPLe(pts[1808], pts[1810], A24minus[177], A24plus[177], 1);
                xTPLe(pts[1810], pts[1812], A24minus[177], A24plus[177], 1);
                xTPLe(pts[1812], pts[1814], A24minus[177], A24plus[177], 1);
                get_3_isog(pts[1814], A24minus[178], A24plus[178], coeff[177]);
                eval_3_isog_mod(pts[1812], pts[1816], coeff[177]);
                get_3_isog(pts[1816], A24minus[179], A24plus[179], coeff[178]);
                lock[196][0] = 0;
                while(lock[196][1]) {
                    #pragma omp flush(lock[196][1])
                }

                eval_3_isog_mod(pts[1810], pts[1817], coeff[177]);
                eval_3_isog_mod(pts[1817], pts[1820], coeff[178]);
                get_3_isog(pts[1820], A24minus[180], A24plus[180], coeff[179]);
                lock[197][0] = 0;
                while(lock[197][1]) {
                    #pragma omp flush(lock[197][1])
                }

                eval_3_isog_mod(pts[1819], pts[1822], coeff[178]);
                eval_3_isog_mod(pts[1822], pts[1824], coeff[179]);
                lock[198][0] = 0;
                while(lock[198][1]) {
                    #pragma omp flush(lock[198][1])
                }

                eval_3_isog_mod(pts[1824], pts[1825], coeff[180]);
                xTPLe(pts[1825], pts[1826], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1826], pts[1827], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1827], pts[1828], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1828], pts[1829], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1829], pts[1830], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1830], pts[1831], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1831], pts[1832], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1832], pts[1833], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1833], pts[1834], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1834], pts[1835], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1835], pts[1836], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1836], pts[1837], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1837], pts[1838], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1838], pts[1839], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1839], pts[1840], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1840], pts[1841], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1841], pts[1842], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1842], pts[1843], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1843], pts[1844], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1844], pts[1845], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1845], pts[1846], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1846], pts[1847], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1847], pts[1848], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1848], pts[1849], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1849], pts[1850], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1850], pts[1851], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1851], pts[1852], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1852], pts[1853], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1853], pts[1854], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1854], pts[1855], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1855], pts[1856], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1856], pts[1857], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1857], pts[1858], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1858], pts[1859], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1859], pts[1860], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1860], pts[1861], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1861], pts[1862], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1862], pts[1863], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1863], pts[1864], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1864], pts[1865], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1865], pts[1866], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1866], pts[1867], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1867], pts[1868], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1868], pts[1869], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1869], pts[1870], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1870], pts[1871], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1871], pts[1872], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1872], pts[1873], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1873], pts[1874], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1874], pts[1875], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1875], pts[1876], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1876], pts[1877], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1877], pts[1878], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1878], pts[1879], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1879], pts[1880], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1880], pts[1881], A24minus[181], A24plus[181], 1);
                xTPLe(pts[1881], pts[1882], A24minus[181], A24plus[181], 1);
                get_3_isog(pts[1882], A24minus[182], A24plus[182], coeff[181]);
                lock[199][0] = 0;
                while(lock[199][1]) {
                    #pragma omp flush(lock[199][1])
                }

                eval_3_isog_mod(pts[1881], pts[1883], coeff[181]);
                get_3_isog(pts[1883], A24minus[183], A24plus[183], coeff[182]);
                eval_3_isog_mod(pts[1879], pts[1885], coeff[181]);
                lock[200][0] = 0;
                while(lock[200][1]) {
                    #pragma omp flush(lock[200][1])
                }

                eval_3_isog_mod(pts[1876], pts[1887], coeff[181]);
                eval_3_isog_mod(pts[1885], pts[1889], coeff[182]);
                eval_3_isog_mod(pts[1887], pts[1891], coeff[182]);
                lock[201][0] = 0;
                while(lock[201][1]) {
                    #pragma omp flush(lock[201][1])
                }

                eval_3_isog_mod(pts[1890], pts[1894], coeff[183]);
                eval_3_isog_mod(pts[1892], pts[1896], coeff[182]);
                lock[202][0] = 0;
                while(lock[202][1]) {
                    #pragma omp flush(lock[202][1])
                }

                eval_3_isog_mod(pts[1894], pts[1897], coeff[184]);
                get_3_isog(pts[1897], A24minus[186], A24plus[186], coeff[185]);
                eval_3_isog_mod(pts[1869], pts[1900], coeff[181]);
                lock[203][0] = 0;
                while(lock[203][1]) {
                    #pragma omp flush(lock[203][1])
                }

                eval_3_isog_mod(pts[1898], pts[1901], coeff[185]);
                xTPLe(pts[1901], pts[1904], A24minus[186], A24plus[186], 1);
                get_3_isog(pts[1904], A24minus[187], A24plus[187], coeff[186]);
                lock[204][0] = 0;
                while(lock[204][1]) {
                    #pragma omp flush(lock[204][1])
                }

                eval_3_isog_mod(pts[1902], pts[1905], coeff[185]);
                eval_3_isog_mod(pts[1905], pts[1908], coeff[186]);
                eval_3_isog_mod(pts[1864], pts[1910], coeff[181]);
                lock[205][0] = 0;
                while(lock[205][1]) {
                    #pragma omp flush(lock[205][1])
                }

                eval_3_isog_mod(pts[1908], pts[1911], coeff[187]);
                xTPLe(pts[1911], pts[1914], A24minus[188], A24plus[188], 1);
                lock[206][0] = 0;
                while(lock[206][1]) {
                    #pragma omp flush(lock[206][1])
                }

                eval_3_isog_mod(pts[1913], pts[1916], coeff[183]);
                xTPLe(pts[1914], pts[1917], A24minus[188], A24plus[188], 1);
                get_3_isog(pts[1917], A24minus[189], A24plus[189], coeff[188]);
                lock[207][0] = 0;
                while(lock[207][1]) {
                    #pragma omp flush(lock[207][1])
                }

                eval_3_isog_mod(pts[1916], pts[1919], coeff[184]);
                eval_3_isog_mod(pts[1911], pts[1921], coeff[188]);
                eval_3_isog_mod(pts[1919], pts[1923], coeff[185]);
                lock[208][0] = 0;
                while(lock[208][1]) {
                    #pragma omp flush(lock[208][1])
                }

                eval_3_isog_mod(pts[1921], pts[1925], coeff[189]);
                get_3_isog(pts[1925], A24minus[191], A24plus[191], coeff[190]);
                eval_3_isog_mod(pts[1923], pts[1927], coeff[186]);
                lock[209][0] = 0;
                while(lock[209][1]) {
                    #pragma omp flush(lock[209][1])
                }

                eval_3_isog_mod(pts[1926], pts[1929], coeff[190]);
                xTPLe(pts[1929], pts[1932], A24minus[191], A24plus[191], 1);
                lock[210][0] = 0;
                while(lock[210][1]) {
                    #pragma omp flush(lock[210][1])
                }

                eval_3_isog_mod(pts[1931], pts[1934], coeff[184]);
                xTPLe(pts[1932], pts[1935], A24minus[191], A24plus[191], 1);
                lock[211][0] = 0;
                while(lock[211][1]) {
                    #pragma omp flush(lock[211][1])
                }

                eval_3_isog_mod(pts[1934], pts[1937], coeff[185]);
                eval_3_isog_mod(pts[1937], pts[1940], coeff[186]);
                eval_3_isog_mod(pts[1848], pts[1941], coeff[181]);
                lock[212][0] = 0;
                while(lock[212][1]) {
                    #pragma omp flush(lock[212][1])
                }

                eval_3_isog_mod(pts[1929], pts[1944], coeff[191]);
                eval_3_isog_mod(pts[1939], pts[1945], coeff[191]);
                eval_3_isog_mod(pts[1941], pts[1947], coeff[182]);
                lock[213][0] = 0;
                while(lock[213][1]) {
                    #pragma omp flush(lock[213][1])
                }

                eval_3_isog_mod(pts[1945], pts[1950], coeff[192]);
                eval_3_isog_mod(pts[1946], pts[1951], coeff[188]);
                eval_3_isog_mod(pts[1950], pts[1954], coeff[193]);
                eval_3_isog_mod(pts[1951], pts[1955], coeff[189]);
                lock[214][0] = 0;
                while(lock[214][1]) {
                    #pragma omp flush(lock[214][1])
                }

                eval_3_isog_mod(pts[1954], pts[1957], coeff[194]);
                xTPLe(pts[1957], pts[1960], A24minus[195], A24plus[195], 1);
                lock[215][0] = 0;
                while(lock[215][1]) {
                    #pragma omp flush(lock[215][1])
                }

                eval_3_isog_mod(pts[1959], pts[1962], coeff[186]);
                xTPLe(pts[1960], pts[1963], A24minus[195], A24plus[195], 1);
                lock[216][0] = 0;
                while(lock[216][1]) {
                    #pragma omp flush(lock[216][1])
                }

                xTPLe(pts[1963], pts[1966], A24minus[195], A24plus[195], 1);
                eval_3_isog_mod(pts[1964], pts[1967], coeff[193]);
                lock[217][0] = 0;
                while(lock[217][1]) {
                    #pragma omp flush(lock[217][1])
                }

                xTPLe(pts[1966], pts[1969], A24minus[195], A24plus[195], 1);
                get_3_isog(pts[1969], A24minus[196], A24plus[196], coeff[195]);
                lock[218][0] = 0;
                while(lock[218][1]) {
                    #pragma omp flush(lock[218][1])
                }

                eval_3_isog_mod(pts[1968], pts[1971], coeff[189]);
                eval_3_isog_mod(pts[1960], pts[1974], coeff[195]);
                eval_3_isog_mod(pts[1970], pts[1976], coeff[195]);
                eval_3_isog_mod(pts[1971], pts[1977], coeff[190]);
                lock[219][0] = 0;
                while(lock[219][1]) {
                    #pragma omp flush(lock[219][1])
                }

                eval_3_isog_mod(pts[1974], pts[1979], coeff[196]);
                eval_3_isog_mod(pts[1976], pts[1981], coeff[196]);
                eval_3_isog_mod(pts[1979], pts[1983], coeff[197]);
                get_3_isog(pts[1983], A24minus[199], A24plus[199], coeff[198]);
                eval_3_isog_mod(pts[1981], pts[1985], coeff[197]);
                lock[220][0] = 0;
                while(lock[220][1]) {
                    #pragma omp flush(lock[220][1])
                }

                eval_3_isog_mod(pts[1984], pts[1987], coeff[198]);
                get_3_isog(pts[1987], A24minus[200], A24plus[200], coeff[199]);
                eval_3_isog_mod(pts[1837], pts[1990], coeff[181]);
                lock[221][0] = 0;
                while(lock[221][1]) {
                    #pragma omp flush(lock[221][1])
                }

                eval_3_isog_mod(pts[1988], pts[1991], coeff[199]);
                xTPLe(pts[1991], pts[1994], A24minus[200], A24plus[200], 1);
                lock[222][0] = 0;
                while(lock[222][1]) {
                    #pragma omp flush(lock[222][1])
                }

                eval_3_isog_mod(pts[1993], pts[1996], coeff[183]);
                xTPLe(pts[1994], pts[1997], A24minus[200], A24plus[200], 1);
                lock[223][0] = 0;
                while(lock[223][1]) {
                    #pragma omp flush(lock[223][1])
                }

                xTPLe(pts[1997], pts[2000], A24minus[200], A24plus[200], 1);
                eval_3_isog_mod(pts[1998], pts[2001], coeff[197]);
                lock[224][0] = 0;
                while(lock[224][1]) {
                    #pragma omp flush(lock[224][1])
                }

                eval_3_isog_mod(pts[2001], pts[2004], coeff[198]);
                eval_3_isog_mod(pts[2002], pts[2005], coeff[186]);
                lock[225][0] = 0;
                while(lock[225][1]) {
                    #pragma omp flush(lock[225][1])
                }

                eval_3_isog_mod(pts[2004], pts[2007], coeff[199]);
                eval_3_isog_mod(pts[2003], pts[2009], coeff[200]);
                get_3_isog(pts[2009], A24minus[202], A24plus[202], coeff[201]);
                eval_3_isog_mod(pts[1997], pts[2011], coeff[200]);
                eval_3_isog_mod(pts[2007], pts[2014], coeff[200]);
                lock[226][0] = 0;
                while(lock[226][1]) {
                    #pragma omp flush(lock[226][1])
                }

                eval_3_isog_mod(pts[2008], pts[2015], coeff[188]);
                eval_3_isog_mod(pts[2012], pts[2018], coeff[201]);
                eval_3_isog_mod(pts[2014], pts[2020], coeff[201]);
                eval_3_isog_mod(pts[2015], pts[2021], coeff[189]);
                lock[227][0] = 0;
                while(lock[227][1]) {
                    #pragma omp flush(lock[227][1])
                }

                eval_3_isog_mod(pts[2018], pts[2023], coeff[202]);
                eval_3_isog_mod(pts[2020], pts[2025], coeff[202]);
                eval_3_isog_mod(pts[2023], pts[2027], coeff[203]);
                get_3_isog(pts[2027], A24minus[205], A24plus[205], coeff[204]);
                eval_3_isog_mod(pts[2025], pts[2029], coeff[203]);
                lock[228][0] = 0;
                while(lock[228][1]) {
                    #pragma omp flush(lock[228][1])
                }

                eval_3_isog_mod(pts[2029], pts[2032], coeff[204]);
                lock[229][0] = 0;
                while(lock[229][1]) {
                    #pragma omp flush(lock[229][1])
                }

                eval_3_isog_mod(pts[2032], pts[2034], coeff[205]);
                xTPLe(pts[2034], pts[2036], A24minus[206], A24plus[206], 1);
                eval_3_isog_mod(pts[1825], pts[2038], coeff[181]);
                xTPLe(pts[2036], pts[2039], A24minus[206], A24plus[206], 1);
                lock[230][0] = 0;
                while(lock[230][1]) {
                    #pragma omp flush(lock[230][1])
                }

                eval_3_isog_mod(pts[2038], pts[2041], coeff[182]);
                eval_3_isog_mod(pts[2041], pts[2044], coeff[183]);
                lock[231][0] = 0;
                while(lock[231][1]) {
                    #pragma omp flush(lock[231][1])
                }

                eval_3_isog_mod(pts[2043], pts[2046], coeff[197]);
                eval_3_isog_mod(pts[2044], pts[2047], coeff[184]);
                lock[232][0] = 0;
                while(lock[232][1]) {
                    #pragma omp flush(lock[232][1])
                }

                eval_3_isog_mod(pts[2046], pts[2049], coeff[198]);
                eval_3_isog_mod(pts[2049], pts[2052], coeff[199]);
                lock[233][0] = 0;
                while(lock[233][1]) {
                    #pragma omp flush(lock[233][1])
                }

                xTPLe(pts[2051], pts[2054], A24minus[206], A24plus[206], 1);
                eval_3_isog_mod(pts[2052], pts[2055], coeff[200]);
                lock[234][0] = 0;
                while(lock[234][1]) {
                    #pragma omp flush(lock[234][1])
                }

                eval_3_isog_mod(pts[2055], pts[2058], coeff[201]);
                eval_3_isog_mod(pts[2056], pts[2059], coeff[188]);
                lock[235][0] = 0;
                while(lock[235][1]) {
                    #pragma omp flush(lock[235][1])
                }

                eval_3_isog_mod(pts[2059], pts[2062], coeff[189]);
                eval_3_isog_mod(pts[2054], pts[2064], coeff[206]);
                eval_3_isog_mod(pts[2051], pts[2065], coeff[206]);
                eval_3_isog_mod(pts[2042], pts[2067], coeff[206]);
                lock[236][0] = 0;
                while(lock[236][1]) {
                    #pragma omp flush(lock[236][1])
                }

                eval_3_isog_mod(pts[2062], pts[2069], coeff[190]);
                eval_3_isog_mod(pts[2066], pts[2072], coeff[207]);
                eval_3_isog_mod(pts[2067], pts[2073], coeff[207]);
                eval_3_isog_mod(pts[2069], pts[2076], coeff[191]);
                lock[237][0] = 0;
                while(lock[237][1]) {
                    #pragma omp flush(lock[237][1])
                }

                eval_3_isog_mod(pts[2072], pts[2078], coeff[208]);
                eval_3_isog_mod(pts[2074], pts[2080], coeff[207]);
                eval_3_isog_mod(pts[2076], pts[2082], coeff[192]);
                lock[238][0] = 0;
                while(lock[238][1]) {
                    #pragma omp flush(lock[238][1])
                }

                eval_3_isog_mod(pts[2079], pts[2084], coeff[209]);
                eval_3_isog_mod(pts[2080], pts[2085], coeff[208]);
                lock[239][0] = 0;
                while(lock[239][1]) {
                    #pragma omp flush(lock[239][1])
                }

                eval_3_isog_mod(pts[2084], pts[2088], coeff[210]);
                eval_3_isog_mod(pts[2086], pts[2090], coeff[207]);
                xTPLe(pts[2088], pts[2092], A24minus[211], A24plus[211], 1);
                get_3_isog(pts[2092], A24minus[212], A24plus[212], coeff[211]);
                eval_3_isog_mod(pts[2090], pts[2094], coeff[208]);
                eval_3_isog_mod(pts[2088], pts[2096], coeff[211]);
                get_3_isog(pts[2096], A24minus[213], A24plus[213], coeff[212]);
                lock[240][0] = 0;
                while(lock[240][1]) {
                    #pragma omp flush(lock[240][1])
                }

                eval_3_isog_mod(pts[2093], pts[2097], coeff[211]);
                eval_3_isog_mod(pts[2097], pts[2100], coeff[212]);
                lock[241][0] = 0;
                while(lock[241][1]) {
                    #pragma omp flush(lock[241][1])
                }

                eval_3_isog_mod(pts[2098], pts[2101], coeff[210]);
                eval_3_isog_mod(pts[2101], pts[2104], coeff[211]);
                lock[242][0] = 0;
                while(lock[242][1]) {
                    #pragma omp flush(lock[242][1])
                }

                eval_3_isog_mod(pts[2102], pts[2105], coeff[198]);
                eval_3_isog_mod(pts[2105], pts[2108], coeff[199]);
                lock[243][0] = 0;
                while(lock[243][1]) {
                    #pragma omp flush(lock[243][1])
                }

                eval_3_isog_mod(pts[2103], pts[2109], coeff[213]);
                get_3_isog(pts[2109], A24minus[215], A24plus[215], coeff[214]);
                eval_3_isog_mod(pts[2108], pts[2112], coeff[200]);
                lock[244][0] = 0;
                while(lock[244][1]) {
                    #pragma omp flush(lock[244][1])
                }

                eval_3_isog_mod(pts[2111], pts[2114], coeff[214]);
                lock[245][0] = 0;
                while(lock[245][1]) {
                    #pragma omp flush(lock[245][1])
                }

                eval_3_isog_mod(pts[2114], pts[2116], coeff[215]);
                xTPLe(pts[2116], pts[2118], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2118], pts[2120], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2120], pts[2122], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2122], pts[2124], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2124], pts[2126], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2126], pts[2128], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2128], pts[2130], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2130], pts[2132], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2132], pts[2134], A24minus[216], A24plus[216], 1);
                xTPLe(pts[2134], pts[2136], A24minus[216], A24plus[216], 1);
                get_3_isog(pts[2136], A24minus[217], A24plus[217], coeff[216]);
                eval_3_isog_mod(pts[2134], pts[2138], coeff[216]);
                get_3_isog(pts[2138], A24minus[218], A24plus[218], coeff[217]);
                lock[246][0] = 0;
                while(lock[246][1]) {
                    #pragma omp flush(lock[246][1])
                }

                eval_3_isog_mod(pts[2132], pts[2139], coeff[216]);
                eval_3_isog_mod(pts[2128], pts[2141], coeff[216]);
                eval_3_isog_mod(pts[2137], pts[2144], coeff[213]);
                eval_3_isog_mod(pts[2139], pts[2145], coeff[217]);
                get_3_isog(pts[2145], A24minus[219], A24plus[219], coeff[218]);
                eval_3_isog_mod(pts[2141], pts[2147], coeff[217]);
                eval_3_isog_mod(pts[2116], pts[2150], coeff[216]);
                lock[247][0] = 0;
                while(lock[247][1]) {
                    #pragma omp flush(lock[247][1])
                }

                eval_3_isog_mod(pts[2146], pts[2152], coeff[218]);
                get_3_isog(pts[2152], A24minus[220], A24plus[220], coeff[219]);
                eval_3_isog_mod(pts[2148], pts[2154], coeff[218]);
                eval_3_isog_mod(pts[2150], pts[2156], coeff[217]);
                lock[248][0] = 0;
                while(lock[248][1]) {
                    #pragma omp flush(lock[248][1])
                }

                eval_3_isog_mod(pts[2151], pts[2157], coeff[215]);
                eval_3_isog_mod(pts[2154], pts[2159], coeff[219]);
                eval_3_isog_mod(pts[2157], pts[2162], coeff[216]);
                lock[249][0] = 0;
                while(lock[249][1]) {
                    #pragma omp flush(lock[249][1])
                }

                eval_3_isog_mod(pts[2160], pts[2164], coeff[220]);
                eval_3_isog_mod(pts[2161], pts[2165], coeff[219]);
                lock[250][0] = 0;
                while(lock[250][1]) {
                    #pragma omp flush(lock[250][1])
                }

                eval_3_isog_mod(pts[2165], pts[2168], coeff[220]);
                eval_3_isog_mod(pts[2166], pts[2169], coeff[218]);
                lock[251][0] = 0;
                while(lock[251][1]) {
                    #pragma omp flush(lock[251][1])
                }

                eval_3_isog_mod(pts[2169], pts[2172], coeff[219]);
                eval_3_isog_mod(pts[2167], pts[2173], coeff[222]);
                get_3_isog(pts[2173], A24minus[224], A24plus[224], coeff[223]);
                lock[252][0] = 0;
                while(lock[252][1]) {
                    #pragma omp flush(lock[252][1])
                }

                eval_3_isog_mod(pts[2172], pts[2175], coeff[220]);
                eval_3_isog_mod(pts[2175], pts[2177], coeff[221]);
                eval_3_isog_mod(pts[2177], pts[2179], coeff[222]);
                eval_3_isog_mod(pts[2179], pts[2181], coeff[223]);
                lock[253][0] = 0;
                while(lock[253][1]) {
                    #pragma omp flush(lock[253][1])
                }

                eval_3_isog_mod(pts[2176], pts[2183], coeff[224]);
                eval_3_isog_mod(pts[2183], pts[2185], coeff[225]);
                get_3_isog(pts[2185], A24minus[227], A24plus[227], coeff[226]);
                lock[254][0] = 0;
                while(lock[254][1]) {
                    #pragma omp flush(lock[254][1])
                }

                eval_3_isog_mod(pts[2186], pts[2187], coeff[226]);
                xTPLe(pts[2187], pts[2188], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2188], pts[2189], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2189], pts[2190], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2190], pts[2191], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2191], pts[2192], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2192], pts[2193], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2193], pts[2194], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2194], pts[2195], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2195], pts[2196], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2196], pts[2197], A24minus[227], A24plus[227], 1);
                xTPLe(pts[2197], pts[2198], A24minus[227], A24plus[227], 1);
                get_3_isog(pts[2198], A24minus[228], A24plus[228], coeff[227]);
                lock[255][0] = 0;
                while(lock[255][1]) {
                    #pragma omp flush(lock[255][1])
                }

                eval_3_isog_mod(pts[2197], pts[2199], coeff[227]);
                get_3_isog(pts[2199], A24minus[229], A24plus[229], coeff[228]);
                eval_3_isog_mod(pts[2194], pts[2202], coeff[227]);
                eval_3_isog_mod(pts[2193], pts[2203], coeff[227]);
                lock[256][0] = 0;
                while(lock[256][1]) {
                    #pragma omp flush(lock[256][1])
                }

                eval_3_isog_mod(pts[2200], pts[2206], coeff[228]);
                get_3_isog(pts[2206], A24minus[230], A24plus[230], coeff[229]);
                eval_3_isog_mod(pts[2201], pts[2207], coeff[228]);
                eval_3_isog_mod(pts[2204], pts[2210], coeff[228]);
                eval_3_isog_mod(pts[2187], pts[2212], coeff[227]);
                lock[257][0] = 0;
                while(lock[257][1]) {
                    #pragma omp flush(lock[257][1])
                }

                eval_3_isog_mod(pts[2207], pts[2213], coeff[229]);
                get_3_isog(pts[2213], A24minus[231], A24plus[231], coeff[230]);
                eval_3_isog_mod(pts[2210], pts[2216], coeff[229]);
                eval_3_isog_mod(pts[2212], pts[2218], coeff[228]);
                lock[258][0] = 0;
                while(lock[258][1]) {
                    #pragma omp flush(lock[258][1])
                }

                eval_3_isog_mod(pts[2214], pts[2219], coeff[230]);
                get_3_isog(pts[2219], A24minus[232], A24plus[232], coeff[231]);
                eval_3_isog_mod(pts[2216], pts[2221], coeff[230]);
                lock[259][0] = 0;
                while(lock[259][1]) {
                    #pragma omp flush(lock[259][1])
                }

                eval_3_isog_mod(pts[2220], pts[2224], coeff[231]);
                get_3_isog(pts[2224], A24minus[233], A24plus[233], coeff[232]);
                eval_3_isog_mod(pts[2222], pts[2226], coeff[231]);
                lock[260][0] = 0;
                while(lock[260][1]) {
                    #pragma omp flush(lock[260][1])
                }

                eval_3_isog_mod(pts[2225], pts[2228], coeff[232]);
                get_3_isog(pts[2228], A24minus[234], A24plus[234], coeff[233]);
                eval_3_isog_mod(pts[2226], pts[2229], coeff[232]);
                eval_3_isog_mod(pts[2229], pts[2231], coeff[233]);
                lock[261][0] = 0;
                while(lock[261][1]) {
                    #pragma omp flush(lock[261][1])
                }

                eval_3_isog_mod(pts[2232], pts[2234], coeff[233]);
                lock[262][0] = 0;
                while(lock[262][1]) {
                    #pragma omp flush(lock[262][1])
                }

                eval_3_isog_mod(pts[2234], pts[2236], coeff[234]);
                lock[263][0] = 0;
                while(lock[263][1]) {
                    #pragma omp flush(lock[263][1])
                }

                eval_3_isog_mod(pts[2236], pts[2237], coeff[235]);
                xTPLe(pts[2237], pts[2238], A24minus[236], A24plus[236], 1);
                xTPLe(pts[2238], pts[2239], A24minus[236], A24plus[236], 1);
                get_3_isog(pts[2239], A24minus[237], A24plus[237], coeff[236]);
                lock[264][0] = 0;
                while(lock[264][1]) {
                    #pragma omp flush(lock[264][1])
                }

                eval_3_isog_mod(pts[2238], pts[2240], coeff[236]);
                get_3_isog(pts[2240], A24minus[238], A24plus[238], coeff[237]);
            }
            #pragma omp section
            {
                eval_3_isog_mod(pts[237], pts[239], coeff[0]);
                get_3_isog(pts[239], A24minus[2], A24plus[2], coeff[1]);
                eval_3_isog_mod(pts[235], pts[241], coeff[0]);
                lock[0][1] = 0;
                while(lock[0][0]) {
                    #pragma omp flush(lock[0][0])
                }

                eval_3_isog_mod(pts[232], pts[243], coeff[0]);
                eval_3_isog_mod(pts[242], pts[246], coeff[1]);
                eval_3_isog_mod(pts[243], pts[247], coeff[1]);
                lock[1][1] = 0;
                while(lock[1][0]) {
                    #pragma omp flush(lock[1][0])
                }

                eval_3_isog_mod(pts[246], pts[250], coeff[2]);
                eval_3_isog_mod(pts[248], pts[252], coeff[1]);
                lock[2][1] = 0;
                while(lock[2][0]) {
                    #pragma omp flush(lock[2][0])
                }

                eval_3_isog_mod(pts[251], pts[254], coeff[3]);
                eval_3_isog_mod(pts[225], pts[256], coeff[0]);
                lock[3][1] = 0;
                while(lock[3][0]) {
                    #pragma omp flush(lock[3][0])
                }

                eval_3_isog_mod(pts[254], pts[257], coeff[4]);
                xTPLe(pts[257], pts[260], A24minus[5], A24plus[5], 1);
                get_3_isog(pts[260], A24minus[6], A24plus[6], coeff[5]);
                lock[4][1] = 0;
                while(lock[4][0]) {
                    #pragma omp flush(lock[4][0])
                }

                eval_3_isog_mod(pts[258], pts[261], coeff[4]);
                eval_3_isog_mod(pts[261], pts[264], coeff[5]);
                eval_3_isog_mod(pts[220], pts[266], coeff[0]);
                lock[5][1] = 0;
                while(lock[5][0]) {
                    #pragma omp flush(lock[5][0])
                }

                eval_3_isog_mod(pts[264], pts[267], coeff[6]);
                xTPLe(pts[267], pts[270], A24minus[7], A24plus[7], 1);
                lock[6][1] = 0;
                while(lock[6][0]) {
                    #pragma omp flush(lock[6][0])
                }

                eval_3_isog_mod(pts[268], pts[271], coeff[5]);
                eval_3_isog_mod(pts[271], pts[274], coeff[6]);
                lock[7][1] = 0;
                while(lock[7][0]) {
                    #pragma omp flush(lock[7][0])
                }

                eval_3_isog_mod(pts[270], pts[276], coeff[7]);
                get_3_isog(pts[276], A24minus[9], A24plus[9], coeff[8]);
                eval_3_isog_mod(pts[267], pts[277], coeff[7]);
                eval_3_isog_mod(pts[213], pts[280], coeff[0]);
                lock[8][1] = 0;
                while(lock[8][0]) {
                    #pragma omp flush(lock[8][0])
                }

                eval_3_isog_mod(pts[278], pts[282], coeff[8]);
                eval_3_isog_mod(pts[279], pts[283], coeff[5]);
                lock[9][1] = 0;
                while(lock[9][0]) {
                    #pragma omp flush(lock[9][0])
                }

                eval_3_isog_mod(pts[283], pts[286], coeff[6]);
                eval_3_isog_mod(pts[284], pts[287], coeff[2]);
                lock[10][1] = 0;
                while(lock[10][0]) {
                    #pragma omp flush(lock[10][0])
                }

                eval_3_isog_mod(pts[287], pts[290], coeff[3]);
                xTPLe(pts[288], pts[291], A24minus[10], A24plus[10], 1);
                lock[11][1] = 0;
                while(lock[11][0]) {
                    #pragma omp flush(lock[11][0])
                }

                xTPLe(pts[291], pts[294], A24minus[10], A24plus[10], 1);
                get_3_isog(pts[294], A24minus[11], A24plus[11], coeff[10]);
                eval_3_isog_mod(pts[292], pts[295], coeff[9]);
                lock[12][1] = 0;
                while(lock[12][0]) {
                    #pragma omp flush(lock[12][0])
                }

                eval_3_isog_mod(pts[288], pts[298], coeff[10]);
                eval_3_isog_mod(pts[295], pts[300], coeff[10]);
                lock[13][1] = 0;
                while(lock[13][0]) {
                    #pragma omp flush(lock[13][0])
                }

                eval_3_isog_mod(pts[298], pts[302], coeff[11]);
                get_3_isog(pts[302], A24minus[13], A24plus[13], coeff[12]);
                eval_3_isog_mod(pts[300], pts[304], coeff[11]);
                eval_3_isog_mod(pts[203], pts[306], coeff[0]);
                lock[14][1] = 0;
                while(lock[14][0]) {
                    #pragma omp flush(lock[14][0])
                }

                eval_3_isog_mod(pts[304], pts[308], coeff[12]);
                eval_3_isog_mod(pts[305], pts[309], coeff[8]);
                lock[15][1] = 0;
                while(lock[15][0]) {
                    #pragma omp flush(lock[15][0])
                }

                eval_3_isog_mod(pts[309], pts[312], coeff[9]);
                eval_3_isog_mod(pts[310], pts[313], coeff[2]);
                lock[16][1] = 0;
                while(lock[16][0]) {
                    #pragma omp flush(lock[16][0])
                }

                eval_3_isog_mod(pts[313], pts[316], coeff[3]);
                xTPLe(pts[314], pts[317], A24minus[14], A24plus[14], 1);
                lock[17][1] = 0;
                while(lock[17][0]) {
                    #pragma omp flush(lock[17][0])
                }

                xTPLe(pts[317], pts[320], A24minus[14], A24plus[14], 1);
                eval_3_isog_mod(pts[318], pts[321], coeff[12]);
                lock[18][1] = 0;
                while(lock[18][0]) {
                    #pragma omp flush(lock[18][0])
                }

                xTPLe(pts[320], pts[323], A24minus[14], A24plus[14], 1);
                get_3_isog(pts[323], A24minus[15], A24plus[15], coeff[14]);
                eval_3_isog_mod(pts[320], pts[326], coeff[14]);
                get_3_isog(pts[326], A24minus[16], A24plus[16], coeff[15]);
                lock[19][1] = 0;
                while(lock[19][0]) {
                    #pragma omp flush(lock[19][0])
                }

                eval_3_isog_mod(pts[314], pts[328], coeff[14]);
                eval_3_isog_mod(pts[311], pts[329], coeff[14]);
                eval_3_isog_mod(pts[325], pts[331], coeff[7]);
                lock[20][1] = 0;
                while(lock[20][0]) {
                    #pragma omp flush(lock[20][0])
                }

                eval_3_isog_mod(pts[329], pts[334], coeff[15]);
                eval_3_isog_mod(pts[331], pts[336], coeff[8]);
                eval_3_isog_mod(pts[334], pts[338], coeff[16]);
                eval_3_isog_mod(pts[336], pts[340], coeff[9]);
                lock[21][1] = 0;
                while(lock[21][0]) {
                    #pragma omp flush(lock[21][0])
                }

                eval_3_isog_mod(pts[338], pts[341], coeff[17]);
                get_3_isog(pts[341], A24minus[19], A24plus[19], coeff[18]);
                lock[22][1] = 0;
                while(lock[22][0]) {
                    #pragma omp flush(lock[22][0])
                }

                eval_3_isog_mod(pts[340], pts[343], coeff[10]);
                eval_3_isog_mod(pts[343], pts[345], coeff[11]);
                eval_3_isog_mod(pts[345], pts[347], coeff[12]);
                eval_3_isog_mod(pts[347], pts[350], coeff[13]);
                lock[23][1] = 0;
                while(lock[23][0]) {
                    #pragma omp flush(lock[23][0])
                }

                eval_3_isog_mod(pts[348], pts[351], coeff[1]);
                eval_3_isog_mod(pts[351], pts[354], coeff[2]);
                lock[24][1] = 0;
                while(lock[24][0]) {
                    #pragma omp flush(lock[24][0])
                }

                eval_3_isog_mod(pts[353], pts[356], coeff[15]);
                eval_3_isog_mod(pts[354], pts[357], coeff[3]);
                lock[25][1] = 0;
                while(lock[25][0]) {
                    #pragma omp flush(lock[25][0])
                }

                eval_3_isog_mod(pts[356], pts[359], coeff[16]);
                eval_3_isog_mod(pts[359], pts[362], coeff[17]);
                lock[26][1] = 0;
                while(lock[26][0]) {
                    #pragma omp flush(lock[26][0])
                }

                eval_3_isog_mod(pts[358], pts[364], coeff[19]);
                get_3_isog(pts[364], A24minus[21], A24plus[21], coeff[20]);
                eval_3_isog_mod(pts[352], pts[366], coeff[19]);
                eval_3_isog_mod(pts[349], pts[367], coeff[19]);
                eval_3_isog_mod(pts[362], pts[369], coeff[18]);
                lock[27][1] = 0;
                while(lock[27][0]) {
                    #pragma omp flush(lock[27][0])
                }

                eval_3_isog_mod(pts[366], pts[372], coeff[20]);
                eval_3_isog_mod(pts[367], pts[373], coeff[20]);
                eval_3_isog_mod(pts[369], pts[375], coeff[19]);
                lock[28][1] = 0;
                while(lock[28][0]) {
                    #pragma omp flush(lock[28][0])
                }

                eval_3_isog_mod(pts[373], pts[378], coeff[21]);
                eval_3_isog_mod(pts[374], pts[379], coeff[21]);
                lock[29][1] = 0;
                while(lock[29][0]) {
                    #pragma omp flush(lock[29][0])
                }

                eval_3_isog_mod(pts[378], pts[382], coeff[22]);
                get_3_isog(pts[382], A24minus[24], A24plus[24], coeff[23]);
                eval_3_isog_mod(pts[379], pts[383], coeff[22]);
                eval_3_isog_mod(pts[383], pts[386], coeff[23]);
                lock[30][1] = 0;
                while(lock[30][0]) {
                    #pragma omp flush(lock[30][0])
                }

                eval_3_isog_mod(pts[385], pts[388], coeff[10]);
                xTPLe(pts[386], pts[389], A24minus[24], A24plus[24], 1);
                get_3_isog(pts[389], A24minus[25], A24plus[25], coeff[24]);
                lock[31][1] = 0;
                while(lock[31][0]) {
                    #pragma omp flush(lock[31][0])
                }

                eval_3_isog_mod(pts[386], pts[392], coeff[24]);
                get_3_isog(pts[392], A24minus[26], A24plus[26], coeff[25]);
                eval_3_isog_mod(pts[390], pts[393], coeff[24]);
                eval_3_isog_mod(pts[393], pts[395], coeff[25]);
                xTPLe(pts[395], pts[397], A24minus[26], A24plus[26], 1);
                xTPLe(pts[397], pts[399], A24minus[26], A24plus[26], 1);
                xTPLe(pts[399], pts[401], A24minus[26], A24plus[26], 1);
                xTPLe(pts[401], pts[403], A24minus[26], A24plus[26], 1);
                xTPLe(pts[403], pts[405], A24minus[26], A24plus[26], 1);
                xTPLe(pts[405], pts[407], A24minus[26], A24plus[26], 1);
                xTPLe(pts[407], pts[410], A24minus[26], A24plus[26], 1);
                lock[32][1] = 0;
                while(lock[32][0]) {
                    #pragma omp flush(lock[32][0])
                }

                eval_3_isog_mod(pts[408], pts[411], coeff[20]);
                eval_3_isog_mod(pts[411], pts[414], coeff[21]);
                lock[33][1] = 0;
                while(lock[33][0]) {
                    #pragma omp flush(lock[33][0])
                }

                eval_3_isog_mod(pts[412], pts[415], coeff[2]);
                eval_3_isog_mod(pts[415], pts[418], coeff[3]);
                lock[34][1] = 0;
                while(lock[34][0]) {
                    #pragma omp flush(lock[34][0])
                }

                eval_3_isog_mod(pts[413], pts[419], coeff[26]);
                get_3_isog(pts[419], A24minus[28], A24plus[28], coeff[27]);
                eval_3_isog_mod(pts[405], pts[422], coeff[26]);
                eval_3_isog_mod(pts[417], pts[424], coeff[23]);
                lock[35][1] = 0;
                while(lock[35][0]) {
                    #pragma omp flush(lock[35][0])
                }

                eval_3_isog_mod(pts[420], pts[426], coeff[27]);
                get_3_isog(pts[426], A24minus[29], A24plus[29], coeff[28]);
                eval_3_isog_mod(pts[422], pts[428], coeff[27]);
                eval_3_isog_mod(pts[423], pts[429], coeff[27]);
                eval_3_isog_mod(pts[424], pts[431], coeff[24]);
                lock[36][1] = 0;
                while(lock[36][0]) {
                    #pragma omp flush(lock[36][0])
                }

                eval_3_isog_mod(pts[427], pts[433], coeff[28]);
                get_3_isog(pts[433], A24minus[30], A24plus[30], coeff[29]);
                eval_3_isog_mod(pts[429], pts[435], coeff[28]);
                eval_3_isog_mod(pts[431], pts[437], coeff[25]);
                lock[37][1] = 0;
                while(lock[37][0]) {
                    #pragma omp flush(lock[37][0])
                }

                eval_3_isog_mod(pts[434], pts[439], coeff[29]);
                get_3_isog(pts[439], A24minus[31], A24plus[31], coeff[30]);
                eval_3_isog_mod(pts[437], pts[442], coeff[26]);
                lock[38][1] = 0;
                while(lock[38][0]) {
                    #pragma omp flush(lock[38][0])
                }

                eval_3_isog_mod(pts[440], pts[444], coeff[30]);
                eval_3_isog_mod(pts[441], pts[445], coeff[29]);
                xTPLe(pts[444], pts[448], A24minus[31], A24plus[31], 1);
                get_3_isog(pts[448], A24minus[32], A24plus[32], coeff[31]);
                eval_3_isog_mod(pts[445], pts[449], coeff[30]);
                eval_3_isog_mod(pts[444], pts[452], coeff[31]);
                get_3_isog(pts[452], A24minus[33], A24plus[33], coeff[32]);
                eval_3_isog_mod(pts[449], pts[453], coeff[31]);
                eval_3_isog_mod(pts[453], pts[456], coeff[32]);
                lock[39][1] = 0;
                while(lock[39][0]) {
                    #pragma omp flush(lock[39][0])
                }

                eval_3_isog_mod(pts[455], pts[458], coeff[11]);
                xTPLe(pts[456], pts[459], A24minus[33], A24plus[33], 1);
                lock[40][1] = 0;
                while(lock[40][0]) {
                    #pragma omp flush(lock[40][0])
                }

                eval_3_isog_mod(pts[458], pts[461], coeff[12]);
                eval_3_isog_mod(pts[461], pts[464], coeff[13]);
                lock[41][1] = 0;
                while(lock[41][0]) {
                    #pragma omp flush(lock[41][0])
                }

                eval_3_isog_mod(pts[459], pts[465], coeff[33]);
                get_3_isog(pts[465], A24minus[35], A24plus[35], coeff[34]);
                eval_3_isog_mod(pts[463], pts[467], coeff[33]);
                lock[42][1] = 0;
                while(lock[42][0]) {
                    #pragma omp flush(lock[42][0])
                }

                eval_3_isog_mod(pts[467], pts[470], coeff[34]);
                lock[43][1] = 0;
                while(lock[43][0]) {
                    #pragma omp flush(lock[43][0])
                }

                eval_3_isog_mod(pts[468], pts[471], coeff[15]);
                eval_3_isog_mod(pts[471], pts[473], coeff[16]);
                eval_3_isog_mod(pts[473], pts[475], coeff[17]);
                eval_3_isog_mod(pts[475], pts[477], coeff[18]);
                eval_3_isog_mod(pts[477], pts[479], coeff[19]);
                eval_3_isog_mod(pts[479], pts[481], coeff[20]);
                eval_3_isog_mod(pts[481], pts[483], coeff[21]);
                eval_3_isog_mod(pts[483], pts[485], coeff[22]);
                eval_3_isog_mod(pts[485], pts[487], coeff[23]);
                eval_3_isog_mod(pts[487], pts[489], coeff[24]);
                eval_3_isog_mod(pts[489], pts[491], coeff[25]);
                eval_3_isog_mod(pts[491], pts[493], coeff[26]);
                eval_3_isog_mod(pts[493], pts[495], coeff[27]);
                eval_3_isog_mod(pts[495], pts[497], coeff[28]);
                eval_3_isog_mod(pts[497], pts[500], coeff[29]);
                lock[44][1] = 0;
                while(lock[44][0]) {
                    #pragma omp flush(lock[44][0])
                }

                eval_3_isog_mod(pts[496], pts[502], coeff[36]);
                get_3_isog(pts[502], A24minus[38], A24plus[38], coeff[37]);
                eval_3_isog_mod(pts[492], pts[504], coeff[36]);
                eval_3_isog_mod(pts[490], pts[505], coeff[36]);
                eval_3_isog_mod(pts[500], pts[507], coeff[30]);
                lock[45][1] = 0;
                while(lock[45][0]) {
                    #pragma omp flush(lock[45][0])
                }

                eval_3_isog_mod(pts[503], pts[509], coeff[37]);
                get_3_isog(pts[509], A24minus[39], A24plus[39], coeff[38]);
                eval_3_isog_mod(pts[505], pts[511], coeff[37]);
                eval_3_isog_mod(pts[507], pts[514], coeff[31]);
                lock[46][1] = 0;
                while(lock[46][0]) {
                    #pragma omp flush(lock[46][0])
                }

                eval_3_isog_mod(pts[508], pts[515], coeff[3]);
                eval_3_isog_mod(pts[511], pts[517], coeff[38]);
                eval_3_isog_mod(pts[514], pts[520], coeff[32]);
                lock[47][1] = 0;
                while(lock[47][0]) {
                    #pragma omp flush(lock[47][0])
                }

                eval_3_isog_mod(pts[517], pts[522], coeff[39]);
                get_3_isog(pts[522], A24minus[41], A24plus[41], coeff[40]);
                eval_3_isog_mod(pts[519], pts[524], coeff[38]);
                eval_3_isog_mod(pts[520], pts[526], coeff[33]);
                lock[48][1] = 0;
                while(lock[48][0]) {
                    #pragma omp flush(lock[48][0])
                }

                eval_3_isog_mod(pts[523], pts[528], coeff[40]);
                eval_3_isog_mod(pts[524], pts[529], coeff[39]);
                eval_3_isog_mod(pts[526], pts[531], coeff[34]);
                lock[49][1] = 0;
                while(lock[49][0]) {
                    #pragma omp flush(lock[49][0])
                }

                eval_3_isog_mod(pts[529], pts[534], coeff[40]);
                eval_3_isog_mod(pts[531], pts[536], coeff[35]);
                eval_3_isog_mod(pts[532], pts[537], coeff[7]);
                lock[50][1] = 0;
                while(lock[50][0]) {
                    #pragma omp flush(lock[50][0])
                }

                eval_3_isog_mod(pts[535], pts[540], coeff[39]);
                eval_3_isog_mod(pts[537], pts[542], coeff[8]);
                eval_3_isog_mod(pts[540], pts[544], coeff[40]);
                eval_3_isog_mod(pts[542], pts[546], coeff[9]);
                eval_3_isog_mod(pts[544], pts[548], coeff[41]);
                eval_3_isog_mod(pts[546], pts[550], coeff[10]);
                eval_3_isog_mod(pts[548], pts[552], coeff[42]);
                eval_3_isog_mod(pts[550], pts[554], coeff[11]);
                lock[51][1] = 0;
                while(lock[51][0]) {
                    #pragma omp flush(lock[51][0])
                }

                eval_3_isog_mod(pts[547], pts[555], coeff[43]);
                get_3_isog(pts[555], A24minus[45], A24plus[45], coeff[44]);
                eval_3_isog_mod(pts[552], pts[557], coeff[43]);
                lock[52][1] = 0;
                while(lock[52][0]) {
                    #pragma omp flush(lock[52][0])
                }

                eval_3_isog_mod(pts[554], pts[559], coeff[12]);
                eval_3_isog_mod(pts[557], pts[561], coeff[44]);
                lock[53][1] = 0;
                while(lock[53][0]) {
                    #pragma omp flush(lock[53][0])
                }

                eval_3_isog_mod(pts[559], pts[563], coeff[13]);
                eval_3_isog_mod(pts[563], pts[566], coeff[14]);
                lock[54][1] = 0;
                while(lock[54][0]) {
                    #pragma omp flush(lock[54][0])
                }

                eval_3_isog_mod(pts[565], pts[568], coeff[43]);
                eval_3_isog_mod(pts[566], pts[569], coeff[15]);
                lock[55][1] = 0;
                while(lock[55][0]) {
                    #pragma omp flush(lock[55][0])
                }

                eval_3_isog_mod(pts[568], pts[571], coeff[44]);
                eval_3_isog_mod(pts[571], pts[574], coeff[45]);
                lock[56][1] = 0;
                while(lock[56][0]) {
                    #pragma omp flush(lock[56][0])
                }

                eval_3_isog_mod(pts[572], pts[575], coeff[17]);
                eval_3_isog_mod(pts[567], pts[577], coeff[46]);
                eval_3_isog_mod(pts[575], pts[580], coeff[18]);
                lock[57][1] = 0;
                while(lock[57][0]) {
                    #pragma omp flush(lock[57][0])
                }

                eval_3_isog_mod(pts[578], pts[582], coeff[47]);
                eval_3_isog_mod(pts[580], pts[584], coeff[19]);
                lock[58][1] = 0;
                while(lock[58][0]) {
                    #pragma omp flush(lock[58][0])
                }

                eval_3_isog_mod(pts[583], pts[586], coeff[48]);
                lock[59][1] = 0;
                while(lock[59][0]) {
                    #pragma omp flush(lock[59][0])
                }

                eval_3_isog_mod(pts[586], pts[588], coeff[49]);
                xTPLe(pts[588], pts[590], A24minus[50], A24plus[50], 1);
                xTPLe(pts[590], pts[592], A24minus[50], A24plus[50], 1);
                xTPLe(pts[592], pts[594], A24minus[50], A24plus[50], 1);
                xTPLe(pts[594], pts[596], A24minus[50], A24plus[50], 1);
                xTPLe(pts[596], pts[598], A24minus[50], A24plus[50], 1);
                xTPLe(pts[598], pts[600], A24minus[50], A24plus[50], 1);
                xTPLe(pts[600], pts[602], A24minus[50], A24plus[50], 1);
                xTPLe(pts[602], pts[604], A24minus[50], A24plus[50], 1);
                xTPLe(pts[604], pts[606], A24minus[50], A24plus[50], 1);
                xTPLe(pts[606], pts[608], A24minus[50], A24plus[50], 1);
                xTPLe(pts[608], pts[610], A24minus[50], A24plus[50], 1);
                xTPLe(pts[610], pts[612], A24minus[50], A24plus[50], 1);
                xTPLe(pts[612], pts[614], A24minus[50], A24plus[50], 1);
                xTPLe(pts[614], pts[616], A24minus[50], A24plus[50], 1);
                xTPLe(pts[616], pts[618], A24minus[50], A24plus[50], 1);
                xTPLe(pts[618], pts[620], A24minus[50], A24plus[50], 1);
                xTPLe(pts[620], pts[622], A24minus[50], A24plus[50], 1);
                xTPLe(pts[622], pts[624], A24minus[50], A24plus[50], 1);
                get_3_isog(pts[624], A24minus[51], A24plus[51], coeff[50]);
                eval_3_isog_mod(pts[622], pts[626], coeff[50]);
                get_3_isog(pts[626], A24minus[52], A24plus[52], coeff[51]);
                lock[60][1] = 0;
                while(lock[60][0]) {
                    #pragma omp flush(lock[60][0])
                }

                eval_3_isog_mod(pts[620], pts[627], coeff[50]);
                eval_3_isog_mod(pts[616], pts[629], coeff[50]);
                eval_3_isog_mod(pts[627], pts[632], coeff[51]);
                get_3_isog(pts[632], A24minus[53], A24plus[53], coeff[52]);
                eval_3_isog_mod(pts[629], pts[634], coeff[51]);
                eval_3_isog_mod(pts[606], pts[636], coeff[50]);
                lock[61][1] = 0;
                while(lock[61][0]) {
                    #pragma omp flush(lock[61][0])
                }

                eval_3_isog_mod(pts[631], pts[637], coeff[41]);
                eval_3_isog_mod(pts[635], pts[640], coeff[52]);
                eval_3_isog_mod(pts[637], pts[642], coeff[42]);
                eval_3_isog_mod(pts[108], pts[643], coeff[0]);
                lock[62][1] = 0;
                while(lock[62][0]) {
                    #pragma omp flush(lock[62][0])
                }

                eval_3_isog_mod(pts[641], pts[646], coeff[52]);
                eval_3_isog_mod(pts[598], pts[647], coeff[50]);
                eval_3_isog_mod(pts[643], pts[649], coeff[1]);
                lock[63][1] = 0;
                while(lock[63][0]) {
                    #pragma omp flush(lock[63][0])
                }

                eval_3_isog_mod(pts[647], pts[652], coeff[51]);
                eval_3_isog_mod(pts[649], pts[654], coeff[2]);
                xTPLe(pts[650], pts[655], A24minus[55], A24plus[55], 1);
                get_3_isog(pts[655], A24minus[56], A24plus[56], coeff[55]);
                eval_3_isog_mod(pts[652], pts[657], coeff[52]);
                lock[64][1] = 0;
                while(lock[64][0]) {
                    #pragma omp flush(lock[64][0])
                }

                eval_3_isog_mod(pts[654], pts[659], coeff[3]);
                eval_3_isog_mod(pts[656], pts[661], coeff[55]);
                eval_3_isog_mod(pts[658], pts[664], coeff[46]);
                lock[65][1] = 0;
                while(lock[65][0]) {
                    #pragma omp flush(lock[65][0])
                }

                eval_3_isog_mod(pts[661], pts[666], coeff[56]);
                eval_3_isog_mod(pts[663], pts[668], coeff[51]);
                eval_3_isog_mod(pts[664], pts[669], coeff[47]);
                xTPLe(pts[666], pts[671], A24minus[57], A24plus[57], 1);
                lock[66][1] = 0;
                while(lock[66][0]) {
                    #pragma omp flush(lock[66][0])
                }

                eval_3_isog_mod(pts[669], pts[674], coeff[48]);
                xTPLe(pts[671], pts[676], A24minus[57], A24plus[57], 1);
                get_3_isog(pts[676], A24minus[58], A24plus[58], coeff[57]);
                eval_3_isog_mod(pts[672], pts[677], coeff[56]);
                eval_3_isog_mod(pts[674], pts[679], coeff[49]);
                lock[67][1] = 0;
                while(lock[67][0]) {
                    #pragma omp flush(lock[67][0])
                }

                eval_3_isog_mod(pts[666], pts[682], coeff[57]);
                eval_3_isog_mod(pts[677], pts[683], coeff[57]);
                eval_3_isog_mod(pts[680], pts[686], coeff[8]);
                lock[68][1] = 0;
                while(lock[68][0]) {
                    #pragma omp flush(lock[68][0])
                }

                eval_3_isog_mod(pts[682], pts[687], coeff[58]);
                get_3_isog(pts[687], A24minus[60], A24plus[60], coeff[59]);
                eval_3_isog_mod(pts[685], pts[690], coeff[51]);
                lock[69][1] = 0;
                while(lock[69][0]) {
                    #pragma omp flush(lock[69][0])
                }

                eval_3_isog_mod(pts[686], pts[691], coeff[9]);
                eval_3_isog_mod(pts[689], pts[693], coeff[56]);
                eval_3_isog_mod(pts[691], pts[695], coeff[10]);
                eval_3_isog_mod(pts[693], pts[697], coeff[57]);
                eval_3_isog_mod(pts[695], pts[699], coeff[11]);
                eval_3_isog_mod(pts[697], pts[701], coeff[58]);
                eval_3_isog_mod(pts[699], pts[703], coeff[12]);
                eval_3_isog_mod(pts[701], pts[705], coeff[59]);
                eval_3_isog_mod(pts[703], pts[707], coeff[13]);
                lock[70][1] = 0;
                while(lock[70][0]) {
                    #pragma omp flush(lock[70][0])
                }

                eval_3_isog_mod(pts[696], pts[709], coeff[60]);
                eval_3_isog_mod(pts[706], pts[712], coeff[56]);
                eval_3_isog_mod(pts[709], pts[714], coeff[61]);
                get_3_isog(pts[714], A24minus[63], A24plus[63], coeff[62]);
                lock[71][1] = 0;
                while(lock[71][0]) {
                    #pragma omp flush(lock[71][0])
                }

                eval_3_isog_mod(pts[710], pts[715], coeff[61]);
                eval_3_isog_mod(pts[712], pts[717], coeff[57]);
                eval_3_isog_mod(pts[715], pts[719], coeff[62]);
                get_3_isog(pts[719], A24minus[64], A24plus[64], coeff[63]);
                eval_3_isog_mod(pts[717], pts[721], coeff[58]);
                lock[72][1] = 0;
                while(lock[72][0]) {
                    #pragma omp flush(lock[72][0])
                }

                eval_3_isog_mod(pts[721], pts[724], coeff[59]);
                eval_3_isog_mod(pts[722], pts[725], coeff[17]);
                lock[73][1] = 0;
                while(lock[73][0]) {
                    #pragma omp flush(lock[73][0])
                }

                eval_3_isog_mod(pts[725], pts[728], coeff[18]);
                xTPLe(pts[726], pts[729], A24minus[64], A24plus[64], 1);
                lock[74][1] = 0;
                while(lock[74][0]) {
                    #pragma omp flush(lock[74][0])
                }

                xTPLe(pts[729], pts[732], A24minus[64], A24plus[64], 1);
                eval_3_isog_mod(pts[730], pts[733], coeff[62]);
                lock[75][1] = 0;
                while(lock[75][0]) {
                    #pragma omp flush(lock[75][0])
                }

                xTPLe(pts[732], pts[735], A24minus[64], A24plus[64], 1);
                get_3_isog(pts[735], A24minus[65], A24plus[65], coeff[64]);
                eval_3_isog_mod(pts[732], pts[738], coeff[64]);
                get_3_isog(pts[738], A24minus[66], A24plus[66], coeff[65]);
                lock[76][1] = 0;
                while(lock[76][0]) {
                    #pragma omp flush(lock[76][0])
                }

                eval_3_isog_mod(pts[729], pts[739], coeff[64]);
                eval_3_isog_mod(pts[723], pts[741], coeff[64]);
                eval_3_isog_mod(pts[739], pts[744], coeff[65]);
                get_3_isog(pts[744], A24minus[67], A24plus[67], coeff[66]);
                eval_3_isog_mod(pts[741], pts[746], coeff[65]);
                lock[77][1] = 0;
                while(lock[77][0]) {
                    #pragma omp flush(lock[77][0])
                }

                eval_3_isog_mod(pts[743], pts[748], coeff[23]);
                eval_3_isog_mod(pts[745], pts[749], coeff[66]);
                get_3_isog(pts[749], A24minus[68], A24plus[68], coeff[67]);
                eval_3_isog_mod(pts[748], pts[752], coeff[24]);
                lock[78][1] = 0;
                while(lock[78][0]) {
                    #pragma omp flush(lock[78][0])
                }

                eval_3_isog_mod(pts[751], pts[754], coeff[67]);
                lock[79][1] = 0;
                while(lock[79][0]) {
                    #pragma omp flush(lock[79][0])
                }

                eval_3_isog_mod(pts[754], pts[756], coeff[68]);
                xTPLe(pts[756], pts[758], A24minus[69], A24plus[69], 1);
                xTPLe(pts[758], pts[760], A24minus[69], A24plus[69], 1);
                xTPLe(pts[760], pts[762], A24minus[69], A24plus[69], 1);
                xTPLe(pts[762], pts[764], A24minus[69], A24plus[69], 1);
                xTPLe(pts[764], pts[766], A24minus[69], A24plus[69], 1);
                xTPLe(pts[766], pts[768], A24minus[69], A24plus[69], 1);
                xTPLe(pts[768], pts[770], A24minus[69], A24plus[69], 1);
                xTPLe(pts[770], pts[772], A24minus[69], A24plus[69], 1);
                xTPLe(pts[772], pts[774], A24minus[69], A24plus[69], 1);
                xTPLe(pts[774], pts[776], A24minus[69], A24plus[69], 1);
                xTPLe(pts[776], pts[778], A24minus[69], A24plus[69], 1);
                xTPLe(pts[778], pts[780], A24minus[69], A24plus[69], 1);
                xTPLe(pts[780], pts[782], A24minus[69], A24plus[69], 1);
                xTPLe(pts[782], pts[784], A24minus[69], A24plus[69], 1);
                xTPLe(pts[784], pts[786], A24minus[69], A24plus[69], 1);
                xTPLe(pts[786], pts[788], A24minus[69], A24plus[69], 1);
                xTPLe(pts[788], pts[790], A24minus[69], A24plus[69], 1);
                xTPLe(pts[790], pts[792], A24minus[69], A24plus[69], 1);
                xTPLe(pts[792], pts[794], A24minus[69], A24plus[69], 1);
                xTPLe(pts[794], pts[796], A24minus[69], A24plus[69], 1);
                xTPLe(pts[796], pts[798], A24minus[69], A24plus[69], 1);
                xTPLe(pts[798], pts[800], A24minus[69], A24plus[69], 1);
                xTPLe(pts[800], pts[802], A24minus[69], A24plus[69], 1);
                xTPLe(pts[802], pts[804], A24minus[69], A24plus[69], 1);
                xTPLe(pts[804], pts[806], A24minus[69], A24plus[69], 1);
                get_3_isog(pts[806], A24minus[70], A24plus[70], coeff[69]);
                eval_3_isog_mod(pts[804], pts[808], coeff[69]);
                get_3_isog(pts[808], A24minus[71], A24plus[71], coeff[70]);
                lock[80][1] = 0;
                while(lock[80][0]) {
                    #pragma omp flush(lock[80][0])
                }

                eval_3_isog_mod(pts[800], pts[810], coeff[69]);
                eval_3_isog_mod(pts[794], pts[812], coeff[69]);
                eval_3_isog_mod(pts[807], pts[813], coeff[52]);
                eval_3_isog_mod(pts[810], pts[815], coeff[70]);
                eval_3_isog_mod(pts[812], pts[817], coeff[70]);
                lock[81][1] = 0;
                while(lock[81][0]) {
                    #pragma omp flush(lock[81][0])
                }

                eval_3_isog_mod(pts[815], pts[820], coeff[71]);
                get_3_isog(pts[820], A24minus[73], A24plus[73], coeff[72]);
                eval_3_isog_mod(pts[817], pts[822], coeff[71]);
                eval_3_isog_mod(pts[818], pts[823], coeff[70]);
                lock[82][1] = 0;
                while(lock[82][0]) {
                    #pragma omp flush(lock[82][0])
                }

                eval_3_isog_mod(pts[821], pts[825], coeff[72]);
                get_3_isog(pts[825], A24minus[74], A24plus[74], coeff[73]);
                eval_3_isog_mod(pts[780], pts[828], coeff[69]);
                lock[83][1] = 0;
                while(lock[83][0]) {
                    #pragma omp flush(lock[83][0])
                }

                eval_3_isog_mod(pts[826], pts[830], coeff[73]);
                eval_3_isog_mod(pts[828], pts[832], coeff[70]);
                xTPLe(pts[830], pts[834], A24minus[74], A24plus[74], 1);
                get_3_isog(pts[834], A24minus[75], A24plus[75], coeff[74]);
                eval_3_isog_mod(pts[832], pts[836], coeff[71]);
                eval_3_isog_mod(pts[830], pts[838], coeff[74]);
                get_3_isog(pts[838], A24minus[76], A24plus[76], coeff[75]);
                lock[84][1] = 0;
                while(lock[84][0]) {
                    #pragma omp flush(lock[84][0])
                }

                eval_3_isog_mod(pts[835], pts[839], coeff[74]);
                eval_3_isog_mod(pts[770], pts[841], coeff[69]);
                eval_3_isog_mod(pts[839], pts[843], coeff[75]);
                eval_3_isog_mod(pts[841], pts[845], coeff[70]);
                xTPLe(pts[843], pts[847], A24minus[76], A24plus[76], 1);
                eval_3_isog_mod(pts[845], pts[849], coeff[71]);
                xTPLe(pts[847], pts[851], A24minus[76], A24plus[76], 1);
                get_3_isog(pts[851], A24minus[77], A24plus[77], coeff[76]);
                eval_3_isog_mod(pts[849], pts[853], coeff[72]);
                lock[85][1] = 0;
                while(lock[85][0]) {
                    #pragma omp flush(lock[85][0])
                }

                eval_3_isog_mod(pts[847], pts[855], coeff[76]);
                get_3_isog(pts[855], A24minus[78], A24plus[78], coeff[77]);
                eval_3_isog_mod(pts[852], pts[857], coeff[76]);
                eval_3_isog_mod(pts[756], pts[859], coeff[69]);
                lock[86][1] = 0;
                while(lock[86][0]) {
                    #pragma omp flush(lock[86][0])
                }

                eval_3_isog_mod(pts[857], pts[862], coeff[77]);
                eval_3_isog_mod(pts[859], pts[864], coeff[70]);
                lock[87][1] = 0;
                while(lock[87][0]) {
                    #pragma omp flush(lock[87][0])
                }

                eval_3_isog_mod(pts[862], pts[866], coeff[78]);
                eval_3_isog_mod(pts[863], pts[867], coeff[75]);
                eval_3_isog_mod(pts[58], pts[870], coeff[0]);
                lock[88][1] = 0;
                while(lock[88][0]) {
                    #pragma omp flush(lock[88][0])
                }

                xTPLe(pts[866], pts[871], A24minus[79], A24plus[79], 1);
                eval_3_isog_mod(pts[868], pts[873], coeff[72]);
                xTPLe(pts[871], pts[876], A24minus[79], A24plus[79], 1);
                eval_3_isog_mod(pts[873], pts[878], coeff[73]);
                lock[89][1] = 0;
                while(lock[89][0]) {
                    #pragma omp flush(lock[89][0])
                }

                eval_3_isog_mod(pts[875], pts[880], coeff[2]);
                eval_3_isog_mod(pts[877], pts[882], coeff[78]);
                eval_3_isog_mod(pts[878], pts[883], coeff[74]);
                eval_3_isog_mod(pts[880], pts[885], coeff[3]);
                lock[90][1] = 0;
                while(lock[90][0]) {
                    #pragma omp flush(lock[90][0])
                }

                eval_3_isog_mod(pts[871], pts[887], coeff[79]);
                eval_3_isog_mod(pts[883], pts[890], coeff[75]);
                eval_3_isog_mod(pts[885], pts[892], coeff[4]);
                eval_3_isog_mod(pts[887], pts[893], coeff[80]);
                get_3_isog(pts[893], A24minus[82], A24plus[82], coeff[81]);
                eval_3_isog_mod(pts[890], pts[896], coeff[76]);
                eval_3_isog_mod(pts[892], pts[898], coeff[5]);
                lock[91][1] = 0;
                while(lock[91][0]) {
                    #pragma omp flush(lock[91][0])
                }

                eval_3_isog_mod(pts[895], pts[900], coeff[81]);
                eval_3_isog_mod(pts[897], pts[902], coeff[70]);
                lock[92][1] = 0;
                while(lock[92][0]) {
                    #pragma omp flush(lock[92][0])
                }

                eval_3_isog_mod(pts[898], pts[903], coeff[6]);
                eval_3_isog_mod(pts[901], pts[905], coeff[78]);
                eval_3_isog_mod(pts[903], pts[907], coeff[7]);
                eval_3_isog_mod(pts[905], pts[909], coeff[79]);
                eval_3_isog_mod(pts[907], pts[911], coeff[8]);
                eval_3_isog_mod(pts[909], pts[913], coeff[80]);
                eval_3_isog_mod(pts[911], pts[915], coeff[9]);
                eval_3_isog_mod(pts[913], pts[917], coeff[81]);
                eval_3_isog_mod(pts[915], pts[919], coeff[10]);
                eval_3_isog_mod(pts[917], pts[921], coeff[82]);
                eval_3_isog_mod(pts[919], pts[923], coeff[11]);
                lock[93][1] = 0;
                while(lock[93][0]) {
                    #pragma omp flush(lock[93][0])
                }

                eval_3_isog_mod(pts[908], pts[926], coeff[83]);
                eval_3_isog_mod(pts[921], pts[928], coeff[83]);
                eval_3_isog_mod(pts[923], pts[930], coeff[12]);
                eval_3_isog_mod(pts[926], pts[932], coeff[84]);
                eval_3_isog_mod(pts[928], pts[934], coeff[84]);
                eval_3_isog_mod(pts[930], pts[936], coeff[13]);
                lock[94][1] = 0;
                while(lock[94][0]) {
                    #pragma omp flush(lock[94][0])
                }

                eval_3_isog_mod(pts[932], pts[937], coeff[85]);
                get_3_isog(pts[937], A24minus[87], A24plus[87], coeff[86]);
                eval_3_isog_mod(pts[934], pts[939], coeff[85]);
                lock[95][1] = 0;
                while(lock[95][0]) {
                    #pragma omp flush(lock[95][0])
                }

                eval_3_isog_mod(pts[936], pts[941], coeff[14]);
                eval_3_isog_mod(pts[939], pts[943], coeff[86]);
                lock[96][1] = 0;
                while(lock[96][0]) {
                    #pragma omp flush(lock[96][0])
                }

                eval_3_isog_mod(pts[943], pts[946], coeff[87]);
                eval_3_isog_mod(pts[944], pts[947], coeff[80]);
                lock[97][1] = 0;
                while(lock[97][0]) {
                    #pragma omp flush(lock[97][0])
                }

                eval_3_isog_mod(pts[947], pts[950], coeff[81]);
                eval_3_isog_mod(pts[948], pts[951], coeff[17]);
                lock[98][1] = 0;
                while(lock[98][0]) {
                    #pragma omp flush(lock[98][0])
                }

                eval_3_isog_mod(pts[950], pts[953], coeff[82]);
                eval_3_isog_mod(pts[953], pts[956], coeff[83]);
                lock[99][1] = 0;
                while(lock[99][0]) {
                    #pragma omp flush(lock[99][0])
                }

                eval_3_isog_mod(pts[954], pts[957], coeff[19]);
                eval_3_isog_mod(pts[957], pts[960], coeff[20]);
                lock[100][1] = 0;
                while(lock[100][0]) {
                    #pragma omp flush(lock[100][0])
                }

                xTPLe(pts[958], pts[961], A24minus[88], A24plus[88], 1);
                xTPLe(pts[961], pts[964], A24minus[88], A24plus[88], 1);
                get_3_isog(pts[964], A24minus[89], A24plus[89], coeff[88]);
                lock[101][1] = 0;
                while(lock[101][0]) {
                    #pragma omp flush(lock[101][0])
                }

                eval_3_isog_mod(pts[962], pts[965], coeff[86]);
                eval_3_isog_mod(pts[961], pts[967], coeff[88]);
                get_3_isog(pts[967], A24minus[90], A24plus[90], coeff[89]);
                eval_3_isog_mod(pts[955], pts[969], coeff[88]);
                eval_3_isog_mod(pts[965], pts[972], coeff[87]);
                lock[102][1] = 0;
                while(lock[102][0]) {
                    #pragma omp flush(lock[102][0])
                }

                eval_3_isog_mod(pts[966], pts[973], coeff[23]);
                eval_3_isog_mod(pts[970], pts[976], coeff[89]);
                eval_3_isog_mod(pts[971], pts[977], coeff[89]);
                eval_3_isog_mod(pts[973], pts[979], coeff[24]);
                lock[103][1] = 0;
                while(lock[103][0]) {
                    #pragma omp flush(lock[103][0])
                }

                eval_3_isog_mod(pts[977], pts[982], coeff[90]);
                eval_3_isog_mod(pts[978], pts[983], coeff[89]);
                eval_3_isog_mod(pts[982], pts[986], coeff[91]);
                eval_3_isog_mod(pts[983], pts[987], coeff[90]);
                lock[104][1] = 0;
                while(lock[104][0]) {
                    #pragma omp flush(lock[104][0])
                }

                eval_3_isog_mod(pts[986], pts[989], coeff[92]);
                xTPLe(pts[989], pts[992], A24minus[93], A24plus[93], 1);
                get_3_isog(pts[992], A24minus[94], A24plus[94], coeff[93]);
                lock[105][1] = 0;
                while(lock[105][0]) {
                    #pragma omp flush(lock[105][0])
                }

                eval_3_isog_mod(pts[991], pts[994], coeff[28]);
                eval_3_isog_mod(pts[989], pts[995], coeff[93]);
                get_3_isog(pts[995], A24minus[95], A24plus[95], coeff[94]);
                lock[106][1] = 0;
                while(lock[106][0]) {
                    #pragma omp flush(lock[106][0])
                }

                eval_3_isog_mod(pts[994], pts[997], coeff[29]);
                eval_3_isog_mod(pts[997], pts[999], coeff[30]);
                eval_3_isog_mod(pts[999], pts[1001], coeff[31]);
                eval_3_isog_mod(pts[1001], pts[1003], coeff[32]);
                eval_3_isog_mod(pts[1003], pts[1005], coeff[33]);
                eval_3_isog_mod(pts[1005], pts[1007], coeff[34]);
                eval_3_isog_mod(pts[1007], pts[1009], coeff[35]);
                eval_3_isog_mod(pts[1009], pts[1011], coeff[36]);
                eval_3_isog_mod(pts[1011], pts[1013], coeff[37]);
                eval_3_isog_mod(pts[1013], pts[1015], coeff[38]);
                eval_3_isog_mod(pts[1015], pts[1017], coeff[39]);
                eval_3_isog_mod(pts[1017], pts[1019], coeff[40]);
                eval_3_isog_mod(pts[1019], pts[1021], coeff[41]);
                eval_3_isog_mod(pts[1021], pts[1023], coeff[42]);
                eval_3_isog_mod(pts[1023], pts[1025], coeff[43]);
                eval_3_isog_mod(pts[1025], pts[1027], coeff[44]);
                eval_3_isog_mod(pts[1027], pts[1029], coeff[45]);
                eval_3_isog_mod(pts[1029], pts[1031], coeff[46]);
                eval_3_isog_mod(pts[1031], pts[1033], coeff[47]);
                eval_3_isog_mod(pts[1033], pts[1035], coeff[48]);
                eval_3_isog_mod(pts[1035], pts[1037], coeff[49]);
                eval_3_isog_mod(pts[1037], pts[1039], coeff[50]);
                eval_3_isog_mod(pts[1039], pts[1041], coeff[51]);
                eval_3_isog_mod(pts[1041], pts[1043], coeff[52]);
                eval_3_isog_mod(pts[1043], pts[1045], coeff[53]);
                eval_3_isog_mod(pts[1045], pts[1047], coeff[54]);
                eval_3_isog_mod(pts[1047], pts[1049], coeff[55]);
                eval_3_isog_mod(pts[1049], pts[1051], coeff[56]);
                eval_3_isog_mod(pts[1051], pts[1053], coeff[57]);
                eval_3_isog_mod(pts[1053], pts[1055], coeff[58]);
                eval_3_isog_mod(pts[1055], pts[1057], coeff[59]);
                eval_3_isog_mod(pts[1057], pts[1059], coeff[60]);
                eval_3_isog_mod(pts[1059], pts[1061], coeff[61]);
                eval_3_isog_mod(pts[1061], pts[1063], coeff[62]);
                eval_3_isog_mod(pts[1063], pts[1065], coeff[63]);
                eval_3_isog_mod(pts[1065], pts[1067], coeff[64]);
                eval_3_isog_mod(pts[1067], pts[1069], coeff[65]);
                lock[107][1] = 0;
                while(lock[107][0]) {
                    #pragma omp flush(lock[107][0])
                }

                eval_3_isog_mod(pts[1064], pts[1071], coeff[95]);
                eval_3_isog_mod(pts[1060], pts[1073], coeff[95]);
                eval_3_isog_mod(pts[1071], pts[1076], coeff[96]);
                get_3_isog(pts[1076], A24minus[98], A24plus[98], coeff[97]);
                eval_3_isog_mod(pts[1073], pts[1078], coeff[96]);
                eval_3_isog_mod(pts[1050], pts[1080], coeff[95]);
                lock[108][1] = 0;
                while(lock[108][0]) {
                    #pragma omp flush(lock[108][0])
                }

                eval_3_isog_mod(pts[1077], pts[1082], coeff[97]);
                get_3_isog(pts[1082], A24minus[99], A24plus[99], coeff[98]);
                eval_3_isog_mod(pts[1078], pts[1083], coeff[97]);
                eval_3_isog_mod(pts[1080], pts[1085], coeff[96]);
                lock[109][1] = 0;
                while(lock[109][0]) {
                    #pragma omp flush(lock[109][0])
                }

                eval_3_isog_mod(pts[1084], pts[1088], coeff[98]);
                eval_3_isog_mod(pts[1085], pts[1089], coeff[97]);
                lock[110][1] = 0;
                while(lock[110][0]) {
                    #pragma omp flush(lock[110][0])
                }

                eval_3_isog_mod(pts[1088], pts[1092], coeff[99]);
                eval_3_isog_mod(pts[1090], pts[1094], coeff[96]);
                xTPLe(pts[1092], pts[1096], A24minus[100], A24plus[100], 1);
                get_3_isog(pts[1096], A24minus[101], A24plus[101], coeff[100]);
                eval_3_isog_mod(pts[1094], pts[1098], coeff[97]);
                eval_3_isog_mod(pts[1092], pts[1100], coeff[100]);
                get_3_isog(pts[1100], A24minus[102], A24plus[102], coeff[101]);
                lock[111][1] = 0;
                while(lock[111][0]) {
                    #pragma omp flush(lock[111][0])
                }

                eval_3_isog_mod(pts[1098], pts[1102], coeff[98]);
                eval_3_isog_mod(pts[1032], pts[1103], coeff[95]);
                eval_3_isog_mod(pts[1102], pts[1106], coeff[99]);
                eval_3_isog_mod(pts[1103], pts[1107], coeff[96]);
                eval_3_isog_mod(pts[1106], pts[1110], coeff[100]);
                eval_3_isog_mod(pts[1107], pts[1111], coeff[97]);
                eval_3_isog_mod(pts[1110], pts[1114], coeff[101]);
                eval_3_isog_mod(pts[1111], pts[1115], coeff[98]);
                lock[112][1] = 0;
                while(lock[112][0]) {
                    #pragma omp flush(lock[112][0])
                }

                eval_3_isog_mod(pts[1109], pts[1117], coeff[102]);
                get_3_isog(pts[1117], A24minus[104], A24plus[104], coeff[103]);
                eval_3_isog_mod(pts[1114], pts[1119], coeff[102]);
                eval_3_isog_mod(pts[1116], pts[1122], coeff[76]);
                lock[113][1] = 0;
                while(lock[113][0]) {
                    #pragma omp flush(lock[113][0])
                }

                eval_3_isog_mod(pts[1119], pts[1124], coeff[103]);
                eval_3_isog_mod(pts[1120], pts[1125], coeff[100]);
                lock[114][1] = 0;
                while(lock[114][0]) {
                    #pragma omp flush(lock[114][0])
                }

                eval_3_isog_mod(pts[1122], pts[1127], coeff[77]);
                eval_3_isog_mod(pts[1126], pts[1130], coeff[97]);
                eval_3_isog_mod(pts[1127], pts[1131], coeff[78]);
                eval_3_isog_mod(pts[1130], pts[1134], coeff[98]);
                eval_3_isog_mod(pts[1131], pts[1135], coeff[79]);
                eval_3_isog_mod(pts[1134], pts[1138], coeff[99]);
                eval_3_isog_mod(pts[1135], pts[1139], coeff[80]);
                eval_3_isog_mod(pts[1138], pts[1142], coeff[100]);
                eval_3_isog_mod(pts[1139], pts[1143], coeff[81]);
                lock[115][1] = 0;
                while(lock[115][0]) {
                    #pragma omp flush(lock[115][0])
                }

                eval_3_isog_mod(pts[1128], pts[1146], coeff[105]);
                eval_3_isog_mod(pts[1141], pts[1147], coeff[105]);
                eval_3_isog_mod(pts[1143], pts[1149], coeff[82]);
                lock[116][1] = 0;
                while(lock[116][0]) {
                    #pragma omp flush(lock[116][0])
                }

                eval_3_isog_mod(pts[1147], pts[1152], coeff[106]);
                eval_3_isog_mod(pts[998], pts[1154], coeff[95]);
                eval_3_isog_mod(pts[1149], pts[1155], coeff[83]);
                eval_3_isog_mod(pts[1152], pts[1157], coeff[107]);
                lock[117][1] = 0;
                while(lock[117][0]) {
                    #pragma omp flush(lock[117][0])
                }

                eval_3_isog_mod(pts[1155], pts[1160], coeff[84]);
                eval_3_isog_mod(pts[1157], pts[1161], coeff[108]);
                eval_3_isog_mod(pts[1160], pts[1164], coeff[85]);
                xTPLe(pts[1161], pts[1165], A24minus[109], A24plus[109], 1);
                eval_3_isog_mod(pts[1164], pts[1168], coeff[86]);
                xTPLe(pts[1165], pts[1169], A24minus[109], A24plus[109], 1);
                eval_3_isog_mod(pts[1168], pts[1172], coeff[87]);
                xTPLe(pts[1169], pts[1173], A24minus[109], A24plus[109], 1);
                eval_3_isog_mod(pts[1172], pts[1176], coeff[88]);
                xTPLe(pts[1173], pts[1177], A24minus[109], A24plus[109], 1);
                get_3_isog(pts[1177], A24minus[110], A24plus[110], coeff[109]);
                eval_3_isog_mod(pts[1176], pts[1180], coeff[89]);
                lock[118][1] = 0;
                while(lock[118][0]) {
                    #pragma omp flush(lock[118][0])
                }

                eval_3_isog_mod(pts[1169], pts[1182], coeff[109]);
                eval_3_isog_mod(pts[1165], pts[1183], coeff[109]);
                eval_3_isog_mod(pts[1179], pts[1186], coeff[102]);
                lock[119][1] = 0;
                while(lock[119][0]) {
                    #pragma omp flush(lock[119][0])
                }

                eval_3_isog_mod(pts[1180], pts[1187], coeff[90]);
                eval_3_isog_mod(pts[1184], pts[1190], coeff[110]);
                eval_3_isog_mod(pts[1185], pts[1191], coeff[110]);
                eval_3_isog_mod(pts[1187], pts[1193], coeff[91]);
                lock[120][1] = 0;
                while(lock[120][0]) {
                    #pragma omp flush(lock[120][0])
                }

                eval_3_isog_mod(pts[1191], pts[1196], coeff[111]);
                eval_3_isog_mod(pts[1193], pts[1198], coeff[92]);
                eval_3_isog_mod(pts[1196], pts[1200], coeff[112]);
                eval_3_isog_mod(pts[1198], pts[1202], coeff[93]);
                lock[121][1] = 0;
                while(lock[121][0]) {
                    #pragma omp flush(lock[121][0])
                }

                eval_3_isog_mod(pts[1200], pts[1203], coeff[113]);
                xTPLe(pts[1203], pts[1206], A24minus[114], A24plus[114], 1);
                lock[122][1] = 0;
                while(lock[122][0]) {
                    #pragma omp flush(lock[122][0])
                }

                eval_3_isog_mod(pts[1204], pts[1207], coeff[107]);
                eval_3_isog_mod(pts[1207], pts[1210], coeff[108]);
                lock[123][1] = 0;
                while(lock[123][0]) {
                    #pragma omp flush(lock[123][0])
                }

                eval_3_isog_mod(pts[1208], pts[1211], coeff[96]);
                eval_3_isog_mod(pts[1211], pts[1214], coeff[97]);
                eval_3_isog_mod(pts[0], pts[1215], coeff[0]);
                eval_3_isog_mod(pts[1214], pts[1218], coeff[98]);
                eval_3_isog_mod(pts[1215], pts[1219], coeff[1]);
                eval_3_isog_mod(pts[1218], pts[1222], coeff[99]);
                eval_3_isog_mod(pts[1219], pts[1223], coeff[2]);
                eval_3_isog_mod(pts[1222], pts[1226], coeff[100]);
                eval_3_isog_mod(pts[1223], pts[1227], coeff[3]);
                lock[124][1] = 0;
                while(lock[124][0]) {
                    #pragma omp flush(lock[124][0])
                }

                eval_3_isog_mod(pts[1212], pts[1230], coeff[114]);
                eval_3_isog_mod(pts[1209], pts[1231], coeff[114]);
                eval_3_isog_mod(pts[1225], pts[1233], coeff[113]);
                eval_3_isog_mod(pts[1227], pts[1235], coeff[4]);
                lock[125][1] = 0;
                while(lock[125][0]) {
                    #pragma omp flush(lock[125][0])
                }

                eval_3_isog_mod(pts[1230], pts[1237], coeff[115]);
                eval_3_isog_mod(pts[1232], pts[1239], coeff[115]);
                eval_3_isog_mod(pts[1235], pts[1242], coeff[5]);
                eval_3_isog_mod(pts[1237], pts[1243], coeff[116]);
                get_3_isog(pts[1243], A24minus[118], A24plus[118], coeff[117]);
                eval_3_isog_mod(pts[1239], pts[1245], coeff[116]);
                eval_3_isog_mod(pts[1242], pts[1248], coeff[6]);
                lock[126][1] = 0;
                while(lock[126][0]) {
                    #pragma omp flush(lock[126][0])
                }

                eval_3_isog_mod(pts[1245], pts[1250], coeff[117]);
                eval_3_isog_mod(pts[1246], pts[1251], coeff[116]);
                lock[127][1] = 0;
                while(lock[127][0]) {
                    #pragma omp flush(lock[127][0])
                }

                eval_3_isog_mod(pts[1248], pts[1253], coeff[7]);
                eval_3_isog_mod(pts[1252], pts[1256], coeff[105]);
                eval_3_isog_mod(pts[1253], pts[1257], coeff[8]);
                eval_3_isog_mod(pts[1256], pts[1260], coeff[106]);
                eval_3_isog_mod(pts[1257], pts[1261], coeff[9]);
                eval_3_isog_mod(pts[1260], pts[1264], coeff[107]);
                eval_3_isog_mod(pts[1261], pts[1265], coeff[10]);
                lock[128][1] = 0;
                while(lock[128][0]) {
                    #pragma omp flush(lock[128][0])
                }

                eval_3_isog_mod(pts[1265], pts[1268], coeff[11]);
                xTPLe(pts[1266], pts[1269], A24minus[121], A24plus[121], 1);
                lock[129][1] = 0;
                while(lock[129][0]) {
                    #pragma omp flush(lock[129][0])
                }

                xTPLe(pts[1269], pts[1272], A24minus[121], A24plus[121], 1);
                eval_3_isog_mod(pts[1270], pts[1273], coeff[110]);
                lock[130][1] = 0;
                while(lock[130][0]) {
                    #pragma omp flush(lock[130][0])
                }

                xTPLe(pts[1272], pts[1275], A24minus[121], A24plus[121], 1);
                xTPLe(pts[1275], pts[1278], A24minus[121], A24plus[121], 1);
                lock[131][1] = 0;
                while(lock[131][0]) {
                    #pragma omp flush(lock[131][0])
                }

                eval_3_isog_mod(pts[1277], pts[1280], coeff[15]);
                xTPLe(pts[1278], pts[1281], A24minus[121], A24plus[121], 1);
                lock[132][1] = 0;
                while(lock[132][0]) {
                    #pragma omp flush(lock[132][0])
                }

                eval_3_isog_mod(pts[1280], pts[1283], coeff[16]);
                eval_3_isog_mod(pts[1283], pts[1286], coeff[17]);
                lock[133][1] = 0;
                while(lock[133][0]) {
                    #pragma omp flush(lock[133][0])
                }

                eval_3_isog_mod(pts[1285], pts[1288], coeff[115]);
                eval_3_isog_mod(pts[1286], pts[1289], coeff[18]);
                lock[134][1] = 0;
                while(lock[134][0]) {
                    #pragma omp flush(lock[134][0])
                }

                eval_3_isog_mod(pts[1288], pts[1291], coeff[116]);
                eval_3_isog_mod(pts[1291], pts[1294], coeff[117]);
                lock[135][1] = 0;
                while(lock[135][0]) {
                    #pragma omp flush(lock[135][0])
                }

                eval_3_isog_mod(pts[1290], pts[1296], coeff[121]);
                get_3_isog(pts[1296], A24minus[123], A24plus[123], coeff[122]);
                eval_3_isog_mod(pts[1287], pts[1297], coeff[121]);
                eval_3_isog_mod(pts[1281], pts[1299], coeff[121]);
                eval_3_isog_mod(pts[1294], pts[1301], coeff[118]);
                lock[136][1] = 0;
                while(lock[136][0]) {
                    #pragma omp flush(lock[136][0])
                }

                eval_3_isog_mod(pts[1298], pts[1304], coeff[122]);
                eval_3_isog_mod(pts[1299], pts[1305], coeff[122]);
                eval_3_isog_mod(pts[1266], pts[1307], coeff[121]);
                lock[137][1] = 0;
                while(lock[137][0]) {
                    #pragma omp flush(lock[137][0])
                }

                eval_3_isog_mod(pts[1302], pts[1309], coeff[22]);
                eval_3_isog_mod(pts[1305], pts[1311], coeff[123]);
                eval_3_isog_mod(pts[1308], pts[1314], coeff[120]);
                lock[138][1] = 0;
                while(lock[138][0]) {
                    #pragma omp flush(lock[138][0])
                }

                eval_3_isog_mod(pts[1311], pts[1316], coeff[124]);
                get_3_isog(pts[1316], A24minus[126], A24plus[126], coeff[125]);
                eval_3_isog_mod(pts[1312], pts[1317], coeff[124]);
                eval_3_isog_mod(pts[1314], pts[1319], coeff[121]);
                eval_3_isog_mod(pts[1317], pts[1321], coeff[125]);
                eval_3_isog_mod(pts[1319], pts[1323], coeff[122]);
                lock[139][1] = 0;
                while(lock[139][0]) {
                    #pragma omp flush(lock[139][0])
                }

                eval_3_isog_mod(pts[1322], pts[1326], coeff[125]);
                eval_3_isog_mod(pts[1324], pts[1328], coeff[26]);
                lock[140][1] = 0;
                while(lock[140][0]) {
                    #pragma omp flush(lock[140][0])
                }

                eval_3_isog_mod(pts[1326], pts[1330], coeff[126]);
                eval_3_isog_mod(pts[1328], pts[1332], coeff[27]);
                lock[141][1] = 0;
                while(lock[141][0]) {
                    #pragma omp flush(lock[141][0])
                }

                eval_3_isog_mod(pts[1331], pts[1334], coeff[125]);
                eval_3_isog_mod(pts[1332], pts[1335], coeff[28]);
                lock[142][1] = 0;
                while(lock[142][0]) {
                    #pragma omp flush(lock[142][0])
                }

                eval_3_isog_mod(pts[1334], pts[1337], coeff[126]);
                eval_3_isog_mod(pts[1337], pts[1340], coeff[127]);
                lock[143][1] = 0;
                while(lock[143][0]) {
                    #pragma omp flush(lock[143][0])
                }

                eval_3_isog_mod(pts[1336], pts[1342], coeff[128]);
                get_3_isog(pts[1342], A24minus[130], A24plus[130], coeff[129]);
                eval_3_isog_mod(pts[1340], pts[1344], coeff[128]);
                lock[144][1] = 0;
                while(lock[144][0]) {
                    #pragma omp flush(lock[144][0])
                }

                eval_3_isog_mod(pts[1343], pts[1346], coeff[129]);
                get_3_isog(pts[1346], A24minus[131], A24plus[131], coeff[130]);
                eval_3_isog_mod(pts[1344], pts[1347], coeff[129]);
                eval_3_isog_mod(pts[1347], pts[1349], coeff[130]);
                xTPLe(pts[1349], pts[1351], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1351], pts[1353], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1353], pts[1355], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1355], pts[1357], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1357], pts[1359], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1359], pts[1361], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1361], pts[1363], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1363], pts[1365], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1365], pts[1367], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1367], pts[1369], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1369], pts[1371], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1371], pts[1373], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1373], pts[1375], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1375], pts[1377], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1377], pts[1379], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1379], pts[1381], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1381], pts[1383], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1383], pts[1385], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1385], pts[1387], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1387], pts[1389], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1389], pts[1391], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1391], pts[1393], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1393], pts[1395], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1395], pts[1397], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1397], pts[1399], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1399], pts[1401], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1401], pts[1403], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1403], pts[1405], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1405], pts[1407], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1407], pts[1409], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1409], pts[1411], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1411], pts[1413], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1413], pts[1415], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1415], pts[1417], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1417], pts[1419], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1419], pts[1421], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1421], pts[1423], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1423], pts[1425], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1425], pts[1427], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1427], pts[1429], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1429], pts[1431], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1431], pts[1433], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1433], pts[1435], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1435], pts[1437], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1437], pts[1439], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1439], pts[1441], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1441], pts[1443], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1443], pts[1445], A24minus[131], A24plus[131], 1);
                xTPLe(pts[1445], pts[1447], A24minus[131], A24plus[131], 1);
                get_3_isog(pts[1447], A24minus[132], A24plus[132], coeff[131]);
                lock[145][1] = 0;
                while(lock[145][0]) {
                    #pragma omp flush(lock[145][0])
                }

                eval_3_isog_mod(pts[1445], pts[1449], coeff[131]);
                get_3_isog(pts[1449], A24minus[133], A24plus[133], coeff[132]);
                eval_3_isog_mod(pts[1439], pts[1452], coeff[131]);
                eval_3_isog_mod(pts[1435], pts[1453], coeff[131]);
                lock[146][1] = 0;
                while(lock[146][0]) {
                    #pragma omp flush(lock[146][0])
                }

                eval_3_isog_mod(pts[1450], pts[1455], coeff[132]);
                get_3_isog(pts[1455], A24minus[134], A24plus[134], coeff[133]);
                eval_3_isog_mod(pts[1453], pts[1458], coeff[132]);
                eval_3_isog_mod(pts[1454], pts[1460], coeff[84]);
                lock[147][1] = 0;
                while(lock[147][0]) {
                    #pragma omp flush(lock[147][0])
                }

                eval_3_isog_mod(pts[1457], pts[1462], coeff[133]);
                eval_3_isog_mod(pts[1458], pts[1463], coeff[133]);
                lock[148][1] = 0;
                while(lock[148][0]) {
                    #pragma omp flush(lock[148][0])
                }

                eval_3_isog_mod(pts[1460], pts[1465], coeff[85]);
                eval_3_isog_mod(pts[1464], pts[1468], coeff[133]);
                eval_3_isog_mod(pts[1465], pts[1470], coeff[86]);
                eval_3_isog_mod(pts[1468], pts[1472], coeff[134]);
                eval_3_isog_mod(pts[1470], pts[1474], coeff[87]);
                lock[149][1] = 0;
                while(lock[149][0]) {
                    #pragma omp flush(lock[149][0])
                }

                eval_3_isog_mod(pts[1472], pts[1476], coeff[135]);
                eval_3_isog_mod(pts[1473], pts[1477], coeff[133]);
                lock[150][1] = 0;
                while(lock[150][0]) {
                    #pragma omp flush(lock[150][0])
                }

                eval_3_isog_mod(pts[1471], pts[1479], coeff[136]);
                get_3_isog(pts[1479], A24minus[138], A24plus[138], coeff[137]);
                eval_3_isog_mod(pts[1477], pts[1481], coeff[134]);
                lock[151][1] = 0;
                while(lock[151][0]) {
                    #pragma omp flush(lock[151][0])
                }

                eval_3_isog_mod(pts[1478], pts[1483], coeff[89]);
                eval_3_isog_mod(pts[1482], pts[1486], coeff[132]);
                eval_3_isog_mod(pts[1483], pts[1487], coeff[90]);
                eval_3_isog_mod(pts[1486], pts[1490], coeff[133]);
                eval_3_isog_mod(pts[1487], pts[1491], coeff[91]);
                eval_3_isog_mod(pts[1490], pts[1494], coeff[134]);
                eval_3_isog_mod(pts[1491], pts[1495], coeff[92]);
                lock[152][1] = 0;
                while(lock[152][0]) {
                    #pragma omp flush(lock[152][0])
                }

                eval_3_isog_mod(pts[1484], pts[1497], coeff[138]);
                eval_3_isog_mod(pts[1494], pts[1499], coeff[135]);
                eval_3_isog_mod(pts[1497], pts[1502], coeff[139]);
                get_3_isog(pts[1502], A24minus[141], A24plus[141], coeff[140]);
                eval_3_isog_mod(pts[1499], pts[1504], coeff[136]);
                lock[153][1] = 0;
                while(lock[153][0]) {
                    #pragma omp flush(lock[153][0])
                }

                eval_3_isog_mod(pts[1500], pts[1505], coeff[132]);
                eval_3_isog_mod(pts[1503], pts[1507], coeff[140]);
                eval_3_isog_mod(pts[1505], pts[1509], coeff[133]);
                xTPLe(pts[1507], pts[1511], A24minus[141], A24plus[141], 1);
                eval_3_isog_mod(pts[1509], pts[1513], coeff[134]);
                xTPLe(pts[1511], pts[1515], A24minus[141], A24plus[141], 1);
                eval_3_isog_mod(pts[1513], pts[1517], coeff[135]);
                xTPLe(pts[1515], pts[1519], A24minus[141], A24plus[141], 1);
                get_3_isog(pts[1519], A24minus[142], A24plus[142], coeff[141]);
                eval_3_isog_mod(pts[1517], pts[1521], coeff[136]);
                lock[154][1] = 0;
                while(lock[154][0]) {
                    #pragma omp flush(lock[154][0])
                }

                eval_3_isog_mod(pts[1515], pts[1523], coeff[141]);
                get_3_isog(pts[1523], A24minus[143], A24plus[143], coeff[142]);
                eval_3_isog_mod(pts[1520], pts[1526], coeff[141]);
                eval_3_isog_mod(pts[1522], pts[1528], coeff[99]);
                lock[155][1] = 0;
                while(lock[155][0]) {
                    #pragma omp flush(lock[155][0])
                }

                eval_3_isog_mod(pts[1525], pts[1530], coeff[142]);
                eval_3_isog_mod(pts[1526], pts[1531], coeff[142]);
                eval_3_isog_mod(pts[1528], pts[1534], coeff[100]);
                lock[156][1] = 0;
                while(lock[156][0]) {
                    #pragma omp flush(lock[156][0])
                }

                eval_3_isog_mod(pts[1530], pts[1535], coeff[143]);
                get_3_isog(pts[1535], A24minus[145], A24plus[145], coeff[144]);
                eval_3_isog_mod(pts[1532], pts[1537], coeff[139]);
                lock[157][1] = 0;
                while(lock[157][0]) {
                    #pragma omp flush(lock[157][0])
                }

                eval_3_isog_mod(pts[1534], pts[1539], coeff[101]);
                eval_3_isog_mod(pts[1537], pts[1541], coeff[140]);
                eval_3_isog_mod(pts[1539], pts[1543], coeff[102]);
                eval_3_isog_mod(pts[1541], pts[1545], coeff[141]);
                eval_3_isog_mod(pts[1543], pts[1547], coeff[103]);
                eval_3_isog_mod(pts[1545], pts[1549], coeff[142]);
                eval_3_isog_mod(pts[1547], pts[1551], coeff[104]);
                eval_3_isog_mod(pts[1549], pts[1553], coeff[143]);
                eval_3_isog_mod(pts[1551], pts[1555], coeff[105]);
                eval_3_isog_mod(pts[1553], pts[1557], coeff[144]);
                eval_3_isog_mod(pts[1555], pts[1559], coeff[106]);
                lock[158][1] = 0;
                while(lock[158][0]) {
                    #pragma omp flush(lock[158][0])
                }

                eval_3_isog_mod(pts[1544], pts[1562], coeff[145]);
                eval_3_isog_mod(pts[1540], pts[1563], coeff[145]);
                eval_3_isog_mod(pts[1558], pts[1565], coeff[138]);
                eval_3_isog_mod(pts[1562], pts[1568], coeff[146]);
                eval_3_isog_mod(pts[1563], pts[1569], coeff[146]);
                eval_3_isog_mod(pts[1565], pts[1571], coeff[139]);
                lock[159][1] = 0;
                while(lock[159][0]) {
                    #pragma omp flush(lock[159][0])
                }

                eval_3_isog_mod(pts[1569], pts[1574], coeff[147]);
                eval_3_isog_mod(pts[1570], pts[1575], coeff[147]);
                lock[160][1] = 0;
                while(lock[160][0]) {
                    #pragma omp flush(lock[160][0])
                }

                eval_3_isog_mod(pts[1574], pts[1578], coeff[148]);
                get_3_isog(pts[1578], A24minus[150], A24plus[150], coeff[149]);
                eval_3_isog_mod(pts[1576], pts[1580], coeff[141]);
                lock[161][1] = 0;
                while(lock[161][0]) {
                    #pragma omp flush(lock[161][0])
                }

                eval_3_isog_mod(pts[1579], pts[1582], coeff[149]);
                eval_3_isog_mod(pts[1580], pts[1583], coeff[142]);
                lock[162][1] = 0;
                while(lock[162][0]) {
                    #pragma omp flush(lock[162][0])
                }

                xTPLe(pts[1582], pts[1585], A24minus[150], A24plus[150], 1);
                eval_3_isog_mod(pts[1584], pts[1588], coeff[112]);
                xTPLe(pts[1585], pts[1589], A24minus[150], A24plus[150], 1);
                eval_3_isog_mod(pts[1588], pts[1592], coeff[113]);
                xTPLe(pts[1589], pts[1593], A24minus[150], A24plus[150], 1);
                eval_3_isog_mod(pts[1592], pts[1596], coeff[114]);
                xTPLe(pts[1593], pts[1597], A24minus[150], A24plus[150], 1);
                eval_3_isog_mod(pts[1596], pts[1600], coeff[115]);
                xTPLe(pts[1597], pts[1601], A24minus[150], A24plus[150], 1);
                eval_3_isog_mod(pts[1600], pts[1604], coeff[116]);
                xTPLe(pts[1601], pts[1605], A24minus[150], A24plus[150], 1);
                get_3_isog(pts[1605], A24minus[151], A24plus[151], coeff[150]);
                eval_3_isog_mod(pts[1604], pts[1608], coeff[117]);
                lock[163][1] = 0;
                while(lock[163][0]) {
                    #pragma omp flush(lock[163][0])
                }

                eval_3_isog_mod(pts[1597], pts[1610], coeff[150]);
                eval_3_isog_mod(pts[1589], pts[1612], coeff[150]);
                eval_3_isog_mod(pts[1606], pts[1614], coeff[149]);
                eval_3_isog_mod(pts[1608], pts[1616], coeff[118]);
                lock[164][1] = 0;
                while(lock[164][0]) {
                    #pragma omp flush(lock[164][0])
                }

                eval_3_isog_mod(pts[1610], pts[1617], coeff[151]);
                get_3_isog(pts[1617], A24minus[153], A24plus[153], coeff[152]);
                eval_3_isog_mod(pts[1613], pts[1620], coeff[151]);
                eval_3_isog_mod(pts[1614], pts[1621], coeff[150]);
                lock[165][1] = 0;
                while(lock[165][0]) {
                    #pragma omp flush(lock[165][0])
                }

                eval_3_isog_mod(pts[1618], pts[1624], coeff[152]);
                get_3_isog(pts[1624], A24minus[154], A24plus[154], coeff[153]);
                eval_3_isog_mod(pts[1620], pts[1626], coeff[152]);
                eval_3_isog_mod(pts[1621], pts[1627], coeff[151]);
                lock[166][1] = 0;
                while(lock[166][0]) {
                    #pragma omp flush(lock[166][0])
                }

                eval_3_isog_mod(pts[1623], pts[1629], coeff[120]);
                eval_3_isog_mod(pts[1626], pts[1631], coeff[153]);
                eval_3_isog_mod(pts[1629], pts[1634], coeff[121]);
                lock[167][1] = 0;
                while(lock[167][0]) {
                    #pragma omp flush(lock[167][0])
                }

                eval_3_isog_mod(pts[1632], pts[1636], coeff[153]);
                eval_3_isog_mod(pts[1634], pts[1638], coeff[122]);
                eval_3_isog_mod(pts[1636], pts[1640], coeff[154]);
                eval_3_isog_mod(pts[1638], pts[1642], coeff[123]);
                lock[168][1] = 0;
                while(lock[168][0]) {
                    #pragma omp flush(lock[168][0])
                }

                eval_3_isog_mod(pts[1640], pts[1644], coeff[155]);
                eval_3_isog_mod(pts[1641], pts[1645], coeff[143]);
                lock[169][1] = 0;
                while(lock[169][0]) {
                    #pragma omp flush(lock[169][0])
                }

                eval_3_isog_mod(pts[1644], pts[1647], coeff[156]);
                xTPLe(pts[1647], pts[1650], A24minus[157], A24plus[157], 1);
                lock[170][1] = 0;
                while(lock[170][0]) {
                    #pragma omp flush(lock[170][0])
                }

                eval_3_isog_mod(pts[1648], pts[1651], coeff[145]);
                eval_3_isog_mod(pts[1651], pts[1654], coeff[146]);
                lock[171][1] = 0;
                while(lock[171][0]) {
                    #pragma omp flush(lock[171][0])
                }

                xTPLe(pts[1653], pts[1656], A24minus[157], A24plus[157], 1);
                eval_3_isog_mod(pts[1654], pts[1657], coeff[147]);
                lock[172][1] = 0;
                while(lock[172][0]) {
                    #pragma omp flush(lock[172][0])
                }

                eval_3_isog_mod(pts[1657], pts[1660], coeff[148]);
                eval_3_isog_mod(pts[1658], pts[1661], coeff[129]);
                lock[173][1] = 0;
                while(lock[173][0]) {
                    #pragma omp flush(lock[173][0])
                }

                eval_3_isog_mod(pts[1661], pts[1664], coeff[130]);
                xTPLe(pts[1662], pts[1665], A24minus[157], A24plus[157], 1);
                lock[174][1] = 0;
                while(lock[174][0]) {
                    #pragma omp flush(lock[174][0])
                }

                xTPLe(pts[1665], pts[1668], A24minus[157], A24plus[157], 1);
                eval_3_isog_mod(pts[1666], pts[1669], coeff[151]);
                lock[175][1] = 0;
                while(lock[175][0]) {
                    #pragma omp flush(lock[175][0])
                }

                eval_3_isog_mod(pts[1669], pts[1672], coeff[152]);
                eval_3_isog_mod(pts[1670], pts[1673], coeff[133]);
                lock[176][1] = 0;
                while(lock[176][0]) {
                    #pragma omp flush(lock[176][0])
                }

                eval_3_isog_mod(pts[1673], pts[1676], coeff[134]);
                eval_3_isog_mod(pts[1671], pts[1677], coeff[157]);
                get_3_isog(pts[1677], A24minus[159], A24plus[159], coeff[158]);
                eval_3_isog_mod(pts[1662], pts[1680], coeff[157]);
                eval_3_isog_mod(pts[1656], pts[1681], coeff[157]);
                lock[177][1] = 0;
                while(lock[177][0]) {
                    #pragma omp flush(lock[177][0])
                }

                eval_3_isog_mod(pts[1676], pts[1683], coeff[135]);
                eval_3_isog_mod(pts[1680], pts[1686], coeff[158]);
                eval_3_isog_mod(pts[1647], pts[1688], coeff[157]);
                eval_3_isog_mod(pts[1683], pts[1690], coeff[136]);
                lock[178][1] = 0;
                while(lock[178][0]) {
                    #pragma omp flush(lock[178][0])
                }

                eval_3_isog_mod(pts[1685], pts[1691], coeff[159]);
                get_3_isog(pts[1691], A24minus[161], A24plus[161], coeff[160]);
                eval_3_isog_mod(pts[1688], pts[1694], coeff[158]);
                eval_3_isog_mod(pts[1690], pts[1696], coeff[137]);
                lock[179][1] = 0;
                while(lock[179][0]) {
                    #pragma omp flush(lock[179][0])
                }

                eval_3_isog_mod(pts[1692], pts[1697], coeff[160]);
                get_3_isog(pts[1697], A24minus[162], A24plus[162], coeff[161]);
                eval_3_isog_mod(pts[1694], pts[1699], coeff[159]);
                lock[180][1] = 0;
                while(lock[180][0]) {
                    #pragma omp flush(lock[180][0])
                }

                eval_3_isog_mod(pts[1696], pts[1701], coeff[138]);
                eval_3_isog_mod(pts[1699], pts[1703], coeff[160]);
                eval_3_isog_mod(pts[1701], pts[1705], coeff[139]);
                eval_3_isog_mod(pts[1703], pts[1707], coeff[161]);
                eval_3_isog_mod(pts[1705], pts[1709], coeff[140]);
                lock[181][1] = 0;
                while(lock[181][0]) {
                    #pragma omp flush(lock[181][0])
                }

                eval_3_isog_mod(pts[1708], pts[1712], coeff[160]);
                eval_3_isog_mod(pts[1709], pts[1713], coeff[141]);
                lock[182][1] = 0;
                while(lock[182][0]) {
                    #pragma omp flush(lock[182][0])
                }

                eval_3_isog_mod(pts[1712], pts[1715], coeff[161]);
                eval_3_isog_mod(pts[1715], pts[1718], coeff[162]);
                lock[183][1] = 0;
                while(lock[183][0]) {
                    #pragma omp flush(lock[183][0])
                }

                xTPLe(pts[1717], pts[1720], A24minus[164], A24plus[164], 1);
                get_3_isog(pts[1720], A24minus[165], A24plus[165], coeff[164]);
                eval_3_isog_mod(pts[1718], pts[1721], coeff[163]);
                lock[184][1] = 0;
                while(lock[184][0]) {
                    #pragma omp flush(lock[184][0])
                }

                eval_3_isog_mod(pts[1717], pts[1723], coeff[164]);
                get_3_isog(pts[1723], A24minus[166], A24plus[166], coeff[165]);
                eval_3_isog_mod(pts[1721], pts[1725], coeff[164]);
                lock[185][1] = 0;
                while(lock[185][0]) {
                    #pragma omp flush(lock[185][0])
                }

                eval_3_isog_mod(pts[1724], pts[1727], coeff[165]);
                get_3_isog(pts[1727], A24minus[167], A24plus[167], coeff[166]);
                lock[186][1] = 0;
                while(lock[186][0]) {
                    #pragma omp flush(lock[186][0])
                }

                eval_3_isog_mod(pts[1726], pts[1729], coeff[146]);
                eval_3_isog_mod(pts[1729], pts[1731], coeff[147]);
                eval_3_isog_mod(pts[1731], pts[1733], coeff[148]);
                eval_3_isog_mod(pts[1733], pts[1735], coeff[149]);
                eval_3_isog_mod(pts[1735], pts[1737], coeff[150]);
                eval_3_isog_mod(pts[1737], pts[1739], coeff[151]);
                eval_3_isog_mod(pts[1739], pts[1741], coeff[152]);
                eval_3_isog_mod(pts[1741], pts[1743], coeff[153]);
                eval_3_isog_mod(pts[1743], pts[1745], coeff[154]);
                eval_3_isog_mod(pts[1745], pts[1747], coeff[155]);
                eval_3_isog_mod(pts[1747], pts[1749], coeff[156]);
                eval_3_isog_mod(pts[1749], pts[1751], coeff[157]);
                eval_3_isog_mod(pts[1751], pts[1753], coeff[158]);
                eval_3_isog_mod(pts[1753], pts[1755], coeff[159]);
                eval_3_isog_mod(pts[1755], pts[1757], coeff[160]);
                lock[187][1] = 0;
                while(lock[187][0]) {
                    #pragma omp flush(lock[187][0])
                }

                eval_3_isog_mod(pts[1752], pts[1759], coeff[167]);
                eval_3_isog_mod(pts[1748], pts[1761], coeff[167]);
                eval_3_isog_mod(pts[1759], pts[1764], coeff[168]);
                get_3_isog(pts[1764], A24minus[170], A24plus[170], coeff[169]);
                eval_3_isog_mod(pts[1761], pts[1766], coeff[168]);
                eval_3_isog_mod(pts[1738], pts[1768], coeff[167]);
                lock[188][1] = 0;
                while(lock[188][0]) {
                    #pragma omp flush(lock[188][0])
                }

                eval_3_isog_mod(pts[1765], pts[1770], coeff[169]);
                get_3_isog(pts[1770], A24minus[171], A24plus[171], coeff[170]);
                eval_3_isog_mod(pts[1766], pts[1771], coeff[169]);
                eval_3_isog_mod(pts[1768], pts[1773], coeff[168]);
                lock[189][1] = 0;
                while(lock[189][0]) {
                    #pragma omp flush(lock[189][0])
                }

                eval_3_isog_mod(pts[1772], pts[1776], coeff[170]);
                eval_3_isog_mod(pts[1730], pts[1778], coeff[167]);
                lock[190][1] = 0;
                while(lock[190][0]) {
                    #pragma omp flush(lock[190][0])
                }

                eval_3_isog_mod(pts[1776], pts[1780], coeff[171]);
                eval_3_isog_mod(pts[1777], pts[1781], coeff[170]);
                xTPLe(pts[1780], pts[1784], A24minus[172], A24plus[172], 1);
                get_3_isog(pts[1784], A24minus[173], A24plus[173], coeff[172]);
                eval_3_isog_mod(pts[1781], pts[1785], coeff[171]);
                eval_3_isog_mod(pts[1780], pts[1788], coeff[172]);
                get_3_isog(pts[1788], A24minus[174], A24plus[174], coeff[173]);
                eval_3_isog_mod(pts[1785], pts[1789], coeff[172]);
                eval_3_isog_mod(pts[1789], pts[1792], coeff[173]);
                lock[191][1] = 0;
                while(lock[191][0]) {
                    #pragma omp flush(lock[191][0])
                }

                eval_3_isog_mod(pts[1790], pts[1793], coeff[171]);
                eval_3_isog_mod(pts[1793], pts[1796], coeff[172]);
                lock[192][1] = 0;
                while(lock[192][0]) {
                    #pragma omp flush(lock[192][0])
                }

                eval_3_isog_mod(pts[1794], pts[1797], coeff[169]);
                eval_3_isog_mod(pts[1797], pts[1800], coeff[170]);
                lock[193][1] = 0;
                while(lock[193][0]) {
                    #pragma omp flush(lock[193][0])
                }

                eval_3_isog_mod(pts[1792], pts[1802], coeff[174]);
                eval_3_isog_mod(pts[1800], pts[1804], coeff[171]);
                lock[194][1] = 0;
                while(lock[194][0]) {
                    #pragma omp flush(lock[194][0])
                }

                eval_3_isog_mod(pts[1803], pts[1806], coeff[175]);
                lock[195][1] = 0;
                while(lock[195][0]) {
                    #pragma omp flush(lock[195][0])
                }

                eval_3_isog_mod(pts[1804], pts[1807], coeff[172]);
                eval_3_isog_mod(pts[1807], pts[1809], coeff[173]);
                eval_3_isog_mod(pts[1809], pts[1811], coeff[174]);
                eval_3_isog_mod(pts[1811], pts[1813], coeff[175]);
                eval_3_isog_mod(pts[1813], pts[1815], coeff[176]);
                lock[196][1] = 0;
                while(lock[196][0]) {
                    #pragma omp flush(lock[196][0])
                }

                eval_3_isog_mod(pts[1808], pts[1818], coeff[177]);
                eval_3_isog_mod(pts[1815], pts[1819], coeff[177]);
                lock[197][1] = 0;
                while(lock[197][0]) {
                    #pragma omp flush(lock[197][0])
                }

                eval_3_isog_mod(pts[1818], pts[1821], coeff[178]);
                eval_3_isog_mod(pts[1821], pts[1823], coeff[179]);
                get_3_isog(pts[1823], A24minus[181], A24plus[181], coeff[180]);
                lock[198][1] = 0;
                while(lock[198][0]) {
                    #pragma omp flush(lock[198][0])
                }

                lock[199][1] = 0;
                while(lock[199][0]) {
                    #pragma omp flush(lock[199][0])
                }

                eval_3_isog_mod(pts[1880], pts[1884], coeff[181]);
                eval_3_isog_mod(pts[1878], pts[1886], coeff[181]);
                lock[200][1] = 0;
                while(lock[200][0]) {
                    #pragma omp flush(lock[200][0])
                }

                eval_3_isog_mod(pts[1884], pts[1888], coeff[182]);
                get_3_isog(pts[1888], A24minus[184], A24plus[184], coeff[183]);
                eval_3_isog_mod(pts[1886], pts[1890], coeff[182]);
                eval_3_isog_mod(pts[1873], pts[1892], coeff[181]);
                lock[201][1] = 0;
                while(lock[201][0]) {
                    #pragma omp flush(lock[201][0])
                }

                eval_3_isog_mod(pts[1889], pts[1893], coeff[183]);
                get_3_isog(pts[1893], A24minus[185], A24plus[185], coeff[184]);
                eval_3_isog_mod(pts[1891], pts[1895], coeff[183]);
                lock[202][1] = 0;
                while(lock[202][0]) {
                    #pragma omp flush(lock[202][0])
                }

                eval_3_isog_mod(pts[1895], pts[1898], coeff[184]);
                eval_3_isog_mod(pts[1896], pts[1899], coeff[183]);
                lock[203][1] = 0;
                while(lock[203][0]) {
                    #pragma omp flush(lock[203][0])
                }

                eval_3_isog_mod(pts[1899], pts[1902], coeff[184]);
                eval_3_isog_mod(pts[1900], pts[1903], coeff[182]);
                lock[204][1] = 0;
                while(lock[204][0]) {
                    #pragma omp flush(lock[204][0])
                }

                eval_3_isog_mod(pts[1903], pts[1906], coeff[183]);
                eval_3_isog_mod(pts[1901], pts[1907], coeff[186]);
                get_3_isog(pts[1907], A24minus[188], A24plus[188], coeff[187]);
                eval_3_isog_mod(pts[1906], pts[1909], coeff[184]);
                lock[205][1] = 0;
                while(lock[205][0]) {
                    #pragma omp flush(lock[205][0])
                }

                eval_3_isog_mod(pts[1909], pts[1912], coeff[185]);
                eval_3_isog_mod(pts[1910], pts[1913], coeff[182]);
                lock[206][1] = 0;
                while(lock[206][0]) {
                    #pragma omp flush(lock[206][0])
                }

                eval_3_isog_mod(pts[1912], pts[1915], coeff[186]);
                eval_3_isog_mod(pts[1915], pts[1918], coeff[187]);
                lock[207][1] = 0;
                while(lock[207][0]) {
                    #pragma omp flush(lock[207][0])
                }

                eval_3_isog_mod(pts[1914], pts[1920], coeff[188]);
                get_3_isog(pts[1920], A24minus[190], A24plus[190], coeff[189]);
                eval_3_isog_mod(pts[1918], pts[1922], coeff[188]);
                eval_3_isog_mod(pts[1858], pts[1924], coeff[181]);
                lock[208][1] = 0;
                while(lock[208][0]) {
                    #pragma omp flush(lock[208][0])
                }

                eval_3_isog_mod(pts[1922], pts[1926], coeff[189]);
                eval_3_isog_mod(pts[1924], pts[1928], coeff[182]);
                lock[209][1] = 0;
                while(lock[209][0]) {
                    #pragma omp flush(lock[209][0])
                }

                eval_3_isog_mod(pts[1927], pts[1930], coeff[187]);
                eval_3_isog_mod(pts[1928], pts[1931], coeff[183]);
                lock[210][1] = 0;
                while(lock[210][0]) {
                    #pragma omp flush(lock[210][0])
                }

                eval_3_isog_mod(pts[1930], pts[1933], coeff[188]);
                eval_3_isog_mod(pts[1933], pts[1936], coeff[189]);
                lock[211][1] = 0;
                while(lock[211][0]) {
                    #pragma omp flush(lock[211][0])
                }

                xTPLe(pts[1935], pts[1938], A24minus[191], A24plus[191], 1);
                get_3_isog(pts[1938], A24minus[192], A24plus[192], coeff[191]);
                eval_3_isog_mod(pts[1936], pts[1939], coeff[190]);
                eval_3_isog_mod(pts[1935], pts[1942], coeff[191]);
                get_3_isog(pts[1942], A24minus[193], A24plus[193], coeff[192]);
                lock[212][1] = 0;
                while(lock[212][0]) {
                    #pragma omp flush(lock[212][0])
                }

                eval_3_isog_mod(pts[1932], pts[1943], coeff[191]);
                eval_3_isog_mod(pts[1940], pts[1946], coeff[187]);
                eval_3_isog_mod(pts[1943], pts[1948], coeff[192]);
                get_3_isog(pts[1948], A24minus[194], A24plus[194], coeff[193]);
                lock[213][1] = 0;
                while(lock[213][0]) {
                    #pragma omp flush(lock[213][0])
                }

                eval_3_isog_mod(pts[1944], pts[1949], coeff[192]);
                eval_3_isog_mod(pts[1947], pts[1952], coeff[183]);
                eval_3_isog_mod(pts[1949], pts[1953], coeff[193]);
                get_3_isog(pts[1953], A24minus[195], A24plus[195], coeff[194]);
                eval_3_isog_mod(pts[1952], pts[1956], coeff[184]);
                lock[214][1] = 0;
                while(lock[214][0]) {
                    #pragma omp flush(lock[214][0])
                }

                eval_3_isog_mod(pts[1955], pts[1958], coeff[190]);
                eval_3_isog_mod(pts[1956], pts[1959], coeff[185]);
                lock[215][1] = 0;
                while(lock[215][0]) {
                    #pragma omp flush(lock[215][0])
                }

                eval_3_isog_mod(pts[1958], pts[1961], coeff[191]);
                eval_3_isog_mod(pts[1961], pts[1964], coeff[192]);
                lock[216][1] = 0;
                while(lock[216][0]) {
                    #pragma omp flush(lock[216][0])
                }

                eval_3_isog_mod(pts[1962], pts[1965], coeff[187]);
                eval_3_isog_mod(pts[1965], pts[1968], coeff[188]);
                lock[217][1] = 0;
                while(lock[217][0]) {
                    #pragma omp flush(lock[217][0])
                }

                eval_3_isog_mod(pts[1967], pts[1970], coeff[194]);
                lock[218][1] = 0;
                while(lock[218][0]) {
                    #pragma omp flush(lock[218][0])
                }

                eval_3_isog_mod(pts[1966], pts[1972], coeff[195]);
                get_3_isog(pts[1972], A24minus[197], A24plus[197], coeff[196]);
                eval_3_isog_mod(pts[1963], pts[1973], coeff[195]);
                eval_3_isog_mod(pts[1957], pts[1975], coeff[195]);
                eval_3_isog_mod(pts[1973], pts[1978], coeff[196]);
                get_3_isog(pts[1978], A24minus[198], A24plus[198], coeff[197]);
                lock[219][1] = 0;
                while(lock[219][0]) {
                    #pragma omp flush(lock[219][0])
                }

                eval_3_isog_mod(pts[1975], pts[1980], coeff[196]);
                eval_3_isog_mod(pts[1977], pts[1982], coeff[191]);
                eval_3_isog_mod(pts[1980], pts[1984], coeff[197]);
                eval_3_isog_mod(pts[1982], pts[1986], coeff[192]);
                lock[220][1] = 0;
                while(lock[220][0]) {
                    #pragma omp flush(lock[220][0])
                }

                eval_3_isog_mod(pts[1985], pts[1988], coeff[198]);
                eval_3_isog_mod(pts[1986], pts[1989], coeff[193]);
                lock[221][1] = 0;
                while(lock[221][0]) {
                    #pragma omp flush(lock[221][0])
                }

                eval_3_isog_mod(pts[1989], pts[1992], coeff[194]);
                eval_3_isog_mod(pts[1990], pts[1993], coeff[182]);
                lock[222][1] = 0;
                while(lock[222][0]) {
                    #pragma omp flush(lock[222][0])
                }

                eval_3_isog_mod(pts[1992], pts[1995], coeff[195]);
                eval_3_isog_mod(pts[1995], pts[1998], coeff[196]);
                lock[223][1] = 0;
                while(lock[223][0]) {
                    #pragma omp flush(lock[223][0])
                }

                eval_3_isog_mod(pts[1996], pts[1999], coeff[184]);
                eval_3_isog_mod(pts[1999], pts[2002], coeff[185]);
                lock[224][1] = 0;
                while(lock[224][0]) {
                    #pragma omp flush(lock[224][0])
                }

                xTPLe(pts[2000], pts[2003], A24minus[200], A24plus[200], 1);
                xTPLe(pts[2003], pts[2006], A24minus[200], A24plus[200], 1);
                get_3_isog(pts[2006], A24minus[201], A24plus[201], coeff[200]);
                lock[225][1] = 0;
                while(lock[225][0]) {
                    #pragma omp flush(lock[225][0])
                }

                eval_3_isog_mod(pts[2005], pts[2008], coeff[187]);
                eval_3_isog_mod(pts[2000], pts[2010], coeff[200]);
                eval_3_isog_mod(pts[1994], pts[2012], coeff[200]);
                eval_3_isog_mod(pts[1991], pts[2013], coeff[200]);
                lock[226][1] = 0;
                while(lock[226][0]) {
                    #pragma omp flush(lock[226][0])
                }

                eval_3_isog_mod(pts[2010], pts[2016], coeff[201]);
                get_3_isog(pts[2016], A24minus[203], A24plus[203], coeff[202]);
                eval_3_isog_mod(pts[2011], pts[2017], coeff[201]);
                eval_3_isog_mod(pts[2013], pts[2019], coeff[201]);
                eval_3_isog_mod(pts[2017], pts[2022], coeff[202]);
                get_3_isog(pts[2022], A24minus[204], A24plus[204], coeff[203]);
                lock[227][1] = 0;
                while(lock[227][0]) {
                    #pragma omp flush(lock[227][0])
                }

                eval_3_isog_mod(pts[2019], pts[2024], coeff[202]);
                eval_3_isog_mod(pts[2021], pts[2026], coeff[190]);
                eval_3_isog_mod(pts[2024], pts[2028], coeff[203]);
                eval_3_isog_mod(pts[2026], pts[2030], coeff[191]);
                lock[228][1] = 0;
                while(lock[228][0]) {
                    #pragma omp flush(lock[228][0])
                }

                eval_3_isog_mod(pts[2028], pts[2031], coeff[204]);
                get_3_isog(pts[2031], A24minus[206], A24plus[206], coeff[205]);
                lock[229][1] = 0;
                while(lock[229][0]) {
                    #pragma omp flush(lock[229][0])
                }

                eval_3_isog_mod(pts[2030], pts[2033], coeff[192]);
                eval_3_isog_mod(pts[2033], pts[2035], coeff[193]);
                eval_3_isog_mod(pts[2035], pts[2037], coeff[194]);
                eval_3_isog_mod(pts[2037], pts[2040], coeff[195]);
                lock[230][1] = 0;
                while(lock[230][0]) {
                    #pragma omp flush(lock[230][0])
                }

                xTPLe(pts[2039], pts[2042], A24minus[206], A24plus[206], 1);
                eval_3_isog_mod(pts[2040], pts[2043], coeff[196]);
                lock[231][1] = 0;
                while(lock[231][0]) {
                    #pragma omp flush(lock[231][0])
                }

                xTPLe(pts[2042], pts[2045], A24minus[206], A24plus[206], 1);
                xTPLe(pts[2045], pts[2048], A24minus[206], A24plus[206], 1);
                lock[232][1] = 0;
                while(lock[232][0]) {
                    #pragma omp flush(lock[232][0])
                }

                eval_3_isog_mod(pts[2047], pts[2050], coeff[185]);
                xTPLe(pts[2048], pts[2051], A24minus[206], A24plus[206], 1);
                lock[233][1] = 0;
                while(lock[233][0]) {
                    #pragma omp flush(lock[233][0])
                }

                eval_3_isog_mod(pts[2050], pts[2053], coeff[186]);
                eval_3_isog_mod(pts[2053], pts[2056], coeff[187]);
                lock[234][1] = 0;
                while(lock[234][0]) {
                    #pragma omp flush(lock[234][0])
                }

                xTPLe(pts[2054], pts[2057], A24minus[206], A24plus[206], 1);
                xTPLe(pts[2057], pts[2060], A24minus[206], A24plus[206], 1);
                get_3_isog(pts[2060], A24minus[207], A24plus[207], coeff[206]);
                lock[235][1] = 0;
                while(lock[235][0]) {
                    #pragma omp flush(lock[235][0])
                }

                eval_3_isog_mod(pts[2058], pts[2061], coeff[202]);
                eval_3_isog_mod(pts[2057], pts[2063], coeff[206]);
                get_3_isog(pts[2063], A24minus[208], A24plus[208], coeff[207]);
                eval_3_isog_mod(pts[2048], pts[2066], coeff[206]);
                eval_3_isog_mod(pts[2061], pts[2068], coeff[203]);
                lock[236][1] = 0;
                while(lock[236][0]) {
                    #pragma omp flush(lock[236][0])
                }

                eval_3_isog_mod(pts[2064], pts[2070], coeff[207]);
                get_3_isog(pts[2070], A24minus[209], A24plus[209], coeff[208]);
                eval_3_isog_mod(pts[2065], pts[2071], coeff[207]);
                eval_3_isog_mod(pts[2034], pts[2074], coeff[206]);
                eval_3_isog_mod(pts[2068], pts[2075], coeff[204]);
                lock[237][1] = 0;
                while(lock[237][0]) {
                    #pragma omp flush(lock[237][0])
                }

                eval_3_isog_mod(pts[2071], pts[2077], coeff[208]);
                get_3_isog(pts[2077], A24minus[210], A24plus[210], coeff[209]);
                eval_3_isog_mod(pts[2073], pts[2079], coeff[208]);
                eval_3_isog_mod(pts[2075], pts[2081], coeff[205]);
                lock[238][1] = 0;
                while(lock[238][0]) {
                    #pragma omp flush(lock[238][0])
                }

                eval_3_isog_mod(pts[2078], pts[2083], coeff[209]);
                get_3_isog(pts[2083], A24minus[211], A24plus[211], coeff[210]);
                eval_3_isog_mod(pts[2081], pts[2086], coeff[206]);
                lock[239][1] = 0;
                while(lock[239][0]) {
                    #pragma omp flush(lock[239][0])
                }

                eval_3_isog_mod(pts[2082], pts[2087], coeff[193]);
                eval_3_isog_mod(pts[2085], pts[2089], coeff[209]);
                eval_3_isog_mod(pts[2087], pts[2091], coeff[194]);
                eval_3_isog_mod(pts[2089], pts[2093], coeff[210]);
                eval_3_isog_mod(pts[2091], pts[2095], coeff[195]);
                lock[240][1] = 0;
                while(lock[240][0]) {
                    #pragma omp flush(lock[240][0])
                }

                eval_3_isog_mod(pts[2094], pts[2098], coeff[209]);
                eval_3_isog_mod(pts[2095], pts[2099], coeff[196]);
                lock[241][1] = 0;
                while(lock[241][0]) {
                    #pragma omp flush(lock[241][0])
                }

                eval_3_isog_mod(pts[2099], pts[2102], coeff[197]);
                xTPLe(pts[2100], pts[2103], A24minus[213], A24plus[213], 1);
                lock[242][1] = 0;
                while(lock[242][0]) {
                    #pragma omp flush(lock[242][0])
                }

                xTPLe(pts[2103], pts[2106], A24minus[213], A24plus[213], 1);
                get_3_isog(pts[2106], A24minus[214], A24plus[214], coeff[213]);
                eval_3_isog_mod(pts[2104], pts[2107], coeff[212]);
                lock[243][1] = 0;
                while(lock[243][0]) {
                    #pragma omp flush(lock[243][0])
                }

                eval_3_isog_mod(pts[2100], pts[2110], coeff[213]);
                eval_3_isog_mod(pts[2107], pts[2111], coeff[213]);
                lock[244][1] = 0;
                while(lock[244][0]) {
                    #pragma omp flush(lock[244][0])
                }

                eval_3_isog_mod(pts[2110], pts[2113], coeff[214]);
                get_3_isog(pts[2113], A24minus[216], A24plus[216], coeff[215]);
                lock[245][1] = 0;
                while(lock[245][0]) {
                    #pragma omp flush(lock[245][0])
                }

                eval_3_isog_mod(pts[2112], pts[2115], coeff[201]);
                eval_3_isog_mod(pts[2115], pts[2117], coeff[202]);
                eval_3_isog_mod(pts[2117], pts[2119], coeff[203]);
                eval_3_isog_mod(pts[2119], pts[2121], coeff[204]);
                eval_3_isog_mod(pts[2121], pts[2123], coeff[205]);
                eval_3_isog_mod(pts[2123], pts[2125], coeff[206]);
                eval_3_isog_mod(pts[2125], pts[2127], coeff[207]);
                eval_3_isog_mod(pts[2127], pts[2129], coeff[208]);
                eval_3_isog_mod(pts[2129], pts[2131], coeff[209]);
                eval_3_isog_mod(pts[2131], pts[2133], coeff[210]);
                eval_3_isog_mod(pts[2133], pts[2135], coeff[211]);
                eval_3_isog_mod(pts[2135], pts[2137], coeff[212]);
                lock[246][1] = 0;
                while(lock[246][0]) {
                    #pragma omp flush(lock[246][0])
                }

                eval_3_isog_mod(pts[2130], pts[2140], coeff[216]);
                eval_3_isog_mod(pts[2126], pts[2142], coeff[216]);
                eval_3_isog_mod(pts[2122], pts[2143], coeff[216]);
                eval_3_isog_mod(pts[2140], pts[2146], coeff[217]);
                eval_3_isog_mod(pts[2142], pts[2148], coeff[217]);
                eval_3_isog_mod(pts[2143], pts[2149], coeff[217]);
                lock[247][1] = 0;
                while(lock[247][0]) {
                    #pragma omp flush(lock[247][0])
                }

                eval_3_isog_mod(pts[2144], pts[2151], coeff[214]);
                eval_3_isog_mod(pts[2147], pts[2153], coeff[218]);
                eval_3_isog_mod(pts[2149], pts[2155], coeff[218]);
                lock[248][1] = 0;
                while(lock[248][0]) {
                    #pragma omp flush(lock[248][0])
                }

                eval_3_isog_mod(pts[2153], pts[2158], coeff[219]);
                get_3_isog(pts[2158], A24minus[221], A24plus[221], coeff[220]);
                eval_3_isog_mod(pts[2155], pts[2160], coeff[219]);
                eval_3_isog_mod(pts[2156], pts[2161], coeff[218]);
                lock[249][1] = 0;
                while(lock[249][0]) {
                    #pragma omp flush(lock[249][0])
                }

                eval_3_isog_mod(pts[2159], pts[2163], coeff[220]);
                get_3_isog(pts[2163], A24minus[222], A24plus[222], coeff[221]);
                eval_3_isog_mod(pts[2162], pts[2166], coeff[217]);
                lock[250][1] = 0;
                while(lock[250][0]) {
                    #pragma omp flush(lock[250][0])
                }

                eval_3_isog_mod(pts[2164], pts[2167], coeff[221]);
                xTPLe(pts[2167], pts[2170], A24minus[222], A24plus[222], 1);
                get_3_isog(pts[2170], A24minus[223], A24plus[223], coeff[222]);
                lock[251][1] = 0;
                while(lock[251][0]) {
                    #pragma omp flush(lock[251][0])
                }

                eval_3_isog_mod(pts[2168], pts[2171], coeff[221]);
                eval_3_isog_mod(pts[2171], pts[2174], coeff[222]);
                lock[252][1] = 0;
                while(lock[252][0]) {
                    #pragma omp flush(lock[252][0])
                }

                eval_3_isog_mod(pts[2174], pts[2176], coeff[223]);
                xTPLe(pts[2176], pts[2178], A24minus[224], A24plus[224], 1);
                xTPLe(pts[2178], pts[2180], A24minus[224], A24plus[224], 1);
                get_3_isog(pts[2180], A24minus[225], A24plus[225], coeff[224]);
                eval_3_isog_mod(pts[2178], pts[2182], coeff[224]);
                get_3_isog(pts[2182], A24minus[226], A24plus[226], coeff[225]);
                lock[253][1] = 0;
                while(lock[253][0]) {
                    #pragma omp flush(lock[253][0])
                }

                eval_3_isog_mod(pts[2181], pts[2184], coeff[224]);
                eval_3_isog_mod(pts[2184], pts[2186], coeff[225]);
                lock[254][1] = 0;
                while(lock[254][0]) {
                    #pragma omp flush(lock[254][0])
                }

                lock[255][1] = 0;
                while(lock[255][0]) {
                    #pragma omp flush(lock[255][0])
                }

                eval_3_isog_mod(pts[2196], pts[2200], coeff[227]);
                eval_3_isog_mod(pts[2195], pts[2201], coeff[227]);
                eval_3_isog_mod(pts[2192], pts[2204], coeff[227]);
                lock[256][1] = 0;
                while(lock[256][0]) {
                    #pragma omp flush(lock[256][0])
                }

                eval_3_isog_mod(pts[2190], pts[2205], coeff[227]);
                eval_3_isog_mod(pts[2202], pts[2208], coeff[228]);
                eval_3_isog_mod(pts[2203], pts[2209], coeff[228]);
                eval_3_isog_mod(pts[2205], pts[2211], coeff[228]);
                lock[257][1] = 0;
                while(lock[257][0]) {
                    #pragma omp flush(lock[257][0])
                }

                eval_3_isog_mod(pts[2208], pts[2214], coeff[229]);
                eval_3_isog_mod(pts[2209], pts[2215], coeff[229]);
                eval_3_isog_mod(pts[2211], pts[2217], coeff[229]);
                lock[258][1] = 0;
                while(lock[258][0]) {
                    #pragma omp flush(lock[258][0])
                }

                eval_3_isog_mod(pts[2215], pts[2220], coeff[230]);
                eval_3_isog_mod(pts[2217], pts[2222], coeff[230]);
                lock[259][1] = 0;
                while(lock[259][0]) {
                    #pragma omp flush(lock[259][0])
                }

                eval_3_isog_mod(pts[2218], pts[2223], coeff[229]);
                eval_3_isog_mod(pts[2221], pts[2225], coeff[231]);
                lock[260][1] = 0;
                while(lock[260][0]) {
                    #pragma omp flush(lock[260][0])
                }

                eval_3_isog_mod(pts[2223], pts[2227], coeff[230]);
                eval_3_isog_mod(pts[2227], pts[2230], coeff[231]);
                eval_3_isog_mod(pts[2230], pts[2232], coeff[232]);
                lock[261][1] = 0;
                while(lock[261][0]) {
                    #pragma omp flush(lock[261][0])
                }

                xTPLe(pts[2231], pts[2233], A24minus[234], A24plus[234], 1);
                get_3_isog(pts[2233], A24minus[235], A24plus[235], coeff[234]);
                lock[262][1] = 0;
                while(lock[262][0]) {
                    #pragma omp flush(lock[262][0])
                }

                eval_3_isog_mod(pts[2231], pts[2235], coeff[234]);
                get_3_isog(pts[2235], A24minus[236], A24plus[236], coeff[235]);
                lock[263][1] = 0;
                while(lock[263][0]) {
                    #pragma omp flush(lock[263][0])
                }

                lock[264][1] = 0;
                while(lock[264][0]) {
                    #pragma omp flush(lock[264][0])
                }

                eval_3_isog_mod(pts[2237], pts[2241], coeff[236]);
            }
        }
    }

    eval_3_isog(pts[2241], coeff[237]);
    get_3_isog(pts[2241], A24minus[239], A24plus[239], coeff[238]);

    fp2add(A24plus[239], A24minus[239], A);
    fp2add(A, A, A);
    fp2sub(A24plus[239], A24minus[239], A24plus[239]);
    j_inv(A, A24plus[239], jinv);
    fp2_encode(jinv, SharedSecretB);

    return 0;
}

#else

int EphemeralKeyGeneration_B(const unsigned char* PrivateKeyB, unsigned char* PublicKeyB)
{ // Bob's ephemeral public key generation
  // Input:  a private key PrivateKeyB in the range [0, 2^Floor(Log(2,oB)) - 1]. 
  // Output: the public key PublicKeyB consisting of 3 elements in GF(p^2) which are encoded by removing leading 0 bytes.
    point_proj_t R1, public_pts[4] = {0}, pts1[MAX_INT_POINTS_BOB1], pts2[MAX_INT_POINTS_BOB2], KernelPoints2[KERNEL_POINTS2], test;
    f2elm_t  A24plus = {0}, A24minus = {0}, A = {0}, C24 = {0}, XPB1, XQB1, XRB1, XPB2, XQB2, XRB2 ;
    unsigned int i, row, m, index = 0, pts_index1[MAX_INT_POINTS_BOB1], pts_index2[MAX_INT_POINTS_BOB2], npts = 0, ii = 0;                 
    #if defined PARALLEL
        int tid, cn;
        cn = omp_get_max_threads();
    #endif
    
    // Initialize basis points
    init_basis((digit_t*)A_gen, public_pts[0]->X, public_pts[1]->X, public_pts[2]->X);
    init_basis((digit_t*)B1_gen, XPB1, XQB1, XRB1);
    init_basis((digit_t*)B2_gen, XPB2, XQB2, XRB2);
    
    
    fpcopy((digit_t*)&Montgomery_one, (public_pts[0]->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, (public_pts[1]->Z)[0]);
    fpcopy((digit_t*)&Montgomery_one, (public_pts[2]->Z)[0]);

    // Initialize constants
    fpcopy((digit_t*)&Montgomery_one, A24plus[0]);
    fp2add(A24plus, A24plus, A24plus);
    fp2copy(A24plus, A24minus);
    fp2neg(A24minus);

#if defined PARALLEL

    // Retrieve kernel point
    #pragma omp parallel num_threads(2)
    {
        int i = omp_get_thread_num();
         if (i == 0) LADDER3PT(XPB1, XQB1, XRB1, (digit_t*)PrivateKeyB, BOB, R1, A);
         if (i == 1) LADDER3PT(XPB2, XQB2, XRB2, &((digit_t*)PrivateKeyB)[Index_Bob1], BOB1, public_pts[3], A);
    }

#else

    // Retrieve kernel point
    LADDER3PT(XPB1, XQB1, XRB1, (digit_t*)PrivateKeyB, BOB, R1, A);    
    LADDER3PT(XPB2, XQB2, XRB2, &((digit_t*)PrivateKeyB)[Index_Bob1], BOB1, public_pts[3], A);
   
#endif
    
    // Traverse tree for 3 isogenies===========
    index = 0; 
    fp2copy(R1->X, pts1[0]->X);
    fp2copy(R1->Z, pts1[0]->Z);
    pts_index1[0] = 0;
    npts = 1;
#if (KERNEL_POINTS1 == 1)
    f2elm_t coeff[3];
    for (row = 0; row < MAX_Bob1 -1 ; row++) {
        while (index < MAX_Bob1 - 1 - row) {
            m = strat_Bob1[ii];
            ii +=1;
            index += m;
            pts_index1[npts] = index;
            xTPLe(R1, R1, A24minus, A24plus, (int)m);
            fp2copy(R1->X, pts1[npts]->X);
            fp2copy(R1->Z, pts1[npts]->Z);
            npts +=1;
        }
        get_3_isog(R1, A24minus, A24plus, coeff);

    #if defined PARALLEL

        #pragma omp parallel for num_threads(cn)
        for (i = 0; i < (npts+3); i++) {
            if(i < npts - 1)
                eval_3_isog(pts1[i], coeff);
            else
                eval_3_isog(public_pts[i%4], coeff);
        }

    #else

        for (i = 0; i < npts-1; i++) {
            eval_3_isog(pts1[i], coeff);
        }     
        eval_3_isog(public_pts[0], coeff);
        eval_3_isog(public_pts[1], coeff);
        eval_3_isog(public_pts[2], coeff);
        eval_3_isog(public_pts[3], coeff);
        
    #endif        

        fp2copy(pts1[npts-2]->X, R1->X); 
        fp2copy(pts1[npts-2]->Z, R1->Z);
        index = pts_index1[npts-2];
        npts -= 1;
    }
   
    get_3_isog(R1, A24minus, A24plus, coeff);
    fp2sub(A24plus, A24minus, C24);  

    #if defined PARALLEL

    #pragma omp parallel for num_threads(3)
    for (i = 0; i < 4; i++) {
        eval_3_isog(public_pts[i], coeff);
    } 

    #else

    eval_3_isog(public_pts[0], coeff);
    eval_3_isog(public_pts[1], coeff);
    eval_3_isog(public_pts[2], coeff);
    eval_3_isog(public_pts[3], coeff);

    #endif    
#else
    //Traverse the tree for d1 isogeny
    point_proj_t KernelPoints1[KERNEL_POINTS1];
    fp2sub(A24plus, A24minus, C24); 
    for (row = 1; row < MAX_Bob1; row++) {
        while (index < MAX_Bob1 - row) {
            fp2copy(R1->X, pts1[npts]->X);
            fp2copy(R1->Z, pts1[npts]->Z);
            pts_index1[npts] = index;
            npts += 1;
            m = splits_Bob1[MAX_Bob1 - index - row];
            xMULe1(R1, R1, A24minus, A24plus, C24, (int)m);
            index += m;
        }
        get_d1_isog(R1, KernelPoints1, A24minus, A24plus, C24);

    #if defined PARALLEL

        #pragma omp parallel for num_threads(3)
        for (i = 0; i < (npts+4); i++) {
            if(i < npts)
                eval_d1_isog(KernelPoints1, pts1[i]);
            else
                eval_d1_isog(KernelPoints1, public_pts[i%4];
        }

    #else

        for (i = 0; i < npts; i++) {
            eval_d1_isog(KernelPoints1, pts1[i];
        }     
        eval_d1_isog(KernelPoints1,public_pts[0]);
        eval_d1_isog(KernelPoints1,public_pts[1]);
        eval_d1_isog(KernelPoints1,public_pts[2]);
        eval_d1_isog(KernelPoints1,public_pts[3]);
        
    #endif        

        fp2copy(pts1[npts-1]->X, R1->X); 
        fp2copy(pts1[npts-1]->Z, R1->Z);
        index = pts_index1[npts-1];
        npts -= 1;
    }
   
    get_d1_isog(R1, KernelPoints1, A24minus, A24plus, C24); 

    #if defined PARALLEL

    #pragma omp parallel for num_threads(cn)
    for (i = 0; i < 4; i++) {
        eval_d1_isog(KernelPoints1, public_pts[i]);
    } 

    #else

    eval_d1_isog(KernelPoints1, public_pts[0]);
    eval_d1_isog(KernelPoints1, public_pts[1]);
    eval_d1_isog(KernelPoints1, public_pts[2]);
    eval_d1_isog(KernelPoints1, public_pts[3]);
    #endif

#endif
    // Traverse tree for d2 isogeny//=================
    index = 0; 
    fp2copy(public_pts[3]->X, pts2[0]->X);
    fp2copy(public_pts[3]->Z, pts2[0]->Z);
    pts_index2[0] = 0;
    npts = 1;
    ii=0;
    for (row = 0; row < MAX_Bob2-1; row++) {
        while (index < MAX_Bob2 - 1 - row) {
            m = strat_Bob2[ii];
            ii +=1;
            index += m;
            pts_index2[npts] = index;
            xMULe2(public_pts[3], public_pts[3], A24plus, A24minus, C24, (int)m);
            fp2copy(public_pts[3]->X, pts2[npts]->X);
            fp2copy(public_pts[3]->Z, pts2[npts]->Z);
            npts += 1;
        }
        get_d2_isog(public_pts[3], KernelPoints2, A24plus, A24minus, C24);

    #if defined PARALLEL
 
        #pragma omp parallel for num_threads(cn)
        for (i = 0; i < (npts + 2); i++) {
            if(i < npts - 1)
                eval_d2_isog(KernelPoints2, pts2[i]);
            else
                eval_d2_isog(KernelPoints2, public_pts[i%3]);
        }
       
    #else        
        
        for (i = 0; i < npts - 1; i++) {
            eval_d2_isog(KernelPoints2, pts2[i]);
        }     
        eval_d2_isog(KernelPoints2, public_pts[0]);
        eval_d2_isog(KernelPoints2, public_pts[1]);
        eval_d2_isog(KernelPoints2, public_pts[2]);

    #endif

        fp2copy(pts2[npts-2]->X, public_pts[3]->X); 
        fp2copy(pts2[npts-2]->Z, public_pts[3]->Z);
        index = pts_index2[npts-2];
        npts -= 1;
    }

    get_d2_isog(public_pts[3], KernelPoints2, A24plus, A24minus, C24);

    #if defined PARALLEL

    #pragma omp parallel for num_threads(cn)
    for(i = 0; i < 3; i++){
        eval_d2_isog(KernelPoints2, public_pts[i]);
    }

    #else

    eval_d2_isog(KernelPoints2, public_pts[0]);
    eval_d2_isog(KernelPoints2, public_pts[1]);
    eval_d2_isog(KernelPoints2, public_pts[2]);

    #endif    

    inv_3_way(public_pts[0]->Z, public_pts[1]->Z, public_pts[2]->Z);
    fp2mul_mont(public_pts[0]->X, public_pts[0]->Z, public_pts[0]->X);
    fp2mul_mont(public_pts[1]->X, public_pts[1]->Z, public_pts[1]->X);
    fp2mul_mont(public_pts[2]->X, public_pts[2]->Z, public_pts[2]->X);

    // Format public key
    fp2_encode(public_pts[0]->X, PublicKeyB);
    fp2_encode(public_pts[1]->X, PublicKeyB + FP2_ENCODED_BYTES);    
    fp2_encode(public_pts[2]->X, PublicKeyB + 2*FP2_ENCODED_BYTES);

    return 0;
}

int EphemeralSecretAgreement_B(const unsigned char* PrivateKeyB, const unsigned char* PublicKeyA, unsigned char* SharedSecretB)
{ // Bob's ephemeral shared secret computation
  // It produces a shared secret key SharedSecretB using his secret key PrivateKeyB and Alice's public key PublicKeyA
  // Inputs: Bob's PrivateKeyB is an integer in the range [0, 2^Floor(Log(2,oB)) - 1]. 
  //         Alice's PublicKeyA consists of 3 elements in GF(p^2) encoded by removing leading 0 bytes.
  // Output: a shared secret SharedSecretB that consists of one element in GF(p^2) encoded by removing leading 0 bytes.  
    point_proj_t R1, R2,  pts1[MAX_INT_POINTS_BOB1], pts2[MAX_INT_POINTS_BOB2], KernelPoints2[KERNEL_POINTS2];
    f2elm_t PKB[3], jinv;
    f2elm_t A, A24plus = {0}, A24minus = {0}, C24={0};
    unsigned int i, row, m, index = 0, pts_index1[MAX_INT_POINTS_BOB1], pts_index2[MAX_INT_POINTS_BOB2], npts = 0, ii = 0;
    #if defined PARALLEL
        int tid, cn;
        cn = omp_get_max_threads();
    #endif
    // Initialize images of Alice's basis
    fp2_decode(PublicKeyA, PKB[0]);
    fp2_decode(PublicKeyA + FP2_ENCODED_BYTES, PKB[1]);
    fp2_decode(PublicKeyA + 2*FP2_ENCODED_BYTES, PKB[2]);

    // Initialize constants
    get_A(PKB[0], PKB[1], PKB[2], A); // TODO: Can return projective A?

    fpadd((digit_t*)&Montgomery_one, (digit_t*)&Montgomery_one, A24minus[0]);
    fp2add(A, A24minus, A24plus);
    fp2sub(A, A24minus, A24minus);
    fp2sub(A24plus, A24minus, C24);

#if defined PARALLEL

    // Retrieve kernel point
    #pragma omp parallel num_threads(2)
    {
        int i = omp_get_thread_num();
        if (i == 0){
            LADDER3PT(PKB[0], PKB[1], PKB[2], (digit_t*)PrivateKeyB, BOB, R1, A);
            xMULe2(R1, R1, A24plus, A24minus, C24, MAX_Bob2);
        }
        if (i == 1){
            LADDER3PT(PKB[0], PKB[1], PKB[2], &((digit_t*)PrivateKeyB)[Index_Bob1], BOB1, R2, A);
            #if (KERNEL_POINTS1 == 1)
                xTPLe(R2, R2, A24minus, A24plus,  MAX_Bob1);
            #else
                xMULe1(R2, R2, A24minus, A24plus,  MAX_Bob1);
            #endif
        }
    }

#else

    // Retrieve kernel point
    LADDER3PT(PKB[0], PKB[1], PKB[2], (digit_t*)PrivateKeyB, BOB, R1, A);
    xMULe2(R1, R1, A24plus, A24minus, C24, MAX_Bob2);
    LADDER3PT(PKB[0], PKB[1], PKB[2], &((digit_t*)PrivateKeyB)[Index_Bob1], BOB1, R2, A);
    #if (KERNEL_POINTS1 == 1)
        xTPLe(R2, R2, A24minus, A24plus,  MAX_Bob1);
    #else
        xMULe1(R2, R2, A24minus, A24plus,  MAX_Bob1);
    #endif

#endif
 
    // Traverse tree for 3-isogeny
    index = 0; 
    fp2copy(R1->X, pts1[0]->X);
    fp2copy(R1->Z, pts1[0]->Z);
    pts_index1[0] = 0;
    npts = 1;
#if (KERNEL_POINTS1 == 1)
    f2elm_t coeff[3];
    for (row = 0; row < MAX_Bob1 -1 ; row++) {
        while (index < MAX_Bob1 - 1 - row) {
            m = strat_Bob1[ii];
            ii +=1;
            index += m;
            pts_index1[npts] = index;
            xTPLe(R1, R1, A24minus, A24plus, (int)m);
            fp2copy(R1->X, pts1[npts]->X);
            fp2copy(R1->Z, pts1[npts]->Z);
            npts +=1;
        }
        get_3_isog(R1, A24minus, A24plus, coeff);

    #if defined PARALLEL

        #pragma omp parallel for num_threads(cn)
        for (i = 0; i < npts; i++) {
            if(i < npts - 1)
                eval_3_isog(pts1[i], coeff);
            else
                eval_3_isog(R2, coeff);
        }

    #else

        for (i = 0; i < npts-1; i++) {
            eval_3_isog(pts1[i], coeff);
        }
        eval_3_isog(R2, coeff);

    #endif

        fp2copy(pts1[npts-2]->X, R1->X); 
        fp2copy(pts1[npts-2]->Z, R1->Z);
        index = pts_index1[npts-2];
        npts -= 1;
    }
    
    get_3_isog(R1, A24minus, A24plus, coeff);
    fp2sub(A24plus, A24minus, C24);
    eval_3_isog(R2, coeff);
//end 3-isogeny
#else
    // Traverse tree for d1 isogeny=======================
    point_proj_t KernelPoints2[KERNEL_POINTS1];
    index = 0; npts = 0;
    for (row = 1; row < MAX_Bob1; row++) {
        while (index < MAX_Bob1 - row) {
            fp2copy(R1->X, pts1[npts]->X);
            fp2copy(R1->Z, pts1[npts]->Z);
            pts_index1[npts] = index;
            npts += 1;
            m = splits_Bob1[MAX_Bob1 - index - row];
            xMULe1(R1, R1, A24minus, A24plus, (int)m);
            index += m;
        }
        get_d1_isog(R1, KernelPoints1,  A24minus, A24plus, C24);

    #if defined PARALLEL

        #pragma omp parallel for num_threads(3)
        for (i = 0; i < (npts+1); i++) {
            if(i < npts)
                eval_d1_isog(KernelPoints1, pts3[i]);
            else
                eval_d1_isog(KernelPoints1, R2);
        }

    #else

        for (i = 0; i < npts; i++) {
            eval_d1_isog(KernelPoints1, pts3[i]);
        }
        eval_d1_isog(KernelPoints1, R2);

    #endif

        fp2copy(pts1[npts-1]->X, R1->X); 
        fp2copy(pts1[npts-1]->Z, R1->Z);
        index = pts_index1[npts-1];
        npts -= 1;
    }
    
    get_d1_isog(R3, KernelPoints1, A24minus, A24plus, C24);
    eval_d1_isog(KernelPoints1, R2);
#endif
    
    // Traverse tree for d2 isogeny=======================
    index = 0;
    fp2copy(R2->X, pts2[0]->X);
    fp2copy(R2->Z, pts2[0]->Z);
    pts_index2[0] = 0;
    npts = 1;
    ii=0;
    for (row = 0; row < MAX_Bob2-1; row++) {
        while (index < MAX_Bob2 - 1 - row) {
            m = strat_Bob2[ii];
            ii +=1;
            index += m;
            pts_index2[npts] = index;
            xMULe2(R2, R2, A24plus, A24minus, C24, (int)m);
            fp2copy(R2->X, pts2[npts]->X);
            fp2copy(R2->Z, pts2[npts]->Z);
            npts += 1;
        }
        get_d2_isog(R2, KernelPoints2, A24plus, A24minus, C24);

    #if defined PARALLEL

        #pragma omp parallel for num_threads(cn)
        for (i = 0; i < npts-1; i++) {
            eval_d2_isog(KernelPoints2, pts2[i]);
        }

    #else
        
        for (i = 0; i < npts-1; i++) {
            eval_d2_isog(KernelPoints2, pts2[i]);
        }     

    #endif
        
        fp2copy(pts2[npts-2]->X, R2->X); 
        fp2copy(pts2[npts-2]->Z, R2->Z);
        index = pts_index2[npts-2];
        npts -= 1;
    }
    
    get_d2_isog(R2, KernelPoints2, A24plus, A24minus, C24);
    fp2add(A24plus, A24minus, A24plus);                 
    fp2add(A24plus, A24plus, A24plus);
    j_inv(A24plus, C24, jinv);
    
    fp2_encode(jinv, SharedSecretB);    // Format shared secret

    return 0;
}
#endif
