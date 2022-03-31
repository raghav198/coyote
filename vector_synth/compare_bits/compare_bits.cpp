#include "../bfv_backend/scalar.hpp"
#include <vector>
#include <stdio.h>
#include <stdlib.h>

ctxt less_than_bits(std::vector<ctxt> ctext1, std::vector<ctxt> ctext2, const uint64_t *p, RuntimeContext &info)
{
    ctxt LT;
    ctxt LocalPRODUCT;
    ctxt SUM;
    int l = ctext1.size();
    std::vector<ctxt> sum_parts(l);
    ctxt negated1;
    ctxt negated2;
    ctxt temp;
    
    seal::RelinKeys rk = info.keys->rk;

    for(int i = l - 1; i >= 0; i--){
        info.eval->negate(ctext1[i], temp);
        LT = temp * ctext2[i];
        std::vector<ctxt> mult_parts(i);
        for(int j = i - 1; j >= 0; j--){
            info.eval->negate(ctext1[j], negated1);
            info.eval->negate(ctext2[j], negated2);
            mult_parts[j] = ((ctext1[j] * ctext2[j]) + (negated1 * negated2));
        }
        info.eval->multiply_many(mult_parts, LocalPRODUCT, rk);
        
        sum_parts[i] = LT * LocalPRODUCT;
    }
    info.eval->add_many(sum_parts, SUM);

    return (SUM ^ (*p-1)) % *p;
}

int main(){

    seal::EncryptionParameters params(seal::scheme_type::bfv);
    size_t poly_modulus_degree = 8192;
    params.set_poly_modulus_degree(poly_modulus_degree);
    params.set_coeff_modulus(seal::CoeffModulus::BFVDefault(poly_modulus_degree));
    params.set_plain_modulus(seal::PlainModulus::Batching(poly_modulus_degree, 20));
    const uint64_t *p = params.plain_modulus().data();

    RuntimeContext info(params);

    std::vector<int64_t> vector1 = {1,0,0,0,0};
    std::vector<int64_t> vector2 = {0,1,1,1,1};
    ctxt ctext1;
    ctxt ctext2;

    ptxt dest1;
    info.batcher->encode(vector1, dest);

    ptxt dest2;
    info.batcher->encode(vector2, dest);

    info.enc->encrypt(dest1, ctext1);
    info.enc->encrypt(dest2, ctext2);
    ctxt enc_output = less_than_bits(ctext1, ctext2, *p, *info);
    int dec_output;
    info.dec->decrypt(enc_output, dec_output);
    printf("%d\n", dec_output);
    
    return 1;
}
