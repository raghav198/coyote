
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000000000001000", info);
    add_bitstring(bits, "01000010000001000000000", info);
    add_bitstring(bits, "10000010000000000000000", info);
    add_bitstring(bits, "00000011000001000000000", info);
    add_bitstring(bits, "11000011000001001000000", info);
    add_bitstring(bits, "00000000000000000000001", info);
    add_bitstring(bits, "10000001000000001000000", info);
    add_bitstring(bits, "01000000000001000000000", info);
    add_bitstring(bits, "00000001000000001000000", info);
    add_bitstring(bits, "00000000000000100000000", info);
    add_bitstring(bits, "11000000000000001000000", info);
    add_bitstring(bits, "00000000000010000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(13);
    ts[0] = encrypt_input("11010111100111110111110000110110111110111111111111010111110111100011110", info);
    ts[1] = encrypt_input("11010110100111100111100000111110111100111101111111011111110110110011011", info);
    ts[2] = encrypt_input("000000110101111001111100011110111100001101100011111", info);
    ts[3] = encrypt_input("000000110111101101111100011011110100001111100011111", info);
    ts[6] = encrypt_input("0011011011011000110110011111000000011111110111111111111", info);
    ts[7] = encrypt_input("0011110011110000111110011111000000011111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[6];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -21, gk, ss[0]); // __s0 = __v0 >> 21
    info.eval->rotate_rows(vs[0], -19, gk, ss[1]); // __s1 = __v0 >> 19
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -21, gk, ss[2]); // __s2 = __v1 >> 21
    
    // __t4 = blend(__v1@00000000000000100000000, __v0@00000000000000000000001)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[1], bits["00000000000000100000000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["00000000000000000000001"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__v0@00000000000000100000000, __v1@00000000000000000000001)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(vs[0], bits["00000000000000100000000"], t5_1);
    info.eval->multiply_plain(vs[1], bits["00000000000000000000001"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[2]); // __v2 = __t4 + __t5
    info.eval->rotate_rows(vs[2], -21, gk, ss[3]); // __s3 = __v2 >> 21
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -21, gk, ss[4]); // __s4 = __v3 >> 21
    info.eval->rotate_rows(vs[3], -19, gk, ss[5]); // __s5 = __v3 >> 19
    
    // __t8 = blend(__v0@00000000000000000001000, __v2@00000000000000000000001)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[0], bits["00000000000000000001000"], t8_1);
    info.eval->multiply_plain(vs[2], bits["00000000000000000000001"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    info.eval->add(ts[8], vs[3], vs[4]); // __v4 = __t8 + __v3
    
    // __t9 = blend(__v0@11000000000000001000000, __v1@00000011000001000000000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[0], bits["11000000000000001000000"], t9_1);
    info.eval->multiply_plain(vs[1], bits["00000011000001000000000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    
    // __t10 = blend(__s4@10000010000000000000000, __s0@01000000000001000000000, __s2@00000001000000001000000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(ss[4], bits["10000010000000000000000"], t10_1);
    info.eval->multiply_plain(ss[0], bits["01000000000001000000000"], t10_2);
    info.eval->multiply_plain(ss[2], bits["00000001000000001000000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    info.eval->add(ts[9], ts[10], vs[5]); // __v5 = __t9 + __t10
    
    // __t11 = blend(__v5@11000011000001001000000, __s3@00000000000010000000000, __v4@00000000000000000001000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[5], bits["11000011000001001000000"], t11_1);
    info.eval->multiply_plain(ss[3], bits["00000000000010000000000"], t11_2);
    info.eval->multiply_plain(vs[4], bits["00000000000000000001000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    
    // __t12 = blend(__s5@10000001000000001000000, __s1@01000010000001000000000, __v0@00000000000010000000000, __s4@00000000000000000001000)
    ctxt t12_1, t12_2, t12_3, t12_4;
    info.eval->multiply_plain(ss[5], bits["10000001000000001000000"], t12_1);
    info.eval->multiply_plain(ss[1], bits["01000010000001000000000"], t12_2);
    info.eval->multiply_plain(vs[0], bits["00000000000010000000000"], t12_3);
    info.eval->multiply_plain(ss[4], bits["00000000000000000001000"], t12_4);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4}, ts[12]);
    
    info.eval->add(ts[11], ts[12], vs[6]); // __v6 = __t11 + __t12
    return vs[6];
}
    