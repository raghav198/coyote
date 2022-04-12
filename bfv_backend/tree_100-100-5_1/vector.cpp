
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0100000", info);
    add_bitstring(bits, "0001000", info);
    add_bitstring(bits, "0000100", info);
    add_bitstring(bits, "0100010", info);
    add_bitstring(bits, "1000000", info);
    add_bitstring(bits, "0000001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(16);
    ts[0] = encrypt_input("110001111110111", info);
    ts[1] = encrypt_input("1100111110111", info);
    ts[2] = encrypt_input("01110001100", info);
    ts[3] = encrypt_input("011001011110", info);
    ts[5] = encrypt_input("10100111000", info);
    ts[6] = encrypt_input("111000000", info);
    ts[8] = encrypt_input("0111000110", info);
    ts[11] = encrypt_input("000000111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[4];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    
    // __t4 = blend(__v0@0000100, __t2@0100010)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["0000100"], t4_1);
    info.eval->add(t4_1, ts[2], ts[4]);
    
    info.eval->multiply(ts[4], ts[3], vs[1]); // __v1 = __t4 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t7 = blend(__v0@0001000, __t6@1000000)
    ctxt t7_1;
    info.eval->multiply_plain(vs[0], bits["0001000"], t7_1);
    info.eval->add(t7_1, ts[6], ts[7]);
    
    info.eval->multiply(ts[5], ts[7], vs[2]); // __v2 = __t5 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -1, gk, ss[0]); // __s0 = __v2 >> 1
    
    // __t9 = blend(__v2@1000000, __v1@0100010)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[2], bits["1000000"], t9_1);
    info.eval->multiply_plain(vs[1], bits["0100010"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    
    // __t10 = blend(__v0@1000000, __t8@0100010)
    ctxt t10_1;
    info.eval->multiply_plain(vs[0], bits["1000000"], t10_1);
    info.eval->add(t10_1, ts[8], ts[10]);
    
    info.eval->add(ts[9], ts[10], vs[3]); // __v3 = __t9 + __t10
    info.eval->rotate_rows(vs[3], -1, gk, ss[1]); // __s1 = __v3 >> 1
    
    // __t12 = blend(__s1@0100000, __v1@0000100, __t11@0000001)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(ss[1], bits["0100000"], t12_1);
    info.eval->multiply_plain(vs[1], bits["0000100"], t12_2);
    info.eval->add_many({t12_1, t12_2, ts[11]}, ts[12]);
    
    
    // __t13 = blend(__v3@0100000, __s0@0000100, __s1@0000001)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(vs[3], bits["0100000"], t13_1);
    info.eval->multiply_plain(ss[0], bits["0000100"], t13_2);
    info.eval->multiply_plain(ss[1], bits["0000001"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[4]); // __v4 = __t12 + __t13
    info.eval->rotate_rows(vs[4], -4, gk, ss[2]); // __s2 = __v4 >> 4
    
    // __t14 = blend(__s2@0100000, __v4@0000001)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(ss[2], bits["0100000"], t14_1);
    info.eval->multiply_plain(vs[4], bits["0000001"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__v4@0100000, __v0@0000001)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[4], bits["0100000"], t15_1);
    info.eval->multiply_plain(vs[0], bits["0000001"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[5]); // __v5 = __t14 * __t15
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -5, gk, ss[3]); // __s3 = __v5 >> 5
    info.eval->multiply(ss[3], vs[5], vs[6]); // __v6 = __s3 * __v5
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    