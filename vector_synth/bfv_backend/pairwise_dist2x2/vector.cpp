
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "11000100", info);
    add_bitstring(bits, "00001000", info);
    add_bitstring(bits, "10000000", info);
    add_bitstring(bits, "00001100", info);
    add_bitstring(bits, "01001100", info);
    add_bitstring(bits, "11000000", info);
    add_bitstring(bits, "00000100", info);
    add_bitstring(bits, "10001000", info);
    add_bitstring(bits, "01000100", info);
    add_bitstring(bits, "01000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(21);
    ts[0] = encrypt_input("111111111111110110110110", info);
    ts[2] = encrypt_input("111111111111110110110110", info);
    ts[4] = encrypt_input("000011011100", info);
    ts[6] = encrypt_input("000011011100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[4];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -6, gk, ss[0]); // __s0 = __v0 >> 6
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -6, gk, ss[1]); // __s1 = __v1 >> 6
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -4, gk, ss[2]); // __s2 = __v2 >> 4
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -4, gk, ss[3]); // __s3 = __v3 >> 4
    
    // __t8 = blend(__s1@10000000, __v1@01000100, __s0@00001000)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(ss[1], bits["10000000"], t8_1);
    info.eval->multiply_plain(vs[1], bits["01000100"], t8_2);
    info.eval->multiply_plain(ss[0], bits["00001000"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3}, ts[8]);
    
    
    // __t9 = blend(__s3@11000000, __v2@00001000, __v3@00000100)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(ss[3], bits["11000000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["00001000"], t9_2);
    info.eval->multiply_plain(vs[3], bits["00000100"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[4]); // __v4 = __t8 - __t9
    
    // __t10 = blend(__s0@11000100, __s1@00001000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(ss[0], bits["11000100"], t10_1);
    info.eval->multiply_plain(ss[1], bits["00001000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__s2@11000000, __v3@00001000, __v2@00000100)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(ss[2], bits["11000000"], t11_1);
    info.eval->multiply_plain(vs[3], bits["00001000"], t11_2);
    info.eval->multiply_plain(vs[2], bits["00000100"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->sub(ts[10], ts[11], vs[5]); // __v5 = __t10 - __t11
    
    // __t12 = blend(__v0@10000000, __s1@01000100, __v1@00001000)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(vs[0], bits["10000000"], t12_1);
    info.eval->multiply_plain(ss[1], bits["01000100"], t12_2);
    info.eval->multiply_plain(vs[1], bits["00001000"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    
    // __t13 = blend(__s2@10000000, __s3@01000000, __v3@00001100)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(ss[2], bits["10000000"], t13_1);
    info.eval->multiply_plain(ss[3], bits["01000000"], t13_2);
    info.eval->multiply_plain(vs[3], bits["00001100"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    info.eval->sub(ts[12], ts[13], vs[6]); // __v6 = __t12 - __t13
    
    // __t14 = blend(__v6@10001000, __v4@01000100)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[6], bits["10001000"], t14_1);
    info.eval->multiply_plain(vs[4], bits["01000100"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__v5@10001000, __v6@01000100)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[5], bits["10001000"], t15_1);
    info.eval->multiply_plain(vs[6], bits["01000100"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[7]); // __v7 = __t14 * __t15
    info.eval->relinearize_inplace(vs[7], rk);
    
    // __t16 = blend(__v1@10000000, __v0@01001100)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(vs[1], bits["10000000"], t16_1);
    info.eval->multiply_plain(vs[0], bits["01001100"], t16_2);
    info.eval->add(t16_1, t16_2, ts[16]);
    
    
    // __t17 = blend(__s3@10000000, __s2@01000000, __v2@00001100)
    ctxt t17_1, t17_2, t17_3;
    info.eval->multiply_plain(ss[3], bits["10000000"], t17_1);
    info.eval->multiply_plain(ss[2], bits["01000000"], t17_2);
    info.eval->multiply_plain(vs[2], bits["00001100"], t17_3);
    info.eval->add_many({t17_1, t17_2, t17_3}, ts[17]);
    
    info.eval->sub(ts[16], ts[17], vs[8]); // __v8 = __t16 - __t17
    
    // __t18 = blend(__v4@10001000, __v5@01000100)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(vs[4], bits["10001000"], t18_1);
    info.eval->multiply_plain(vs[5], bits["01000100"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    info.eval->multiply(vs[8], ts[18], vs[9]); // __v9 = __v8 * __t18
    info.eval->relinearize_inplace(vs[9], rk);
    
    // __t19 = blend(__v7@10000000, __v9@01001100)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(vs[7], bits["10000000"], t19_1);
    info.eval->multiply_plain(vs[9], bits["01001100"], t19_2);
    info.eval->add(t19_1, t19_2, ts[19]);
    
    
    // __t20 = blend(__v9@10000000, __v7@01001100)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[9], bits["10000000"], t20_1);
    info.eval->multiply_plain(vs[7], bits["01001100"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    info.eval->add(ts[19], ts[20], vs[10]); // __v10 = __t19 + __t20
    return vs[10];
}
    