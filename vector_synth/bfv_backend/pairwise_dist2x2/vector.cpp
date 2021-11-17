
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "11100000", info);
    add_bitstring(bits, "00100000", info);
    add_bitstring(bits, "11000000", info);
    add_bitstring(bits, "00110000", info);
    add_bitstring(bits, "00010000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(20);
    ts[0] = encrypt_input("110110111111110110111111", info);
    ts[2] = encrypt_input("110110111111110110111111", info);
    ts[4] = encrypt_input("111110110111111110110111", info);
    ts[6] = encrypt_input("111110110111111110110111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[4];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -4, gk, ss[0]); // __s0 = __v0 >> 4
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -4, gk, ss[1]); // __s1 = __v1 >> 4
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -4, gk, ss[2]); // __s2 = __v2 >> 4
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -4, gk, ss[3]); // __s3 = __v3 >> 4
    
    // __t8 = blend(__s1@11000000, __v1@00100000, __v0@00010000)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(ss[1], bits["11000000"], t8_1);
    info.eval->multiply_plain(vs[1], bits["00100000"], t8_2);
    info.eval->multiply_plain(vs[0], bits["00010000"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3}, ts[8]);
    
    
    // __t9 = blend(__s3@11000000, __v3@00100000, __v2@00010000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(ss[3], bits["11000000"], t9_1);
    info.eval->multiply_plain(vs[3], bits["00100000"], t9_2);
    info.eval->multiply_plain(vs[2], bits["00010000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[4]); // __v4 = __t8 - __t9
    
    // __t10 = blend(__v1@11000000, __s1@00100000, __s0@00010000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[1], bits["11000000"], t10_1);
    info.eval->multiply_plain(ss[1], bits["00100000"], t10_2);
    info.eval->multiply_plain(ss[0], bits["00010000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__v3@11000000, __s3@00100000, __s2@00010000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[3], bits["11000000"], t11_1);
    info.eval->multiply_plain(ss[3], bits["00100000"], t11_2);
    info.eval->multiply_plain(ss[2], bits["00010000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->sub(ts[10], ts[11], vs[5]); // __v5 = __t10 - __t11
    
    // __t12 = blend(__v5@11000000, __v4@00110000)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[5], bits["11000000"], t12_1);
    info.eval->multiply_plain(vs[4], bits["00110000"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__v4@11000000, __v5@00110000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[4], bits["11000000"], t13_1);
    info.eval->multiply_plain(vs[5], bits["00110000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[6]); // __v6 = __t12 * __t13
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t14 = blend(__v0@11100000, __v1@00010000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[0], bits["11100000"], t14_1);
    info.eval->multiply_plain(vs[1], bits["00010000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__v2@11100000, __v3@00010000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[2], bits["11100000"], t15_1);
    info.eval->multiply_plain(vs[3], bits["00010000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->sub(ts[14], ts[15], vs[7]); // __v7 = __t14 - __t15
    
    // __t16 = blend(__s0@11100000, __s1@00010000)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(ss[0], bits["11100000"], t16_1);
    info.eval->multiply_plain(ss[1], bits["00010000"], t16_2);
    info.eval->add(t16_1, t16_2, ts[16]);
    
    
    // __t17 = blend(__s2@11100000, __s3@00010000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(ss[2], bits["11100000"], t17_1);
    info.eval->multiply_plain(ss[3], bits["00010000"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    info.eval->sub(ts[16], ts[17], vs[8]); // __v8 = __t16 - __t17
    info.eval->multiply(vs[7], vs[8], vs[9]); // __v9 = __v7 * __v8
    info.eval->relinearize_inplace(vs[9], rk);
    
    // __t18 = blend(__v9@11100000, __v6@00010000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(vs[9], bits["11100000"], t18_1);
    info.eval->multiply_plain(vs[6], bits["00010000"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    
    // __t19 = blend(__v6@11100000, __v9@00010000)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(vs[6], bits["11100000"], t19_1);
    info.eval->multiply_plain(vs[9], bits["00010000"], t19_2);
    info.eval->add(t19_1, t19_2, ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[10]); // __v10 = __t18 + __t19
    return vs[10];
}
    