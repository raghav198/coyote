
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0001", info);
    add_bitstring(bits, "0110", info);
    add_bitstring(bits, "0011", info);
    add_bitstring(bits, "0010", info);
    add_bitstring(bits, "1000", info);
    add_bitstring(bits, "1001", info);
    add_bitstring(bits, "1100", info);
    add_bitstring(bits, "0100", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(19);
    ts[0] = encrypt_input("01111100", info);
    ts[2] = encrypt_input("11011100", info);
    ts[4] = encrypt_input("01110110", info);
    ts[6] = encrypt_input("01110110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[10];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -2, gk, ss[1]); // __s1 = __v0 >> 2
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -3, gk, ss[2]); // __s2 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -1, gk, ss[3]); // __s3 = __v1 >> 1
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -1, gk, ss[4]); // __s4 = __v2 >> 1
    info.eval->rotate_rows(vs[2], -3, gk, ss[5]); // __s5 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -2, gk, ss[6]); // __s6 = __v2 >> 2
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -1, gk, ss[7]); // __s7 = __v3 >> 1
    info.eval->rotate_rows(vs[3], -3, gk, ss[8]); // __s8 = __v3 >> 3
    info.eval->rotate_rows(vs[3], -2, gk, ss[9]); // __s9 = __v3 >> 2
    
    // __t8 = blend(__s1@1000, __v1@0100, __s3@0010, __s0@0001)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(ss[1], bits["1000"], t8_1);
    info.eval->multiply_plain(vs[1], bits["0100"], t8_2);
    info.eval->multiply_plain(ss[3], bits["0010"], t8_3);
    info.eval->multiply_plain(ss[0], bits["0001"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__s5@1000, __s9@0100, __s7@0010, __v2@0001)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[5], bits["1000"], t9_1);
    info.eval->multiply_plain(ss[9], bits["0100"], t9_2);
    info.eval->multiply_plain(ss[7], bits["0010"], t9_3);
    info.eval->multiply_plain(vs[2], bits["0001"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[4]); // __v4 = __t8 - __t9
    
    // __t10 = blend(__v1@1100, __s3@0010, __s2@0001)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[1], bits["1100"], t10_1);
    info.eval->multiply_plain(ss[3], bits["0010"], t10_2);
    info.eval->multiply_plain(ss[2], bits["0001"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__s8@1000, __s9@0100, __s7@0010, __v3@0001)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(ss[8], bits["1000"], t11_1);
    info.eval->multiply_plain(ss[9], bits["0100"], t11_2);
    info.eval->multiply_plain(ss[7], bits["0010"], t11_3);
    info.eval->multiply_plain(vs[3], bits["0001"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->sub(ts[10], ts[11], vs[5]); // __v5 = __t10 - __t11
    
    // __t12 = blend(__v1@1000, __v0@0100, __s0@0010, __s2@0001)
    ctxt t12_1, t12_2, t12_3, t12_4;
    info.eval->multiply_plain(vs[1], bits["1000"], t12_1);
    info.eval->multiply_plain(vs[0], bits["0100"], t12_2);
    info.eval->multiply_plain(ss[0], bits["0010"], t12_3);
    info.eval->multiply_plain(ss[2], bits["0001"], t12_4);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4}, ts[12]);
    
    
    // __t13 = blend(__s8@1000, __s6@0100, __s4@0010, __v3@0001)
    ctxt t13_1, t13_2, t13_3, t13_4;
    info.eval->multiply_plain(ss[8], bits["1000"], t13_1);
    info.eval->multiply_plain(ss[6], bits["0100"], t13_2);
    info.eval->multiply_plain(ss[4], bits["0010"], t13_3);
    info.eval->multiply_plain(vs[3], bits["0001"], t13_4);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4}, ts[13]);
    
    info.eval->sub(ts[12], ts[13], vs[6]); // __v6 = __t12 - __t13
    
    // __t14 = blend(__v5@1100, __v4@0010, __v6@0001)
    ctxt t14_1, t14_2, t14_3;
    info.eval->multiply_plain(vs[5], bits["1100"], t14_1);
    info.eval->multiply_plain(vs[4], bits["0010"], t14_2);
    info.eval->multiply_plain(vs[6], bits["0001"], t14_3);
    info.eval->add_many({t14_1, t14_2, t14_3}, ts[14]);
    
    
    // __t15 = blend(__v6@1000, __v4@0100, __v5@0011)
    ctxt t15_1, t15_2, t15_3;
    info.eval->multiply_plain(vs[6], bits["1000"], t15_1);
    info.eval->multiply_plain(vs[4], bits["0100"], t15_2);
    info.eval->multiply_plain(vs[5], bits["0011"], t15_3);
    info.eval->add_many({t15_1, t15_2, t15_3}, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[7]); // __v7 = __t14 * __t15
    info.eval->relinearize_inplace(vs[7], rk);
    
    // __t16 = blend(__s1@1000, __v0@0100, __s0@0011)
    ctxt t16_1, t16_2, t16_3;
    info.eval->multiply_plain(ss[1], bits["1000"], t16_1);
    info.eval->multiply_plain(vs[0], bits["0100"], t16_2);
    info.eval->multiply_plain(ss[0], bits["0011"], t16_3);
    info.eval->add_many({t16_1, t16_2, t16_3}, ts[16]);
    
    
    // __t17 = blend(__s5@1000, __s6@0100, __s4@0010, __v2@0001)
    ctxt t17_1, t17_2, t17_3, t17_4;
    info.eval->multiply_plain(ss[5], bits["1000"], t17_1);
    info.eval->multiply_plain(ss[6], bits["0100"], t17_2);
    info.eval->multiply_plain(ss[4], bits["0010"], t17_3);
    info.eval->multiply_plain(vs[2], bits["0001"], t17_4);
    info.eval->add_many({t17_1, t17_2, t17_3, t17_4}, ts[17]);
    
    info.eval->sub(ts[16], ts[17], vs[8]); // __v8 = __t16 - __t17
    
    // __t18 = blend(__v4@1001, __v6@0110)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(vs[4], bits["1001"], t18_1);
    info.eval->multiply_plain(vs[6], bits["0110"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    info.eval->multiply(vs[8], ts[18], vs[9]); // __v9 = __v8 * __t18
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->add(vs[9], vs[7], vs[10]); // __v10 = __v9 + __v7
    return vs[10];
}
    