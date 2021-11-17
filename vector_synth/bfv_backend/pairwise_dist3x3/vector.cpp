
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0001001000000000000", info);
    add_bitstring(bits, "0101001000000000000", info);
    add_bitstring(bits, "0000000010000000000", info);
    add_bitstring(bits, "0000000000000000001", info);
    add_bitstring(bits, "0100000000101010000", info);
    add_bitstring(bits, "0000001010000000000", info);
    add_bitstring(bits, "0100000000000010000", info);
    add_bitstring(bits, "0100000010000010101", info);
    add_bitstring(bits, "0000000010000010001", info);
    add_bitstring(bits, "0001001000101000100", info);
    add_bitstring(bits, "0000000000101010100", info);
    add_bitstring(bits, "0100100000000000000", info);
    add_bitstring(bits, "0000000000000010000", info);
    add_bitstring(bits, "0000001010000000101", info);
    add_bitstring(bits, "0000000000101000101", info);
    add_bitstring(bits, "0000000010000000001", info);
    add_bitstring(bits, "0000000000000000101", info);
    add_bitstring(bits, "0000101000000000101", info);
    add_bitstring(bits, "0000000010000010000", info);
    add_bitstring(bits, "0100100000000000001", info);
    add_bitstring(bits, "0100000010000010000", info);
    add_bitstring(bits, "0000000000101000100", info);
    add_bitstring(bits, "0100001010000010000", info);
    add_bitstring(bits, "0000000000101000000", info);
    add_bitstring(bits, "0000101000000000000", info);
    add_bitstring(bits, "0101001000101000100", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(22);
    ts[0] = encrypt_input("1111111111110111111110110111111110110111111111111110110", info);
    ts[2] = encrypt_input("1111110111111111111110110111111110110111111111111110110", info);
    ts[4] = encrypt_input("1111111111110111111111111110110111111110110111111110110", info);
    ts[6] = encrypt_input("1111110111111111111111111110110111111110110111111110110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[12];
    ctxt ss[5];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[1]); // __s1 = __v1 >> 1
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -1, gk, ss[2]); // __s2 = __v2 >> 1
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -1, gk, ss[3]); // __s3 = __v3 >> 1
    
    // __t8 = blend(__v0@0100000010000010101, __v1@0000101000000000000, __s0@0000000000101000000)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(vs[0], bits["0100000010000010101"], t8_1);
    info.eval->multiply_plain(vs[1], bits["0000101000000000000"], t8_2);
    info.eval->multiply_plain(ss[0], bits["0000000000101000000"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3}, ts[8]);
    
    
    // __t9 = blend(__v2@0100000010000010101, __v3@0000101000000000000, __s2@0000000000101000000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(vs[2], bits["0100000010000010101"], t9_1);
    info.eval->multiply_plain(vs[3], bits["0000101000000000000"], t9_2);
    info.eval->multiply_plain(ss[2], bits["0000000000101000000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[4]); // __v4 = __t8 - __t9
    
    // __t10 = blend(__s1@0100100000000000001, __v0@0001001000000000000, __s0@0000000010000010000, __v1@0000000000101000100)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(ss[1], bits["0100100000000000001"], t10_1);
    info.eval->multiply_plain(vs[0], bits["0001001000000000000"], t10_2);
    info.eval->multiply_plain(ss[0], bits["0000000010000010000"], t10_3);
    info.eval->multiply_plain(vs[1], bits["0000000000101000100"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4}, ts[10]);
    
    
    // __t11 = blend(__s3@0100100000000000001, __v2@0001001000000000000, __s2@0000000010000010000, __v3@0000000000101000100)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(ss[3], bits["0100100000000000001"], t11_1);
    info.eval->multiply_plain(vs[2], bits["0001001000000000000"], t11_2);
    info.eval->multiply_plain(ss[2], bits["0000000010000010000"], t11_3);
    info.eval->multiply_plain(vs[3], bits["0000000000101000100"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->sub(ts[10], ts[11], vs[5]); // __v5 = __t10 - __t11
    
    // __t12 = blend(__s0@0101001000000000000, __v1@0000000010000000001, __s1@0000000000101010100)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(ss[0], bits["0101001000000000000"], t12_1);
    info.eval->multiply_plain(vs[1], bits["0000000010000000001"], t12_2);
    info.eval->multiply_plain(ss[1], bits["0000000000101010100"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    
    // __t13 = blend(__s2@0101001000000000000, __v3@0000000010000000001, __s3@0000000000101010100)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(ss[2], bits["0101001000000000000"], t13_1);
    info.eval->multiply_plain(vs[3], bits["0000000010000000001"], t13_2);
    info.eval->multiply_plain(ss[3], bits["0000000000101010100"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    info.eval->sub(ts[12], ts[13], vs[6]); // __v6 = __t12 - __t13
    
    // __t14 = blend(__v6@0101001000101000100, __v5@0000000010000010001)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[6], bits["0101001000101000100"], t14_1);
    info.eval->multiply_plain(vs[5], bits["0000000010000010001"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__v4@0100000010000010000, __v5@0001001000101000100, __v6@0000000000000000001)
    ctxt t15_1, t15_2, t15_3;
    info.eval->multiply_plain(vs[4], bits["0100000010000010000"], t15_1);
    info.eval->multiply_plain(vs[5], bits["0001001000101000100"], t15_2);
    info.eval->multiply_plain(vs[6], bits["0000000000000000001"], t15_3);
    info.eval->add_many({t15_1, t15_2, t15_3}, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[7]); // __v7 = __t14 * __t15
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -1, gk, ss[4]); // __s4 = __v7 >> 1
    
    // __t16 = blend(__v1@0100000000000010000, __s1@0000001010000000000, __v0@0000000000101000000, __s0@0000000000000000101)
    ctxt t16_1, t16_2, t16_3, t16_4;
    info.eval->multiply_plain(vs[1], bits["0100000000000010000"], t16_1);
    info.eval->multiply_plain(ss[1], bits["0000001010000000000"], t16_2);
    info.eval->multiply_plain(vs[0], bits["0000000000101000000"], t16_3);
    info.eval->multiply_plain(ss[0], bits["0000000000000000101"], t16_4);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4}, ts[16]);
    
    
    // __t17 = blend(__v3@0100000000000010000, __s3@0000001010000000000, __v2@0000000000101000000, __s2@0000000000000000101)
    ctxt t17_1, t17_2, t17_3, t17_4;
    info.eval->multiply_plain(vs[3], bits["0100000000000010000"], t17_1);
    info.eval->multiply_plain(ss[3], bits["0000001010000000000"], t17_2);
    info.eval->multiply_plain(vs[2], bits["0000000000101000000"], t17_3);
    info.eval->multiply_plain(ss[2], bits["0000000000000000101"], t17_4);
    info.eval->add_many({t17_1, t17_2, t17_3, t17_4}, ts[17]);
    
    info.eval->sub(ts[16], ts[17], vs[8]); // __v8 = __t16 - __t17
    
    // __t18 = blend(__v5@0100100000000000000, __v8@0000001010000000101, __v4@0000000000101000000, __v6@0000000000000010000)
    ctxt t18_1, t18_2, t18_3, t18_4;
    info.eval->multiply_plain(vs[5], bits["0100100000000000000"], t18_1);
    info.eval->multiply_plain(vs[8], bits["0000001010000000101"], t18_2);
    info.eval->multiply_plain(vs[4], bits["0000000000101000000"], t18_3);
    info.eval->multiply_plain(vs[6], bits["0000000000000010000"], t18_4);
    info.eval->add_many({t18_1, t18_2, t18_3, t18_4}, ts[18]);
    
    
    // __t19 = blend(__v8@0100000000101010000, __v4@0000101000000000101, __v6@0000000010000000000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(vs[8], bits["0100000000101010000"], t19_1);
    info.eval->multiply_plain(vs[4], bits["0000101000000000101"], t19_2);
    info.eval->multiply_plain(vs[6], bits["0000000010000000000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3}, ts[19]);
    
    info.eval->multiply(ts[18], ts[19], vs[9]); // __v9 = __t18 * __t19
    info.eval->relinearize_inplace(vs[9], rk);
    
    // __t20 = blend(__v7@0100001010000010000, __v9@0000000000101000101)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[7], bits["0100001010000010000"], t20_1);
    info.eval->multiply_plain(vs[9], bits["0000000000101000101"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    
    // __t21 = blend(__v9@0100001010000010000, __v7@0000000000101000101)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(vs[9], bits["0100001010000010000"], t21_1);
    info.eval->multiply_plain(vs[7], bits["0000000000101000101"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[10]); // __v10 = __t20 + __t21
    info.eval->add(ss[4], vs[9], vs[11]); // __v11 = __s4 + __v9
    return vs[11];
}
    