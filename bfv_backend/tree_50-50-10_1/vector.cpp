
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0001000", info);
    add_bitstring(bits, "0000001", info);
    add_bitstring(bits, "0100001", info);
    add_bitstring(bits, "0000010", info);
    add_bitstring(bits, "0100000", info);
    add_bitstring(bits, "0000100", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(29);
    ts[0] = encrypt_input("1110001110111", info);
    ts[1] = encrypt_input("10100011101011", info);
    ts[2] = encrypt_input("011101101111110", info);
    ts[3] = encrypt_input("01000111111111111", info);
    ts[5] = encrypt_input("011111111100111", info);
    ts[6] = encrypt_input("0011110111000", info);
    ts[9] = encrypt_input("000011100", info);
    ts[12] = encrypt_input("000111000", info);
    ts[13] = encrypt_input("000001110", info);
    ts[16] = encrypt_input("00001100", info);
    ts[19] = encrypt_input("000111000", info);
    ts[20] = encrypt_input("000111000", info);
    ts[21] = encrypt_input("000111000", info);
    ts[23] = encrypt_input("000110000", info);
    ts[24] = encrypt_input("000111000", info);
    ts[25] = encrypt_input("00000011", info);
    ts[28] = encrypt_input("000111000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[16];
    ctxt ss[5];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    
    // __t4 = blend(__v0@0000001, __t2@0101110)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["0000001"], t4_1);
    info.eval->add(t4_1, ts[2], ts[4]);
    
    info.eval->multiply(ts[4], ts[3], vs[1]); // __v1 = __t4 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t7 = blend(__v1@0000100, __t5@0111001)
    ctxt t7_1;
    info.eval->multiply_plain(vs[1], bits["0000100"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    
    // __t8 = blend(__v1@0100001, __t6@0011100)
    ctxt t8_1;
    info.eval->multiply_plain(vs[1], bits["0100001"], t8_1);
    info.eval->add(t8_1, ts[6], ts[8]);
    
    info.eval->multiply(ts[7], ts[8], vs[2]); // __v2 = __t7 * __t8
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -1, gk, ss[1]); // __s1 = __v2 >> 1
    
    // __t10 = blend(__v1@0001000, __v0@0000100)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[1], bits["0001000"], t10_1);
    info.eval->multiply_plain(vs[0], bits["0000100"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__v2@0001000, __t9@0000100)
    ctxt t11_1;
    info.eval->multiply_plain(vs[2], bits["0001000"], t11_1);
    info.eval->add(t11_1, ts[9], ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[3]); // __v3 = __t10 + __t11
    
    // __t14 = blend(__v3@0000100, __v1@0000010, __t12@0001000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[3], bits["0000100"], t14_1);
    info.eval->multiply_plain(vs[1], bits["0000010"], t14_2);
    info.eval->add_many({t14_1, t14_2, ts[12]}, ts[14]);
    
    
    // __t15 = blend(__v3@0001000, __v2@0000100, __t13@0000010)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[3], bits["0001000"], t15_1);
    info.eval->multiply_plain(vs[2], bits["0000100"], t15_2);
    info.eval->add_many({t15_1, t15_2, ts[13]}, ts[15]);
    
    info.eval->add(ts[14], ts[15], vs[4]); // __v4 = __t14 + __t15
    info.eval->rotate_rows(vs[4], -1, gk, ss[2]); // __s2 = __v4 >> 1
    info.eval->add(ss[2], vs[4], vs[5]); // __v5 = __s2 + __v4
    
    // __t17 = blend(__v2@0100000, __t16@0000100)
    ctxt t17_1;
    info.eval->multiply_plain(vs[2], bits["0100000"], t17_1);
    info.eval->add(t17_1, ts[16], ts[17]);
    
    
    // __t18 = blend(__s0@0100000, __v5@0000100)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(ss[0], bits["0100000"], t18_1);
    info.eval->multiply_plain(vs[5], bits["0000100"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    info.eval->multiply(ts[17], ts[18], vs[6]); // __v6 = __t17 * __t18
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -2, gk, ss[3]); // __s3 = __v6 >> 2
    info.eval->add(ts[19], ts[20], vs[7]); // __v7 = __t19 + __t20
    
    // __t22 = blend(__s2@0000001, __t21@0001000)
    ctxt t22_1;
    info.eval->multiply_plain(ss[2], bits["0000001"], t22_1);
    info.eval->add(t22_1, ts[21], ts[22]);
    
    info.eval->multiply(ss[3], ts[22], vs[8]); // __v8 = __s3 * __t22
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->add(ts[23], vs[7], vs[9]); // __v9 = __t23 + __v7
    info.eval->add(ts[24], vs[8], vs[10]); // __v10 = __t24 + __v8
    info.eval->add(vs[9], vs[10], vs[11]); // __v11 = __v9 + __v10
    
    // __t26 = blend(__v11@0001000, __v8@0000001)
    ctxt t26_1, t26_2;
    info.eval->multiply_plain(vs[11], bits["0001000"], t26_1);
    info.eval->multiply_plain(vs[8], bits["0000001"], t26_2);
    info.eval->add(t26_1, t26_2, ts[26]);
    
    
    // __t27 = blend(__s1@0001000, __t25@0000001)
    ctxt t27_1;
    info.eval->multiply_plain(ss[1], bits["0001000"], t27_1);
    info.eval->add(t27_1, ts[25], ts[27]);
    
    info.eval->multiply(ts[26], ts[27], vs[12]); // __v12 = __t26 * __t27
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->multiply(vs[12], vs[2], vs[13]); // __v13 = __v12 * __v2
    info.eval->relinearize_inplace(vs[13], rk);
    info.eval->rotate_rows(vs[13], -4, gk, ss[4]); // __s4 = __v13 >> 4
    info.eval->multiply(ss[4], ts[28], vs[14]); // __v14 = __s4 * __t28
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->multiply(vs[14], vs[12], vs[15]); // __v15 = __v14 * __v12
    info.eval->relinearize_inplace(vs[15], rk);
    return vs[15];
}
    