
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000001", info);
    add_bitstring(bits, "000010000", info);
    add_bitstring(bits, "010000000", info);
    add_bitstring(bits, "000001000", info);
    add_bitstring(bits, "000001001", info);
    add_bitstring(bits, "100000000", info);
    add_bitstring(bits, "000100000", info);
    add_bitstring(bits, "000000010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(25);
    ts[0] = encrypt_input("1100011011110101110", info);
    ts[1] = encrypt_input("111001111111110110", info);
    ts[2] = encrypt_input("001110001110100", info);
    ts[3] = encrypt_input("00111111001110110", info);
    ts[5] = encrypt_input("00000001010", info);
    ts[6] = encrypt_input("0000111110000", info);
    ts[9] = encrypt_input("00001110000", info);
    ts[10] = encrypt_input("1010001110000", info);
    ts[12] = encrypt_input("00000001010", info);
    ts[14] = encrypt_input("01110000000", info);
    ts[15] = encrypt_input("00000000110", info);
    ts[18] = encrypt_input("0000011000", info);
    ts[19] = encrypt_input("01110000000", info);
    ts[22] = encrypt_input("0111000111000", info);
    ts[23] = encrypt_input("00000110000", info);
    ts[24] = encrypt_input("00000111000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[15];
    ctxt ss[5];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    
    // __t4 = blend(__v0@000100000, __t2@001000101)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["000100000"], t4_1);
    info.eval->add(t4_1, ts[2], ts[4]);
    
    info.eval->multiply(ts[4], ts[3], vs[1]); // __v1 = __t4 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -2, gk, ss[0]); // __s0 = __v1 >> 2
    
    // __t7 = blend(__v0@000010000, __s0@000001000, __v1@000000001, __t5@000000010)
    ctxt t7_1, t7_2, t7_3;
    info.eval->multiply_plain(vs[0], bits["000010000"], t7_1);
    info.eval->multiply_plain(ss[0], bits["000001000"], t7_2);
    info.eval->multiply_plain(vs[1], bits["000000001"], t7_3);
    info.eval->add_many({t7_1, t7_2, t7_3, ts[5]}, ts[7]);
    
    
    // __t8 = blend(__v0@000000010, __s0@000000001, __t6@000011000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[0], bits["000000010"], t8_1);
    info.eval->multiply_plain(ss[0], bits["000000001"], t8_2);
    info.eval->add_many({t8_1, t8_2, ts[6]}, ts[8]);
    
    info.eval->multiply(ts[7], ts[8], vs[2]); // __v2 = __t7 * __t8
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t11 = blend(__v0@100000000, __t9@000010000)
    ctxt t11_1;
    info.eval->multiply_plain(vs[0], bits["100000000"], t11_1);
    info.eval->add(t11_1, ts[9], ts[11]);
    
    info.eval->add(ts[11], ts[10], vs[3]); // __v3 = __t11 + __t10
    info.eval->rotate_rows(vs[3], -1, gk, ss[1]); // __s1 = __v3 >> 1
    info.eval->add(vs[3], ss[0], vs[4]); // __v4 = __v3 + __s0
    
    // __t13 = blend(__v4@000010000, __t12@000000010)
    ctxt t13_1;
    info.eval->multiply_plain(vs[4], bits["000010000"], t13_1);
    info.eval->add(t13_1, ts[12], ts[13]);
    
    info.eval->add(ts[13], vs[2], vs[5]); // __v5 = __t13 + __v2
    info.eval->rotate_rows(vs[5], -1, gk, ss[2]); // __s2 = __v5 >> 1
    
    // __t16 = blend(__v2@000001001, __t14@010000000)
    ctxt t16_1;
    info.eval->multiply_plain(vs[2], bits["000001001"], t16_1);
    info.eval->add(t16_1, ts[14], ts[16]);
    
    
    // __t17 = blend(__s1@010000000, __s2@000001000, __t15@000000001)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(ss[1], bits["010000000"], t17_1);
    info.eval->multiply_plain(ss[2], bits["000001000"], t17_2);
    info.eval->add_many({t17_1, t17_2, ts[15]}, ts[17]);
    
    info.eval->add(ts[16], ts[17], vs[6]); // __v6 = __t16 + __t17
    info.eval->add(ss[2], vs[6], vs[7]); // __v7 = __s2 + __v6
    info.eval->rotate_rows(vs[7], -2, gk, ss[3]); // __s3 = __v7 >> 2
    
    // __t20 = blend(__s3@010000000, __t18@000001000)
    ctxt t20_1;
    info.eval->multiply_plain(ss[3], bits["010000000"], t20_1);
    info.eval->add(t20_1, ts[18], ts[20]);
    
    
    // __t21 = blend(__v6@000001000, __t19@010000000)
    ctxt t21_1;
    info.eval->multiply_plain(vs[6], bits["000001000"], t21_1);
    info.eval->add(t21_1, ts[19], ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[8]); // __v8 = __t20 + __t21
    info.eval->add(vs[8], ts[22], vs[9]); // __v9 = __v8 + __t22
    info.eval->add(vs[6], vs[9], vs[10]); // __v10 = __v6 + __v9
    info.eval->rotate_rows(vs[10], -4, gk, ss[4]); // __s4 = __v10 >> 4
    info.eval->add(ts[23], vs[9], vs[11]); // __v11 = __t23 + __v9
    info.eval->multiply(ss[4], vs[11], vs[12]); // __v12 = __s4 * __v11
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->multiply(vs[12], ts[24], vs[13]); // __v13 = __v12 * __t24
    info.eval->relinearize_inplace(vs[13], rk);
    info.eval->multiply(vs[13], vs[0], vs[14]); // __v14 = __v13 * __v0
    info.eval->relinearize_inplace(vs[14], rk);
    return vs[14];
}
    