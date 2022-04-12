
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000100", info);
    add_bitstring(bits, "00000100000", info);
    add_bitstring(bits, "11001000100", info);
    add_bitstring(bits, "00000000010", info);
    add_bitstring(bits, "01000000000", info);
    add_bitstring(bits, "00001000000", info);
    add_bitstring(bits, "00000001100", info);
    add_bitstring(bits, "00000001000", info);
    add_bitstring(bits, "10000000100", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(24);
    ts[0] = encrypt_input("111011111001011011110111110", info);
    ts[1] = encrypt_input("11101111111110110111111111111", info);
    ts[2] = encrypt_input("010100000001110", info);
    ts[3] = encrypt_input("0111000000000", info);
    ts[5] = encrypt_input("0000000001010", info);
    ts[6] = encrypt_input("000011100111000", info);
    ts[9] = encrypt_input("10110000000000", info);
    ts[10] = encrypt_input("0000011101110100", info);
    ts[13] = encrypt_input("000001110011100", info);
    ts[15] = encrypt_input("0000000111000", info);
    ts[16] = encrypt_input("0000000111000", info);
    ts[19] = encrypt_input("0000111000000", info);
    ts[22] = encrypt_input("0000110000000", info);
    ts[23] = encrypt_input("0000111000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[15];
    ctxt ss[7];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -9, gk, ss[0]); // __s0 = __v0 >> 9
    
    // __t4 = blend(__v0@00000000010, __t3@01000000000)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["00000000010"], t4_1);
    info.eval->add(t4_1, ts[3], ts[4]);
    
    info.eval->add(ts[2], ts[4], vs[1]); // __v1 = __t2 + __t4
    info.eval->add(ts[5], vs[1], vs[2]); // __v2 = __t5 + __v1
    info.eval->rotate_rows(vs[2], -9, gk, ss[1]); // __s1 = __v2 >> 9
    
    // __t7 = blend(__s0@11001000100, __s1@00000001000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[0], bits["11001000100"], t7_1);
    info.eval->multiply_plain(ss[1], bits["00000001000"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    
    // __t8 = blend(__v0@10000000100, __v1@01000000000, __t6@00001001000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[0], bits["10000000100"], t8_1);
    info.eval->multiply_plain(vs[1], bits["01000000000"], t8_2);
    info.eval->add_many({t8_1, t8_2, ts[6]}, ts[8]);
    
    info.eval->multiply(ts[7], ts[8], vs[3]); // __v3 = __t7 * __t8
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -4, gk, ss[2]); // __s2 = __v3 >> 4
    info.eval->add(ts[9], vs[3], vs[4]); // __v4 = __t9 + __v3
    info.eval->rotate_rows(vs[4], -4, gk, ss[3]); // __s3 = __v4 >> 4
    
    // __t11 = blend(__v0@00001000000, __s2@00000100000, __v3@00000001100)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[0], bits["00001000000"], t11_1);
    info.eval->multiply_plain(ss[2], bits["00000100000"], t11_2);
    info.eval->multiply_plain(vs[3], bits["00000001100"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    
    // __t12 = blend(__s3@00001000000, __t10@00000101100)
    ctxt t12_1;
    info.eval->multiply_plain(ss[3], bits["00001000000"], t12_1);
    info.eval->add(t12_1, ts[10], ts[12]);
    
    info.eval->multiply(ts[11], ts[12], vs[5]); // __v5 = __t11 * __t12
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t14 = blend(__s0@00000100000, __v5@00000000100)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(ss[0], bits["00000100000"], t14_1);
    info.eval->multiply_plain(vs[5], bits["00000000100"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    info.eval->multiply(ts[14], ts[13], vs[6]); // __v6 = __t14 * __t13
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -10, gk, ss[4]); // __s4 = __v6 >> 10
    info.eval->add(vs[5], vs[6], vs[7]); // __v7 = __v5 + __v6
    info.eval->rotate_rows(vs[7], -10, gk, ss[5]); // __s5 = __v7 >> 10
    info.eval->multiply(ts[15], ts[16], vs[8]); // __v8 = __t15 * __t16
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t17 = blend(__v5@00001000000, __v8@00000001000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(vs[5], bits["00001000000"], t17_1);
    info.eval->multiply_plain(vs[8], bits["00000001000"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    
    // __t18 = blend(__s5@00001000000, __s4@00000001000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(ss[5], bits["00001000000"], t18_1);
    info.eval->multiply_plain(ss[4], bits["00000001000"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    info.eval->add(ts[17], ts[18], vs[9]); // __v9 = __t17 + __t18
    
    // __t20 = blend(__v9@00001000000, __v5@00000001000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[9], bits["00001000000"], t20_1);
    info.eval->multiply_plain(vs[5], bits["00000001000"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    
    // __t21 = blend(__v9@00000001000, __t19@00001000000)
    ctxt t21_1;
    info.eval->multiply_plain(vs[9], bits["00000001000"], t21_1);
    info.eval->add(t21_1, ts[19], ts[21]);
    
    info.eval->multiply(ts[20], ts[21], vs[10]); // __v10 = __t20 * __t21
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -8, gk, ss[6]); // __s6 = __v10 >> 8
    info.eval->multiply(ss[6], vs[10], vs[11]); // __v11 = __s6 * __v10
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->multiply(ts[22], vs[11], vs[12]); // __v12 = __t22 * __v11
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->add(ts[23], vs[12], vs[13]); // __v13 = __t23 + __v12
    info.eval->add(vs[13], vs[3], vs[14]); // __v14 = __v13 + __v3
    return vs[14];
}
    