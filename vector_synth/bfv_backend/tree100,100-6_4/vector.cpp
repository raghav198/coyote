
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000000000000101010000000", info);
    add_bitstring(bits, "000000000000000001000000000", info);
    add_bitstring(bits, "000000000000000100010000000", info);
    add_bitstring(bits, "000000000100000000000001000", info);
    add_bitstring(bits, "000000000000000010100000000", info);
    add_bitstring(bits, "000000001011000000000000000", info);
    add_bitstring(bits, "000000000000000000000100000", info);
    add_bitstring(bits, "000000000000000000100000000", info);
    add_bitstring(bits, "000000000000000000000001000", info);
    add_bitstring(bits, "000000101010001000000000000", info);
    add_bitstring(bits, "000000000000000001010000000", info);
    add_bitstring(bits, "000000000000001000000000000", info);
    add_bitstring(bits, "000000000000000010000000000", info);
    add_bitstring(bits, "000000000000110000000000001", info);
    add_bitstring(bits, "000001100100110100000000000", info);
    add_bitstring(bits, "000010000101010000000000000", info);
    add_bitstring(bits, "000001010000100100000000000", info);
    add_bitstring(bits, "000010010000001000000000000", info);
    add_bitstring(bits, "000000000000000000010000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(17);
    ts[0] = encrypt_input("11100111000001111101111110111011100001111110111111", info);
    ts[1] = encrypt_input("1010011100000111111011111001110111000011111011111", info);
    ts[2] = encrypt_input("00001110111111010100111111001110110110001011110111", info);
    ts[3] = encrypt_input("0000111011111101110011111100111011101110011110010111", info);
    ts[4] = encrypt_input("011111100111001100111001110000111011100000", info);
    ts[5] = encrypt_input("01111001000011100111001110000111011100000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[9];
    ctxt ss[15];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -4, gk, ss[0]); // __s0 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -17, gk, ss[1]); // __s1 = __v0 >> 17
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -4, gk, ss[2]); // __s2 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -17, gk, ss[3]); // __s3 = __v1 >> 17
    
    // __t6 = blend(__v0@000000000100000000000001000, __v1@000000000000110000000000001, __t4@011001001001001000010100000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[0], bits["000000000100000000000001000"], t6_1);
    info.eval->multiply_plain(vs[1], bits["000000000000110000000000001"], t6_2);
    info.eval->add_many({t6_1, t6_2, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__v1@000000000100000000000001000, __v0@000000000000110000000000001, __t5@011001001001001000010100000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[1], bits["000000000100000000000001000"], t7_1);
    info.eval->multiply_plain(vs[0], bits["000000000000110000000000001"], t7_2);
    info.eval->add_many({t7_1, t7_2, ts[5]}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -4, gk, ss[4]); // __s4 = __v2 >> 4
    info.eval->rotate_rows(vs[2], -17, gk, ss[5]); // __s5 = __v2 >> 17
    
    // __t8 = blend(__s0@000010010000001000000000000, __s4@000001100100110100000000000, __s2@000000001011000000000000000, __s5@000000000000000010000000000)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(ss[0], bits["000010010000001000000000000"], t8_1);
    info.eval->multiply_plain(ss[4], bits["000001100100110100000000000"], t8_2);
    info.eval->multiply_plain(ss[2], bits["000000001011000000000000000"], t8_3);
    info.eval->multiply_plain(ss[5], bits["000000000000000010000000000"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__s5@000010000101010000000000000, __s1@000001010000100100000000000, __s3@000000101010001000000000000, __s4@000000000000000010000000000)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[5], bits["000010000101010000000000000"], t9_1);
    info.eval->multiply_plain(ss[1], bits["000001010000100100000000000"], t9_2);
    info.eval->multiply_plain(ss[3], bits["000000101010001000000000000"], t9_3);
    info.eval->multiply_plain(ss[4], bits["000000000000000010000000000"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -10, gk, ss[6]); // __s6 = __v3 >> 10
    info.eval->rotate_rows(vs[3], -4, gk, ss[7]); // __s7 = __v3 >> 4
    
    // __t10 = blend(__s6@000000000000001000000000000, __s7@000000000000000010100000000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(ss[6], bits["000000000000001000000000000"], t10_1);
    info.eval->multiply_plain(ss[7], bits["000000000000000010100000000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__s7@000000000000001000000000000, __s6@000000000000000010100000000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(ss[7], bits["000000000000001000000000000"], t11_1);
    info.eval->multiply_plain(ss[6], bits["000000000000000010100000000"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[4]); // __v4 = __t10 * __t11
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -4, gk, ss[8]); // __s8 = __v4 >> 4
    
    // __t12 = blend(__s7@000000000000000100010000000, __v4@000000000000000010000000000, __s4@000000000000000001000000000)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(ss[7], bits["000000000000000100010000000"], t12_1);
    info.eval->multiply_plain(vs[4], bits["000000000000000010000000000"], t12_2);
    info.eval->multiply_plain(ss[4], bits["000000000000000001000000000"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    
    // __t13 = blend(__s6@000000000000000101010000000, __v3@000000000000000010000000000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(ss[6], bits["000000000000000101010000000"], t13_1);
    info.eval->multiply_plain(vs[3], bits["000000000000000010000000000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[5]); // __v5 = __t12 * __t13
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -4, gk, ss[9]); // __s9 = __v5 >> 4
    info.eval->rotate_rows(vs[5], -5, gk, ss[10]); // __s10 = __v5 >> 5
    
    // __t14 = blend(__s7@000000000000000001000000000, __s8@000000000000000000100000000, __s9@000000000000000000010000000)
    ctxt t14_1, t14_2, t14_3;
    info.eval->multiply_plain(ss[7], bits["000000000000000001000000000"], t14_1);
    info.eval->multiply_plain(ss[8], bits["000000000000000000100000000"], t14_2);
    info.eval->multiply_plain(ss[9], bits["000000000000000000010000000"], t14_3);
    info.eval->add_many({t14_1, t14_2, t14_3}, ts[14]);
    
    
    // __t15 = blend(__v5@000000000000000001010000000, __v4@000000000000000000100000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[5], bits["000000000000000001010000000"], t15_1);
    info.eval->multiply_plain(vs[4], bits["000000000000000000100000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[6]); // __v6 = __t14 * __t15
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -4, gk, ss[11]); // __s11 = __v6 >> 4
    info.eval->rotate_rows(vs[6], -5, gk, ss[12]); // __s12 = __v6 >> 5
    
    // __t16 = blend(__s10@000000000000000000000100000, __s12@000000000000000000000001000)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(ss[10], bits["000000000000000000000100000"], t16_1);
    info.eval->multiply_plain(ss[12], bits["000000000000000000000001000"], t16_2);
    info.eval->add(t16_1, t16_2, ts[16]);
    
    info.eval->multiply(ss[11], ts[16], vs[7]); // __v7 = __s11 * __t16
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -4, gk, ss[13]); // __s13 = __v7 >> 4
    info.eval->rotate_rows(vs[7], -2, gk, ss[14]); // __s14 = __v7 >> 2
    info.eval->multiply(ss[13], ss[14], vs[8]); // __v8 = __s13 * __s14
    info.eval->relinearize_inplace(vs[8], rk);
    return vs[8];
}
    