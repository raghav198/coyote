
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000000000100000000", info);
    add_bitstring(bits, "000000000000001100100", info);
    add_bitstring(bits, "000000000000010000000", info);
    add_bitstring(bits, "000000000000000011001", info);
    add_bitstring(bits, "000000000000000000001", info);
    add_bitstring(bits, "000000000000110000000", info);
    add_bitstring(bits, "000000000000000001001", info);
    add_bitstring(bits, "000001011000000000000", info);
    add_bitstring(bits, "000010000100000000000", info);
    add_bitstring(bits, "000000000000000111000", info);
    add_bitstring(bits, "000000100001000010000", info);
    add_bitstring(bits, "000000000000001000000", info);
    add_bitstring(bits, "000000000000000000100", info);
    add_bitstring(bits, "000000000010010100000", info);
    add_bitstring(bits, "000000000000110010000", info);
    add_bitstring(bits, "000000000001001010000", info);
    add_bitstring(bits, "000000000000111000000", info);
    add_bitstring(bits, "000001110000000000000", info);
    add_bitstring(bits, "000000000000000000111", info);
    add_bitstring(bits, "000000000000000100000", info);
    add_bitstring(bits, "000010000100001000000", info);
    add_bitstring(bits, "000000000001110000000", info);
    add_bitstring(bits, "000000001110000000000", info);
    add_bitstring(bits, "000000000000000000010", info);
    add_bitstring(bits, "000000000000000010000", info);
    add_bitstring(bits, "000000100000000000000", info);
    add_bitstring(bits, "000000000000010001010", info);
    add_bitstring(bits, "000000000000000000110", info);
    add_bitstring(bits, "000000000101100000000", info);
    add_bitstring(bits, "000000000000001100000", info);
    add_bitstring(bits, "000000000010000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(23);
    ts[0] = encrypt_input("000000000011111111111111111110111001111111111111111111011001111111111111111111011100000", info);
    ts[1] = encrypt_input("000000000011111111111111111110111001111111111111111111011001111111111111111111011100000", info);
    ts[2] = encrypt_input("000000000000011111111111111111111110111111111111111111111111111111111111111111111100000", info);
    ts[3] = encrypt_input("000000000000011111111111111111111110111111111111111111111111111111111111111111111100000", info);
    ts[4] = encrypt_input("000000000000000111111111111111111111111111111111111111111111111111111111111111111110000", info);
    ts[5] = encrypt_input("000000000000000111111111111111111111111111111111111111111111111111111111111111111110000", info);
    ts[6] = encrypt_input("111111111111111111101110000111111111111111111101110000111111111111111111101100000000000", info);
    ts[7] = encrypt_input("111111111111111111101110000111111111111111111101110000111111111111111111101100000000000", info);
    ts[8] = encrypt_input("000001111111111111111111111001111111111111111111111111111111111111111111111000000000000", info);
    ts[9] = encrypt_input("000001111111111111111111111001111111111111111111111111111111111111111111111000000000000", info);
    ts[12] = encrypt_input("000000000000000011111111111111111111110111111111111111111111110011111111111111111111111", info);
    ts[13] = encrypt_input("000000000000000011111111111111111111110111111111111111111111110011111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[23];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -15, gk, ss[1]); // __s1 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -14, gk, ss[2]); // __s2 = __v0 >> 14
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -16, gk, ss[3]); // __s3 = __v1 >> 16
    info.eval->rotate_rows(vs[1], -19, gk, ss[4]); // __s4 = __v1 >> 19
    info.eval->rotate_rows(vs[1], -13, gk, ss[5]); // __s5 = __v1 >> 13
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -18, gk, ss[6]); // __s6 = __v2 >> 18
    info.eval->rotate_rows(vs[2], -3, gk, ss[7]); // __s7 = __v2 >> 3
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -4, gk, ss[8]); // __s8 = __v3 >> 4
    info.eval->rotate_rows(vs[3], -6, gk, ss[9]); // __s9 = __v3 >> 6
    info.eval->rotate_rows(vs[3], -15, gk, ss[10]); // __s10 = __v3 >> 15
    info.eval->rotate_rows(vs[3], -8, gk, ss[11]); // __s11 = __v3 >> 8
    
    // __t10 = blend(__s1@000010000100000000000, __s2@000000100000000000000, __v0@000000000010010100000, __s0@000000000001001010000, __t8@000001011000000000000)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(ss[1], bits["000010000100000000000"], t10_1);
    info.eval->multiply_plain(ss[2], bits["000000100000000000000"], t10_2);
    info.eval->multiply_plain(vs[0], bits["000000000010010100000"], t10_3);
    info.eval->multiply_plain(ss[0], bits["000000000001001010000"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, ts[8]}, ts[10]);
    
    
    // __t11 = blend(__s8@000010000100001000000, __s9@000000100001000010000, __v3@000000000010000000000, __s11@000000000000010000000, __s10@000000000000000100000, __t9@000001011000000000000)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5;
    info.eval->multiply_plain(ss[8], bits["000010000100001000000"], t11_1);
    info.eval->multiply_plain(ss[9], bits["000000100001000010000"], t11_2);
    info.eval->multiply_plain(vs[3], bits["000000000010000000000"], t11_3);
    info.eval->multiply_plain(ss[11], bits["000000000000010000000"], t11_4);
    info.eval->multiply_plain(ss[10], bits["000000000000000100000"], t11_5);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5, ts[9]}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[4]); // __v4 = __t10 * __t11
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -14, gk, ss[12]); // __s12 = __v4 >> 14
    info.eval->rotate_rows(vs[4], -8, gk, ss[13]); // __s13 = __v4 >> 8
    info.eval->rotate_rows(vs[4], -4, gk, ss[14]); // __s14 = __v4 >> 4
    info.eval->rotate_rows(vs[4], -20, gk, ss[15]); // __s15 = __v4 >> 20
    info.eval->rotate_rows(vs[4], -2, gk, ss[16]); // __s16 = __v4 >> 2
    
    // __t14 = blend(__s5@000001110000000000000, __s3@000000001110000000000, __s4@000000000001110000000, __t12@000000000000000011001)
    ctxt t14_1, t14_2, t14_3;
    info.eval->multiply_plain(ss[5], bits["000001110000000000000"], t14_1);
    info.eval->multiply_plain(ss[3], bits["000000001110000000000"], t14_2);
    info.eval->multiply_plain(ss[4], bits["000000000001110000000"], t14_3);
    info.eval->add_many({t14_1, t14_2, t14_3, ts[12]}, ts[14]);
    
    
    // __t15 = blend(__v4@000001011000000000000, __s15@000000100000000000000, __s14@000000000101100000000, __s16@000000000010000000000, __s13@000000000000010000000, __t13@000000000000000011001)
    ctxt t15_1, t15_2, t15_3, t15_4, t15_5;
    info.eval->multiply_plain(vs[4], bits["000001011000000000000"], t15_1);
    info.eval->multiply_plain(ss[15], bits["000000100000000000000"], t15_2);
    info.eval->multiply_plain(ss[14], bits["000000000101100000000"], t15_3);
    info.eval->multiply_plain(ss[16], bits["000000000010000000000"], t15_4);
    info.eval->multiply_plain(ss[13], bits["000000000000010000000"], t15_5);
    info.eval->add_many({t15_1, t15_2, t15_3, t15_4, t15_5, ts[13]}, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[5]); // __v5 = __t14 * __t15
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -9, gk, ss[17]); // __s17 = __v5 >> 9
    info.eval->rotate_rows(vs[5], -12, gk, ss[18]); // __s18 = __v5 >> 12
    info.eval->rotate_rows(vs[5], -3, gk, ss[19]); // __s19 = __v5 >> 3
    info.eval->rotate_rows(vs[5], -17, gk, ss[20]); // __s20 = __v5 >> 17
    info.eval->rotate_rows(vs[5], -19, gk, ss[21]); // __s21 = __v5 >> 19
    info.eval->rotate_rows(vs[5], -20, gk, ss[22]); // __s22 = __v5 >> 20
    
    // __t16 = blend(__s6@000000000000111000000, __v2@000000000000000111000, __s7@000000000000000000111)
    ctxt t16_1, t16_2, t16_3;
    info.eval->multiply_plain(ss[6], bits["000000000000111000000"], t16_1);
    info.eval->multiply_plain(vs[2], bits["000000000000000111000"], t16_2);
    info.eval->multiply_plain(ss[7], bits["000000000000000000111"], t16_3);
    info.eval->add_many({t16_1, t16_2, t16_3}, ts[16]);
    
    
    // __t17 = blend(__s20@000000000000110000000, __s21@000000000000001100100, __v5@000000000000000011001, __s22@000000000000000000010)
    ctxt t17_1, t17_2, t17_3, t17_4;
    info.eval->multiply_plain(ss[20], bits["000000000000110000000"], t17_1);
    info.eval->multiply_plain(ss[21], bits["000000000000001100100"], t17_2);
    info.eval->multiply_plain(vs[5], bits["000000000000000011001"], t17_3);
    info.eval->multiply_plain(ss[22], bits["000000000000000000010"], t17_4);
    info.eval->add_many({t17_1, t17_2, t17_3, t17_4}, ts[17]);
    
    info.eval->multiply(ts[16], ts[17], vs[6]); // __v6 = __t16 * __t17
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t18 = blend(__s19@000000000000110010000, __s17@000000000000000001001, __s18@000000000000000000110)
    ctxt t18_1, t18_2, t18_3;
    info.eval->multiply_plain(ss[19], bits["000000000000110010000"], t18_1);
    info.eval->multiply_plain(ss[17], bits["000000000000000001001"], t18_2);
    info.eval->multiply_plain(ss[18], bits["000000000000000000110"], t18_3);
    info.eval->add_many({t18_1, t18_2, t18_3}, ts[18]);
    
    info.eval->add(ts[18], vs[6], vs[7]); // __v7 = __t18 + __v6
    
    // __t19 = blend(__s16@000000000000100000000, __s14@000000000000010001010, __v4@000000000000000010000, __s12@000000000000000000100)
    ctxt t19_1, t19_2, t19_3, t19_4;
    info.eval->multiply_plain(ss[16], bits["000000000000100000000"], t19_1);
    info.eval->multiply_plain(ss[14], bits["000000000000010001010"], t19_2);
    info.eval->multiply_plain(vs[4], bits["000000000000000010000"], t19_3);
    info.eval->multiply_plain(ss[12], bits["000000000000000000100"], t19_4);
    info.eval->add_many({t19_1, t19_2, t19_3, t19_4}, ts[19]);
    
    info.eval->add(ts[19], vs[7], vs[8]); // __v8 = __t19 + __v7
    
    // __t20 = blend(__s17@000000000000001000000, __s19@000000000000000100000, __s12@000000000000000000001)
    ctxt t20_1, t20_2, t20_3;
    info.eval->multiply_plain(ss[17], bits["000000000000001000000"], t20_1);
    info.eval->multiply_plain(ss[19], bits["000000000000000100000"], t20_2);
    info.eval->multiply_plain(ss[12], bits["000000000000000000001"], t20_3);
    info.eval->add_many({t20_1, t20_2, t20_3}, ts[20]);
    
    
    // __t21 = blend(__v6@000000000000001100000, __v7@000000000000000000001)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(vs[6], bits["000000000000001100000"], t21_1);
    info.eval->multiply_plain(vs[7], bits["000000000000000000001"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[9]); // __v9 = __t20 + __t21
    
    // __t22 = blend(__v4@000000000000001000000, __s14@000000000000000100000)
    ctxt t22_1, t22_2;
    info.eval->multiply_plain(vs[4], bits["000000000000001000000"], t22_1);
    info.eval->multiply_plain(ss[14], bits["000000000000000100000"], t22_2);
    info.eval->add(t22_1, t22_2, ts[22]);
    
    info.eval->add(ts[22], vs[9], vs[10]); // __v10 = __t22 + __v9
    return vs[10];
}
    