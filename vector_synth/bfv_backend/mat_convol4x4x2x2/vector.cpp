
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "101000001100001000", info);
    add_bitstring(bits, "010000000000010000", info);
    add_bitstring(bits, "000000000000001000", info);
    add_bitstring(bits, "000000001000000000", info);
    add_bitstring(bits, "000000000000011000", info);
    add_bitstring(bits, "101000100000000000", info);
    add_bitstring(bits, "000000000000010000", info);
    add_bitstring(bits, "000000001000010000", info);
    add_bitstring(bits, "001010000000000000", info);
    add_bitstring(bits, "010000000000000000", info);
    add_bitstring(bits, "000000100000000000", info);
    add_bitstring(bits, "100000000100001000", info);
    add_bitstring(bits, "011000001000000000", info);
    add_bitstring(bits, "010010000000000000", info);
    add_bitstring(bits, "000000000100001000", info);
    add_bitstring(bits, "000000101000000000", info);
    add_bitstring(bits, "001000000100001000", info);
    add_bitstring(bits, "000000000100000000", info);
    add_bitstring(bits, "100000000000000000", info);
    add_bitstring(bits, "000000100100000000", info);
    add_bitstring(bits, "110010101000010000", info);
    add_bitstring(bits, "000010100000010000", info);
    add_bitstring(bits, "000010000000000000", info);
    add_bitstring(bits, "000010101000000000", info);
    add_bitstring(bits, "100000000000010000", info);
    add_bitstring(bits, "000010100000000000", info);
    add_bitstring(bits, "001000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(20);
    ts[0] = encrypt_input("11111001101111010011110111110110111101101111100000", info);
    ts[1] = encrypt_input("11111001101111010011110111110110111101101111100000", info);
    ts[2] = encrypt_input("0000000000001111111110011011011010", info);
    ts[3] = encrypt_input("0000000000001111111110011011011010", info);
    ts[4] = encrypt_input("001111001111100011111111110001111011111000", info);
    ts[7] = encrypt_input("000000000111110001111111111000", info);
    ts[10] = encrypt_input("000000000111110001111111111000", info);
    ts[15] = encrypt_input("001111101111100011111111110001111011111000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[9];
    ctxt ss[26];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -2, gk, ss[1]); // __s1 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -4, gk, ss[2]); // __s2 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -16, gk, ss[3]); // __s3 = __v0 >> 16
    info.eval->rotate_rows(vs[0], -15, gk, ss[4]); // __s4 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -14, gk, ss[5]); // __s5 = __v0 >> 14
    info.eval->rotate_rows(vs[0], -12, gk, ss[6]); // __s6 = __v0 >> 12
    info.eval->rotate_rows(vs[0], -17, gk, ss[7]); // __s7 = __v0 >> 17
    info.eval->rotate_rows(vs[0], -10, gk, ss[8]); // __s8 = __v0 >> 10
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[9]); // __s9 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -2, gk, ss[10]); // __s10 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -6, gk, ss[11]); // __s11 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -7, gk, ss[12]); // __s12 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -8, gk, ss[13]); // __s13 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -10, gk, ss[14]); // __s14 = __v1 >> 10
    info.eval->rotate_rows(vs[1], -12, gk, ss[15]); // __s15 = __v1 >> 12
    info.eval->rotate_rows(vs[1], -14, gk, ss[16]); // __s16 = __v1 >> 14
    info.eval->rotate_rows(vs[1], -15, gk, ss[17]); // __s17 = __v1 >> 15
    info.eval->rotate_rows(vs[1], -5, gk, ss[18]); // __s18 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -9, gk, ss[19]); // __s19 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -11, gk, ss[20]); // __s20 = __v1 >> 11
    info.eval->rotate_rows(vs[1], -13, gk, ss[21]); // __s21 = __v1 >> 13
    info.eval->rotate_rows(vs[1], -3, gk, ss[22]); // __s22 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -4, gk, ss[23]); // __s23 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -16, gk, ss[24]); // __s24 = __v1 >> 16
    info.eval->rotate_rows(vs[1], -17, gk, ss[25]); // __s25 = __v1 >> 17
    
    // __t5 = blend(__s22@100000000000000000, __s10@010000000000000000, __s12@001000000000000000, __s14@000010000000000000, __s15@000000100100000000, __s16@000000001000010000, __s25@000000000000001000)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7;
    info.eval->multiply_plain(ss[22], bits["100000000000000000"], t5_1);
    info.eval->multiply_plain(ss[10], bits["010000000000000000"], t5_2);
    info.eval->multiply_plain(ss[12], bits["001000000000000000"], t5_3);
    info.eval->multiply_plain(ss[14], bits["000010000000000000"], t5_4);
    info.eval->multiply_plain(ss[15], bits["000000100100000000"], t5_5);
    info.eval->multiply_plain(ss[16], bits["000000001000010000"], t5_6);
    info.eval->multiply_plain(ss[25], bits["000000000000001000"], t5_7);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7}, ts[5]);
    
    
    // __t6 = blend(__s4@100000000000000000, __s3@010000000000000000, __s6@000000100000000000, __t4@001010001100011000)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(ss[4], bits["100000000000000000"], t6_1);
    info.eval->multiply_plain(ss[3], bits["010000000000000000"], t6_2);
    info.eval->multiply_plain(ss[6], bits["000000100000000000"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3, ts[4]}, ts[6]);
    
    info.eval->multiply(ts[5], ts[6], vs[2]); // __v2 = __t5 * __t6
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t8 = blend(__s9@100000000000000000, __s12@010010000000000000, __s22@001000000000000000, __s19@000000101000000000, __s14@000000000100000000, __s24@000000000000010000, __s17@000000000000001000)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5, t8_6, t8_7;
    info.eval->multiply_plain(ss[9], bits["100000000000000000"], t8_1);
    info.eval->multiply_plain(ss[12], bits["010010000000000000"], t8_2);
    info.eval->multiply_plain(ss[22], bits["001000000000000000"], t8_3);
    info.eval->multiply_plain(ss[19], bits["000000101000000000"], t8_4);
    info.eval->multiply_plain(ss[14], bits["000000000100000000"], t8_5);
    info.eval->multiply_plain(ss[24], bits["000000000000010000"], t8_6);
    info.eval->multiply_plain(ss[17], bits["000000000000001000"], t8_7);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5, t8_6, t8_7}, ts[8]);
    
    
    // __t9 = blend(__s5@101000100000000000, __s6@010000000000000000, __s4@000010000000000000, __s0@000000001000000000, __t7@000000000100011000)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[5], bits["101000100000000000"], t9_1);
    info.eval->multiply_plain(ss[6], bits["010000000000000000"], t9_2);
    info.eval->multiply_plain(ss[4], bits["000010000000000000"], t9_3);
    info.eval->multiply_plain(ss[0], bits["000000001000000000"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, ts[7]}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t11 = blend(__s11@100000000000000000, __s23@010000000000000000, __s18@001010000000000000, __s12@000000100000000000, __s20@000000001000000000, __s16@000000000100000000, __s9@000000000000011000)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5, t11_6, t11_7;
    info.eval->multiply_plain(ss[11], bits["100000000000000000"], t11_1);
    info.eval->multiply_plain(ss[23], bits["010000000000000000"], t11_2);
    info.eval->multiply_plain(ss[18], bits["001010000000000000"], t11_3);
    info.eval->multiply_plain(ss[12], bits["000000100000000000"], t11_4);
    info.eval->multiply_plain(ss[20], bits["000000001000000000"], t11_5);
    info.eval->multiply_plain(ss[16], bits["000000000100000000"], t11_6);
    info.eval->multiply_plain(ss[9], bits["000000000000011000"], t11_7);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5, t11_6, t11_7}, ts[11]);
    
    
    // __t12 = blend(__v0@100000000000000000, __s8@010000000000000000, __s1@001000000000000000, __s2@000010000000000000, __s4@000000100000000000, __s5@000000001000000000, __t10@000000000100011000)
    ctxt t12_1, t12_2, t12_3, t12_4, t12_5, t12_6;
    info.eval->multiply_plain(vs[0], bits["100000000000000000"], t12_1);
    info.eval->multiply_plain(ss[8], bits["010000000000000000"], t12_2);
    info.eval->multiply_plain(ss[1], bits["001000000000000000"], t12_3);
    info.eval->multiply_plain(ss[2], bits["000010000000000000"], t12_4);
    info.eval->multiply_plain(ss[4], bits["000000100000000000"], t12_5);
    info.eval->multiply_plain(ss[5], bits["000000001000000000"], t12_6);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4, t12_5, t12_6, ts[10]}, ts[12]);
    
    info.eval->multiply(ts[11], ts[12], vs[4]); // __v4 = __t11 * __t12
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t13 = blend(__v3@101000001100001000, __v2@010000000000010000, __v4@000010100000000000)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(vs[3], bits["101000001100001000"], t13_1);
    info.eval->multiply_plain(vs[2], bits["010000000000010000"], t13_2);
    info.eval->multiply_plain(vs[4], bits["000010100000000000"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    
    // __t14 = blend(__v2@100000000100001000, __v4@011000001000000000, __v3@000010100000010000)
    ctxt t14_1, t14_2, t14_3;
    info.eval->multiply_plain(vs[2], bits["100000000100001000"], t14_1);
    info.eval->multiply_plain(vs[4], bits["011000001000000000"], t14_2);
    info.eval->multiply_plain(vs[3], bits["000010100000010000"], t14_3);
    info.eval->add_many({t14_1, t14_2, t14_3}, ts[14]);
    
    info.eval->add(ts[13], ts[14], vs[5]); // __v5 = __t13 + __t14
    
    // __t16 = blend(__s18@100000000000000000, __s11@010000000000000000, __s13@001000000000000000, __s19@000010000000000000, __s20@000000100000000000, __s21@000000001000000000, __s17@000000000100000000, __v1@000000000000010000, __s10@000000000000001000)
    ctxt t16_1, t16_2, t16_3, t16_4, t16_5, t16_6, t16_7, t16_8, t16_9;
    info.eval->multiply_plain(ss[18], bits["100000000000000000"], t16_1);
    info.eval->multiply_plain(ss[11], bits["010000000000000000"], t16_2);
    info.eval->multiply_plain(ss[13], bits["001000000000000000"], t16_3);
    info.eval->multiply_plain(ss[19], bits["000010000000000000"], t16_4);
    info.eval->multiply_plain(ss[20], bits["000000100000000000"], t16_5);
    info.eval->multiply_plain(ss[21], bits["000000001000000000"], t16_6);
    info.eval->multiply_plain(ss[17], bits["000000000100000000"], t16_7);
    info.eval->multiply_plain(vs[1], bits["000000000000010000"], t16_8);
    info.eval->multiply_plain(ss[10], bits["000000000000001000"], t16_9);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4, t16_5, t16_6, t16_7, t16_8, t16_9}, ts[16]);
    
    
    // __t17 = blend(__s6@100000000000000000, __s0@010000000000000000, __s7@000000100000000000, __t15@001010001100011000)
    ctxt t17_1, t17_2, t17_3;
    info.eval->multiply_plain(ss[6], bits["100000000000000000"], t17_1);
    info.eval->multiply_plain(ss[0], bits["010000000000000000"], t17_2);
    info.eval->multiply_plain(ss[7], bits["000000100000000000"], t17_3);
    info.eval->add_many({t17_1, t17_2, t17_3, ts[15]}, ts[17]);
    
    info.eval->multiply(ts[16], ts[17], vs[6]); // __v6 = __t16 * __t17
    info.eval->relinearize_inplace(vs[6], rk);
    
    // __t18 = blend(__v6@110010101000010000, __v2@001000000000000000, __v4@000000000100001000)
    ctxt t18_1, t18_2, t18_3;
    info.eval->multiply_plain(vs[6], bits["110010101000010000"], t18_1);
    info.eval->multiply_plain(vs[2], bits["001000000000000000"], t18_2);
    info.eval->multiply_plain(vs[4], bits["000000000100001000"], t18_3);
    info.eval->add_many({t18_1, t18_2, t18_3}, ts[18]);
    
    info.eval->add(vs[5], ts[18], vs[7]); // __v7 = __v5 + __t18
    
    // __t19 = blend(__v4@100000000000010000, __v3@010000000000000000, __v6@001000000100001000, __v2@000010101000000000)
    ctxt t19_1, t19_2, t19_3, t19_4;
    info.eval->multiply_plain(vs[4], bits["100000000000010000"], t19_1);
    info.eval->multiply_plain(vs[3], bits["010000000000000000"], t19_2);
    info.eval->multiply_plain(vs[6], bits["001000000100001000"], t19_3);
    info.eval->multiply_plain(vs[2], bits["000010101000000000"], t19_4);
    info.eval->add_many({t19_1, t19_2, t19_3, t19_4}, ts[19]);
    
    info.eval->add(vs[7], ts[19], vs[8]); // __v8 = __v7 + __t19
    return vs[8];
}
    