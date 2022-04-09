
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0010000100000100000000", info);
    add_bitstring(bits, "0000100000001001100000", info);
    add_bitstring(bits, "0000001100100000000000", info);
    add_bitstring(bits, "0000000000001100100000", info);
    add_bitstring(bits, "0001000000000001100100", info);
    add_bitstring(bits, "0000000100000000011000", info);
    add_bitstring(bits, "0100001000001000000000", info);
    add_bitstring(bits, "0000000011000001000000", info);
    add_bitstring(bits, "0000010000100000100000", info);
    add_bitstring(bits, "0000010001000000000000", info);
    add_bitstring(bits, "0000000000000000010100", info);
    add_bitstring(bits, "0000100000000000000000", info);
    add_bitstring(bits, "0001100011001001100000", info);
    add_bitstring(bits, "0001000000000001001000", info);
    add_bitstring(bits, "0110010000000000000000", info);
    add_bitstring(bits, "0010000000000010010000", info);
    add_bitstring(bits, "0000000100001000000000", info);
    add_bitstring(bits, "0000000100100000000000", info);
    add_bitstring(bits, "0001000100000000000000", info);
    add_bitstring(bits, "0000100000000011000000", info);
    add_bitstring(bits, "0001000000000000000000", info);
    add_bitstring(bits, "0000010000000000000000", info);
    add_bitstring(bits, "0000000001001000000000", info);
    add_bitstring(bits, "0000000010000001000100", info);
    add_bitstring(bits, "0000010011000000000000", info);
    add_bitstring(bits, "0000000000000000000100", info);
    add_bitstring(bits, "0000000010000000000000", info);
    add_bitstring(bits, "0000000100000010001000", info);
    add_bitstring(bits, "0000100000000000010000", info);
    add_bitstring(bits, "0011000000000000000000", info);
    add_bitstring(bits, "0000000000100000000000", info);
    add_bitstring(bits, "0000000000000011001000", info);
    add_bitstring(bits, "0000000000000000100000", info);
    add_bitstring(bits, "0000000011000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(22);
    ts[0] = encrypt_input("0000111111111111111111101100000000000011111111111111111110111001111111111111111111011100", info);
    ts[1] = encrypt_input("0000111111111111111111101100000000000011111111111111111110111001111111111111111111011100", info);
    ts[2] = encrypt_input("0000000000111111111111111111111111111111111111111111111100111111111111111111111100000000", info);
    ts[3] = encrypt_input("0000000000111111111111111111111111111111111111111111111100111111111111111111111100000000", info);
    ts[4] = encrypt_input("0000000000111111111111111111111100000001111111111111111111111100011111111111111111111111", info);
    ts[5] = encrypt_input("0000000000111111111111111111111100000001111111111111111111111100011111111111111111111111", info);
    ts[6] = encrypt_input("0000000000111111111111111111101100000000001111111111111111111011111111111111111111110111", info);
    ts[7] = encrypt_input("0000000000111111111111111111101100000000001111111111111111111011111111111111111111110111", info);
    ts[8] = encrypt_input("1111111111111111111111100001111111111111111111111000000111111111111111111111110000000000", info);
    ts[9] = encrypt_input("1111111111111111111111100001111111111111111111111000000111111111111111111111110000000000", info);
    ts[12] = encrypt_input("0000000000000011111111111111111111111111111111111111111111100011111111111111111111111000", info);
    ts[13] = encrypt_input("0000000000000011111111111111111111111111111111111111111111100011111111111111111111111000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[9];
    ctxt ss[24];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -20, gk, ss[0]); // __s0 = __v0 >> 20
    info.eval->rotate_rows(vs[0], -21, gk, ss[1]); // __s1 = __v0 >> 21
    info.eval->rotate_rows(vs[0], -13, gk, ss[2]); // __s2 = __v0 >> 13
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -18, gk, ss[3]); // __s3 = __v1 >> 18
    info.eval->rotate_rows(vs[1], -2, gk, ss[4]); // __s4 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -13, gk, ss[5]); // __s5 = __v1 >> 13
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -19, gk, ss[6]); // __s6 = __v2 >> 19
    info.eval->rotate_rows(vs[2], -20, gk, ss[7]); // __s7 = __v2 >> 20
    info.eval->rotate_rows(vs[2], -10, gk, ss[8]); // __s8 = __v2 >> 10
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -16, gk, ss[9]); // __s9 = __v3 >> 16
    info.eval->rotate_rows(vs[3], -19, gk, ss[10]); // __s10 = __v3 >> 19
    info.eval->rotate_rows(vs[3], -4, gk, ss[11]); // __s11 = __v3 >> 4
    
    // __t10 = blend(__s0@0010000000000010010000, __s1@0001000000000001001000, __v0@0000100000000000000000, __s2@0000000100100000000000, __t8@1000010000010000000000)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(ss[0], bits["0010000000000010010000"], t10_1);
    info.eval->multiply_plain(ss[1], bits["0001000000000001001000"], t10_2);
    info.eval->multiply_plain(vs[0], bits["0000100000000000000000"], t10_3);
    info.eval->multiply_plain(ss[2], bits["0000000100100000000000"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, ts[8]}, ts[10]);
    
    
    // __t11 = blend(__s11@0011000000000000000000, __s9@0000100000000011000000, __s10@0000000100000000011000, __v3@0000000000100000000000, __t9@1000010000010000000000)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(ss[11], bits["0011000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[9], bits["0000100000000011000000"], t11_2);
    info.eval->multiply_plain(ss[10], bits["0000000100000000011000"], t11_3);
    info.eval->multiply_plain(vs[3], bits["0000000000100000000000"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, ts[9]}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[4]); // __v4 = __t10 * __t11
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -1, gk, ss[12]); // __s12 = __v4 >> 1
    info.eval->rotate_rows(vs[4], -2, gk, ss[13]); // __s13 = __v4 >> 2
    info.eval->rotate_rows(vs[4], -5, gk, ss[14]); // __s14 = __v4 >> 5
    
    // __t14 = blend(__s5@0110010000000000000000, __s3@0000001100100000000000, __s4@0000000000001100100000, __t12@0000000000000011001000)
    ctxt t14_1, t14_2, t14_3;
    info.eval->multiply_plain(ss[5], bits["0110010000000000000000"], t14_1);
    info.eval->multiply_plain(ss[3], bits["0000001100100000000000"], t14_2);
    info.eval->multiply_plain(ss[4], bits["0000000000001100100000"], t14_3);
    info.eval->add_many({t14_1, t14_2, t14_3, ts[12]}, ts[14]);
    
    
    // __t15 = blend(__s12@0100001000001000000000, __s13@0010000100000100000000, __s14@0000010000100000100000, __t13@0000000000000011001000)
    ctxt t15_1, t15_2, t15_3;
    info.eval->multiply_plain(ss[12], bits["0100001000001000000000"], t15_1);
    info.eval->multiply_plain(ss[13], bits["0010000100000100000000"], t15_2);
    info.eval->multiply_plain(ss[14], bits["0000010000100000100000"], t15_3);
    info.eval->add_many({t15_1, t15_2, t15_3, ts[13]}, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[5]); // __v5 = __t14 * __t15
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -15, gk, ss[15]); // __s15 = __v5 >> 15
    info.eval->rotate_rows(vs[5], -5, gk, ss[16]); // __s16 = __v5 >> 5
    info.eval->rotate_rows(vs[5], -3, gk, ss[17]); // __s17 = __v5 >> 3
    info.eval->rotate_rows(vs[5], -16, gk, ss[18]); // __s18 = __v5 >> 16
    info.eval->rotate_rows(vs[5], -14, gk, ss[19]); // __s19 = __v5 >> 14
    info.eval->rotate_rows(vs[5], -9, gk, ss[20]); // __s20 = __v5 >> 9
    
    // __t16 = blend(__s8@0000010001000000000000, __s6@0000000100000010001000, __s7@0000000010000001000100, __v2@0000000000100000000000)
    ctxt t16_1, t16_2, t16_3, t16_4;
    info.eval->multiply_plain(ss[8], bits["0000010001000000000000"], t16_1);
    info.eval->multiply_plain(ss[6], bits["0000000100000010001000"], t16_2);
    info.eval->multiply_plain(ss[7], bits["0000000010000001000100"], t16_3);
    info.eval->multiply_plain(vs[2], bits["0000000000100000000000"], t16_4);
    info.eval->add_many({t16_1, t16_2, t16_3, t16_4}, ts[16]);
    
    
    // __t17 = blend(__s20@0000010000000000000000, __s19@0000000100100000000000, __s18@0000000011000000000000, __v5@0000000000000011001000, __s16@0000000000000000000100)
    ctxt t17_1, t17_2, t17_3, t17_4, t17_5;
    info.eval->multiply_plain(ss[20], bits["0000010000000000000000"], t17_1);
    info.eval->multiply_plain(ss[19], bits["0000000100100000000000"], t17_2);
    info.eval->multiply_plain(ss[18], bits["0000000011000000000000"], t17_3);
    info.eval->multiply_plain(vs[5], bits["0000000000000011001000"], t17_4);
    info.eval->multiply_plain(ss[16], bits["0000000000000000000100"], t17_5);
    info.eval->add_many({t17_1, t17_2, t17_3, t17_4, t17_5}, ts[17]);
    
    info.eval->multiply(ts[16], ts[17], vs[6]); // __v6 = __t16 * __t17
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -19, gk, ss[21]); // __s21 = __v6 >> 19
    info.eval->rotate_rows(vs[6], -15, gk, ss[22]); // __s22 = __v6 >> 15
    
    // __t18 = blend(__s20@0001000000000000000000, __s18@0000100000000000000000, __s19@0000010000000000000000, __s16@0000000100001000000000, __s17@0000000011000001000000, __s15@0000000000000000100000)
    ctxt t18_1, t18_2, t18_3, t18_4, t18_5, t18_6;
    info.eval->multiply_plain(ss[20], bits["0001000000000000000000"], t18_1);
    info.eval->multiply_plain(ss[18], bits["0000100000000000000000"], t18_2);
    info.eval->multiply_plain(ss[19], bits["0000010000000000000000"], t18_3);
    info.eval->multiply_plain(ss[16], bits["0000000100001000000000"], t18_4);
    info.eval->multiply_plain(ss[17], bits["0000000011000001000000"], t18_5);
    info.eval->multiply_plain(ss[15], bits["0000000000000000100000"], t18_6);
    info.eval->add_many({t18_1, t18_2, t18_3, t18_4, t18_5, t18_6}, ts[18]);
    
    
    // __t19 = blend(__s22@0001000100000000000000, __s21@0000100000001001100000, __v6@0000010011000000000000)
    ctxt t19_1, t19_2, t19_3;
    info.eval->multiply_plain(ss[22], bits["0001000100000000000000"], t19_1);
    info.eval->multiply_plain(ss[21], bits["0000100000001001100000"], t19_2);
    info.eval->multiply_plain(vs[6], bits["0000010011000000000000"], t19_3);
    info.eval->add_many({t19_1, t19_2, t19_3}, ts[19]);
    
    info.eval->add(ts[18], ts[19], vs[7]); // __v7 = __t18 + __t19
    info.eval->rotate_rows(vs[7], -12, gk, ss[23]); // __s23 = __v7 >> 12
    
    // __t20 = blend(__s12@0001000000000001100100, __v4@0000100000000000010000, __s14@0000000010000000000000, __s13@0000000001001000000000)
    ctxt t20_1, t20_2, t20_3, t20_4;
    info.eval->multiply_plain(ss[12], bits["0001000000000001100100"], t20_1);
    info.eval->multiply_plain(vs[4], bits["0000100000000000010000"], t20_2);
    info.eval->multiply_plain(ss[14], bits["0000000010000000000000"], t20_3);
    info.eval->multiply_plain(ss[13], bits["0000000001001000000000"], t20_4);
    info.eval->add_many({t20_1, t20_2, t20_3, t20_4}, ts[20]);
    
    
    // __t21 = blend(__v7@0001100011001001100000, __s23@0000000000000000010100)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(vs[7], bits["0001100011001001100000"], t21_1);
    info.eval->multiply_plain(ss[23], bits["0000000000000000010100"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    info.eval->add(ts[20], ts[21], vs[8]); // __v8 = __t20 + __t21
    return vs[8];
}
    