
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000000000000000000000000000000001101010000", info);
    add_bitstring(bits, "000000000000000000000000000000000000000000100", info);
    add_bitstring(bits, "000000000000001000010000000000000000000000000", info);
    add_bitstring(bits, "000000000000000100001000000000000000000000000", info);
    add_bitstring(bits, "000000000000000000000000101010000000000000000", info);
    add_bitstring(bits, "000000000000000000000000010000100000000000000", info);
    add_bitstring(bits, "000000000000000010000000000000000000101000000", info);
    add_bitstring(bits, "000000000001001000010010100000101000000000001", info);
    add_bitstring(bits, "100000000000000000000000000000000000000000000", info);
    add_bitstring(bits, "000000010000000000001000000000010000001000100", info);
    add_bitstring(bits, "000000000000000000110000000000000000000000000", info);
    add_bitstring(bits, "000000000000000000000000000000010001000000000", info);
    add_bitstring(bits, "000000000000000000000000000000000010000000000", info);
    add_bitstring(bits, "000000000000000000000100010000100000000000000", info);
    add_bitstring(bits, "000000000001000000010100000000101000000000001", info);
    add_bitstring(bits, "000000000000000000001010000000000000000000000", info);
    add_bitstring(bits, "000000000001000000000000010000111000000000001", info);
    add_bitstring(bits, "100000000000000000000000011000000000100000000", info);
    add_bitstring(bits, "000000000000000000000000000010000000000000000", info);
    add_bitstring(bits, "000000000000000100100100000000000011000000000", info);
    add_bitstring(bits, "000000000000000000000000000000001010000000000", info);
    add_bitstring(bits, "000000000000000000000000000010000010000000000", info);
    add_bitstring(bits, "100000000000000100000000010000000001000000000", info);
    add_bitstring(bits, "000000000000000000000000000000000000000000001", info);
    add_bitstring(bits, "000000010001000000000000000000000000000000000", info);
    add_bitstring(bits, "000000000000000000000100000000000000000000000", info);
    add_bitstring(bits, "000000000000001100100110101000000011000010100", info);
    add_bitstring(bits, "000000000000001000000010101000000000000010100", info);
    add_bitstring(bits, "000000000000000010000000000000000000000000000", info);
    add_bitstring(bits, "000000000000000000000000000000001000000000000", info);
    add_bitstring(bits, "000000000000000100000000001000000001100000000", info);
    add_bitstring(bits, "000000000000001000100000000000000000000000000", info);
    add_bitstring(bits, "000000000000000000000000000000010000101010000", info);
    add_bitstring(bits, "000000000000000000000000000000000000000000101", info);
    add_bitstring(bits, "100000010000000000011000000010000000000000000", info);
    add_bitstring(bits, "000000010001000010000000000000000000000000000", info);
    add_bitstring(bits, "000000000000000010000000000010000000000010000", info);
    add_bitstring(bits, "000000000000000000000000101000000000000000000", info);
    add_bitstring(bits, "000000000000000010000000000000000010000010000", info);
    add_bitstring(bits, "000000000000000000100000000000000000001000100", info);
    add_bitstring(bits, "000000000000000100000010000000000000000000000", info);
    add_bitstring(bits, "000000010000000000101000000000010000000000000", info);
    add_bitstring(bits, "000000000000001000000110100000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("000000000000001111111111111111111111111000111111111111111111111111111111111111111111111111110111111111111111111111111001111111111111111111111111000000000000000000000", info);
    ts[1] = encrypt_input("000000000000001111111111111111111111111000111111111111111111111111111111111111111111111111110111111111111111111111111001111111111111111111111111000000000000000000000", info);
    ts[2] = encrypt_input("001111111111111111111111111001111111111111111111111111111111111111111111111111111111111111111111111111110011111111111111111111111110111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111110000011111111111111111111111110111111111111111111111111001111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111110011111111111111111111111110011111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111110", info);
    ts[3] = encrypt_input("001111111111111111111111111001111111111111111111111111111111111111111111111111111111111111111111111111110011111111111111111111111110111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111110000011111111111111111111111110111111111111111111111111001111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111110011111111111111111111111110011111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[11];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -17, gk, ss[0]); // __s0 = __v0 >> 17
    info.eval->rotate_rows(vs[0], -7, gk, ss[1]); // __s1 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -38, gk, ss[2]); // __s2 = __v0 >> 38
    info.eval->rotate_rows(vs[0], -1, gk, ss[3]); // __s3 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -27, gk, ss[4]); // __s4 = __v0 >> 27
    info.eval->rotate_rows(vs[0], -13, gk, ss[5]); // __s5 = __v0 >> 13
    info.eval->rotate_rows(vs[0], -5, gk, ss[6]); // __s6 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -21, gk, ss[7]); // __s7 = __v0 >> 21
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -9, gk, ss[8]); // __s8 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -1, gk, ss[9]); // __s9 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -38, gk, ss[10]); // __s10 = __v1 >> 38
    
    // __t4 = blend(__s4@100000000000000000000000000000000000000000000, __s2@000000010001000010000000000000000000000000000, __v0@000000000000001000010000000000000000000000000, __s3@000000000000000000001010000000000000000000000, __s6@000000000000000000000000101010000000000000000, __s1@000000000000000000000000010000100000000000000, __s0@000000000000000000000000000000010000101010000, __s5@000000000000000000000000000000001000000000000, __s7@000000000000000000000000000000000000000000101)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7, t4_8, t4_9;
    info.eval->multiply_plain(ss[4], bits["100000000000000000000000000000000000000000000"], t4_1);
    info.eval->multiply_plain(ss[2], bits["000000010001000010000000000000000000000000000"], t4_2);
    info.eval->multiply_plain(vs[0], bits["000000000000001000010000000000000000000000000"], t4_3);
    info.eval->multiply_plain(ss[3], bits["000000000000000000001010000000000000000000000"], t4_4);
    info.eval->multiply_plain(ss[6], bits["000000000000000000000000101010000000000000000"], t4_5);
    info.eval->multiply_plain(ss[1], bits["000000000000000000000000010000100000000000000"], t4_6);
    info.eval->multiply_plain(ss[0], bits["000000000000000000000000000000010000101010000"], t4_7);
    info.eval->multiply_plain(ss[5], bits["000000000000000000000000000000001000000000000"], t4_8);
    info.eval->multiply_plain(ss[7], bits["000000000000000000000000000000000000000000101"], t4_9);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7, t4_8, t4_9}, ts[4]);
    
    
    // __t5 = blend(__s10@100000000000000000000000011000000000100000000, __s9@000000010000000000001000000000010000001000100, __s8@000000000001001000010010100000101000000000001, __v1@000000000000000010000000000010000000000010000)
    ctxt t5_1, t5_2, t5_3, t5_4;
    info.eval->multiply_plain(ss[10], bits["100000000000000000000000011000000000100000000"], t5_1);
    info.eval->multiply_plain(ss[9], bits["000000010000000000001000000000010000001000100"], t5_2);
    info.eval->multiply_plain(ss[8], bits["000000000001001000010010100000101000000000001"], t5_3);
    info.eval->multiply_plain(vs[1], bits["000000000000000010000000000010000000000010000"], t5_4);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4}, ts[5]);
    
    info.eval->sub(ts[4], ts[5], vs[2]); // __v2 = __t4 - __t5
    
    // __t6 = blend(__s4@100000000000000000000000000000000000000000000, __s2@000000010001000000000000000000000000000000000, __s3@000000000000000100001000000000000000000000000, __v0@000000000000000000110000000000000000000000000, __s1@000000000000000000000100010000100000000000000, __s6@000000000000000000000000000010000000000000000, __s0@000000000000000000000000000000010001000000000, __s5@000000000000000000000000000000001010000000000, __s7@000000000000000000000000000000000000000000001)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7, t6_8, t6_9;
    info.eval->multiply_plain(ss[4], bits["100000000000000000000000000000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[2], bits["000000010001000000000000000000000000000000000"], t6_2);
    info.eval->multiply_plain(ss[3], bits["000000000000000100001000000000000000000000000"], t6_3);
    info.eval->multiply_plain(vs[0], bits["000000000000000000110000000000000000000000000"], t6_4);
    info.eval->multiply_plain(ss[1], bits["000000000000000000000100010000100000000000000"], t6_5);
    info.eval->multiply_plain(ss[6], bits["000000000000000000000000000010000000000000000"], t6_6);
    info.eval->multiply_plain(ss[0], bits["000000000000000000000000000000010001000000000"], t6_7);
    info.eval->multiply_plain(ss[5], bits["000000000000000000000000000000001010000000000"], t6_8);
    info.eval->multiply_plain(ss[7], bits["000000000000000000000000000000000000000000001"], t6_9);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7, t6_8, t6_9}, ts[6]);
    
    
    // __t7 = blend(__s10@100000000000000100000000010000000001000000000, __s9@000000010000000000101000000000010000000000000, __s8@000000000001000000010100000000101000000000001, __v1@000000000000000000000000000010000010000000000)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(ss[10], bits["100000000000000100000000010000000001000000000"], t7_1);
    info.eval->multiply_plain(ss[9], bits["000000010000000000101000000000010000000000000"], t7_2);
    info.eval->multiply_plain(ss[8], bits["000000000001000000010100000000101000000000001"], t7_3);
    info.eval->multiply_plain(vs[1], bits["000000000000000000000000000010000010000000000"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4}, ts[7]);
    
    info.eval->sub(ts[6], ts[7], vs[3]); // __v3 = __t6 - __t7
    
    // __t8 = blend(__v2@100000010000000000011000000010000000000000000, __v3@000000000001000000000000010000111000000000001)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[2], bits["100000010000000000011000000010000000000000000"], t8_1);
    info.eval->multiply_plain(vs[3], bits["000000000001000000000000010000111000000000001"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v3@100000010000000000011000000010000000000000000, __v2@000000000001000000000000010000111000000000001)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[3], bits["100000010000000000011000000010000000000000000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["000000000001000000000000010000111000000000001"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t10 = blend(__v0@000000000000001000100000000000000000000000000, __s3@000000000000000100000010000000000000000000000, __s2@000000000000000010000000000000000000000000000, __s1@000000000000000000000100000000000000000000000, __s6@000000000000000000000000101000000000000000000, __s5@000000000000000000000000000000000010000000000, __s0@000000000000000000000000000000000001101010000, __s7@000000000000000000000000000000000000000000100)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5, t10_6, t10_7, t10_8;
    info.eval->multiply_plain(vs[0], bits["000000000000001000100000000000000000000000000"], t10_1);
    info.eval->multiply_plain(ss[3], bits["000000000000000100000010000000000000000000000"], t10_2);
    info.eval->multiply_plain(ss[2], bits["000000000000000010000000000000000000000000000"], t10_3);
    info.eval->multiply_plain(ss[1], bits["000000000000000000000100000000000000000000000"], t10_4);
    info.eval->multiply_plain(ss[6], bits["000000000000000000000000101000000000000000000"], t10_5);
    info.eval->multiply_plain(ss[5], bits["000000000000000000000000000000000010000000000"], t10_6);
    info.eval->multiply_plain(ss[0], bits["000000000000000000000000000000000001101010000"], t10_7);
    info.eval->multiply_plain(ss[7], bits["000000000000000000000000000000000000000000100"], t10_8);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5, t10_6, t10_7, t10_8}, ts[10]);
    
    
    // __t11 = blend(__s8@000000000000001000000110100000000000000000000, __s10@000000000000000100000000001000000001100000000, __v1@000000000000000010000000000000000010000010000, __s9@000000000000000000100000000000000000001000100)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(ss[8], bits["000000000000001000000110100000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[10], bits["000000000000000100000000001000000001100000000"], t11_2);
    info.eval->multiply_plain(vs[1], bits["000000000000000010000000000000000010000010000"], t11_3);
    info.eval->multiply_plain(ss[9], bits["000000000000000000100000000000000000001000100"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->sub(ts[10], ts[11], vs[5]); // __v5 = __t10 - __t11
    
    // __t12 = blend(__v5@000000000000001100100110101000000011000010100, __v2@000000000000000010000000000000000000101000000)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[5], bits["000000000000001100100110101000000011000010100"], t12_1);
    info.eval->multiply_plain(vs[2], bits["000000000000000010000000000000000000101000000"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__v2@000000000000001000000010101000000000000010100, __v3@000000000000000100100100000000000011000000000, __v5@000000000000000010000000000000000000101000000)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(vs[2], bits["000000000000001000000010101000000000000010100"], t13_1);
    info.eval->multiply_plain(vs[3], bits["000000000000000100100100000000000011000000000"], t13_2);
    info.eval->multiply_plain(vs[5], bits["000000000000000010000000000000000000101000000"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[6]); // __v6 = __t12 * __t13
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    