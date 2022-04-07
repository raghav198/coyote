
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000001000000000010010000000", info);
    add_bitstring(bits, "000000000000100000001011000", info);
    add_bitstring(bits, "000000100000000000000000000", info);
    add_bitstring(bits, "010000000000000000000000000", info);
    add_bitstring(bits, "100000000000001000000000000", info);
    add_bitstring(bits, "000001000010100000001011000", info);
    add_bitstring(bits, "110000010000001000110100000", info);
    add_bitstring(bits, "000000000110000000000000000", info);
    add_bitstring(bits, "000000100000000010010000000", info);
    add_bitstring(bits, "000001000010000000000000000", info);
    add_bitstring(bits, "010000000000000000100000000", info);
    add_bitstring(bits, "100000000000001010011101000", info);
    add_bitstring(bits, "000000000000100000000010000", info);
    add_bitstring(bits, "000000100000000010000000000", info);
    add_bitstring(bits, "000000000100000000001001000", info);
    add_bitstring(bits, "000001100000000000000000000", info);
    add_bitstring(bits, "010000010100000000100000000", info);
    add_bitstring(bits, "000000000010000000001001000", info);
    add_bitstring(bits, "000000000000000000000100000", info);
    add_bitstring(bits, "000000010000000000100100000", info);
    add_bitstring(bits, "100000000100001000010100000", info);
    add_bitstring(bits, "010000000000100000100010000", info);
    add_bitstring(bits, "000001010010000000000000000", info);
    add_bitstring(bits, "000000010000000000100000000", info);
    add_bitstring(bits, "000000000000000010000000000", info);
    add_bitstring(bits, "100001010010001010011101000", info);
    add_bitstring(bits, "110000000000001000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(12);
    ts[0] = encrypt_input("000000000111111111111111111111111111111111111111111111111110000000001111111111111111111111110001111111111111111111111111000", info);
    ts[1] = encrypt_input("000000000111111111111111111111111111111111111111111111111110000000001111111111111111111111110001111111111111111111111111000", info);
    ts[2] = encrypt_input("111111111111111111111111111111111111111111111111111111111111111111111111110000011111111111111111111111101111111111111111111111111111111111111111111111111100111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111100111111111111111111111111011111111111111111111111100111111111111111111111111101111111111111111111111111011111111111111111111111111111111111111111111111111", info);
    ts[3] = encrypt_input("111111111111111111111111111111111111111111111111111111111111111111111111110000011111111111111111111111101111111111111111111111111111111111111111111111111100111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111100111111111111111111111111011111111111111111111111100111111111111111111111111101111111111111111111111111011111111111111111111111111111111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[6];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -25, gk, ss[0]); // __s0 = __v0 >> 25
    info.eval->rotate_rows(vs[0], -18, gk, ss[1]); // __s1 = __v0 >> 18
    info.eval->rotate_rows(vs[0], -23, gk, ss[2]); // __s2 = __v0 >> 23
    info.eval->rotate_rows(vs[0], -2, gk, ss[3]); // __s3 = __v0 >> 2
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -4, gk, ss[4]); // __s4 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -24, gk, ss[5]); // __s5 = __v1 >> 24
    
    // __t4 = blend(__s1@100000000000001000000000000, __s2@000000100000000010010000000, __v0@000000000100000000001001000, __s3@000000000000100000000010000, __s0@000000000000000000000100000)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5;
    info.eval->multiply_plain(ss[1], bits["100000000000001000000000000"], t4_1);
    info.eval->multiply_plain(ss[2], bits["000000100000000010010000000"], t4_2);
    info.eval->multiply_plain(vs[0], bits["000000000100000000001001000"], t4_3);
    info.eval->multiply_plain(ss[3], bits["000000000000100000000010000"], t4_4);
    info.eval->multiply_plain(ss[0], bits["000000000000000000000100000"], t4_5);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5}, ts[4]);
    
    
    // __t5 = blend(__v1@100000000100001000010100000, __s4@000000100000000010000000000, __s5@000000000000100000001011000)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(vs[1], bits["100000000100001000010100000"], t5_1);
    info.eval->multiply_plain(ss[4], bits["000000100000000010000000000"], t5_2);
    info.eval->multiply_plain(ss[5], bits["000000000000100000001011000"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    info.eval->sub(ts[4], ts[5], vs[2]); // __v2 = __t4 - __t5
    
    // __t6 = blend(__s1@010000000000000000000000000, __s2@000001100000000000000000000, __s0@000000010000000000100000000, __v0@000000000110000000000000000)
    ctxt t6_1, t6_2, t6_3, t6_4;
    info.eval->multiply_plain(ss[1], bits["010000000000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[2], bits["000001100000000000000000000"], t6_2);
    info.eval->multiply_plain(ss[0], bits["000000010000000000100000000"], t6_3);
    info.eval->multiply_plain(vs[0], bits["000000000110000000000000000"], t6_4);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4}, ts[6]);
    
    
    // __t7 = blend(__v1@010000010100000000100000000, __s5@000001000010000000000000000, __s4@000000100000000000000000000)
    ctxt t7_1, t7_2, t7_3;
    info.eval->multiply_plain(vs[1], bits["010000010100000000100000000"], t7_1);
    info.eval->multiply_plain(ss[5], bits["000001000010000000000000000"], t7_2);
    info.eval->multiply_plain(ss[4], bits["000000100000000000000000000"], t7_3);
    info.eval->add_many({t7_1, t7_2, t7_3}, ts[7]);
    
    info.eval->sub(ts[6], ts[7], vs[3]); // __v3 = __t6 - __t7
    info.eval->multiply(vs[2], vs[3], vs[4]); // __v4 = __v2 * __v3
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t8 = blend(__s1@110000000000001000000000000, __s2@000001000000000010010000000, __s0@000000010000000000100100000, __v0@000000000010000000001001000, __s3@000000000000100000000010000)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5;
    info.eval->multiply_plain(ss[1], bits["110000000000001000000000000"], t8_1);
    info.eval->multiply_plain(ss[2], bits["000001000000000010010000000"], t8_2);
    info.eval->multiply_plain(ss[0], bits["000000010000000000100100000"], t8_3);
    info.eval->multiply_plain(vs[0], bits["000000000010000000001001000"], t8_4);
    info.eval->multiply_plain(ss[3], bits["000000000000100000000010000"], t8_5);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5}, ts[8]);
    
    
    // __t9 = blend(__v1@110000010000001000110100000, __s5@000001000010100000001011000, __s4@000000000000000010000000000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(vs[1], bits["110000010000001000110100000"], t9_1);
    info.eval->multiply_plain(ss[5], bits["000001000010100000001011000"], t9_2);
    info.eval->multiply_plain(ss[4], bits["000000000000000010000000000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[5]); // __v5 = __t8 - __t9
    
    // __t10 = blend(__v2@100000000000001010011101000, __v5@010000000000100000100010000, __v3@000001010010000000000000000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[2], bits["100000000000001010011101000"], t10_1);
    info.eval->multiply_plain(vs[5], bits["010000000000100000100010000"], t10_2);
    info.eval->multiply_plain(vs[3], bits["000001010010000000000000000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__v5@100001010010001010011101000, __v3@010000000000000000100000000, __v2@000000000000100000000010000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[5], bits["100001010010001010011101000"], t11_1);
    info.eval->multiply_plain(vs[3], bits["010000000000000000100000000"], t11_2);
    info.eval->multiply_plain(vs[2], bits["000000000000100000000010000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[6]); // __v6 = __t10 * __t11
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    