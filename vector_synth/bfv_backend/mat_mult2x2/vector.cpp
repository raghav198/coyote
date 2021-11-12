
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "1000100", info);
    add_bitstring(bits, "0001100", info);
    add_bitstring(bits, "0000100", info);
    add_bitstring(bits, "1010000", info);
    add_bitstring(bits, "1000000", info);
    add_bitstring(bits, "0001000", info);
    add_bitstring(bits, "0010000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("11011110100001111011111", info);
    ts[1] = encrypt_input("11011110100001111011111", info);
    ts[2] = encrypt_input("00110101111001101111111", info);
    ts[3] = encrypt_input("00110101111001101111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[5];
    ctxt ss[10];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -1, gk, ss[1]); // __s1 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -6, gk, ss[2]); // __s2 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -5, gk, ss[3]); // __s3 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -4, gk, ss[4]); // __s4 = __v0 >> 4
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[5]); // __s5 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -5, gk, ss[6]); // __s6 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -4, gk, ss[7]); // __s7 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -6, gk, ss[8]); // __s8 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -3, gk, ss[9]); // __s9 = __v1 >> 3
    
    // __t4 = blend(__s2@1000000, __s1@0010000, __s4@0001000, __s3@0000100)
    ctxt t4_1, t4_2, t4_3, t4_4;
    info.eval->multiply_plain(ss[2], bits["1000000"], t4_1);
    info.eval->multiply_plain(ss[1], bits["0010000"], t4_2);
    info.eval->multiply_plain(ss[4], bits["0001000"], t4_3);
    info.eval->multiply_plain(ss[3], bits["0000100"], t4_4);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4}, ts[4]);
    
    
    // __t5 = blend(__s6@1000100, __s7@0010000, __v1@0001000)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(ss[6], bits["1000100"], t5_1);
    info.eval->multiply_plain(ss[7], bits["0010000"], t5_2);
    info.eval->multiply_plain(vs[1], bits["0001000"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__v0@1000000, __s0@0010000, __s3@0001000, __s2@0000100)
    ctxt t6_1, t6_2, t6_3, t6_4;
    info.eval->multiply_plain(vs[0], bits["1000000"], t6_1);
    info.eval->multiply_plain(ss[0], bits["0010000"], t6_2);
    info.eval->multiply_plain(ss[3], bits["0001000"], t6_3);
    info.eval->multiply_plain(ss[2], bits["0000100"], t6_4);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4}, ts[6]);
    
    
    // __t7 = blend(__s7@1000000, __s9@0010000, __s5@0001000, __s8@0000100)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(ss[7], bits["1000000"], t7_1);
    info.eval->multiply_plain(ss[9], bits["0010000"], t7_2);
    info.eval->multiply_plain(ss[5], bits["0001000"], t7_3);
    info.eval->multiply_plain(ss[8], bits["0000100"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__v2@1010000, __v3@0001100)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[2], bits["1010000"], t8_1);
    info.eval->multiply_plain(vs[3], bits["0001100"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v3@1010000, __v2@0001100)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[3], bits["1010000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["0001100"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    return vs[4];
}
    