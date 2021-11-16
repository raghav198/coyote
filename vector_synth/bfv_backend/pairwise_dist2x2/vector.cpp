
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "1110110000", info);
    add_bitstring(bits, "0100010000", info);
    add_bitstring(bits, "0001000100", info);
    add_bitstring(bits, "1100110000", info);
    add_bitstring(bits, "1000100000", info);
    add_bitstring(bits, "0010001000", info);
    add_bitstring(bits, "0001001100", info);
    add_bitstring(bits, "0010000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("11111011111011111011111000", info);
    ts[2] = encrypt_input("00111110111110111110111110", info);
    ts[4] = encrypt_input("01100001110000", info);
    ts[6] = encrypt_input("00011000011100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[5];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -8, gk, ss[0]); // __s0 = __v0 >> 8
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -8, gk, ss[1]); // __s1 = __v1 >> 8
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -9, gk, ss[2]); // __s2 = __v2 >> 9
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -9, gk, ss[3]); // __s3 = __v3 >> 9
    
    // __t8 = blend(__s0@1100110000, __s1@0010000000, __v1@0001001100)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(ss[0], bits["1100110000"], t8_1);
    info.eval->multiply_plain(ss[1], bits["0010000000"], t8_2);
    info.eval->multiply_plain(vs[1], bits["0001001100"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3}, ts[8]);
    
    
    // __t9 = blend(__s2@1000100000, __v2@0100010000, __s3@0010001000, __v3@0001000100)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[2], bits["1000100000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["0100010000"], t9_2);
    info.eval->multiply_plain(ss[3], bits["0010001000"], t9_3);
    info.eval->multiply_plain(vs[3], bits["0001000100"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[4]); // __v4 = __t8 - __t9
    
    // __t10 = blend(__v0@1100110000, __v1@0010000000, __s1@0001001100)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[0], bits["1100110000"], t10_1);
    info.eval->multiply_plain(vs[1], bits["0010000000"], t10_2);
    info.eval->multiply_plain(ss[1], bits["0001001100"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    info.eval->sub(ts[10], ts[9], vs[5]); // __v5 = __t10 - __t9
    
    // __t12 = blend(__v5@1110110000, __v4@0001001100)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[5], bits["1110110000"], t12_1);
    info.eval->multiply_plain(vs[4], bits["0001001100"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__v4@1110110000, __v5@0001001100)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[4], bits["1110110000"], t13_1);
    info.eval->multiply_plain(vs[5], bits["0001001100"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[6]); // __v6 = __t12 * __t13
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -8, gk, ss[4]); // __s4 = __v6 >> 8
    info.eval->add(vs[6], ss[4], vs[7]); // __v7 = __v6 + __s4
    return vs[7];
}
    