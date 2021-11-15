
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000100010000000", info);
    add_bitstring(bits, "100000000000100000", info);
    add_bitstring(bits, "010000010000010000", info);
    add_bitstring(bits, "000000110000010000", info);
    add_bitstring(bits, "000000100000000000", info);
    add_bitstring(bits, "000000000010000000", info);
    add_bitstring(bits, "100000110000110000", info);
    add_bitstring(bits, "010000000000000000", info);
    add_bitstring(bits, "110000000000100000", info);
    add_bitstring(bits, "010010110000010010", info);
    add_bitstring(bits, "000010000000000010", info);
    add_bitstring(bits, "100000000010100000", info);
    add_bitstring(bits, "100010000000100010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(15);
    ts[0] = encrypt_input("110111111111011111101101011111110111111111011111111101011110110111111111011111111101011110", info);
    ts[2] = encrypt_input("111100001101001111100011011011111000110110", info);
    ts[4] = encrypt_input("000011110000001111100000111100", info);
    ts[7] = encrypt_input("000011111000001111000000111110", info);
    ts[12] = encrypt_input("000011111000001111100000111110", info);
    ts[13] = encrypt_input("111101111000111100111111111100111110111111111100111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[6];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -16, gk, ss[0]); // __s0 = __v0 >> 16
    info.eval->rotate_rows(vs[0], -14, gk, ss[1]); // __s1 = __v0 >> 14
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[2]); // __s2 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -4, gk, ss[3]); // __s3 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -14, gk, ss[4]); // __s4 = __v1 >> 14
    info.eval->rotate_rows(vs[1], -15, gk, ss[5]); // __s5 = __v1 >> 15
    
    // __t5 = blend(__v0@100000000000100000, __s0@010000000000000000, __s1@000000110000010000, __t4@000010000010000010)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(vs[0], bits["100000000000100000"], t5_1);
    info.eval->multiply_plain(ss[0], bits["010000000000000000"], t5_2);
    info.eval->multiply_plain(ss[1], bits["000000110000010000"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3, ts[4]}, ts[5]);
    
    
    // __t6 = blend(__v1@100010000000100010, __s5@010000010000010000, __s4@000000100000000000, __s3@000000000010000000)
    ctxt t6_1, t6_2, t6_3, t6_4;
    info.eval->multiply_plain(vs[1], bits["100010000000100010"], t6_1);
    info.eval->multiply_plain(ss[5], bits["010000010000010000"], t6_2);
    info.eval->multiply_plain(ss[4], bits["000000100000000000"], t6_3);
    info.eval->multiply_plain(ss[3], bits["000000000010000000"], t6_4);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4}, ts[6]);
    
    info.eval->multiply(ts[5], ts[6], vs[2]); // __v2 = __t5 * __t6
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t8 = blend(__s1@110000000000100000, __v0@000000110000010000, __t7@000010000010000010)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(ss[1], bits["110000000000100000"], t8_1);
    info.eval->multiply_plain(vs[0], bits["000000110000010000"], t8_2);
    info.eval->add_many({t8_1, t8_2, ts[7]}, ts[8]);
    
    
    // __t9 = blend(__s4@100000000000100000, __s2@010000010000010000, __s3@000010000000000010, __v1@000000100010000000)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[4], bits["100000000000100000"], t9_1);
    info.eval->multiply_plain(ss[2], bits["010000010000010000"], t9_2);
    info.eval->multiply_plain(ss[3], bits["000010000000000010"], t9_3);
    info.eval->multiply_plain(vs[1], bits["000000100010000000"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t10 = blend(__v3@100000000010100000, __v2@010010110000010010)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[3], bits["100000000010100000"], t10_1);
    info.eval->multiply_plain(vs[2], bits["010010110000010010"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__v2@100000000010100000, __v3@010010110000010010)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(vs[2], bits["100000000010100000"], t11_1);
    info.eval->multiply_plain(vs[3], bits["010010110000010010"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->add(ts[00], ts[01], vs[4]); // __v4 = __t00 + __t01
    
    // __t14 = blend(__s0@100000110000110000, __v0@010000000000000000, __t02@000010000010000010)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(ss[0], bits["100000110000110000"], t14_1);
    info.eval->multiply_plain(vs[0], bits["010000000000000000"], t14_2);
    info.eval->add_many({t14_1, t14_2, ts[02]}, ts[14]);
    
    info.eval->multiply(ts[04], ts[03], vs[5]); // __v5 = __t04 * __t03
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->add(vs[4], vs[5], vs[6]); // __v6 = __v4 + __v5
    return vs[6];
}
    