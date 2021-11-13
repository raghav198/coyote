
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000010", info);
    add_bitstring(bits, "10101000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("1101011011110101101111110111111111011111", info);
    ts[1] = encrypt_input("1101011011110101101111110111111111011111", info);
    ts[2] = encrypt_input("1101011110110111111111010111101101111111", info);
    ts[3] = encrypt_input("1101011110110111111111010111101101111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[5];
    ctxt ss[2];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -7, gk, ss[0]); // __s0 = __v0 >> 7
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -7, gk, ss[1]); // __s1 = __v1 >> 7
    
    // __t4 = blend(__v0@10101000, __s0@00000010)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[0], bits["10101000"], t4_1);
    info.eval->multiply_plain(ss[0], bits["00000010"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__v1@10101000, __s1@00000010)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(vs[1], bits["10101000"], t5_1);
    info.eval->multiply_plain(ss[1], bits["00000010"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__s0@10101000, __v0@00000010)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(ss[0], bits["10101000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["00000010"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    
    // __t7 = blend(__s1@10101000, __v1@00000010)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[1], bits["10101000"], t7_1);
    info.eval->multiply_plain(vs[1], bits["00000010"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__v2@10101000, __v3@00000010)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[2], bits["10101000"], t8_1);
    info.eval->multiply_plain(vs[3], bits["00000010"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v3@10101000, __v2@00000010)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[3], bits["10101000"], t9_1);
    info.eval->multiply_plain(vs[2], bits["00000010"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    return vs[4];
}
    