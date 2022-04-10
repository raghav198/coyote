
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000100010010", info);
    add_bitstring(bits, "00000100001010", info);
    add_bitstring(bits, "00000000000001", info);
    add_bitstring(bits, "00000000010000", info);
    add_bitstring(bits, "00000000001000", info);
    add_bitstring(bits, "00000010001001", info);
    add_bitstring(bits, "00000010000001", info);
    add_bitstring(bits, "10001001000000", info);
    add_bitstring(bits, "10000010000000", info);
    add_bitstring(bits, "00000001000000", info);
    add_bitstring(bits, "00001001000000", info);
    add_bitstring(bits, "10000110001010", info);
    add_bitstring(bits, "10000000000000", info);
    add_bitstring(bits, "00000000010001", info);
    add_bitstring(bits, "00001000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(11);
    ts[0] = encrypt_input("00000011111111111111111111111110001111111111111111111111110001111111111111111111111111", info);
    ts[1] = encrypt_input("00000011111111111111111111111110001111111111111111111111110001111111111111111111111111", info);
    ts[2] = encrypt_input("11111111111111111111111110001111111111111111111111110111111111111111111111111111111111111111111111111101111111111111111111111111011111111111111111111111111111111111111111111111111011111111111111111111111101111111111111111111111111", info);
    ts[3] = encrypt_input("11111111111111111111111110001111111111111111111111110111111111111111111111111111111111111111111111111101111111111111111111111111011111111111111111111111111111111111111111111111111011111111111111111111111101111111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[2];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -8, gk, ss[0]); // __s0 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -13, gk, ss[1]); // __s1 = __v0 >> 13
    vs[1] = ts[2]; // vector load instr
    
    // __t4 = blend(__s0@10001001000000, __v0@00000010000001)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(ss[0], bits["10001001000000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["00000010000001"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    info.eval->sub(ts[4], vs[1], vs[2]); // __v2 = __t4 - __v1
    
    // __t5 = blend(__s0@00001001000000, __s1@00000100010010, __v0@00000000001000)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(ss[0], bits["00001001000000"], t5_1);
    info.eval->multiply_plain(ss[1], bits["00000100010010"], t5_2);
    info.eval->multiply_plain(vs[0], bits["00000000001000"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    info.eval->sub(ts[5], vs[1], vs[3]); // __v3 = __t5 - __v1
    
    // __t6 = blend(__v2@00001000000000, __v3@00000001000000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[2], bits["00001000000000"], t6_1);
    info.eval->multiply_plain(vs[3], bits["00000001000000"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    
    // __t7 = blend(__v3@00001000000000, __v2@00000001000000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[3], bits["00001000000000"], t7_1);
    info.eval->multiply_plain(vs[2], bits["00000001000000"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[4]); // __v4 = __t6 * __t7
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t8 = blend(__s0@10000000000000, __s1@00000100010010, __v0@00000010001001)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(ss[0], bits["10000000000000"], t8_1);
    info.eval->multiply_plain(ss[1], bits["00000100010010"], t8_2);
    info.eval->multiply_plain(vs[0], bits["00000010001001"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3}, ts[8]);
    
    info.eval->sub(ts[8], vs[1], vs[5]); // __v5 = __t8 - __v1
    
    // __t9 = blend(__v2@10000010000000, __v3@00000100001010, __v5@00000000010001)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(vs[2], bits["10000010000000"], t9_1);
    info.eval->multiply_plain(vs[3], bits["00000100001010"], t9_2);
    info.eval->multiply_plain(vs[5], bits["00000000010001"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    
    // __t10 = blend(__v5@10000110001010, __v3@00000000010000, __v2@00000000000001)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[5], bits["10000110001010"], t10_1);
    info.eval->multiply_plain(vs[3], bits["00000000010000"], t10_2);
    info.eval->multiply_plain(vs[2], bits["00000000000001"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    info.eval->multiply(ts[9], ts[10], vs[6]); // __v6 = __t9 * __t10
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    