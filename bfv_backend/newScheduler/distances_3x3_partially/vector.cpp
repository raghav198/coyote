
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00010101000", info);
    add_bitstring(bits, "00001001001", info);
    add_bitstring(bits, "00100100100", info);
    add_bitstring(bits, "00110010001", info);
    add_bitstring(bits, "10010010000", info);
    add_bitstring(bits, "10101000000", info);
    add_bitstring(bits, "10001101100", info);
    add_bitstring(bits, "00000010101", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("00111111111111111111111111111110011111111111111111111111111111001111111111111111111111111111000", info);
    ts[1] = encrypt_input("00111111111111111111111111111110011111111111111111111111111111001111111111111111111111111111000", info);
    ts[2] = encrypt_input("00000011111111111111111111111111111011111111111111111111111111110011111111111111111111111111111", info);
    ts[3] = encrypt_input("00000011111111111111111111111111111011111111111111111111111111110011111111111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[5];
    ctxt ss[4];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -9, gk, ss[0]); // __s0 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -2, gk, ss[1]); // __s1 = __v0 >> 2
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -8, gk, ss[2]); // __s2 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -5, gk, ss[3]); // __s3 = __v1 >> 5
    
    // __t4 = blend(__s0@10010010000, __v0@00100100100, __s1@00001001001)
    ctxt t4_1, t4_2, t4_3;
    info.eval->multiply_plain(ss[0], bits["10010010000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["00100100100"], t4_2);
    info.eval->multiply_plain(ss[1], bits["00001001001"], t4_3);
    info.eval->add_many({t4_1, t4_2, t4_3}, ts[4]);
    
    
    // __t5 = blend(__s3@10101000000, __s2@00010101000, __v1@00000010101)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(ss[3], bits["10101000000"], t5_1);
    info.eval->multiply_plain(ss[2], bits["00010101000"], t5_2);
    info.eval->multiply_plain(vs[1], bits["00000010101"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    info.eval->sub(ts[4], ts[5], vs[2]); // __v2 = __t4 - __t5
    
    // __t6 = blend(__s0@10010010000, __v0@00100100100, __s1@00001001001)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(ss[0], bits["10010010000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["00100100100"], t6_2);
    info.eval->multiply_plain(ss[1], bits["00001001001"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    
    // __t7 = blend(__s3@10101000000, __s2@00010101000, __v1@00000010101)
    ctxt t7_1, t7_2, t7_3;
    info.eval->multiply_plain(ss[3], bits["10101000000"], t7_1);
    info.eval->multiply_plain(ss[2], bits["00010101000"], t7_2);
    info.eval->multiply_plain(vs[1], bits["00000010101"], t7_3);
    info.eval->add_many({t7_1, t7_2, t7_3}, ts[7]);
    
    info.eval->sub(ts[6], ts[7], vs[3]); // __v3 = __t6 - __t7
    
    // __t8 = blend(__v2@10001101100, __v3@00110010001)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[2], bits["10001101100"], t8_1);
    info.eval->multiply_plain(vs[3], bits["00110010001"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v3@10001101100, __v2@00110010001)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[3], bits["10001101100"], t9_1);
    info.eval->multiply_plain(vs[2], bits["00110010001"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    return vs[4];
}
    