
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "01000100010", info);
    add_bitstring(bits, "10000010101", info);
    add_bitstring(bits, "00001110000", info);
    add_bitstring(bits, "10100000000", info);
    add_bitstring(bits, "00000000111", info);
    add_bitstring(bits, "00100010001", info);
    add_bitstring(bits, "00000100010", info);
    add_bitstring(bits, "00000000100", info);
    add_bitstring(bits, "10001000000", info);
    add_bitstring(bits, "11100000000", info);
    add_bitstring(bits, "00101100010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("11111111111111111111111111110111111111111111111111111111111111111111111111111111111111100000000", info);
    ts[1] = encrypt_input("11111111111111111111111111110111111111111111111111111111111111111111111111111111111111100000000", info);
    ts[2] = encrypt_input("01111111111111111111111111111000011111111111111111111111111111000111111111111111111111111111110", info);
    ts[3] = encrypt_input("01111111111111111111111111111000011111111111111111111111111111000111111111111111111111111111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[5];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -8, gk, ss[0]); // __s0 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -4, gk, ss[1]); // __s1 = __v0 >> 4
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[2]); // __s2 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -7, gk, ss[3]); // __s3 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -6, gk, ss[4]); // __s4 = __v1 >> 6
    info.eval->sub(vs[0], vs[1], vs[2]); // __v2 = __v0 - __v1
    
    // __t4 = blend(__v0@11100000000, __s1@00001110000, __s0@00000000111)
    ctxt t4_1, t4_2, t4_3;
    info.eval->multiply_plain(vs[0], bits["11100000000"], t4_1);
    info.eval->multiply_plain(ss[1], bits["00001110000"], t4_2);
    info.eval->multiply_plain(ss[0], bits["00000000111"], t4_3);
    info.eval->add_many({t4_1, t4_2, t4_3}, ts[4]);
    
    
    // __t5 = blend(__s4@10001000000, __v1@01000100010, __s2@00100010001, __s3@00000000100)
    ctxt t5_1, t5_2, t5_3, t5_4;
    info.eval->multiply_plain(ss[4], bits["10001000000"], t5_1);
    info.eval->multiply_plain(vs[1], bits["01000100010"], t5_2);
    info.eval->multiply_plain(ss[2], bits["00100010001"], t5_3);
    info.eval->multiply_plain(ss[3], bits["00000000100"], t5_4);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4}, ts[5]);
    
    info.eval->sub(ts[4], ts[5], vs[3]); // __v3 = __t4 - __t5
    info.eval->multiply(vs[3], vs[2], vs[4]); // __v4 = __v3 * __v2
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t6 = blend(__v0@10100000000, __s1@00001110000, __s0@00000000111)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(vs[0], bits["10100000000"], t6_1);
    info.eval->multiply_plain(ss[1], bits["00001110000"], t6_2);
    info.eval->multiply_plain(ss[0], bits["00000000111"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    
    // __t7 = blend(__s4@10001000000, __s2@00100010001, __v1@00000100010, __s3@00000000100)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(ss[4], bits["10001000000"], t7_1);
    info.eval->multiply_plain(ss[2], bits["00100010001"], t7_2);
    info.eval->multiply_plain(vs[1], bits["00000100010"], t7_3);
    info.eval->multiply_plain(ss[3], bits["00000000100"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4}, ts[7]);
    
    info.eval->sub(ts[6], ts[7], vs[5]); // __v5 = __t6 - __t7
    
    // __t8 = blend(__v3@10000010101, __v5@00101100010)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[3], bits["10000010101"], t8_1);
    info.eval->multiply_plain(vs[5], bits["00101100010"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v5@10000010101, __v3@00101100010)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[5], bits["10000010101"], t9_1);
    info.eval->multiply_plain(vs[3], bits["00101100010"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[6]); // __v6 = __t8 * __t9
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    