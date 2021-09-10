
#include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00100000", info);
    add_bitstring(bits, "00010000", info);
    add_bitstring(bits, "00000001", info);
    add_bitstring(bits, "00110000", info);
    add_bitstring(bits, "00100011", info);
    add_bitstring(bits, "00010010", info);
    add_bitstring(bits, "00000010", info);
    add_bitstring(bits, "00100001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("1111111110110111101111110111111101011010", info);
    ts[1] = encrypt_input("1111111110110111101111110111111101011010", info);
    ts[2] = encrypt_input("1111011010110101111111111111101101111011", info);
    ts[3] = encrypt_input("1111011010110101111111111111101101111011", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[11];

    vs[0] = ts[0];
    vs[1] = ts[2];
    info.eval->rotate_rows(vs[0], -4, gk, ss[0]); // __s0 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -2, gk, ss[1]); // __s1 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -3, gk, ss[2]); // __s2 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -1, gk, ss[3]); // __s3 = __v0 >> 1
    info.eval->rotate_rows(vs[1], -5, gk, ss[4]); // __s4 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -6, gk, ss[5]); // __s5 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -4, gk, ss[6]); // __s6 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -7, gk, ss[7]); // __s7 = __v1 >> 7

    // __t4 = blend(__s1@00100001, __s0@00010010)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(ss[1], bits["00100001"], t4_1);
    info.eval->multiply_plain(ss[0], bits["00010010"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);

    // __t5 = blend(__s4@00110000, __s5@00000010, __s6@00000001)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(ss[4], bits["00110000"], t5_1);
    info.eval->multiply_plain(ss[5], bits["00000010"], t5_2);
    info.eval->multiply_plain(ss[6], bits["00000001"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);

    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);

    // __t6 = blend(__s3@00100000, __v0@00010010, __s2@00000001)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(ss[3], bits["00100000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["00010010"], t6_2);
    info.eval->multiply_plain(ss[2], bits["00000001"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);

    // __t7 = blend(__v1@00100001, __s7@00010000, __s4@00000010)
    ctxt t7_1, t7_2, t7_3;
    info.eval->multiply_plain(vs[1], bits["00100001"], t7_1);
    info.eval->multiply_plain(ss[7], bits["00010000"], t7_2);
    info.eval->multiply_plain(ss[4], bits["00000010"], t7_3);
    info.eval->add_many({t7_1, t7_2, t7_3}, ts[7]);

    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);

    // __t8 = blend(__v3@00100011, __v2@00010000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[3], bits["00100011"], t8_1);
    info.eval->multiply_plain(vs[2], bits["00010000"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);

    // __t9 = blend(__v2@00100011, __v3@00010000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[2], bits["00100011"], t9_1);
    info.eval->multiply_plain(vs[3], bits["00010000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);

    info.eval->add(ts[8], ts[9], vs[4]);           // __v4 = __t8 + __t9
    info.eval->rotate_rows(vs[4], -7, gk, ss[8]);  // __s8 = __v4 >> 7
    info.eval->rotate_rows(vs[4], -3, gk, ss[9]);  // __s9 = __v4 >> 3
    info.eval->rotate_rows(vs[4], -4, gk, ss[10]); // __s10 = __v4 >> 4
    info.eval->multiply(vs[4], ss[8], vs[5]);      // __v5 = __v4 * __s8
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->multiply(ss[10], ss[9], vs[6]); // __v6 = __s10 * __s9
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->add(vs[6], vs[5], vs[7]); // __v7 = __v6 + __v5
    return vs[7];
}
