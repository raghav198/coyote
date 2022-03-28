#include "util.hpp"

ptxt encode_bits(std::string bitstring, RuntimeContext &info)
{
    std::vector<int64_t> vals(info.batcher->slot_count());
    for (int i = 0; i < bitstring.length(); i++)
    {
        vals[i] = bitstring[i] - '0';
    }
    ptxt dest;
    info.batcher->encode(vals, dest);
    return dest;
}

ctxt encrypt_input(std::string bitstring, RuntimeContext &info)
{
    ptxt encoded = encode_bits(bitstring, info);
    ctxt encrypted;
    info.enc->encrypt(encoded, encrypted);
    return encrypted;
}

void add_bitstring(std::map<std::string, ptxt> &bits, std::string bitstring, RuntimeContext &info)
{
    ptxt encoded = encode_bits(bitstring, info);
    bits[bitstring] = encoded;
}