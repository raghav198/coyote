#include "util.hpp"

#include <map>

struct ScalarProgram
{
    int num_registers();
    std::vector<std::string> vars_used();
    std::vector<ctxt> computation(std::map<std::string, ctxt> locs, RuntimeContext &info);
    void run(RuntimeContext &info)
    {
        std::string alphabet = "abcdefghijklmnopqrstuvwxyz";

        std::map<std::string, ctxt> locs;
        for (std::string c : vars_used())
        {
            ptxt dest_p;
            std::vector<int64_t> vals(info.batcher->slot_count());
            vals[0] = 1;
            info.batcher->encode(vals, dest_p);
            ctxt dest_c;
            info.enc->encrypt(dest_p, dest_c);
            locs[c] = dest_c;
        }

        computation(locs, info);
    }
};