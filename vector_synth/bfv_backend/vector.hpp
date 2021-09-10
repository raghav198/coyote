#include "util.hpp"

struct VectorProgram
{
    ctxt computation(std::vector<ctxt>, std::map<std::string, ptxt> bits, RuntimeContext &info);

    std::map<std::string, ptxt> make_bits(RuntimeContext &info);
    std::vector<ctxt> initialize_temps(RuntimeContext &info);

    void run(RuntimeContext &info)
    {
        std::map<std::string, ptxt> bits = make_bits(info);
        std::vector<ctxt> temps = initialize_temps(info);
        computation(temps, bits, info);
    }
};