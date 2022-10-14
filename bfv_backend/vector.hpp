#include "util.hpp"

struct VectorProgram
{

    RuntimeContext &info;

    ctxt computation(std::vector<ctxt>, std::map<std::string, ptxt> bits, RuntimeContext &info);

    std::map<std::string, ptxt> make_bits(RuntimeContext &info);
    std::vector<ctxt> initialize_temps(RuntimeContext &info);

    std::map<std::string, ptxt> bits;
    std::vector<ctxt> temps;

    VectorProgram(RuntimeContext &info) : info(info){

    }

    void setup()
    {
        bits = make_bits(info);
        temps = initialize_temps(info);
    }

    void run()
    {
        computation(temps, bits, info);
    }
};