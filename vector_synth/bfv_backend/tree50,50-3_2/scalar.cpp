
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 1;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"662", "380"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["662"], locs["380"], regs[0]);
    std::vector<ctxt> answer;
    answer.push_back(regs[0]);
    return answer;
}
    