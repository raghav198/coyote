
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 3;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"930", "857", "213", "74"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["930"], locs["213"], regs[0]);
    info.eval->add(locs["74"], locs["857"], regs[1]);
    info.eval->add(regs[0], regs[1], regs[2]);
    std::vector<ctxt> answer;
    answer.push_back(regs[2]);
    return answer;
}
    