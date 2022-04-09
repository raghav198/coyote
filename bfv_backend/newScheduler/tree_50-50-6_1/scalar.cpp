
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 4;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"649", "798", "938", "184", "1003"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["938"], locs["1003"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(regs[0], locs["184"], regs[1]);
    info.eval->add(regs[1], locs["798"], regs[2]);
    info.eval->multiply(regs[2], locs["649"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[3]);
    return answer;
}
    