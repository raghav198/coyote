
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 5;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"649", "317", "798", "184", "1003", "938"};
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
    info.eval->multiply(regs[3], locs["317"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[4]);
    return answer;
}
    