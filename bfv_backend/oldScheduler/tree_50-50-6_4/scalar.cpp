
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 2;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"938", "1003", "184"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["938"], locs["1003"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(regs[0], locs["184"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[1]);
    return answer;
}
    