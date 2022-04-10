
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 4;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"720", "916", "861", "252", "184"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["252"], locs["916"], regs[0]);
    info.eval->multiply(locs["861"], locs["720"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->multiply(regs[2], locs["184"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[3]);
    return answer;
}
    