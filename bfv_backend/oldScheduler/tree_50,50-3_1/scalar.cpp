
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 3;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"508", "1003", "252", "938"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["508"], locs["252"], regs[0]);
    info.eval->multiply(regs[0], locs["938"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(regs[1], locs["1003"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[2]);
    return answer;
}
    