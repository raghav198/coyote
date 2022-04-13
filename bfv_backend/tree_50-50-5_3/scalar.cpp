
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 7;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"774", "790", "508", "611", "102", "409", "697", "609"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["774"], locs["697"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["609"], locs["611"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(locs["409"], regs[1], regs[2]);
    info.eval->multiply(regs[0], regs[2], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(locs["508"], regs[3], regs[4]);
    info.eval->add(locs["102"], locs["790"], regs[5]);
    info.eval->add(regs[4], regs[5], regs[6]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    return answer;
}
    