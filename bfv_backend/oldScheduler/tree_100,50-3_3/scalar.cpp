
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 7;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"30", "720", "657", "731", "781", "103", "711", "916"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["916"], locs["30"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["720"], locs["711"], regs[1]);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(locs["657"], locs["781"], regs[3]);
    info.eval->add(locs["731"], locs["103"], regs[4]);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    return answer;
}
    