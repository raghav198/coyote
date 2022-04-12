
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 4;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"752", "535", "63", "718", "517"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["535"], locs["517"], regs[0]);
    info.eval->multiply(locs["752"], locs["63"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(regs[1], locs["718"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(regs[0], regs[2], regs[3]);
    std::vector<ctxt> answer;
    answer.push_back(regs[3]);
    return answer;
}
    