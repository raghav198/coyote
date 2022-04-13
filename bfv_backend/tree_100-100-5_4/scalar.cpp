
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 12;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"368", "253", "383", "940", "762", "76", "149", "216", "385", "322", "993", "255", "658"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["253"], locs["385"], regs[0]);
    info.eval->add(locs["368"], regs[0], regs[1]);
    info.eval->add(locs["322"], locs["76"], regs[2]);
    info.eval->add(locs["149"], regs[2], regs[3]);
    info.eval->multiply(regs[1], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(locs["216"], regs[4], regs[5]);
    info.eval->add(locs["658"], locs["383"], regs[6]);
    info.eval->add(locs["762"], locs["255"], regs[7]);
    info.eval->add(regs[6], regs[7], regs[8]);
    info.eval->add(locs["940"], regs[8], regs[9]);
    info.eval->multiply(regs[9], locs["993"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(regs[5], regs[10], regs[11]);
    std::vector<ctxt> answer;
    answer.push_back(regs[11]);
    return answer;
}
    