
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 6;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"934", "90", "98", "29", "506", "874", "818"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["29"], locs["506"], regs[0]);
    info.eval->add(locs["90"], regs[0], regs[1]);
    info.eval->multiply(regs[1], locs["874"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(regs[2], locs["98"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(locs["934"], locs["818"], regs[4]);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[5]);
    return answer;
}
    