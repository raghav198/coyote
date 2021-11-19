
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 7;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"388", "896", "107", "437", "4", "877", "406", "238"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["238"], locs["4"], regs[0]);
    info.eval->multiply(locs["437"], locs["107"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(locs["388"], locs["406"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(locs["877"], locs["896"], regs[4]);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    return answer;
}
    