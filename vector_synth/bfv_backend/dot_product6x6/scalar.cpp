
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 23;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"a:0", "b:4", "b:1", "a:4", "b:5", "a:2", "b:2", "a:3", "a:1", "b:3", "a:5", "b:0"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["a:0"];
    regs[1] = locs["b:0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["a:1"];
    regs[4] = locs["b:1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    regs[6] = locs["a:2"];
    regs[7] = locs["b:2"];
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->add(regs[2], regs[9], regs[10]);
    regs[11] = locs["a:3"];
    regs[12] = locs["b:3"];
    info.eval->multiply(regs[11], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    regs[14] = locs["a:4"];
    regs[15] = locs["b:4"];
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    regs[17] = locs["a:5"];
    regs[18] = locs["b:5"];
    info.eval->multiply(regs[17], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[16], regs[19], regs[20]);
    info.eval->add(regs[13], regs[20], regs[21]);
    info.eval->add(regs[10], regs[21], regs[22]);
    std::vector<ctxt> answer;
    answer.push_back(regs[22]);
    return answer;
}
    