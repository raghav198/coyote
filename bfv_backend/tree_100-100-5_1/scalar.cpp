
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 18;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"406", "74", "867", "704", "459", "269", "318", "694", "460", "243", "270", "593", "873", "76", "747", "231", "48", "884", "82"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["243"], locs["269"], regs[0]);
    info.eval->multiply(regs[0], locs["704"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(locs["747"], locs["82"], regs[2]);
    info.eval->multiply(locs["231"], regs[2], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(regs[1], regs[3], regs[4]);
    info.eval->multiply(locs["406"], locs["694"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(locs["460"], locs["76"], regs[6]);
    info.eval->add(regs[5], regs[6], regs[7]);
    info.eval->multiply(locs["873"], locs["74"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[8], locs["884"], regs[9]);
    info.eval->add(regs[7], regs[9], regs[10]);
    info.eval->multiply(regs[4], regs[10], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->multiply(locs["270"], locs["318"], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(regs[12], locs["48"], regs[13]);
    info.eval->add(locs["459"], regs[13], regs[14]);
    info.eval->add(locs["867"], locs["593"], regs[15]);
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->multiply(regs[11], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[17]);
    return answer;
}
    