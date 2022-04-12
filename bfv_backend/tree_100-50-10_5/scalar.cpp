
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 20;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"716", "600", "176", "473", "644", "770", "25", "849", "560", "894", "227", "638", "1014", "596", "610", "733", "817", "211", "383", "250"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["733"], locs["227"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(regs[0], locs["473"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(locs["849"], locs["383"], regs[2]);
    info.eval->multiply(locs["770"], regs[2], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["560"], locs["894"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(locs["716"], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[5], locs["638"], regs[6]);
    info.eval->add(regs[6], locs["25"], regs[7]);
    info.eval->add(regs[3], regs[7], regs[8]);
    info.eval->add(regs[8], locs["596"], regs[9]);
    info.eval->add(regs[9], locs["176"], regs[10]);
    info.eval->add(regs[10], locs["600"], regs[11]);
    info.eval->multiply(regs[1], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(locs["250"], locs["211"], regs[13]);
    info.eval->multiply(locs["733"], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(locs["644"], regs[14], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(regs[15], locs["610"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->multiply(regs[16], locs["1014"], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(regs[17], locs["817"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(regs[12], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[19]);
    return answer;
}
    