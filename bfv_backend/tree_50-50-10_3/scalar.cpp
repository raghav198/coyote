
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 34;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"533", "530", "1017", "761", "1011", "816", "290", "522", "114", "702", "621", "755", "413", "779", "35", "234", "134", "805", "894", "603", "362", "133", "65", "379", "571", "30", "145", "67", "318", "707", "390", "941", "231", "840", "967"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["145"], locs["967"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["379"], regs[0], regs[1]);
    info.eval->add(locs["805"], regs[1], regs[2]);
    info.eval->multiply(regs[2], locs["114"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(regs[3], locs["35"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(locs["761"], locs["318"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(locs["530"], locs["362"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["390"], locs["522"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(regs[8], locs["707"], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(regs[9], locs["894"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(regs[5], regs[10], regs[11]);
    info.eval->multiply(regs[4], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->multiply(locs["30"], locs["941"], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->multiply(locs["67"], locs["134"], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(locs["533"], locs["621"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(locs["1017"], regs[16], regs[17]);
    info.eval->multiply(regs[13], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(locs["65"], locs["413"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(locs["603"], locs["571"], regs[20]);
    info.eval->multiply(regs[19], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->multiply(regs[21], locs["755"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->multiply(locs["1011"], locs["234"], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->multiply(regs[23], locs["779"], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->add(regs[22], regs[24], regs[25]);
    info.eval->add(regs[18], regs[25], regs[26]);
    info.eval->multiply(regs[26], locs["231"], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->multiply(regs[12], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->multiply(locs["840"], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->add(locs["816"], regs[29], regs[30]);
    info.eval->multiply(locs["702"], locs["290"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->multiply(regs[31], locs["133"], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->add(regs[30], regs[32], regs[33]);
    std::vector<ctxt> answer;
    answer.push_back(regs[33]);
    return answer;
}
    