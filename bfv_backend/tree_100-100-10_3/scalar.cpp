
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 33;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"896", "867", "246", "132", "1017", "71", "1003", "289", "267", "210", "490", "22", "291", "736", "784", "1014", "357", "913", "854", "198", "926", "145", "52", "645", "260", "678", "917", "305", "14", "259", "726", "964", "379"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["678"], locs["784"], regs[0]);
    info.eval->multiply(locs["260"], regs[0], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[1], locs["913"], regs[2]);
    info.eval->multiply(locs["210"], locs["71"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(regs[2], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(locs["52"], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(locs["964"], locs["145"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(locs["198"], locs["289"], regs[7]);
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->add(regs[9], locs["917"], regs[10]);
    info.eval->add(locs["726"], regs[10], regs[11]);
    info.eval->multiply(locs["305"], locs["926"], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(locs["267"], locs["1003"], regs[13]);
    info.eval->add(locs["14"], locs["854"], regs[14]);
    info.eval->multiply(locs["1014"], locs["259"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->multiply(locs["854"], locs["867"], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(regs[16], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(locs["246"], locs["132"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[19], locs["896"], regs[20]);
    info.eval->multiply(locs["357"], locs["736"], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->multiply(locs["490"], locs["1017"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->multiply(regs[21], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->multiply(regs[20], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->multiply(regs[18], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(regs[25], locs["645"], regs[26]);
    info.eval->multiply(regs[26], locs["379"], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->multiply(regs[13], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->add(regs[12], regs[28], regs[29]);
    info.eval->multiply(regs[11], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->add(locs["291"], locs["22"], regs[31]);
    info.eval->multiply(regs[30], regs[31], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[32]);
    return answer;
}
    