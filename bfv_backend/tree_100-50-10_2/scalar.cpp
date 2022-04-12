
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 43;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"533", "345", "581", "761", "752", "523", "632", "129", "37", "760", "212", "116", "1012", "753", "729", "922", "891", "944", "956", "207", "50", "852", "820", "930", "173", "148", "263", "574", "102", "613", "873", "364", "342", "407", "215", "362", "624", "542", "14", "49", "722"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["407"], locs["37"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["345"], locs["14"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->add(regs[2], locs["956"], regs[3]);
    info.eval->add(locs["215"], locs["873"], regs[4]);
    info.eval->add(regs[4], locs["342"], regs[5]);
    info.eval->add(regs[5], locs["944"], regs[6]);
    info.eval->multiply(locs["533"], regs[6], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->add(regs[7], locs["752"], regs[8]);
    info.eval->add(regs[8], locs["207"], regs[9]);
    info.eval->multiply(locs["613"], locs["148"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(locs["50"], locs["760"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(regs[11], locs["820"], regs[12]);
    info.eval->multiply(locs["542"], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->multiply(regs[10], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(regs[14], locs["1012"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(regs[9], regs[15], regs[16]);
    info.eval->add(locs["102"], locs["852"], regs[17]);
    info.eval->multiply(locs["407"], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(locs["345"], locs["207"], regs[19]);
    info.eval->add(locs["753"], locs["49"], regs[20]);
    info.eval->multiply(regs[19], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(locs["362"], locs["116"], regs[22]);
    info.eval->add(regs[22], locs["722"], regs[23]);
    info.eval->multiply(regs[21], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->multiply(regs[18], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->multiply(regs[25], locs["364"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(locs["761"], locs["574"], regs[27]);
    info.eval->add(locs["930"], locs["632"], regs[28]);
    info.eval->add(regs[27], regs[28], regs[29]);
    info.eval->add(locs["891"], locs["212"], regs[30]);
    info.eval->multiply(regs[30], locs["129"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->add(regs[29], regs[31], regs[32]);
    info.eval->multiply(regs[32], locs["729"], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->multiply(regs[33], locs["523"], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->multiply(regs[26], regs[34], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->multiply(locs["263"], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->multiply(regs[16], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->multiply(regs[3], regs[37], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(locs["173"], locs["922"], regs[39]);
    info.eval->multiply(locs["581"], locs["624"], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->multiply(regs[39], regs[40], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->multiply(regs[38], regs[41], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[42]);
    return answer;
}
    