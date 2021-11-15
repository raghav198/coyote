
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 69;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:1,0", "b:1,1", "a:0,0", "b:0,2", "b:0,0", "b:2,2", "a:1,2", "a:0,2", "b:0,1", "b:1,2", "a:1,0", "a:1,1", "a:0,1", "a:2,1", "a:2,2", "b:2,0", "a:2,0", "b:2,1"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["a:0,0"];
    regs[1] = locs["b:0,0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["a:0,1"];
    regs[4] = locs["b:1,0"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    regs[7] = locs["a:0,2"];
    info.eval->multiply(regs[7], locs["b:2,0"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[6], regs[8], regs[9]);
    regs[10] = locs["a:0,0"];
    regs[11] = locs["b:0,1"];
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["a:0,1"];
    regs[14] = locs["b:1,1"];
    info.eval->multiply(regs[13], regs[14], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(regs[12], regs[15], regs[16]);
    regs[17] = locs["a:0,2"];
    info.eval->multiply(regs[17], locs["b:2,1"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(regs[16], regs[18], regs[19]);
    regs[20] = locs["a:0,0"];
    regs[21] = locs["b:0,2"];
    info.eval->multiply(regs[20], regs[21], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    regs[23] = locs["a:0,1"];
    regs[24] = locs["b:1,2"];
    info.eval->multiply(regs[23], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(regs[22], regs[25], regs[26]);
    regs[27] = locs["a:0,2"];
    info.eval->multiply(regs[27], locs["b:2,2"], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->add(regs[26], regs[28], regs[29]);
    regs[30] = locs["a:1,0"];
    info.eval->multiply(regs[30], regs[1], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    regs[32] = locs["a:1,1"];
    info.eval->multiply(regs[32], regs[4], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(regs[31], regs[33], regs[34]);
    regs[35] = locs["a:1,2"];
    info.eval->multiply(regs[35], locs["b:2,0"], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->add(regs[34], regs[36], regs[37]);
    regs[38] = locs["a:1,0"];
    info.eval->multiply(regs[38], regs[11], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    regs[40] = locs["a:1,1"];
    info.eval->multiply(regs[40], regs[14], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->add(regs[39], regs[41], regs[42]);
    regs[43] = locs["a:1,2"];
    info.eval->multiply(regs[43], locs["b:2,1"], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(regs[42], regs[44], regs[45]);
    regs[46] = locs["a:1,0"];
    info.eval->multiply(regs[46], regs[21], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    regs[48] = locs["a:1,1"];
    info.eval->multiply(regs[48], regs[24], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->add(regs[47], regs[49], regs[50]);
    regs[51] = locs["a:1,2"];
    info.eval->multiply(regs[51], locs["b:2,2"], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->add(regs[50], regs[52], regs[53]);
    info.eval->multiply(locs["a:2,0"], regs[1], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->multiply(locs["a:2,1"], regs[4], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(regs[54], regs[55], regs[56]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,0"], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->add(regs[56], regs[57], regs[58]);
    info.eval->multiply(locs["a:2,0"], regs[11], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->multiply(locs["a:2,1"], regs[14], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    info.eval->add(regs[59], regs[60], regs[61]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,1"], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    info.eval->add(regs[61], regs[62], regs[63]);
    info.eval->multiply(locs["a:2,0"], regs[21], regs[64]);
    info.eval->relinearize_inplace(regs[64], rk);
    info.eval->multiply(locs["a:2,1"], regs[24], regs[65]);
    info.eval->relinearize_inplace(regs[65], rk);
    info.eval->add(regs[64], regs[65], regs[66]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,2"], regs[67]);
    info.eval->relinearize_inplace(regs[67], rk);
    info.eval->add(regs[66], regs[67], regs[68]);
    std::vector<ctxt> answer;
    answer.push_back(regs[9]);
    answer.push_back(regs[19]);
    answer.push_back(regs[29]);
    answer.push_back(regs[37]);
    answer.push_back(regs[45]);
    answer.push_back(regs[53]);
    answer.push_back(regs[58]);
    answer.push_back(regs[63]);
    answer.push_back(regs[68]);
    return answer;
}
    