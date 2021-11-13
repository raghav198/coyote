
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 81;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:1,0", "b:1,1", "b:2,1", "b:1,2", "a:1,0", "a:1,2", "a:2,0", "a:2,1", "a:1,1", "a:0,2", "b:0,2", "b:2,2", "a:2,2", "b:0,0", "b:2,0", "b:0,1", "a:0,0", "a:0,1"};
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
    regs[31] = locs["b:0,0"];
    info.eval->multiply(regs[30], regs[31], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    regs[33] = locs["a:1,1"];
    regs[34] = locs["b:1,0"];
    info.eval->multiply(regs[33], regs[34], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->add(regs[32], regs[35], regs[36]);
    regs[37] = locs["a:1,2"];
    info.eval->multiply(regs[37], locs["b:2,0"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(regs[36], regs[38], regs[39]);
    regs[40] = locs["a:1,0"];
    regs[41] = locs["b:0,1"];
    info.eval->multiply(regs[40], regs[41], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    regs[43] = locs["a:1,1"];
    regs[44] = locs["b:1,1"];
    info.eval->multiply(regs[43], regs[44], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    info.eval->add(regs[42], regs[45], regs[46]);
    regs[47] = locs["a:1,2"];
    info.eval->multiply(regs[47], locs["b:2,1"], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(regs[46], regs[48], regs[49]);
    regs[50] = locs["a:1,0"];
    regs[51] = locs["b:0,2"];
    info.eval->multiply(regs[50], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    regs[53] = locs["a:1,1"];
    regs[54] = locs["b:1,2"];
    info.eval->multiply(regs[53], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(regs[52], regs[55], regs[56]);
    regs[57] = locs["a:1,2"];
    info.eval->multiply(regs[57], locs["b:2,2"], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->add(regs[56], regs[58], regs[59]);
    regs[60] = locs["b:0,0"];
    info.eval->multiply(locs["a:2,0"], regs[60], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    regs[62] = locs["b:1,0"];
    info.eval->multiply(locs["a:2,1"], regs[62], regs[63]);
    info.eval->relinearize_inplace(regs[63], rk);
    info.eval->add(regs[61], regs[63], regs[64]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,0"], regs[65]);
    info.eval->relinearize_inplace(regs[65], rk);
    info.eval->add(regs[64], regs[65], regs[66]);
    regs[67] = locs["b:0,1"];
    info.eval->multiply(locs["a:2,0"], regs[67], regs[68]);
    info.eval->relinearize_inplace(regs[68], rk);
    regs[69] = locs["b:1,1"];
    info.eval->multiply(locs["a:2,1"], regs[69], regs[70]);
    info.eval->relinearize_inplace(regs[70], rk);
    info.eval->add(regs[68], regs[70], regs[71]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,1"], regs[72]);
    info.eval->relinearize_inplace(regs[72], rk);
    info.eval->add(regs[71], regs[72], regs[73]);
    regs[74] = locs["b:0,2"];
    info.eval->multiply(locs["a:2,0"], regs[74], regs[75]);
    info.eval->relinearize_inplace(regs[75], rk);
    regs[76] = locs["b:1,2"];
    info.eval->multiply(locs["a:2,1"], regs[76], regs[77]);
    info.eval->relinearize_inplace(regs[77], rk);
    info.eval->add(regs[75], regs[77], regs[78]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,2"], regs[79]);
    info.eval->relinearize_inplace(regs[79], rk);
    info.eval->add(regs[78], regs[79], regs[80]);
    std::vector<ctxt> answer;
    answer.push_back(regs[9]);
    answer.push_back(regs[19]);
    answer.push_back(regs[29]);
    answer.push_back(regs[39]);
    answer.push_back(regs[49]);
    answer.push_back(regs[59]);
    answer.push_back(regs[66]);
    answer.push_back(regs[73]);
    answer.push_back(regs[80]);
    return answer;
}
    