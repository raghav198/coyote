
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 82;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"a:0,1", "a:3,0", "a:2,3", "a:3,1", "a:2,1", "a:3,3", "b:1,2", "b:0,2", "a:1,2", "a:1,3", "b:1,0", "b:0,0", "a:1,0", "a:2,0", "a:0,2", "b:1,1", "b:2,0", "b:2,1", "b:0,1", "a:3,2", "a:2,2", "b:2,2", "a:0,0", "a:0,3", "a:1,1"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["b:0,0"];
    regs[1] = locs["a:0,0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["b:0,1"];
    regs[4] = locs["a:0,1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    regs[7] = locs["b:0,2"];
    regs[8] = locs["a:0,2"];
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(regs[6], regs[9], regs[10]);
    regs[11] = locs["b:1,0"];
    regs[12] = locs["a:1,0"];
    info.eval->multiply(regs[11], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[10], regs[13], regs[14]);
    regs[15] = locs["b:1,1"];
    regs[16] = locs["a:1,1"];
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->add(regs[14], regs[17], regs[18]);
    regs[19] = locs["b:1,2"];
    regs[20] = locs["a:1,2"];
    info.eval->multiply(regs[19], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(regs[18], regs[21], regs[22]);
    info.eval->multiply(locs["b:2,0"], locs["a:2,0"], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->add(regs[22], regs[23], regs[24]);
    info.eval->multiply(locs["b:2,1"], locs["a:2,1"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(regs[24], regs[25], regs[26]);
    info.eval->multiply(locs["b:2,2"], locs["a:2,2"], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[26], regs[27], regs[28]);
    info.eval->multiply(regs[0], regs[4], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->multiply(regs[3], regs[8], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->add(regs[29], regs[30], regs[31]);
    regs[32] = locs["a:0,3"];
    info.eval->multiply(regs[7], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(regs[31], regs[33], regs[34]);
    info.eval->multiply(regs[11], regs[16], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->add(regs[34], regs[35], regs[36]);
    info.eval->multiply(regs[15], regs[20], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->add(regs[36], regs[37], regs[38]);
    regs[39] = locs["a:1,3"];
    info.eval->multiply(regs[19], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->add(regs[38], regs[40], regs[41]);
    info.eval->multiply(locs["b:2,0"], locs["a:2,1"], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->add(regs[41], regs[42], regs[43]);
    info.eval->multiply(locs["b:2,1"], locs["a:2,2"], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(regs[43], regs[44], regs[45]);
    info.eval->multiply(locs["b:2,2"], locs["a:2,3"], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->add(regs[45], regs[46], regs[47]);
    info.eval->multiply(regs[0], regs[12], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->multiply(regs[3], regs[16], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->add(regs[48], regs[49], regs[50]);
    info.eval->multiply(regs[7], regs[20], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->add(regs[50], regs[51], regs[52]);
    info.eval->multiply(regs[11], locs["a:2,0"], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->add(regs[52], regs[53], regs[54]);
    info.eval->multiply(regs[15], locs["a:2,1"], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(regs[54], regs[55], regs[56]);
    info.eval->multiply(regs[19], locs["a:2,2"], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->add(regs[56], regs[57], regs[58]);
    info.eval->multiply(locs["b:2,0"], locs["a:3,0"], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->add(regs[58], regs[59], regs[60]);
    info.eval->multiply(locs["b:2,1"], locs["a:3,1"], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->add(regs[60], regs[61], regs[62]);
    info.eval->multiply(locs["b:2,2"], locs["a:3,2"], regs[63]);
    info.eval->relinearize_inplace(regs[63], rk);
    info.eval->add(regs[62], regs[63], regs[64]);
    info.eval->multiply(regs[0], regs[16], regs[65]);
    info.eval->relinearize_inplace(regs[65], rk);
    info.eval->multiply(regs[3], regs[20], regs[66]);
    info.eval->relinearize_inplace(regs[66], rk);
    info.eval->add(regs[65], regs[66], regs[67]);
    info.eval->multiply(regs[7], regs[39], regs[68]);
    info.eval->relinearize_inplace(regs[68], rk);
    info.eval->add(regs[67], regs[68], regs[69]);
    info.eval->multiply(regs[11], locs["a:2,1"], regs[70]);
    info.eval->relinearize_inplace(regs[70], rk);
    info.eval->add(regs[69], regs[70], regs[71]);
    info.eval->multiply(regs[15], locs["a:2,2"], regs[72]);
    info.eval->relinearize_inplace(regs[72], rk);
    info.eval->add(regs[71], regs[72], regs[73]);
    info.eval->multiply(regs[19], locs["a:2,3"], regs[74]);
    info.eval->relinearize_inplace(regs[74], rk);
    info.eval->add(regs[73], regs[74], regs[75]);
    info.eval->multiply(locs["b:2,0"], locs["a:3,1"], regs[76]);
    info.eval->relinearize_inplace(regs[76], rk);
    info.eval->add(regs[75], regs[76], regs[77]);
    info.eval->multiply(locs["b:2,1"], locs["a:3,2"], regs[78]);
    info.eval->relinearize_inplace(regs[78], rk);
    info.eval->add(regs[77], regs[78], regs[79]);
    info.eval->multiply(locs["b:2,2"], locs["a:3,3"], regs[80]);
    info.eval->relinearize_inplace(regs[80], rk);
    info.eval->add(regs[79], regs[80], regs[81]);
    std::vector<ctxt> answer;
    answer.push_back(regs[28]);
    answer.push_back(regs[47]);
    answer.push_back(regs[64]);
    answer.push_back(regs[81]);
    return answer;
}
    