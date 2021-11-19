
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 81;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"a:2,1", "a:2,0", "b:0,1", "b:1,1", "b:2,1", "a:2,2", "a:1,2", "a:0,0", "b:0,0", "a:0,2", "b:1,0", "b:2,0", "b:1,2", "b:2,2", "a:0,1", "a:1,0", "b:0,2", "a:1,1"};
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
    regs[8] = locs["b:2,0"];
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(regs[6], regs[9], regs[10]);
    regs[11] = locs["a:0,0"];
    regs[12] = locs["b:0,1"];
    info.eval->multiply(regs[11], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    regs[14] = locs["a:0,1"];
    regs[15] = locs["b:1,1"];
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[13], regs[16], regs[17]);
    regs[18] = locs["a:0,2"];
    regs[19] = locs["b:2,1"];
    info.eval->multiply(regs[18], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->add(regs[17], regs[20], regs[21]);
    regs[22] = locs["a:0,0"];
    regs[23] = locs["b:0,2"];
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    regs[25] = locs["a:0,1"];
    regs[26] = locs["b:1,2"];
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[24], regs[27], regs[28]);
    regs[29] = locs["a:0,2"];
    regs[30] = locs["b:2,2"];
    info.eval->multiply(regs[29], regs[30], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->add(regs[28], regs[31], regs[32]);
    regs[33] = locs["a:1,0"];
    info.eval->multiply(regs[33], regs[1], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    regs[35] = locs["a:1,1"];
    info.eval->multiply(regs[35], regs[4], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->add(regs[34], regs[36], regs[37]);
    regs[38] = locs["a:1,2"];
    info.eval->multiply(regs[38], regs[8], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->add(regs[37], regs[39], regs[40]);
    regs[41] = locs["a:1,0"];
    info.eval->multiply(regs[41], regs[12], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    regs[43] = locs["a:1,1"];
    info.eval->multiply(regs[43], regs[15], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(regs[42], regs[44], regs[45]);
    regs[46] = locs["a:1,2"];
    info.eval->multiply(regs[46], regs[19], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->add(regs[45], regs[47], regs[48]);
    regs[49] = locs["a:1,0"];
    info.eval->multiply(regs[49], regs[23], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    regs[51] = locs["a:1,1"];
    info.eval->multiply(regs[51], regs[26], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->add(regs[50], regs[52], regs[53]);
    regs[54] = locs["a:1,2"];
    info.eval->multiply(regs[54], regs[30], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(regs[53], regs[55], regs[56]);
    regs[57] = locs["a:2,0"];
    info.eval->multiply(regs[57], regs[1], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    regs[59] = locs["a:2,1"];
    info.eval->multiply(regs[59], regs[4], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    info.eval->add(regs[58], regs[60], regs[61]);
    regs[62] = locs["a:2,2"];
    info.eval->multiply(regs[62], regs[8], regs[63]);
    info.eval->relinearize_inplace(regs[63], rk);
    info.eval->add(regs[61], regs[63], regs[64]);
    regs[65] = locs["a:2,0"];
    info.eval->multiply(regs[65], regs[12], regs[66]);
    info.eval->relinearize_inplace(regs[66], rk);
    regs[67] = locs["a:2,1"];
    info.eval->multiply(regs[67], regs[15], regs[68]);
    info.eval->relinearize_inplace(regs[68], rk);
    info.eval->add(regs[66], regs[68], regs[69]);
    regs[70] = locs["a:2,2"];
    info.eval->multiply(regs[70], regs[19], regs[71]);
    info.eval->relinearize_inplace(regs[71], rk);
    info.eval->add(regs[69], regs[71], regs[72]);
    regs[73] = locs["a:2,0"];
    info.eval->multiply(regs[73], regs[23], regs[74]);
    info.eval->relinearize_inplace(regs[74], rk);
    regs[75] = locs["a:2,1"];
    info.eval->multiply(regs[75], regs[26], regs[76]);
    info.eval->relinearize_inplace(regs[76], rk);
    info.eval->add(regs[74], regs[76], regs[77]);
    regs[78] = locs["a:2,2"];
    info.eval->multiply(regs[78], regs[30], regs[79]);
    info.eval->relinearize_inplace(regs[79], rk);
    info.eval->add(regs[77], regs[79], regs[80]);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    answer.push_back(regs[21]);
    answer.push_back(regs[32]);
    answer.push_back(regs[40]);
    answer.push_back(regs[48]);
    answer.push_back(regs[56]);
    answer.push_back(regs[64]);
    answer.push_back(regs[72]);
    answer.push_back(regs[80]);
    return answer;
}
    