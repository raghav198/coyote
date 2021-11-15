
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 107;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:1,0", "b:2,2", "b:1,1", "a:2,1", "b:0,1", "b:0,2", "b:1,2", "a:0,2", "b:0,0", "a:0,1", "a:0,0", "a:2,0", "b:2,0", "a:1,0", "a:1,1", "a:2,2", "a:1,2", "b:2,1"};
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
    regs[11] = locs["a:1,0"];
    regs[12] = locs["b:0,1"];
    info.eval->multiply(regs[11], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    regs[14] = locs["a:1,1"];
    regs[15] = locs["b:1,1"];
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[13], regs[16], regs[17]);
    regs[18] = locs["a:1,2"];
    regs[19] = locs["b:2,1"];
    info.eval->multiply(regs[18], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->add(regs[17], regs[20], regs[21]);
    regs[22] = locs["a:2,0"];
    regs[23] = locs["b:0,2"];
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    regs[25] = locs["a:2,1"];
    regs[26] = locs["b:1,2"];
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[24], regs[27], regs[28]);
    regs[29] = locs["a:2,2"];
    regs[30] = locs["b:2,2"];
    info.eval->multiply(regs[29], regs[30], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->add(regs[28], regs[31], regs[32]);
    info.eval->multiply(regs[21], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->multiply(regs[22], regs[12], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->multiply(regs[25], regs[15], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->add(regs[34], regs[35], regs[36]);
    info.eval->multiply(regs[29], regs[19], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->add(regs[36], regs[37], regs[38]);
    info.eval->multiply(regs[11], regs[23], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->multiply(regs[14], regs[26], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->add(regs[39], regs[40], regs[41]);
    info.eval->multiply(regs[18], regs[30], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->add(regs[41], regs[42], regs[43]);
    info.eval->multiply(regs[38], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(regs[33], regs[44], regs[45]);
    info.eval->multiply(regs[10], regs[45], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->multiply(regs[0], regs[12], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->multiply(regs[3], regs[15], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(regs[47], regs[48], regs[49]);
    info.eval->multiply(regs[7], regs[19], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->add(regs[49], regs[50], regs[51]);
    info.eval->multiply(regs[11], regs[1], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->multiply(regs[14], regs[4], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->add(regs[52], regs[53], regs[54]);
    info.eval->multiply(regs[18], regs[8], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(regs[54], regs[55], regs[56]);
    info.eval->multiply(regs[22], regs[23], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->multiply(regs[25], regs[26], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->add(regs[57], regs[58], regs[59]);
    info.eval->multiply(regs[29], regs[30], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    info.eval->add(regs[59], regs[60], regs[61]);
    info.eval->multiply(regs[56], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    info.eval->multiply(regs[22], regs[1], regs[63]);
    info.eval->relinearize_inplace(regs[63], rk);
    info.eval->multiply(regs[25], regs[4], regs[64]);
    info.eval->relinearize_inplace(regs[64], rk);
    info.eval->add(regs[63], regs[64], regs[65]);
    info.eval->multiply(regs[29], regs[8], regs[66]);
    info.eval->relinearize_inplace(regs[66], rk);
    info.eval->add(regs[65], regs[66], regs[67]);
    info.eval->multiply(regs[11], regs[23], regs[68]);
    info.eval->relinearize_inplace(regs[68], rk);
    info.eval->multiply(regs[14], regs[26], regs[69]);
    info.eval->relinearize_inplace(regs[69], rk);
    info.eval->add(regs[68], regs[69], regs[70]);
    info.eval->multiply(regs[18], regs[30], regs[71]);
    info.eval->relinearize_inplace(regs[71], rk);
    info.eval->add(regs[70], regs[71], regs[72]);
    info.eval->multiply(regs[67], regs[72], regs[73]);
    info.eval->relinearize_inplace(regs[73], rk);
    info.eval->add(regs[62], regs[73], regs[74]);
    info.eval->multiply(regs[51], regs[74], regs[75]);
    info.eval->relinearize_inplace(regs[75], rk);
    info.eval->sub(regs[46], regs[75], regs[76]);
    info.eval->multiply(regs[0], regs[23], regs[77]);
    info.eval->relinearize_inplace(regs[77], rk);
    info.eval->multiply(regs[3], regs[26], regs[78]);
    info.eval->relinearize_inplace(regs[78], rk);
    info.eval->add(regs[77], regs[78], regs[79]);
    info.eval->multiply(regs[7], regs[30], regs[80]);
    info.eval->relinearize_inplace(regs[80], rk);
    info.eval->add(regs[79], regs[80], regs[81]);
    info.eval->multiply(regs[11], regs[1], regs[82]);
    info.eval->relinearize_inplace(regs[82], rk);
    info.eval->multiply(regs[14], regs[4], regs[83]);
    info.eval->relinearize_inplace(regs[83], rk);
    info.eval->add(regs[82], regs[83], regs[84]);
    info.eval->multiply(regs[18], regs[8], regs[85]);
    info.eval->relinearize_inplace(regs[85], rk);
    info.eval->add(regs[84], regs[85], regs[86]);
    info.eval->multiply(regs[22], regs[12], regs[87]);
    info.eval->relinearize_inplace(regs[87], rk);
    info.eval->multiply(regs[25], regs[15], regs[88]);
    info.eval->relinearize_inplace(regs[88], rk);
    info.eval->add(regs[87], regs[88], regs[89]);
    info.eval->multiply(regs[29], regs[19], regs[90]);
    info.eval->relinearize_inplace(regs[90], rk);
    info.eval->add(regs[89], regs[90], regs[91]);
    info.eval->multiply(regs[86], regs[91], regs[92]);
    info.eval->relinearize_inplace(regs[92], rk);
    info.eval->multiply(regs[22], regs[1], regs[93]);
    info.eval->relinearize_inplace(regs[93], rk);
    info.eval->multiply(regs[25], regs[4], regs[94]);
    info.eval->relinearize_inplace(regs[94], rk);
    info.eval->add(regs[93], regs[94], regs[95]);
    info.eval->multiply(regs[29], regs[8], regs[96]);
    info.eval->relinearize_inplace(regs[96], rk);
    info.eval->add(regs[95], regs[96], regs[97]);
    info.eval->multiply(regs[11], regs[12], regs[98]);
    info.eval->relinearize_inplace(regs[98], rk);
    info.eval->multiply(regs[14], regs[15], regs[99]);
    info.eval->relinearize_inplace(regs[99], rk);
    info.eval->add(regs[98], regs[99], regs[100]);
    info.eval->multiply(regs[18], regs[19], regs[101]);
    info.eval->relinearize_inplace(regs[101], rk);
    info.eval->add(regs[100], regs[101], regs[102]);
    info.eval->multiply(regs[97], regs[102], regs[103]);
    info.eval->relinearize_inplace(regs[103], rk);
    info.eval->add(regs[92], regs[103], regs[104]);
    info.eval->multiply(regs[81], regs[104], regs[105]);
    info.eval->relinearize_inplace(regs[105], rk);
    info.eval->add(regs[76], regs[105], regs[106]);
    std::vector<ctxt> answer;
    answer.push_back(regs[106]);
    return answer;
}
    