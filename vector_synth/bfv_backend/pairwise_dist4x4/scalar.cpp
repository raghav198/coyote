
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 156;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"d:0", "d:1", "a:2", "b:2", "a:3", "d:3", "c:2", "b:0", "a:0", "c:3", "b:3", "c:0", "a:1", "b:1", "c:1", "d:2"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["a:0"];
    regs[1] = locs["c:0"];
    info.eval->sub(regs[0], regs[1], regs[2]);
    regs[3] = locs["a:0"];
    info.eval->sub(regs[3], regs[1], regs[4]);
    info.eval->multiply(regs[2], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    regs[6] = locs["b:0"];
    regs[7] = locs["d:0"];
    info.eval->sub(regs[6], regs[7], regs[8]);
    info.eval->sub(regs[6], regs[7], regs[9]);
    info.eval->multiply(regs[8], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->add(regs[5], regs[10], regs[11]);
    regs[12] = locs["a:0"];
    regs[13] = locs["c:1"];
    info.eval->sub(regs[12], regs[13], regs[14]);
    regs[15] = locs["a:0"];
    info.eval->sub(regs[15], regs[13], regs[16]);
    info.eval->multiply(regs[14], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    regs[18] = locs["d:1"];
    info.eval->sub(regs[6], regs[18], regs[19]);
    info.eval->sub(regs[6], regs[18], regs[20]);
    info.eval->multiply(regs[19], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(regs[17], regs[21], regs[22]);
    regs[23] = locs["a:0"];
    regs[24] = locs["c:2"];
    info.eval->sub(regs[23], regs[24], regs[25]);
    regs[26] = locs["a:0"];
    info.eval->sub(regs[26], regs[24], regs[27]);
    info.eval->multiply(regs[25], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    regs[29] = locs["d:2"];
    info.eval->sub(regs[6], regs[29], regs[30]);
    info.eval->sub(regs[6], regs[29], regs[31]);
    info.eval->multiply(regs[30], regs[31], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->add(regs[28], regs[32], regs[33]);
    regs[34] = locs["a:0"];
    regs[35] = locs["c:3"];
    info.eval->sub(regs[34], regs[35], regs[36]);
    regs[37] = locs["a:0"];
    info.eval->sub(regs[37], regs[35], regs[38]);
    info.eval->multiply(regs[36], regs[38], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    regs[40] = locs["d:3"];
    info.eval->sub(regs[6], regs[40], regs[41]);
    info.eval->sub(regs[6], regs[40], regs[42]);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[39], regs[43], regs[44]);
    regs[45] = locs["a:1"];
    info.eval->sub(regs[45], regs[1], regs[46]);
    regs[47] = locs["a:1"];
    info.eval->sub(regs[47], regs[1], regs[48]);
    info.eval->multiply(regs[46], regs[48], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    regs[50] = locs["b:1"];
    info.eval->sub(regs[50], regs[7], regs[51]);
    info.eval->sub(regs[50], regs[7], regs[52]);
    info.eval->multiply(regs[51], regs[52], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->add(regs[49], regs[53], regs[54]);
    regs[55] = locs["a:1"];
    info.eval->sub(regs[55], regs[13], regs[56]);
    regs[57] = locs["a:1"];
    info.eval->sub(regs[57], regs[13], regs[58]);
    info.eval->multiply(regs[56], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->sub(regs[50], regs[18], regs[60]);
    info.eval->sub(regs[50], regs[18], regs[61]);
    info.eval->multiply(regs[60], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    info.eval->add(regs[59], regs[62], regs[63]);
    regs[64] = locs["a:1"];
    info.eval->sub(regs[64], regs[24], regs[65]);
    regs[66] = locs["a:1"];
    info.eval->sub(regs[66], regs[24], regs[67]);
    info.eval->multiply(regs[65], regs[67], regs[68]);
    info.eval->relinearize_inplace(regs[68], rk);
    info.eval->sub(regs[50], regs[29], regs[69]);
    info.eval->sub(regs[50], regs[29], regs[70]);
    info.eval->multiply(regs[69], regs[70], regs[71]);
    info.eval->relinearize_inplace(regs[71], rk);
    info.eval->add(regs[68], regs[71], regs[72]);
    regs[73] = locs["a:1"];
    info.eval->sub(regs[73], regs[35], regs[74]);
    regs[75] = locs["a:1"];
    info.eval->sub(regs[75], regs[35], regs[76]);
    info.eval->multiply(regs[74], regs[76], regs[77]);
    info.eval->relinearize_inplace(regs[77], rk);
    info.eval->sub(regs[50], regs[40], regs[78]);
    info.eval->sub(regs[50], regs[40], regs[79]);
    info.eval->multiply(regs[78], regs[79], regs[80]);
    info.eval->relinearize_inplace(regs[80], rk);
    info.eval->add(regs[77], regs[80], regs[81]);
    regs[82] = locs["a:2"];
    info.eval->sub(regs[82], regs[1], regs[83]);
    regs[84] = locs["a:2"];
    info.eval->sub(regs[84], regs[1], regs[85]);
    info.eval->multiply(regs[83], regs[85], regs[86]);
    info.eval->relinearize_inplace(regs[86], rk);
    regs[87] = locs["b:2"];
    info.eval->sub(regs[87], regs[7], regs[88]);
    info.eval->sub(regs[87], regs[7], regs[89]);
    info.eval->multiply(regs[88], regs[89], regs[90]);
    info.eval->relinearize_inplace(regs[90], rk);
    info.eval->add(regs[86], regs[90], regs[91]);
    regs[92] = locs["a:2"];
    info.eval->sub(regs[92], regs[13], regs[93]);
    regs[94] = locs["a:2"];
    info.eval->sub(regs[94], regs[13], regs[95]);
    info.eval->multiply(regs[93], regs[95], regs[96]);
    info.eval->relinearize_inplace(regs[96], rk);
    info.eval->sub(regs[87], regs[18], regs[97]);
    info.eval->sub(regs[87], regs[18], regs[98]);
    info.eval->multiply(regs[97], regs[98], regs[99]);
    info.eval->relinearize_inplace(regs[99], rk);
    info.eval->add(regs[96], regs[99], regs[100]);
    regs[101] = locs["a:2"];
    info.eval->sub(regs[101], regs[24], regs[102]);
    regs[103] = locs["a:2"];
    info.eval->sub(regs[103], regs[24], regs[104]);
    info.eval->multiply(regs[102], regs[104], regs[105]);
    info.eval->relinearize_inplace(regs[105], rk);
    info.eval->sub(regs[87], regs[29], regs[106]);
    info.eval->sub(regs[87], regs[29], regs[107]);
    info.eval->multiply(regs[106], regs[107], regs[108]);
    info.eval->relinearize_inplace(regs[108], rk);
    info.eval->add(regs[105], regs[108], regs[109]);
    regs[110] = locs["a:2"];
    info.eval->sub(regs[110], regs[35], regs[111]);
    regs[112] = locs["a:2"];
    info.eval->sub(regs[112], regs[35], regs[113]);
    info.eval->multiply(regs[111], regs[113], regs[114]);
    info.eval->relinearize_inplace(regs[114], rk);
    info.eval->sub(regs[87], regs[40], regs[115]);
    info.eval->sub(regs[87], regs[40], regs[116]);
    info.eval->multiply(regs[115], regs[116], regs[117]);
    info.eval->relinearize_inplace(regs[117], rk);
    info.eval->add(regs[114], regs[117], regs[118]);
    regs[119] = locs["a:3"];
    info.eval->sub(regs[119], regs[1], regs[120]);
    regs[121] = locs["a:3"];
    info.eval->sub(regs[121], regs[1], regs[122]);
    info.eval->multiply(regs[120], regs[122], regs[123]);
    info.eval->relinearize_inplace(regs[123], rk);
    regs[124] = locs["b:3"];
    info.eval->sub(regs[124], regs[7], regs[125]);
    info.eval->sub(regs[124], regs[7], regs[126]);
    info.eval->multiply(regs[125], regs[126], regs[127]);
    info.eval->relinearize_inplace(regs[127], rk);
    info.eval->add(regs[123], regs[127], regs[128]);
    regs[129] = locs["a:3"];
    info.eval->sub(regs[129], regs[13], regs[130]);
    regs[131] = locs["a:3"];
    info.eval->sub(regs[131], regs[13], regs[132]);
    info.eval->multiply(regs[130], regs[132], regs[133]);
    info.eval->relinearize_inplace(regs[133], rk);
    info.eval->sub(regs[124], regs[18], regs[134]);
    info.eval->sub(regs[124], regs[18], regs[135]);
    info.eval->multiply(regs[134], regs[135], regs[136]);
    info.eval->relinearize_inplace(regs[136], rk);
    info.eval->add(regs[133], regs[136], regs[137]);
    regs[138] = locs["a:3"];
    info.eval->sub(regs[138], regs[24], regs[139]);
    regs[140] = locs["a:3"];
    info.eval->sub(regs[140], regs[24], regs[141]);
    info.eval->multiply(regs[139], regs[141], regs[142]);
    info.eval->relinearize_inplace(regs[142], rk);
    info.eval->sub(regs[124], regs[29], regs[143]);
    info.eval->sub(regs[124], regs[29], regs[144]);
    info.eval->multiply(regs[143], regs[144], regs[145]);
    info.eval->relinearize_inplace(regs[145], rk);
    info.eval->add(regs[142], regs[145], regs[146]);
    regs[147] = locs["a:3"];
    info.eval->sub(regs[147], regs[35], regs[148]);
    regs[149] = locs["a:3"];
    info.eval->sub(regs[149], regs[35], regs[150]);
    info.eval->multiply(regs[148], regs[150], regs[151]);
    info.eval->relinearize_inplace(regs[151], rk);
    info.eval->sub(regs[124], regs[40], regs[152]);
    info.eval->sub(regs[124], regs[40], regs[153]);
    info.eval->multiply(regs[152], regs[153], regs[154]);
    info.eval->relinearize_inplace(regs[154], rk);
    info.eval->add(regs[151], regs[154], regs[155]);
    std::vector<ctxt> answer;
    answer.push_back(regs[11]);
    answer.push_back(regs[22]);
    answer.push_back(regs[33]);
    answer.push_back(regs[44]);
    answer.push_back(regs[54]);
    answer.push_back(regs[63]);
    answer.push_back(regs[72]);
    answer.push_back(regs[81]);
    answer.push_back(regs[91]);
    answer.push_back(regs[100]);
    answer.push_back(regs[109]);
    answer.push_back(regs[118]);
    answer.push_back(regs[128]);
    answer.push_back(regs[137]);
    answer.push_back(regs[146]);
    answer.push_back(regs[155]);
    return answer;
}
    