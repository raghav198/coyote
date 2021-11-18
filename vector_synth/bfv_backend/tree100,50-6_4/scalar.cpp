
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"408", "49", "791", "680", "659", "500", "204", "608", "14", "697", "743", "719", "88", "913", "42", "252", "618", "6", "107", "3", "129", "989", "1000", "152", "991", "878", "506", "219", "767", "515", "520", "244", "955", "661", "604", "959", "725", "988", "262", "912", "862", "98", "553", "994", "354", "852", "199", "951", "281", "742", "522", "355", "443", "569", "359", "176", "259", "216", "887", "225", "93", "13", "294"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["989"], locs["862"], regs[0]);
    info.eval->add(locs["1000"], locs["129"], regs[1]);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(locs["955"], locs["680"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["553"], locs["354"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->add(regs[2], regs[5], regs[6]);
    info.eval->add(locs["281"], locs["659"], regs[7]);
    info.eval->multiply(locs["219"], locs["6"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[7], regs[8], regs[9]);
    info.eval->multiply(locs["913"], locs["294"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(locs["252"], locs["199"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(regs[9], regs[12], regs[13]);
    info.eval->multiply(regs[6], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(locs["742"], locs["42"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(locs["98"], locs["225"], regs[16]);
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(locs["791"], locs["742"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(locs["743"], locs["204"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[18], regs[19], regs[20]);
    info.eval->add(regs[17], regs[20], regs[21]);
    info.eval->multiply(locs["608"], locs["216"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->multiply(locs["515"], locs["262"], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->add(regs[22], regs[23], regs[24]);
    info.eval->add(locs["719"], locs["697"], regs[25]);
    info.eval->multiply(locs["661"], locs["506"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(regs[25], regs[26], regs[27]);
    info.eval->add(regs[24], regs[27], regs[28]);
    info.eval->add(regs[21], regs[28], regs[29]);
    info.eval->add(regs[14], regs[29], regs[30]);
    info.eval->multiply(locs["3"], locs["176"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->multiply(locs["13"], locs["14"], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->add(regs[31], regs[32], regs[33]);
    info.eval->add(locs["522"], locs["88"], regs[34]);
    info.eval->multiply(locs["852"], locs["355"], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->multiply(regs[34], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->multiply(regs[33], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->multiply(locs["959"], locs["152"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->multiply(locs["991"], locs["994"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->add(regs[38], regs[39], regs[40]);
    info.eval->multiply(locs["49"], locs["244"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->add(locs["604"], locs["951"], regs[42]);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->multiply(regs[40], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(regs[37], regs[44], regs[45]);
    info.eval->multiply(locs["500"], locs["618"], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->multiply(locs["443"], locs["878"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->add(regs[46], regs[47], regs[48]);
    info.eval->multiply(locs["569"], locs["912"], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->add(locs["359"], locs["408"], regs[50]);
    info.eval->multiply(regs[49], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->multiply(regs[48], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->add(locs["725"], locs["767"], regs[53]);
    info.eval->add(locs["520"], locs["988"], regs[54]);
    info.eval->add(regs[53], regs[54], regs[55]);
    info.eval->add(locs["887"], locs["259"], regs[56]);
    info.eval->add(locs["107"], locs["93"], regs[57]);
    info.eval->add(regs[56], regs[57], regs[58]);
    info.eval->add(regs[55], regs[58], regs[59]);
    info.eval->multiply(regs[52], regs[59], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    info.eval->add(regs[45], regs[60], regs[61]);
    info.eval->add(regs[30], regs[61], regs[62]);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    