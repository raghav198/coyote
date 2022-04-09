
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"834", "971", "198", "742", "825", "69", "88", "1015", "103", "178", "437", "940", "1008", "1019", "619", "995", "694", "546", "781", "692", "385", "985", "576", "452", "922", "711", "665", "228", "290", "573", "252", "390", "733", "657", "873", "45", "222", "762", "67", "577", "794", "445", "817", "471", "494", "194", "890", "340", "896", "519", "640", "386", "788", "539", "284", "450", "751", "116", "811", "501", "95"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["711"], locs["228"], regs[0]);
    info.eval->add(locs["657"], locs["781"], regs[1]);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->add(locs["103"], locs["194"], regs[3]);
    info.eval->add(locs["1008"], locs["971"], regs[4]);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["619"], locs["781"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(locs["995"], locs["640"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(locs["971"], locs["694"], regs[10]);
    info.eval->add(locs["437"], locs["873"], regs[11]);
    info.eval->add(regs[10], regs[11], regs[12]);
    info.eval->multiply(regs[9], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[6], regs[13], regs[14]);
    info.eval->multiply(locs["733"], locs["751"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(locs["519"], locs["45"], regs[16]);
    info.eval->add(regs[15], regs[16], regs[17]);
    info.eval->multiply(locs["501"], locs["794"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(locs["445"], locs["576"], regs[19]);
    info.eval->add(regs[18], regs[19], regs[20]);
    info.eval->multiply(regs[17], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(locs["890"], locs["940"], regs[22]);
    info.eval->multiply(locs["116"], locs["252"], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->add(regs[22], regs[23], regs[24]);
    info.eval->add(locs["573"], locs["69"], regs[25]);
    info.eval->multiply(locs["546"], locs["1019"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->multiply(regs[24], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->multiply(regs[21], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->multiply(regs[14], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->multiply(locs["834"], locs["95"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->add(locs["67"], locs["817"], regs[32]);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->multiply(locs["742"], locs["825"], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->multiply(locs["390"], locs["985"], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->add(regs[34], regs[35], regs[36]);
    info.eval->add(regs[33], regs[36], regs[37]);
    info.eval->multiply(locs["896"], locs["471"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->multiply(locs["284"], locs["178"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->add(regs[38], regs[39], regs[40]);
    info.eval->multiply(locs["386"], locs["222"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->add(locs["577"], locs["385"], regs[42]);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->multiply(regs[40], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(regs[37], regs[44], regs[45]);
    info.eval->multiply(locs["340"], locs["290"], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->multiply(locs["452"], locs["198"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->add(regs[46], regs[47], regs[48]);
    info.eval->multiply(locs["811"], locs["1015"], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->add(locs["450"], locs["890"], regs[50]);
    info.eval->multiply(regs[49], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->add(regs[48], regs[51], regs[52]);
    info.eval->add(locs["88"], locs["788"], regs[53]);
    info.eval->add(locs["494"], locs["762"], regs[54]);
    info.eval->add(regs[53], regs[54], regs[55]);
    info.eval->add(locs["539"], locs["665"], regs[56]);
    info.eval->multiply(locs["692"], locs["922"], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->multiply(regs[56], regs[57], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->multiply(regs[55], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->add(regs[52], regs[59], regs[60]);
    info.eval->multiply(regs[45], regs[60], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->multiply(regs[30], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    