
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"733", "976", "971", "309", "896", "619", "103", "811", "731", "150", "286", "450", "494", "539", "834", "361", "390", "501", "526", "950", "282", "936", "519", "88", "981", "720", "752", "573", "470", "93", "995", "742", "546", "1012", "91", "657", "67", "233", "303", "127", "437", "386", "552", "890", "52", "736", "445", "137", "452", "284", "114", "409", "793", "340", "116", "53", "577", "854", "1010", "1008", "711", "692", "821"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["720"], locs["711"], regs[0]);
    info.eval->multiply(locs["1012"], locs["657"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(locs["731"], locs["103"], regs[3]);
    info.eval->multiply(locs["981"], locs["1008"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->add(regs[2], regs[5], regs[6]);
    info.eval->multiply(locs["91"], locs["619"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->add(locs["409"], locs["995"], regs[8]);
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(locs["736"], locs["971"], regs[10]);
    info.eval->add(locs["752"], locs["437"], regs[11]);
    info.eval->add(regs[10], regs[11], regs[12]);
    info.eval->add(regs[9], regs[12], regs[13]);
    info.eval->multiply(regs[6], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(locs["52"], locs["733"], regs[15]);
    info.eval->add(locs["821"], locs["519"], regs[16]);
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->add(locs["286"], locs["501"], regs[18]);
    info.eval->add(locs["976"], locs["445"], regs[19]);
    info.eval->multiply(regs[18], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->multiply(regs[17], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(locs["552"], locs["890"], regs[22]);
    info.eval->add(locs["470"], locs["116"], regs[23]);
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->multiply(locs["950"], locs["573"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->multiply(locs["309"], locs["546"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[24], regs[27], regs[28]);
    info.eval->add(regs[21], regs[28], regs[29]);
    info.eval->multiply(regs[14], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->multiply(locs["361"], locs["834"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->multiply(locs["936"], locs["67"], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->add(regs[31], regs[32], regs[33]);
    info.eval->add(locs["233"], locs["742"], regs[34]);
    info.eval->add(locs["137"], locs["390"], regs[35]);
    info.eval->add(regs[34], regs[35], regs[36]);
    info.eval->add(regs[33], regs[36], regs[37]);
    info.eval->add(locs["303"], locs["896"], regs[38]);
    info.eval->multiply(locs["282"], locs["284"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->multiply(regs[38], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->multiply(locs["53"], locs["386"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->multiply(locs["793"], locs["577"], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[40], regs[43], regs[44]);
    info.eval->multiply(regs[37], regs[44], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    info.eval->add(locs["127"], locs["340"], regs[46]);
    info.eval->multiply(locs["114"], locs["452"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->add(regs[46], regs[47], regs[48]);
    info.eval->multiply(locs["93"], locs["811"], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->add(locs["854"], locs["450"], regs[50]);
    info.eval->multiply(regs[49], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->add(regs[48], regs[51], regs[52]);
    info.eval->add(locs["1010"], locs["88"], regs[53]);
    info.eval->add(locs["742"], locs["494"], regs[54]);
    info.eval->multiply(regs[53], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->multiply(locs["526"], locs["539"], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->add(locs["150"], locs["692"], regs[57]);
    info.eval->add(regs[56], regs[57], regs[58]);
    info.eval->add(regs[55], regs[58], regs[59]);
    info.eval->multiply(regs[52], regs[59], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    info.eval->add(regs[45], regs[60], regs[61]);
    info.eval->multiply(regs[30], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    