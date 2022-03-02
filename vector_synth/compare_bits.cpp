# include "../vector_synth/bfv_backend/scalar.hpp"
// #include <stdio.h>

std::ctext ScalarProgram::less_than_bits(std::ctext ctext1, std::ctext ctext2, std::integer l, RuntimeContext &info)
{
    int SUM = 0;
    int LT;
    int LocalPRODUCT;

    for(int i = l - 1; i >= 0; i--){
        LT = ((ctext1[i] - ctext2[i]) % 2) * ctext2[i];
        LocalPRODUCT = 1;
        for(int j = i - 1; j >= 0; j--){
            LocalPRODUCT *= 1 - ((ctext1[j] - ctext2[j]) % 2);
        }
        SUM += LT * LocalPRODUCT;
    }

    return (0 - SUM) % 2;
}

// int Sless_than_bits(int ctext1 [], int ctext2 [], int l)
// {

//     int SUM = 0;
//     int LT;
//     int LocalPRODUCT;

//     for(int i = l - 1; i >= 0; i--){
//         LT = ((ctext1[i] - ctext2[i]) % 2) * ctext2[i];
//         LocalPRODUCT = 1;
//         for(int j = i - 1; j >= 0; j--){
//             LocalPRODUCT *= 1 - ((ctext1[j] - ctext2[j]) % 2);
//         }
//         SUM += LT * LocalPRODUCT;
//     }

//     return (0 - SUM) % 2;
// }

// int main(){
//     int ctext1 [] = {1,0,0,0,0};
//     int ctext2 [] = {0,1,1,1,1};
//     int output = Sless_than_bits(ctext1, ctext2, 5);
//     printf("%d\n", output);
    
//     return 1;
// }
