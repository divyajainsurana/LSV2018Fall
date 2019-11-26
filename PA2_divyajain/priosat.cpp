#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "base/abc/abc.h"
#include "sat/cnf/cnf.h"
#include "aig/aig/aig.h"
#include "aig/saig/saig.h"

extern "C" Aig_Man_t * Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
static int Abc_LsvCommandPrioSAT( Abc_Frame_t * , int , char ** );

namespace
{

void myPrintPrime(int min, Vec_Int_t* prime_implicant_All, int ciNum) {
    int i = 0, j = 0;
    int entry = 0, conflict = 0;
    Vec_IntForEachEntry(prime_implicant_All, entry, i) {
        conflict = 0;
        int keepMin = min;
        int keepEntry = entry;
        for (j = 0; j < ciNum; j++) {
            if (keepMin%3 + entry%3 == 1) {
                conflict = 1;
                break;
            }
            keepMin /= 3;
            entry /= 3;
        }
        if (!conflict) {
            for (j = 0; j < ciNum; j++) {
                if (keepEntry%3 == 2)
                    printf("-");
                else
                    printf("%d", keepEntry%3);
                keepEntry /= 3;
            }
            printf("\n");
        }
    }
}


int minterm_2To3(int mEntry1, int ciNum) {
    int i = 0;
    int ret = 0;
    for (i = 0; i < ciNum; i++) {
        ret += (mEntry1%2) * pow(3, i);
        mEntry1 /= 2;
    }
    return ret;
}

int match(int mEntry1, int mEntry2, int* combined, int ciNum) {

    (*combined) = 0;
    int mE1 = mEntry1-1;
    if (mEntry1 < 0)
        mE1 = -mEntry1-1;
    int mE2 = mEntry2-1;
    if (mEntry2 < 0)
        mE2 = -mEntry2-1;

    int i = 0;
    int mismatch = 0;
    int mismatchIdx = 0;
    int mE1_At_MisMatchIdx = 0;
    for (i = 0; i < ciNum; i++) {
        (*combined) += mE1%2 * pow(3, i);
        if (mE1%2 != mE2%2) {
            mismatch++;
            mismatchIdx = i;
            mE1_At_MisMatchIdx = mE1%2;
            if (mismatch > 1)
                return 0;
        }
        mE1/=2;
        mE2/=2;
    }
    (*combined) += (2 - mE1_At_MisMatchIdx)*pow(3, mismatchIdx);
    return 1;
}

int match_3(int mEntry1, int mEntry2, int* combined, int ciNum) {

    (*combined) = 0;
    int mE1 = mEntry1;
    if (mEntry1 < 0)
        mE1 = -mEntry1;
    int mE2 = mEntry2;
    if (mEntry2 < 0)
        mE2 = -mEntry2;

    int i = 0;
    int mismatch = 0;
    int mismatchIdx = 0;
    int mE1_At_MisMatchIdx = 0;
    for (i = 0; i < ciNum; i++) {
        (*combined) += mE1%3 * pow(3, i);
        if (mE1%3 != mE2%3) {
            mismatch++;
            mismatchIdx = i;
            mE1_At_MisMatchIdx = mE1%3;
            if (mismatch > 1)
                return 0;
        }
        mE1/=3;
        mE2/=3;
    }
    (*combined) += (2 - mE1_At_MisMatchIdx)*pow(3, mismatchIdx);
    //printf("Yield %d\n", (*combined));
    return 1;
}

int Abc_LsvCommandPrioSAT(Abc_Frame_t * pAbc, int argc, char ** argv )
{

    int k_smallest_min = 0;
    sscanf(argv[2], "%d", &k_smallest_min);
        int i = 0, j = 0, k = 0, l = 0;
    int index = 0;
    int pow_Of_PI = 0;
    Abc_Ntk_t * pNtk = NULL;
    Aig_Man_t * pMan = NULL;
    int satResult = 0;
    int* unitassumplits = 0;

    Aig_Obj_t * pObj = NULL, * pObj_PI = NULL;
    sat_solver * pSat = NULL;
    Cnf_Dat_t * pCnf = NULL;

    //3 different arrays to collect minterm
    //1st way: size: 2^I, 0 means offset, 1 means onset
    int* minterm_All_IsOnset = 0;
    //2nd way: size: number of minterm, store idx of minterm
    Vec_Int_t* minterm_OnsetOnly = 0;
    //3rd way: 2D array, size: size of input + 1, store minterm by number of 1
    Vec_Ptr_t* minterm_OnsetOnly_ByNumberOfOne = 0;
    Vec_Ptr_t* prime_With_n_DontCare = 0;
    Vec_Ptr_t* pEntry = 0;
    Vec_Int_t* prime_implicant_All = 0;
    int mEntry1 = 0, mEntry2 = 0;
    int combined = 0;
    //end variable declaration

    //process options
    
    // step.1: get the current network
    pNtk = Abc_FrameReadNtk(pAbc);
    if ( pNtk == NULL )
    {
        Abc_Print( -1, "Empty network.\n" );
        return 1;
    }

    // step.2: check whether the current network is strashed
    if ( !Abc_NtkIsStrash(pAbc->pNtkCur) ) {
        // get the new network
        Abc_Ntk_t * pNtkRes = Abc_NtkStrash( pNtk, 0, 1, 0 );
        if ( pNtkRes == NULL )
        {
            Abc_Print( -1, "Strashing has failed.\n" );
            return 1;
        }
        // replace the current network
        Abc_FrameReplaceCurrentNetwork( pAbc, pNtkRes );
    }

    pNtk = Abc_FrameReadNtk(pAbc);
    pMan = Abc_NtkToDar(pNtk, 0, 1);  //pMan = Abc_AigAlloc(pNtk);
    
    unitassumplits = (int *)malloc( (Aig_ManCiNum(pMan) +1) * sizeof(int));

    pow_Of_PI = pow(2, Aig_ManCiNum(pMan));

    minterm_All_IsOnset = (int *)malloc( pow_Of_PI * sizeof(int));
    minterm_OnsetOnly = Vec_IntStart(0);
    minterm_OnsetOnly_ByNumberOfOne = Vec_PtrStart(Aig_ManCiNum(pMan)+1);
    for (i = 0; i < Aig_ManCiNum(pMan)+1; i++) {
        Vec_PtrWriteEntry(minterm_OnsetOnly_ByNumberOfOne, i, Vec_IntStart(0));
    }
    //printf("%d\n", pow_Of_PI);
    prime_implicant_All = Vec_IntStart(0);

    pCnf = Cnf_DeriveSimple( pMan, Aig_ManCoNum(pMan) );  
    pSat = sat_solver_new();
    sat_solver_setnvars( pSat, pCnf->nVars );
    for ( i = 0; i < pCnf->nClauses; i++ )
        if ( !sat_solver_addclause( pSat, pCnf->pClauses[i], pCnf->pClauses[i+1] ) )
            assert( 0 );

   
    Aig_ManForEachCo( pMan, pObj, i ) {
        unitassumplits[0] = toLitCond( pCnf->pVarNums[pObj->Id], 0 );
        for (index = 0; index < pow_Of_PI; index++) {
            int keep = index;
            int numberOfOne = 0;
            Aig_ManForEachCi(pMan, pObj_PI, j) {
                if (keep%2)
                    numberOfOne++;
                unitassumplits[j+1] = toLitCond(pCnf->pVarNums[pObj_PI->Id], keep%2^1 );
                keep = keep / 2;
            }
            
	   // printf("numberOfOne = %d\n", numberOfOne);

            satResult = sat_solver_solve( pSat, unitassumplits, (unitassumplits)+(Aig_ManCiNum(pMan)+1) , (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0, (ABC_INT64_T)0 );

            if ( satResult == l_False )
            {
                minterm_All_IsOnset[index] = 0;
            }
            else if ( satResult == l_True ) //Output %d of miter \"%s\" was asserted in frame
            {
                minterm_All_IsOnset[index] = 1;
                Vec_IntPush(minterm_OnsetOnly, index);
                Vec_IntPush((Vec_Int_t *)Vec_PtrEntry(minterm_OnsetOnly_ByNumberOfOne, numberOfOne), index+1);

                            }
            else //No output asserted
            {
                printf("No_output_asserted\n");
            }



        }
    }// ForEachCo

    
       prime_With_n_DontCare = Vec_PtrStart(0);
    for (i = 0; i < Aig_ManCiNum(pMan); i++) {
        Vec_PtrPush(prime_With_n_DontCare, Vec_PtrStart(0));
    }
    Vec_PtrForEachEntry( Vec_Ptr_t*, prime_With_n_DontCare, pEntry, i ) {
        // i = 0, with CiNum entries
        // i = 1, with CiNum-1 entries
        // ...
        // i = CiNum-1, with 1 entry
        for (j = 0; j < Aig_ManCiNum(pMan)-i; j++) {
            Vec_PtrPush(pEntry, Vec_IntStart(0));
        }
    }
    //how to mark prime used?
    //negative: can't, becuz 0 = -0
    //now: shift 1, 0 -> 1

    for (i = 0; i < Aig_ManCiNum(pMan); i++) {
        //printf("i %d\n", i);
        //printf("size %d\n", Vec_PtrSize(minterm_OnsetOnly_ByNumberOfOne));
        Vec_Int_t* vec1 = (Vec_Int_t *)Vec_PtrEntry(minterm_OnsetOnly_ByNumberOfOne, i);
        Vec_Int_t* vec2 = (Vec_Int_t *)Vec_PtrEntry(minterm_OnsetOnly_ByNumberOfOne, i+1);
        //printf("i %d\n", i);

        Vec_IntForEachEntry(vec1, mEntry1, j) {
            Vec_IntForEachEntry(vec2, mEntry2, k) {
                if(match(mEntry1, mEntry2, &combined, Aig_ManCiNum(pMan))) {
                    Vec_IntPush((Vec_Int_t*)Vec_PtrEntry((Vec_Ptr_t*)Vec_PtrEntry(prime_With_n_DontCare, 0), i), (combined));
                    if (mEntry1 > 0) {
                        Vec_IntWriteEntry(vec1, j, -mEntry1);
                    }
                    if (mEntry2 > 0) {
                        Vec_IntWriteEntry(vec2, k, -mEntry2);
                    }
                }
            }
        }
        Vec_IntForEachEntry(vec1, mEntry1, j) {
            if (mEntry1 > 0) {
                Vec_IntPush(prime_implicant_All, minterm_2To3(mEntry1, Aig_ManCiNum(pMan)));
            }
        }
        if (i == Aig_ManCiNum(pMan)-1) {
            Vec_IntForEachEntry(vec2, mEntry1, j) {
                if (mEntry1 > 0) {
                    Vec_IntPush(prime_implicant_All, minterm_2To3(mEntry1, Aig_ManCiNum(pMan)));
                }
            }
        }
    }

    Vec_PtrForEachEntry( Vec_Ptr_t*, prime_With_n_DontCare, pEntry, i ) {
        if (i == 0)
            continue;
        //printf("i %d\n", i);
        // i = 0, with CiNum entries
        // i = 1, with CiNum-1 entries
        // ...
        // i = CiNum-1, with 1 entry
        Vec_Ptr_t* vecPtr1 = (Vec_Ptr_t*)Vec_PtrEntry(prime_With_n_DontCare, i-1);
        // there are Ci-(i-1) entries, so Ci-(i-1)-1 = Ci-i comparisons is needed
        for (j = 0; j < Aig_ManCiNum(pMan)-i; j++) {
            //printf("j %d\n", j);
            Vec_Int_t* vec1 = (Vec_Int_t *)Vec_PtrEntry(vecPtr1, j);
            Vec_Int_t* vec2 = (Vec_Int_t *)Vec_PtrEntry(vecPtr1, j+1);
            Vec_IntForEachEntry(vec1, mEntry1, k) {
                Vec_IntForEachEntry(vec2, mEntry2, l) {
                    if(match_3(mEntry1, mEntry2, &combined, Aig_ManCiNum(pMan))) {
                        Vec_IntPush((Vec_Int_t*)Vec_PtrEntry(pEntry, j), (combined));
                        if (mEntry1 > 0)
                            Vec_IntWriteEntry(vec1, k, -mEntry1);
                        if (mEntry2 > 0)
                            Vec_IntWriteEntry(vec2, l, -mEntry2);
                    }
                }
            }
            Vec_IntForEachEntry(vec1, mEntry1, k) {
                if (mEntry1 > 0) {
                    Vec_IntPush(prime_implicant_All, mEntry1);
                }
            }
            if (j == Aig_ManCiNum(pMan)-i-1) {
                Vec_IntForEachEntry(vec2, mEntry1, k) {
                    if (mEntry1 > 0) {
                        Vec_IntPush(prime_implicant_All, mEntry1);
                    }
                }
            }
            Vec_IntUniqify((Vec_Int_t*)Vec_PtrEntry(pEntry, j));
        }


    }
        if (k_smallest_min > Vec_IntSize(minterm_OnsetOnly))
        k_smallest_min = Vec_IntSize(minterm_OnsetOnly);


    printf("#smallest %d minterms:\n", k_smallest_min);
    for (i = 0; i < k_smallest_min; i++) {
    int j = 0;
    int smallest_min = Vec_IntEntry(minterm_OnsetOnly, i);
    for (j = 0; j < Aig_ManCiNum(pMan); j++) {
	            printf("%d", smallest_min%2);
        smallest_min /= 2;
    }
    printf("\n");
}


    

    printf("\n#primes:\n");
    for (i = 0; i < k_smallest_min; i++) {
        myPrintPrime(minterm_2To3(Vec_IntEntry(minterm_OnsetOnly, i), Aig_ManCiNum(pMan)), prime_implicant_All, Aig_ManCiNum(pMan));
        printf(";\n");
    }

    printf("\n#largest %d minterms:\n", k_smallest_min);
    for (i = Vec_IntSize(minterm_OnsetOnly)-1; i > Vec_IntSize(minterm_OnsetOnly)-1- k_smallest_min ; i--) {
	    int j =0;
	    int largest_min=Vec_IntEntry(minterm_OnsetOnly, i);

        for (j = 0; j < Aig_ManCiNum(pMan); j++) {
	            printf("%d", largest_min%2);
        largest_min /= 2;
    }
    printf("\n");
}
    

    printf("\n#primes:\n");
    for (i = Vec_IntSize(minterm_OnsetOnly)-1; i > Vec_IntSize(minterm_OnsetOnly)-1- k_smallest_min ; i--) {
        myPrintPrime(minterm_2To3(Vec_IntEntry(minterm_OnsetOnly, i), Aig_ManCiNum(pMan)), prime_implicant_All, Aig_ManCiNum(pMan));
        printf(";\n");
    }


    return 0;

}

// called during ABC startup
void init(Abc_Frame_t* pAbc)
{
    Cmd_CommandAdd( pAbc, "PA2", "priosat", Abc_LsvCommandPrioSAT, 0);
}

// called during ABC termination
void destroy(Abc_Frame_t* pAbc)
{
}

// this object should not be modified after the call to Abc_FrameAddInitializer
Abc_FrameInitializer_t frame_initializer = { init, destroy };

// register the initializer a constructor of a global object
// called before main (and ABC startup)
struct registrar
{
    registrar() 
    {
        Abc_FrameAddInitializer(&frame_initializer);
    }
} hello_registrar;

} // unnamed namespace

