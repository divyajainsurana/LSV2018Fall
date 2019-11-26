#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "base/abc/abc.h"
#include <iostream>

namespace
{
int Abc_ObjRecognizeExor( Abc_Frame_t * pAbc, int argc, char ** argv)
{
Abc_Ntk_t * pNtk = Abc_FrameReadNtk(pAbc);

    Abc_Obj_t * pObj;
    Abc_Obj_t * p0, * p1;
    Abc_Obj_t * ppFan0;
    Abc_Obj_t * ppFan1;
    int i;
        FILE* fout = fopen("pa1_r07943158.txt","w");

    for ( i = 0; (i < Vec_PtrSize((pNtk)->vObjs)) && (((pObj) = Abc_NtkObj(pNtk, i)), 1); i++ ) {   
        if ( (pObj) == NULL ) {
		printf("Empty Network\n");
		} else
	{
   assert( !Abc_ObjIsComplement(pObj) );
   if ( !Abc_ObjIsNode(pObj) )
   {}
 //   printf("there is no node\n");
    else  if ( Abc_NodeIsExorType(pObj) ){
    ppFan0 = Abc_ObjFanin0(pObj);
    ppFan1 = Abc_ObjFanin1(pObj);
     p0=Abc_ObjFanin0(ppFan0);
     p1=Abc_ObjFanin1(ppFan1);
    fprintf( fout, "Exor Node  %d = (%d , %d ) \n", pObj->Id, p0->Id, p1->Id );
  
             
             }
}} 
return 1;
}

// called during ABC startup
void init(Abc_Frame_t* pAbc)
{
    Cmd_CommandAdd( pAbc, "PA1", "lsv_xai", Abc_ObjRecognizeExor, 1);
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
