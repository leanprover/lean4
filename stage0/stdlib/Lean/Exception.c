// Lean compiler output
// Module: Lean.Exception
// Imports: Lean.Message Lean.InternalExceptionId Lean.Data.Options Lean.Util.MonadCache Lean.ErrorExplanation
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_getRef___boxed(lean_object*);
static lean_object* l_Lean_termThrowErrorAt___________closed__1;
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxRecDepth(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_unknownIdentifierMessageTag___closed__0;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21;
static lean_object* l_Lean_termThrowErrorAt___________closed__7;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8;
static lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__4;
static lean_object* l_Lean_throwInterruptException___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Exception___hyg_772_;
LEAN_EXPORT lean_object* l_Lean_unknownIdentifierMessageTag;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_termThrowError_______closed__4;
LEAN_EXPORT lean_object* l_Lean_termThrowError____;
LEAN_EXPORT lean_object* l_Lean_instInhabitedException;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_hasSyntheticSorry___boxed(lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7;
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13;
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedException___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___redArg___closed__2;
static lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_termThrowErrorAt___________closed__6;
LEAN_EXPORT lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17;
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_termThrowErrorAt________;
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11;
static lean_object* l_Lean_termThrowErrorAt___________closed__11;
LEAN_EXPORT lean_object* l_Lean_ofExcept___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1;
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg(lean_object*);
static lean_object* l_Lean_termThrowErrorAt___________closed__10;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
static lean_object* l_Lean_termThrowError_______closed__17;
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___redArg___closed__3;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_instInhabitedException___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwNamedErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_getRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_termThrowError_______closed__15;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwNamedErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Exception_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2(lean_object*, lean_object*);
static lean_object* l_Lean_termThrowError_______closed__11;
LEAN_EXPORT lean_object* l_Lean_throwNamedError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12;
static lean_object* l_Lean_termThrowError_______closed__13;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2;
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_throwInterruptException___redArg___closed__0;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_termThrowError_______closed__3;
static lean_object* l_Lean_termThrowError_______closed__10;
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_termThrowErrorAt___________closed__4;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_termThrowErrorAt___________closed__0;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
static lean_object* l_Lean_termThrowError_______closed__16;
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_termThrowErrorAt___________closed__9;
static lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static lean_object* l_Lean_termThrowError_______closed__12;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__3;
static lean_object* l_Lean_unknownIdentifierMessageTag___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_termThrowError_______closed__14;
static lean_object* l_Lean_termThrowErrorAt___________closed__5;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18;
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_termThrowError_______closed__1;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxRecDepth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_termThrowErrorAt___________closed__8;
static lean_object* l_Lean_throwUnknownConstantAt___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InternalExceptionId_toString(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___redArg___closed__0;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Exception___hyg_772_(lean_object*);
static lean_object* l_Lean_termThrowError_______closed__7;
static lean_object* l_Lean_termThrowError_______closed__6;
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9;
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16;
static lean_object* l_Lean_termThrowError_______closed__5;
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwUnknownConstantAt___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Exception_isInterrupt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_termThrowError_______closed__2;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___redArg(lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14;
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1(lean_object*, lean_object*);
static lean_object* l_Lean_termThrowError_______closed__8;
static lean_object* l_Lean_termThrowErrorAt___________closed__3;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_interruptExceptionId;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1;
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15;
static lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0;
static lean_object* l_Lean_termThrowError_______closed__0;
static lean_object* l_Lean_termThrowError_______closed__9;
static lean_object* l_Lean_termThrowErrorAt___________closed__2;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Exception___hyg_772_;
LEAN_EXPORT lean_object* l_Lean_Exception_toMessageData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_InternalExceptionId_toString(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_MessageData_ofFormat(x_5);
return x_6;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_hasSyntheticSorry(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_MessageData_hasSyntheticSorry(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_hasSyntheticSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_hasSyntheticSorry(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_getRef(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_getRef___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Exception_getRef(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedException___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedException___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedException___closed__0;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instInhabitedException() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedException___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_alloc_closure((void*)(l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg___lam__1), 5, 3);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_ctor_set(x_1, 1, x_5);
lean_ctor_set(x_1, 0, x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_2(x_1, x_5, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_throwError___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_9, 0, x_6);
lean_inc(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_throwError___redArg___lam__1), 5, 4);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_9);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwError___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_unknownIdentifierMessageTag___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknownIdentifier", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_unknownIdentifierMessageTag___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_unknownIdentifierMessageTag___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_unknownIdentifierMessageTag() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_unknownIdentifierMessageTag___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_apply_3(x_2, lean_box(0), x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_throwError___redArg(x_1, x_2, x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwErrorAt___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_MessageData_tagWithErrorName(x_1, x_2);
x_8 = lean_apply_2(x_3, x_6, x_7);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_throwError___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_10, 0, x_7);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_throwNamedError___redArg___lam__1), 6, 5);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_8);
lean_closure_set(x_11, 3, x_6);
lean_closure_set(x_11, 4, x_10);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwNamedError___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedErrorAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_throwNamedError___redArg(x_1, x_2, x_4, x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwNamedErrorAt___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_unknownIdentifierMessageTag;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_mkUnknownIdentifierMessage(x_4);
x_6 = l_Lean_throwErrorAt___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownIdentifierAt___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstantAt___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwUnknownConstantAt___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = l_Lean_throwUnknownConstantAt___redArg___closed__1;
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
x_8 = l_Lean_MessageData_ofConstName(x_4, x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_throwUnknownConstantAt___redArg___closed__3;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwUnknownIdentifierAt___redArg(x_1, x_2, x_3, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstantAt___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstantAt___redArg(x_1, x_2, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_throwUnknownConstant___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstant___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_1(x_3, x_6);
x_8 = l_Lean_throwError___redArg(x_1, x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ofExcept___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Exception___hyg_772_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interrupt", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Exception___hyg_772_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Exception___hyg_772_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Exception___hyg_772_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Exception___hyg_772_;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwInterruptException___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_interruptExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_throwInterruptException___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_throwInterruptException___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_throwInterruptException___redArg___closed__1;
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwInterruptException___redArg(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwInterruptException(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isInterrupt(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_throwInterruptException___redArg___closed__0;
x_6 = lean_nat_dec_eq(x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isInterrupt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_isInterrupt(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Kernel_Exception_toMessageData(x_1, x_4);
x_6 = l_Lean_throwError___redArg(x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
if (lean_obj_tag(x_4) == 16)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_inc(x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_7);
x_9 = l_Lean_throwInterruptException___redArg(x_2);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_throwKernelException___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_12, 0, x_6);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_7);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_11, lean_box(0), x_13);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_14, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwKernelException___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwKernelException___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_throwKernelException___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ofExceptKernelException___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_4, x_5);
x_8 = lean_apply_3(x_6, lean_box(0), x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__0), 5, 1);
lean_closure_set(x_2, 0, x_1);
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instMonadRecDepthReaderT___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instMonadRecDepthReaderT___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthReaderT___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instMonadRecDepthReaderT___redArg___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instMonadRecDepthReaderT___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_instMonadRecDepthReaderT___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthStateRefT_x27OfMonad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_instMonadRecDepthStateRefT_x27OfMonad(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instMonadRecDepthReaderT___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_instMonadRecDepthReaderT___redArg(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadRecDepthMonadCacheTOfMonad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_instMonadRecDepthMonadCacheTOfMonad(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information", 157, 157);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___redArg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___redArg___closed__5;
x_2 = l_Lean_throwMaxRecDepthAt___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_dec(x_6);
x_7 = l_Lean_throwMaxRecDepthAt___redArg___closed__6;
lean_ctor_set(x_3, 1, x_7);
lean_ctor_set(x_3, 0, x_2);
x_8 = lean_apply_2(x_5, lean_box(0), x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_throwMaxRecDepthAt___redArg___closed__6;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_apply_2(x_9, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwMaxRecDepthAt___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Exception_isMaxRecDepth(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Lean_throwMaxRecDepthAt___redArg___closed__0;
x_9 = lean_string_dec_eq(x_7, x_8);
if (x_9 == 0)
{
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_throwMaxRecDepthAt___redArg___closed__1;
x_11 = lean_string_dec_eq(x_6, x_10);
return x_11;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Exception_isMaxRecDepth___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Exception_isMaxRecDepth(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = lean_apply_3(x_2, lean_box(0), x_10, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_6);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
lean_dec(x_3);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_2);
lean_inc(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(x_10, 0, x_6);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_8);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
lean_dec(x_5);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__0), 2, 1);
lean_closure_set(x_11, 0, x_4);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_withIncRecDepth___redArg___lam__2), 7, 6);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_7);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_10);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_withIncRecDepth___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withIncRecDepth___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("termThrowError__", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termThrowError_______closed__1;
x_2 = l_Lean_termThrowError_______closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("andthen", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termThrowError_______closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwError ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termThrowError_______closed__5;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("orelse", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termThrowError_______closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termThrowError_______closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termThrowError_______closed__11;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_termThrowError_______closed__12;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termThrowError_______closed__13;
x_2 = l_Lean_termThrowError_______closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termThrowError_______closed__13;
x_2 = l_Lean_termThrowError_______closed__14;
x_3 = l_Lean_termThrowError_______closed__8;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termThrowError_______closed__15;
x_2 = l_Lean_termThrowError_______closed__6;
x_3 = l_Lean_termThrowError_______closed__4;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_termThrowError_______closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termThrowError_______closed__16;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_termThrowError_______closed__2;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_termThrowError____() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_termThrowError_______closed__17;
return x_1;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("termThrowErrorAt____", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_termThrowErrorAt___________closed__0;
x_2 = l_Lean_termThrowError_______closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwErrorAt ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termThrowErrorAt___________closed__2;
x_2 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1024u);
x_2 = l_Lean_termThrowError_______closed__12;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termThrowErrorAt___________closed__4;
x_2 = l_Lean_termThrowErrorAt___________closed__3;
x_3 = l_Lean_termThrowError_______closed__4;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ppSpace", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termThrowErrorAt___________closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_termThrowErrorAt___________closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termThrowErrorAt___________closed__8;
x_2 = l_Lean_termThrowErrorAt___________closed__5;
x_3 = l_Lean_termThrowError_______closed__4;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termThrowError_______closed__15;
x_2 = l_Lean_termThrowErrorAt___________closed__9;
x_3 = l_Lean_termThrowError_______closed__4;
x_4 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt___________closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_termThrowErrorAt___________closed__10;
x_2 = lean_unsigned_to_nat(1022u);
x_3 = l_Lean_termThrowErrorAt___________closed__1;
x_4 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_termThrowErrorAt________() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_termThrowErrorAt___________closed__11;
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("interpolatedStrKind", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4;
x_2 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3;
x_3 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2;
x_4 = l_Lean_termThrowError_______closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.throwError", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwError", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8;
x_2 = l_Lean_termThrowError_______closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12;
x_2 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16;
x_2 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3;
x_3 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2;
x_4 = l_Lean_termThrowError_______closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("termM!_", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19;
x_2 = l_Lean_termThrowError_______closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("m!", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_termThrowError_______closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
lean_dec(x_1);
x_10 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1;
lean_inc(x_9);
x_11 = l_Lean_Syntax_isOfKind(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_SourceInfo_fromRef(x_14, x_11);
lean_dec(x_14);
x_16 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
x_17 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7;
x_18 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9;
x_19 = l_Lean_addMacroScope(x_12, x_18, x_13);
x_20 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13;
lean_inc(x_15);
x_21 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_20);
x_22 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15;
lean_inc(x_15);
x_23 = l_Lean_Syntax_node1(x_15, x_22, x_9);
x_24 = l_Lean_Syntax_node2(x_15, x_16, x_21, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 5);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_SourceInfo_fromRef(x_28, x_30);
lean_dec(x_28);
x_32 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
x_33 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7;
x_34 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9;
x_35 = l_Lean_addMacroScope(x_26, x_34, x_27);
x_36 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13;
lean_inc(x_31);
x_37 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_36);
x_38 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15;
x_39 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17;
x_40 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18;
lean_inc(x_31);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20;
x_43 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21;
lean_inc(x_31);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_31);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_31);
x_45 = l_Lean_Syntax_node2(x_31, x_42, x_44, x_9);
x_46 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22;
lean_inc(x_31);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_46);
lean_inc(x_31);
x_48 = l_Lean_Syntax_node3(x_31, x_39, x_41, x_45, x_47);
lean_inc(x_31);
x_49 = l_Lean_Syntax_node1(x_31, x_38, x_48);
x_50 = l_Lean_Syntax_node2(x_31, x_32, x_37, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_3);
return x_51;
}
}
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.throwErrorAt", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0;
x_2 = l_String_toSubstring_x27(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("throwErrorAt", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2;
x_2 = l_Lean_termThrowError_______closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_termThrowErrorAt___________closed__1;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1;
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_SourceInfo_fromRef(x_16, x_13);
lean_dec(x_16);
x_18 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
x_19 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1;
x_20 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3;
x_21 = l_Lean_addMacroScope(x_14, x_20, x_15);
x_22 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5;
lean_inc(x_17);
x_23 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_23, 3, x_22);
x_24 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15;
lean_inc(x_17);
x_25 = l_Lean_Syntax_node2(x_17, x_24, x_9, x_11);
x_26 = l_Lean_Syntax_node2(x_17, x_18, x_23, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 5);
lean_inc(x_30);
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
x_33 = l_Lean_SourceInfo_fromRef(x_30, x_32);
lean_dec(x_30);
x_34 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5;
x_35 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1;
x_36 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3;
x_37 = l_Lean_addMacroScope(x_28, x_36, x_29);
x_38 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5;
lean_inc(x_33);
x_39 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
x_40 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15;
x_41 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17;
x_42 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18;
lean_inc(x_33);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20;
x_45 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21;
lean_inc(x_33);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_33);
x_47 = l_Lean_Syntax_node2(x_33, x_44, x_46, x_11);
x_48 = l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22;
lean_inc(x_33);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_33);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_33);
x_50 = l_Lean_Syntax_node3(x_33, x_41, x_43, x_47, x_49);
lean_inc(x_33);
x_51 = l_Lean_Syntax_node2(x_33, x_40, x_9, x_50);
x_52 = l_Lean_Syntax_node2(x_33, x_34, x_39, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
return x_53;
}
}
}
}
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_InternalExceptionId(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanation(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Exception(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_InternalExceptionId(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ErrorExplanation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedException___closed__0 = _init_l_Lean_instInhabitedException___closed__0();
lean_mark_persistent(l_Lean_instInhabitedException___closed__0);
l_Lean_instInhabitedException___closed__1 = _init_l_Lean_instInhabitedException___closed__1();
lean_mark_persistent(l_Lean_instInhabitedException___closed__1);
l_Lean_instInhabitedException = _init_l_Lean_instInhabitedException();
lean_mark_persistent(l_Lean_instInhabitedException);
l_Lean_unknownIdentifierMessageTag___closed__0 = _init_l_Lean_unknownIdentifierMessageTag___closed__0();
lean_mark_persistent(l_Lean_unknownIdentifierMessageTag___closed__0);
l_Lean_unknownIdentifierMessageTag___closed__1 = _init_l_Lean_unknownIdentifierMessageTag___closed__1();
lean_mark_persistent(l_Lean_unknownIdentifierMessageTag___closed__1);
l_Lean_unknownIdentifierMessageTag = _init_l_Lean_unknownIdentifierMessageTag();
lean_mark_persistent(l_Lean_unknownIdentifierMessageTag);
l_Lean_throwUnknownConstantAt___redArg___closed__0 = _init_l_Lean_throwUnknownConstantAt___redArg___closed__0();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___redArg___closed__0);
l_Lean_throwUnknownConstantAt___redArg___closed__1 = _init_l_Lean_throwUnknownConstantAt___redArg___closed__1();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___redArg___closed__1);
l_Lean_throwUnknownConstantAt___redArg___closed__2 = _init_l_Lean_throwUnknownConstantAt___redArg___closed__2();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___redArg___closed__2);
l_Lean_throwUnknownConstantAt___redArg___closed__3 = _init_l_Lean_throwUnknownConstantAt___redArg___closed__3();
lean_mark_persistent(l_Lean_throwUnknownConstantAt___redArg___closed__3);
l_Lean_initFn___closed__0____x40_Lean_Exception___hyg_772_ = _init_l_Lean_initFn___closed__0____x40_Lean_Exception___hyg_772_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Exception___hyg_772_);
l_Lean_initFn___closed__1____x40_Lean_Exception___hyg_772_ = _init_l_Lean_initFn___closed__1____x40_Lean_Exception___hyg_772_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Exception___hyg_772_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Exception___hyg_772_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_interruptExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_interruptExceptionId);
lean_dec_ref(res);
}l_Lean_throwInterruptException___redArg___closed__0 = _init_l_Lean_throwInterruptException___redArg___closed__0();
lean_mark_persistent(l_Lean_throwInterruptException___redArg___closed__0);
l_Lean_throwInterruptException___redArg___closed__1 = _init_l_Lean_throwInterruptException___redArg___closed__1();
lean_mark_persistent(l_Lean_throwInterruptException___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___redArg___closed__5);
l_Lean_throwMaxRecDepthAt___redArg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___redArg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___redArg___closed__6);
l_Lean_termThrowError_______closed__0 = _init_l_Lean_termThrowError_______closed__0();
lean_mark_persistent(l_Lean_termThrowError_______closed__0);
l_Lean_termThrowError_______closed__1 = _init_l_Lean_termThrowError_______closed__1();
lean_mark_persistent(l_Lean_termThrowError_______closed__1);
l_Lean_termThrowError_______closed__2 = _init_l_Lean_termThrowError_______closed__2();
lean_mark_persistent(l_Lean_termThrowError_______closed__2);
l_Lean_termThrowError_______closed__3 = _init_l_Lean_termThrowError_______closed__3();
lean_mark_persistent(l_Lean_termThrowError_______closed__3);
l_Lean_termThrowError_______closed__4 = _init_l_Lean_termThrowError_______closed__4();
lean_mark_persistent(l_Lean_termThrowError_______closed__4);
l_Lean_termThrowError_______closed__5 = _init_l_Lean_termThrowError_______closed__5();
lean_mark_persistent(l_Lean_termThrowError_______closed__5);
l_Lean_termThrowError_______closed__6 = _init_l_Lean_termThrowError_______closed__6();
lean_mark_persistent(l_Lean_termThrowError_______closed__6);
l_Lean_termThrowError_______closed__7 = _init_l_Lean_termThrowError_______closed__7();
lean_mark_persistent(l_Lean_termThrowError_______closed__7);
l_Lean_termThrowError_______closed__8 = _init_l_Lean_termThrowError_______closed__8();
lean_mark_persistent(l_Lean_termThrowError_______closed__8);
l_Lean_termThrowError_______closed__9 = _init_l_Lean_termThrowError_______closed__9();
lean_mark_persistent(l_Lean_termThrowError_______closed__9);
l_Lean_termThrowError_______closed__10 = _init_l_Lean_termThrowError_______closed__10();
lean_mark_persistent(l_Lean_termThrowError_______closed__10);
l_Lean_termThrowError_______closed__11 = _init_l_Lean_termThrowError_______closed__11();
lean_mark_persistent(l_Lean_termThrowError_______closed__11);
l_Lean_termThrowError_______closed__12 = _init_l_Lean_termThrowError_______closed__12();
lean_mark_persistent(l_Lean_termThrowError_______closed__12);
l_Lean_termThrowError_______closed__13 = _init_l_Lean_termThrowError_______closed__13();
lean_mark_persistent(l_Lean_termThrowError_______closed__13);
l_Lean_termThrowError_______closed__14 = _init_l_Lean_termThrowError_______closed__14();
lean_mark_persistent(l_Lean_termThrowError_______closed__14);
l_Lean_termThrowError_______closed__15 = _init_l_Lean_termThrowError_______closed__15();
lean_mark_persistent(l_Lean_termThrowError_______closed__15);
l_Lean_termThrowError_______closed__16 = _init_l_Lean_termThrowError_______closed__16();
lean_mark_persistent(l_Lean_termThrowError_______closed__16);
l_Lean_termThrowError_______closed__17 = _init_l_Lean_termThrowError_______closed__17();
lean_mark_persistent(l_Lean_termThrowError_______closed__17);
l_Lean_termThrowError____ = _init_l_Lean_termThrowError____();
lean_mark_persistent(l_Lean_termThrowError____);
l_Lean_termThrowErrorAt___________closed__0 = _init_l_Lean_termThrowErrorAt___________closed__0();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__0);
l_Lean_termThrowErrorAt___________closed__1 = _init_l_Lean_termThrowErrorAt___________closed__1();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__1);
l_Lean_termThrowErrorAt___________closed__2 = _init_l_Lean_termThrowErrorAt___________closed__2();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__2);
l_Lean_termThrowErrorAt___________closed__3 = _init_l_Lean_termThrowErrorAt___________closed__3();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__3);
l_Lean_termThrowErrorAt___________closed__4 = _init_l_Lean_termThrowErrorAt___________closed__4();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__4);
l_Lean_termThrowErrorAt___________closed__5 = _init_l_Lean_termThrowErrorAt___________closed__5();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__5);
l_Lean_termThrowErrorAt___________closed__6 = _init_l_Lean_termThrowErrorAt___________closed__6();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__6);
l_Lean_termThrowErrorAt___________closed__7 = _init_l_Lean_termThrowErrorAt___________closed__7();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__7);
l_Lean_termThrowErrorAt___________closed__8 = _init_l_Lean_termThrowErrorAt___________closed__8();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__8);
l_Lean_termThrowErrorAt___________closed__9 = _init_l_Lean_termThrowErrorAt___________closed__9();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__9);
l_Lean_termThrowErrorAt___________closed__10 = _init_l_Lean_termThrowErrorAt___________closed__10();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__10);
l_Lean_termThrowErrorAt___________closed__11 = _init_l_Lean_termThrowErrorAt___________closed__11();
lean_mark_persistent(l_Lean_termThrowErrorAt___________closed__11);
l_Lean_termThrowErrorAt________ = _init_l_Lean_termThrowErrorAt________();
lean_mark_persistent(l_Lean_termThrowErrorAt________);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__0);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__1);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__2);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__3);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__4);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__5);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__6);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__7);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__8);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__9);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__10);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__11);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__12);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__13);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__14);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__15);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__16);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__17);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__18);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__19);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__20);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__21);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowError______1___closed__22);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__0);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__1);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__2);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__3);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__4);
l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5 = _init_l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5();
lean_mark_persistent(l_Lean___aux__Lean__Exception______macroRules__Lean__termThrowErrorAt__________1___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
