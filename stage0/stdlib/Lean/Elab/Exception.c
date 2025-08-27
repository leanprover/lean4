// Lean compiler output
// Module: Lean.Elab.Exception
// Imports: Lean.InternalExceptionId Lean.Exception
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___redArg(lean_object*);
static lean_object* l_Lean_Elab_throwAbortTactic___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortTacticException___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
uint8_t l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId_1935416772____hygCtx___hyg_23_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwPostpone___redArg___closed__1;
static lean_object* l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_;
static lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0;
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___redArg(lean_object*);
static lean_object* l_Lean_Elab_throwPostpone___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_(lean_object*);
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAbortTactic___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Elab_abortCommandExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_;
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3;
lean_object* l_Lean_KVMap_getName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_(lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_;
static lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0;
static lean_object* l_Lean_Elab_throwAbortTerm___redArg___closed__1;
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAbortCommand___redArg___closed__0;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__1;
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1;
static lean_object* l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_;
static lean_object* l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone___redArg(lean_object*);
static lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(lean_object*);
static lean_object* l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Elab_abortTermExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortTacticException(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___redArg(lean_object*);
static lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2;
static lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insert(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_postponeExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_autoBoundImplicitExceptionId;
static lean_object* l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_;
static lean_object* l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_;
static lean_object* l_Lean_Elab_mkMessageCore___closed__0;
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_KVMap_empty;
static lean_object* l_Lean_Elab_throwAbortTerm___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_(lean_object*);
static lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortExceptionId___boxed(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Elab_throwAbortCommand___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_abortTacticExceptionId;
static lean_object* l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_;
static lean_object* _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("postpone", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsupportedSyntax", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("abortCommandElab", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("abortTermElab", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("abortTactic", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("autoBoundImplicit", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_throwPostpone___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_postponeExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwPostpone___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwPostpone___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Elab_throwPostpone___redArg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwPostpone(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwPostpone___redArg(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwUnsupportedSyntax___redArg(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed syntax", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1;
x_4 = l_Lean_throwError___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwIllFormedSyntax___redArg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_autoBoundImplicitExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_KVMap_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("localId", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0;
x_7 = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1;
x_8 = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__3;
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = l_Lean_KVMap_insert(x_7, x_8, x_9);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_6);
x_11 = lean_apply_2(x_4, lean_box(0), x_1);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0;
x_14 = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1;
x_15 = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__3;
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = l_Lean_KVMap_insert(x_14, x_15, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_apply_2(x_12, lean_box(0), x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAutoBoundImplicitLocal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0;
x_6 = l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId_1935416772____hygCtx___hyg_23_(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__3;
x_9 = l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1;
x_10 = l_Lean_KVMap_getName(x_4, x_8, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_isAutoBoundImplicitLocalException_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a universe level named `", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has already been declared", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1;
x_5 = l_Lean_MessageData_ofName(x_3);
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_throwError___redArg(x_1, x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg(x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_abortCommandExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwAbortCommand___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Elab_throwAbortCommand___redArg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwAbortCommand___redArg(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_abortTermExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwAbortTerm___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Elab_throwAbortTerm___redArg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwAbortTerm___redArg(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_abortTacticExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTactic___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwAbortTactic___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_Lean_Elab_throwAbortTactic___redArg___closed__1;
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwAbortTactic___redArg(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortTacticException(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Elab_throwAbortTactic___redArg___closed__0;
x_5 = l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId_1935416772____hygCtx___hyg_23_(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortTacticException___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_isAbortTacticException(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_isAbortExceptionId(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Elab_throwAbortCommand___redArg___closed__0;
x_7 = l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId_1935416772____hygCtx___hyg_23_(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Elab_throwAbortTerm___redArg___closed__0;
x_9 = l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId_1935416772____hygCtx___hyg_23_(x_1, x_8);
x_2 = x_9;
goto block_5;
}
else
{
x_2 = x_7;
goto block_5;
}
block_5:
{
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_throwAbortTactic___redArg___closed__0;
x_4 = l_Lean_beqInternalExceptionId____x40_Lean_InternalExceptionId_1935416772____hygCtx___hyg_23_(x_1, x_3);
return x_4;
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_isAbortExceptionId___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_isAbortExceptionId(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_mkMessageCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_inc_ref(x_2);
x_7 = l_Lean_FileMap_toPosition(x_2, x_5);
x_8 = l_Lean_FileMap_toPosition(x_2, x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 0;
x_11 = l_Lean_Elab_mkMessageCore___closed__0;
x_12 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_12, 4, x_3);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_4);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 2, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
x_8 = l_Lean_Elab_mkMessageCore(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* initialize_Lean_InternalExceptionId(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Exception(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Exception(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_InternalExceptionId(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_);
l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3148402294____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_postponeExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_postponeExceptionId);
lean_dec_ref(res);
}l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_);
l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception_2911972506____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_unsupportedSyntaxExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_unsupportedSyntaxExceptionId);
lean_dec_ref(res);
}l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_);
l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3103249956____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortCommandExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortCommandExceptionId);
lean_dec_ref(res);
}l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_);
l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception_125629251____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortTermExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortTermExceptionId);
lean_dec_ref(res);
}l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_);
l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3863513224____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_abortTacticExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_abortTacticExceptionId);
lean_dec_ref(res);
}l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__0____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_);
l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_ = _init_l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_Elab_initFn___closed__1____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_Exception_3789179955____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_autoBoundImplicitExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_autoBoundImplicitExceptionId);
lean_dec_ref(res);
}l_Lean_Elab_throwPostpone___redArg___closed__0 = _init_l_Lean_Elab_throwPostpone___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwPostpone___redArg___closed__0);
l_Lean_Elab_throwPostpone___redArg___closed__1 = _init_l_Lean_Elab_throwPostpone___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwPostpone___redArg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0 = _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__0);
l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___redArg___closed__1);
l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0 = _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___redArg___closed__0);
l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1 = _init_l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___redArg___closed__1);
l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0 = _init_l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__0);
l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1 = _init_l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__1);
l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__2 = _init_l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__2);
l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__3 = _init_l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_throwAutoBoundImplicitLocal___redArg___closed__3);
l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0 = _init_l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0();
lean_mark_persistent(l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__0);
l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1 = _init_l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_isAutoBoundImplicitLocalException_x3f___closed__1);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__0);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__1);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__2);
l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3 = _init_l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3();
lean_mark_persistent(l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___redArg___closed__3);
l_Lean_Elab_throwAbortCommand___redArg___closed__0 = _init_l_Lean_Elab_throwAbortCommand___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwAbortCommand___redArg___closed__0);
l_Lean_Elab_throwAbortCommand___redArg___closed__1 = _init_l_Lean_Elab_throwAbortCommand___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbortCommand___redArg___closed__1);
l_Lean_Elab_throwAbortTerm___redArg___closed__0 = _init_l_Lean_Elab_throwAbortTerm___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwAbortTerm___redArg___closed__0);
l_Lean_Elab_throwAbortTerm___redArg___closed__1 = _init_l_Lean_Elab_throwAbortTerm___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbortTerm___redArg___closed__1);
l_Lean_Elab_throwAbortTactic___redArg___closed__0 = _init_l_Lean_Elab_throwAbortTactic___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwAbortTactic___redArg___closed__0);
l_Lean_Elab_throwAbortTactic___redArg___closed__1 = _init_l_Lean_Elab_throwAbortTactic___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbortTactic___redArg___closed__1);
l_Lean_Elab_mkMessageCore___closed__0 = _init_l_Lean_Elab_mkMessageCore___closed__0();
lean_mark_persistent(l_Lean_Elab_mkMessageCore___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
