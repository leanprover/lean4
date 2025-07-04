// Lean compiler output
// Module: Lean.Elab.Level
// Imports: Lean.Log Lean.Parser.Level Lean.Elab.Exception Lean.Elab.AutoBound
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
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__18;
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3;
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mvar___override(lean_object*);
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__12;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4;
lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1;
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__3;
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__7;
static lean_object* l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level___hyg_296_;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__5;
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_List_elem___at___Lean_Environment_realizeConst_spec__4(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__17;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM;
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level___hyg_296_;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__0;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level___hyg_296_;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__20;
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM;
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level___hyg_296_;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_maxUniverseOffset;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__21;
static lean_object* l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level___hyg_296_;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__2;
static lean_object* l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level___hyg_296_;
static lean_object* l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level___hyg_296_;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__16;
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8;
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2;
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueNat;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__13;
static lean_object* l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level___hyg_296_;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_296_(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6;
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2;
extern lean_object* l_Lean_Elab_relaxedAutoImplicit;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__1;
size_t lean_usize_sub(size_t, size_t);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__15;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM;
static lean_object* l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level___hyg_296_;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__11;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__14;
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__8;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__6;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonad___lam__0), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonad___lam__1), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_instMonad___lam__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_map), 7, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0;
x_2 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_pure), 5, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6;
x_2 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2;
x_3 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1;
x_4 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5;
x_5 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_EStateM_bind), 7, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8;
x_2 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9;
x_2 = lean_alloc_closure((void*)(l_ReaderT_read), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0___boxed), 3, 0);
x_2 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9;
x_3 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10;
x_4 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, lean_box(0));
lean_closure_set(x_4, 2, x_2);
lean_closure_set(x_4, 3, lean_box(0));
lean_closure_set(x_4, 4, lean_box(0));
lean_closure_set(x_4, 5, x_3);
lean_closure_set(x_4, 6, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 1);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_2);
x_8 = lean_apply_2(x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_10);
x_12 = lean_apply_2(x_3, x_11, x_5);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadRefLevelElabM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed), 3, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1), 5, 0);
x_3 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9;
x_4 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, lean_box(0));
lean_closure_set(x_5, 4, lean_box(0));
lean_closure_set(x_5, 5, x_4);
lean_closure_set(x_5, 6, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Level_instAddMessageContextLevelElabM() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed), 3, 0);
x_4 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9;
x_5 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_4);
lean_closure_set(x_5, 3, lean_box(0));
lean_closure_set(x_5, 4, lean_box(0));
lean_closure_set(x_5, 5, x_1);
lean_closure_set(x_5, 6, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = l_Lean_Name_num___override(x_5, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_12);
lean_inc(x_11);
x_13 = l_Lean_Name_num___override(x_11, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_1, 0, x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
lean_inc(x_22);
lean_inc(x_21);
x_24 = l_Lean_Name_num___override(x_21, x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_22, x_25);
lean_dec(x_22);
if (lean_is_scalar(x_23)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_23;
}
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_9 = l_Lean_MetavarContext_addLevelMVarDecl(x_8, x_7);
lean_ctor_set(x_5, 1, x_9);
x_10 = l_Lean_Level_mvar___override(x_7);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
lean_inc(x_11);
x_15 = l_Lean_MetavarContext_addLevelMVarDecl(x_13, x_11);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_14);
x_17 = l_Lean_Level_mvar___override(x_11);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
lean_inc(x_19);
x_24 = l_Lean_MetavarContext_addLevelMVarDecl(x_21, x_19);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 3, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
x_26 = l_Lean_Level_mvar___override(x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Level_mkFreshLevelMVar(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level___hyg_296_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxUniverseOffset", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level___hyg_296_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level___hyg_296_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level___hyg_296_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level___hyg_296_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum universe level offset", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level___hyg_296_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level___hyg_296_;
x_2 = l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level___hyg_296_;
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level___hyg_296_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level___hyg_296_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level___hyg_296_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Level", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level___hyg_296_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level___hyg_296_;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level___hyg_296_;
x_3 = l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level___hyg_296_;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level___hyg_296_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_296_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level___hyg_296_;
x_3 = l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level___hyg_296_;
x_4 = l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level___hyg_296_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Options___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Level_maxUniverseOffset;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum universe level offset threshold (", 41, 41);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(") has been reached, you can increase the limit using option `set_option maxUniverseOffset <limit>`, but you are probably misusing universe levels since offsets are usually small natural numbers", 193, 193);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0;
x_8 = l_Lean_Option_get___redArg(x_1, x_6, x_7);
x_9 = lean_nat_dec_le(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_10 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2;
x_11 = l_Nat_reprFast(x_8);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___redArg(x_3, x_4, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_KVMap_instValueNat;
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_1);
lean_closure_set(x_8, 3, x_2);
lean_closure_set(x_8, 4, x_6);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed syntax", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1;
x_4 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0;
x_6 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_4, x_5);
x_7 = lean_nat_dec_le(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2;
x_9 = l_Nat_reprFast(x_6);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_MessageData_ofFormat(x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_14, x_2, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 1;
x_9 = lean_usize_sub(x_2, x_8);
x_10 = lean_array_uget(x_1, x_9);
lean_inc(x_5);
x_11 = l_Lean_Elab_Level_elabLevel(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_mkLevelIMax_x27(x_12, x_4);
x_2 = x_9;
x_4 = x_14;
x_6 = x_13;
goto _start;
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_2 = x_9;
x_4 = x_16;
x_6 = x_17;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 1;
x_9 = lean_usize_sub(x_2, x_8);
x_10 = lean_array_uget(x_1, x_9);
lean_inc(x_5);
x_11 = l_Lean_Elab_Level_elabLevel(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_mkLevelMax_x27(x_12, x_4);
x_2 = x_9;
x_4 = x_14;
x_6 = x_13;
goto _start;
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_2 = x_9;
x_4 = x_16;
x_6 = x_17;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
else
{
lean_object* x_19; 
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown universe level '", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__5;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level___hyg_296_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__4;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level___hyg_296_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__7;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level___hyg_296_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__4;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level___hyg_296_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imax", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__9;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level___hyg_296_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__4;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level___hyg_296_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hole", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__11;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level___hyg_296_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__4;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level___hyg_296_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__13;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__15;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("addLit", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__17;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level___hyg_296_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__4;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level___hyg_296_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected universe level syntax kind", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_relaxedAutoImplicit;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_67; 
x_67 = !lean_is_exclusive(x_2);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_2, 0);
x_69 = lean_ctor_get(x_2, 1);
x_70 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_1);
x_71 = l_Lean_Syntax_getKind(x_1);
x_72 = l_Lean_Elab_Level_elabLevel___closed__6;
x_73 = lean_name_eq(x_71, x_72);
x_74 = l_Lean_replaceRef(x_1, x_69);
lean_dec(x_69);
lean_inc(x_68);
lean_ctor_set(x_2, 1, x_74);
if (x_73 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = l_Lean_Elab_Level_elabLevel___closed__8;
x_76 = lean_name_eq(x_71, x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = l_Lean_Elab_Level_elabLevel___closed__10;
x_78 = lean_name_eq(x_71, x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = l_Lean_Elab_Level_elabLevel___closed__12;
x_80 = lean_name_eq(x_71, x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = l_Lean_Elab_Level_elabLevel___closed__14;
x_82 = lean_name_eq(x_71, x_81);
if (x_82 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = l_Lean_Elab_Level_elabLevel___closed__16;
x_84 = lean_name_eq(x_71, x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
lean_dec(x_68);
x_85 = l_Lean_Elab_Level_elabLevel___closed__18;
x_86 = lean_name_eq(x_71, x_85);
lean_dec(x_71);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_1);
x_87 = l_Lean_Elab_Level_elabLevel___closed__20;
x_88 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_87, x_2, x_3);
lean_dec(x_2);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Lean_Syntax_getArg(x_1, x_89);
lean_inc(x_2);
x_91 = l_Lean_Elab_Level_elabLevel(x_90, x_2, x_3);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_unsigned_to_nat(2u);
x_95 = l_Lean_Syntax_getArg(x_1, x_94);
lean_dec(x_1);
x_96 = l_Lean_Syntax_isNatLit_x3f(x_95);
lean_dec(x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
lean_dec(x_92);
x_97 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_2, x_93);
lean_dec(x_2);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_98, x_2, x_93);
lean_dec(x_2);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 0);
lean_dec(x_101);
x_102 = l_Lean_Level_addOffsetAux(x_98, x_92);
lean_ctor_set(x_99, 0, x_102);
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_99, 1);
lean_inc(x_103);
lean_dec(x_99);
x_104 = l_Lean_Level_addOffsetAux(x_98, x_92);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_98);
lean_dec(x_92);
x_106 = !lean_is_exclusive(x_99);
if (x_106 == 0)
{
return x_99;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_99, 0);
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_99);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_91;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_dec(x_71);
x_110 = lean_ctor_get(x_3, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_3, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_3, 2);
lean_inc(x_112);
x_113 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_114 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_113, x_112);
if (x_114 == 0)
{
if (x_70 == 0)
{
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_68);
x_9 = x_2;
x_10 = x_113;
goto block_22;
}
else
{
lean_object* x_115; uint8_t x_116; uint8_t x_117; 
x_115 = l_Lean_Elab_Level_elabLevel___closed__21;
x_116 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_68, x_115);
lean_dec(x_68);
lean_inc(x_113);
x_117 = l_Lean_Elab_isValidAutoBoundLevelName(x_113, x_116);
if (x_117 == 0)
{
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
x_9 = x_2;
x_10 = x_113;
goto block_22;
}
else
{
uint8_t x_118; 
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_3);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_3, 2);
lean_dec(x_119);
x_120 = lean_ctor_get(x_3, 1);
lean_dec(x_120);
x_121 = lean_ctor_get(x_3, 0);
lean_dec(x_121);
lean_inc(x_113);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_113);
lean_ctor_set(x_122, 1, x_112);
lean_ctor_set(x_3, 2, x_122);
x_4 = x_113;
x_5 = x_3;
goto block_8;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_3);
lean_inc(x_113);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_113);
lean_ctor_set(x_123, 1, x_112);
x_124 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_124, 0, x_110);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_124, 2, x_123);
x_4 = x_113;
x_5 = x_124;
goto block_8;
}
}
}
}
else
{
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_2);
lean_dec(x_68);
x_4 = x_113;
x_5 = x_3;
goto block_8;
}
}
}
else
{
lean_object* x_125; 
lean_dec(x_71);
lean_dec(x_68);
x_125 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_2, x_3);
lean_dec(x_2);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_127, x_2, x_3);
lean_dec(x_2);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 0);
lean_dec(x_130);
x_131 = l_Lean_Level_ofNat(x_127);
lean_dec(x_127);
lean_ctor_set(x_128, 0, x_131);
return x_128;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = l_Lean_Level_ofNat(x_127);
lean_dec(x_127);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_127);
x_135 = !lean_is_exclusive(x_128);
if (x_135 == 0)
{
return x_128;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_128, 0);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_128);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
}
else
{
lean_object* x_139; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_1);
x_139 = l_Lean_Elab_Level_mkFreshLevelMVar(x_2, x_3);
lean_dec(x_2);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_71);
lean_dec(x_68);
x_140 = lean_unsigned_to_nat(1u);
x_141 = l_Lean_Syntax_getArg(x_1, x_140);
lean_dec(x_1);
x_142 = l_Lean_Syntax_getArgs(x_141);
lean_dec(x_141);
x_143 = lean_box(0);
x_144 = l_Array_back_x21___redArg(x_143, x_142);
lean_inc(x_2);
x_145 = l_Lean_Elab_Level_elabLevel(x_144, x_2, x_3);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
x_148 = lean_array_get_size(x_142);
x_149 = lean_nat_sub(x_148, x_140);
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_nat_dec_le(x_149, x_148);
if (x_151 == 0)
{
lean_dec(x_149);
x_23 = x_2;
x_24 = x_146;
x_25 = x_142;
x_26 = x_145;
x_27 = x_147;
x_28 = x_150;
x_29 = x_148;
goto block_44;
}
else
{
lean_dec(x_148);
x_23 = x_2;
x_24 = x_146;
x_25 = x_142;
x_26 = x_145;
x_27 = x_147;
x_28 = x_150;
x_29 = x_149;
goto block_44;
}
}
else
{
lean_dec(x_142);
lean_dec(x_2);
return x_145;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_71);
lean_dec(x_68);
x_152 = lean_unsigned_to_nat(1u);
x_153 = l_Lean_Syntax_getArg(x_1, x_152);
lean_dec(x_1);
x_154 = l_Lean_Syntax_getArgs(x_153);
lean_dec(x_153);
x_155 = lean_box(0);
x_156 = l_Array_back_x21___redArg(x_155, x_154);
lean_inc(x_2);
x_157 = l_Lean_Elab_Level_elabLevel(x_156, x_2, x_3);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
x_160 = lean_array_get_size(x_154);
x_161 = lean_nat_sub(x_160, x_152);
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_nat_dec_le(x_161, x_160);
if (x_163 == 0)
{
lean_dec(x_161);
x_45 = x_158;
x_46 = x_2;
x_47 = x_154;
x_48 = x_159;
x_49 = x_157;
x_50 = x_162;
x_51 = x_160;
goto block_66;
}
else
{
lean_dec(x_160);
x_45 = x_158;
x_46 = x_2;
x_47 = x_154;
x_48 = x_159;
x_49 = x_157;
x_50 = x_162;
x_51 = x_161;
goto block_66;
}
}
else
{
lean_dec(x_154);
lean_dec(x_2);
return x_157;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_71);
lean_dec(x_68);
x_164 = lean_unsigned_to_nat(1u);
x_165 = l_Lean_Syntax_getArg(x_1, x_164);
lean_dec(x_1);
x_1 = x_165;
goto _start;
}
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; 
x_167 = lean_ctor_get(x_2, 0);
x_168 = lean_ctor_get(x_2, 1);
x_169 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_2);
lean_inc(x_1);
x_170 = l_Lean_Syntax_getKind(x_1);
x_171 = l_Lean_Elab_Level_elabLevel___closed__6;
x_172 = lean_name_eq(x_170, x_171);
x_173 = l_Lean_replaceRef(x_1, x_168);
lean_dec(x_168);
lean_inc(x_167);
x_174 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_174, 0, x_167);
lean_ctor_set(x_174, 1, x_173);
lean_ctor_set_uint8(x_174, sizeof(void*)*2, x_169);
if (x_172 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = l_Lean_Elab_Level_elabLevel___closed__8;
x_176 = lean_name_eq(x_170, x_175);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = l_Lean_Elab_Level_elabLevel___closed__10;
x_178 = lean_name_eq(x_170, x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = l_Lean_Elab_Level_elabLevel___closed__12;
x_180 = lean_name_eq(x_170, x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = l_Lean_Elab_Level_elabLevel___closed__14;
x_182 = lean_name_eq(x_170, x_181);
if (x_182 == 0)
{
lean_object* x_183; uint8_t x_184; 
x_183 = l_Lean_Elab_Level_elabLevel___closed__16;
x_184 = lean_name_eq(x_170, x_183);
if (x_184 == 0)
{
lean_object* x_185; uint8_t x_186; 
lean_dec(x_167);
x_185 = l_Lean_Elab_Level_elabLevel___closed__18;
x_186 = lean_name_eq(x_170, x_185);
lean_dec(x_170);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_1);
x_187 = l_Lean_Elab_Level_elabLevel___closed__20;
x_188 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_187, x_174, x_3);
lean_dec(x_174);
return x_188;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_unsigned_to_nat(0u);
x_190 = l_Lean_Syntax_getArg(x_1, x_189);
lean_inc(x_174);
x_191 = l_Lean_Elab_Level_elabLevel(x_190, x_174, x_3);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_unsigned_to_nat(2u);
x_195 = l_Lean_Syntax_getArg(x_1, x_194);
lean_dec(x_1);
x_196 = l_Lean_Syntax_isNatLit_x3f(x_195);
lean_dec(x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
lean_dec(x_192);
x_197 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_174, x_193);
lean_dec(x_174);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_196, 0);
lean_inc(x_198);
lean_dec(x_196);
x_199 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_198, x_174, x_193);
lean_dec(x_174);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_201 = x_199;
} else {
 lean_dec_ref(x_199);
 x_201 = lean_box(0);
}
x_202 = l_Lean_Level_addOffsetAux(x_198, x_192);
if (lean_is_scalar(x_201)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_201;
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_200);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_198);
lean_dec(x_192);
x_204 = lean_ctor_get(x_199, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_206 = x_199;
} else {
 lean_dec_ref(x_199);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
else
{
lean_dec(x_174);
lean_dec(x_1);
return x_191;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_dec(x_170);
x_208 = lean_ctor_get(x_3, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_3, 1);
lean_inc(x_209);
x_210 = lean_ctor_get(x_3, 2);
lean_inc(x_210);
x_211 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_212 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_211, x_210);
if (x_212 == 0)
{
if (x_169 == 0)
{
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_167);
x_9 = x_174;
x_10 = x_211;
goto block_22;
}
else
{
lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_213 = l_Lean_Elab_Level_elabLevel___closed__21;
x_214 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_167, x_213);
lean_dec(x_167);
lean_inc(x_211);
x_215 = l_Lean_Elab_isValidAutoBoundLevelName(x_211, x_214);
if (x_215 == 0)
{
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
x_9 = x_174;
x_10 = x_211;
goto block_22;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_174);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_216 = x_3;
} else {
 lean_dec_ref(x_3);
 x_216 = lean_box(0);
}
lean_inc(x_211);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_211);
lean_ctor_set(x_217, 1, x_210);
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(0, 3, 0);
} else {
 x_218 = x_216;
}
lean_ctor_set(x_218, 0, x_208);
lean_ctor_set(x_218, 1, x_209);
lean_ctor_set(x_218, 2, x_217);
x_4 = x_211;
x_5 = x_218;
goto block_8;
}
}
}
else
{
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_174);
lean_dec(x_167);
x_4 = x_211;
x_5 = x_3;
goto block_8;
}
}
}
else
{
lean_object* x_219; 
lean_dec(x_170);
lean_dec(x_167);
x_219 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; 
x_220 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_174, x_3);
lean_dec(x_174);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_219, 0);
lean_inc(x_221);
lean_dec(x_219);
x_222 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_221, x_174, x_3);
lean_dec(x_174);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
x_225 = l_Lean_Level_ofNat(x_221);
lean_dec(x_221);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_223);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_221);
x_227 = lean_ctor_get(x_222, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_222, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_229 = x_222;
} else {
 lean_dec_ref(x_222);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
}
}
else
{
lean_object* x_231; 
lean_dec(x_170);
lean_dec(x_167);
lean_dec(x_1);
x_231 = l_Lean_Elab_Level_mkFreshLevelMVar(x_174, x_3);
lean_dec(x_174);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_170);
lean_dec(x_167);
x_232 = lean_unsigned_to_nat(1u);
x_233 = l_Lean_Syntax_getArg(x_1, x_232);
lean_dec(x_1);
x_234 = l_Lean_Syntax_getArgs(x_233);
lean_dec(x_233);
x_235 = lean_box(0);
x_236 = l_Array_back_x21___redArg(x_235, x_234);
lean_inc(x_174);
x_237 = l_Lean_Elab_Level_elabLevel(x_236, x_174, x_3);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
x_240 = lean_array_get_size(x_234);
x_241 = lean_nat_sub(x_240, x_232);
x_242 = lean_unsigned_to_nat(0u);
x_243 = lean_nat_dec_le(x_241, x_240);
if (x_243 == 0)
{
lean_dec(x_241);
x_23 = x_174;
x_24 = x_238;
x_25 = x_234;
x_26 = x_237;
x_27 = x_239;
x_28 = x_242;
x_29 = x_240;
goto block_44;
}
else
{
lean_dec(x_240);
x_23 = x_174;
x_24 = x_238;
x_25 = x_234;
x_26 = x_237;
x_27 = x_239;
x_28 = x_242;
x_29 = x_241;
goto block_44;
}
}
else
{
lean_dec(x_234);
lean_dec(x_174);
return x_237;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_170);
lean_dec(x_167);
x_244 = lean_unsigned_to_nat(1u);
x_245 = l_Lean_Syntax_getArg(x_1, x_244);
lean_dec(x_1);
x_246 = l_Lean_Syntax_getArgs(x_245);
lean_dec(x_245);
x_247 = lean_box(0);
x_248 = l_Array_back_x21___redArg(x_247, x_246);
lean_inc(x_174);
x_249 = l_Lean_Elab_Level_elabLevel(x_248, x_174, x_3);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
x_252 = lean_array_get_size(x_246);
x_253 = lean_nat_sub(x_252, x_244);
x_254 = lean_unsigned_to_nat(0u);
x_255 = lean_nat_dec_le(x_253, x_252);
if (x_255 == 0)
{
lean_dec(x_253);
x_45 = x_250;
x_46 = x_174;
x_47 = x_246;
x_48 = x_251;
x_49 = x_249;
x_50 = x_254;
x_51 = x_252;
goto block_66;
}
else
{
lean_dec(x_252);
x_45 = x_250;
x_46 = x_174;
x_47 = x_246;
x_48 = x_251;
x_49 = x_249;
x_50 = x_254;
x_51 = x_253;
goto block_66;
}
}
else
{
lean_dec(x_246);
lean_dec(x_174);
return x_249;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_170);
lean_dec(x_167);
x_256 = lean_unsigned_to_nat(1u);
x_257 = l_Lean_Syntax_getArg(x_1, x_256);
lean_dec(x_1);
x_1 = x_257;
x_2 = x_174;
goto _start;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Level_param___override(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
block_22:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = l_Lean_Elab_Level_elabLevel___closed__1;
x_12 = lean_mk_syntax_ident(x_10);
x_13 = l_Lean_MessageData_ofSyntax(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_Level_elabLevel___closed__3;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_16, x_9, x_3);
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
block_44:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = l_Array_toSubarray___redArg(x_25, x_28, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 2);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_array_get_size(x_31);
x_35 = lean_nat_dec_le(x_33, x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_33);
x_36 = lean_nat_dec_lt(x_32, x_34);
if (x_36 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
return x_26;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
lean_dec(x_26);
x_37 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_38 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_39 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__3(x_31, x_37, x_38, x_24, x_23, x_27);
lean_dec(x_31);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_34);
x_40 = lean_nat_dec_lt(x_32, x_33);
if (x_40 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
return x_26;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
lean_dec(x_26);
x_41 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_42 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_43 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__3(x_31, x_41, x_42, x_24, x_23, x_27);
lean_dec(x_31);
return x_43;
}
}
}
block_66:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = l_Array_toSubarray___redArg(x_47, x_50, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_array_get_size(x_53);
x_57 = lean_nat_dec_le(x_55, x_56);
if (x_57 == 0)
{
uint8_t x_58; 
lean_dec(x_55);
x_58 = lean_nat_dec_lt(x_54, x_56);
if (x_58 == 0)
{
lean_dec(x_56);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_45);
return x_49;
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; 
lean_dec(x_49);
x_59 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_60 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_61 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__4(x_53, x_59, x_60, x_45, x_46, x_48);
lean_dec(x_53);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_56);
x_62 = lean_nat_dec_lt(x_54, x_55);
if (x_62 == 0)
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_45);
return x_49;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
lean_dec(x_49);
x_63 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_64 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_65 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__4(x_53, x_63, x_64, x_45, x_46, x_48);
lean_dec(x_53);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__3(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__4(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Level(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_AutoBound(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Level(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Level(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AutoBound(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__0);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10);
l_Lean_Elab_Level_instMonadOptionsLevelElabM = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM);
l_Lean_Elab_Level_instMonadRefLevelElabM = _init_l_Lean_Elab_Level_instMonadRefLevelElabM();
lean_mark_persistent(l_Lean_Elab_Level_instMonadRefLevelElabM);
l_Lean_Elab_Level_instAddMessageContextLevelElabM = _init_l_Lean_Elab_Level_instAddMessageContextLevelElabM();
lean_mark_persistent(l_Lean_Elab_Level_instAddMessageContextLevelElabM);
l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM = _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM();
lean_mark_persistent(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM);
l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level___hyg_296_ = _init_l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level___hyg_296_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level___hyg_296_);
l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level___hyg_296_ = _init_l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level___hyg_296_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level___hyg_296_);
l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level___hyg_296_ = _init_l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level___hyg_296_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level___hyg_296_);
l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level___hyg_296_ = _init_l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level___hyg_296_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level___hyg_296_);
l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level___hyg_296_ = _init_l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level___hyg_296_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level___hyg_296_);
l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level___hyg_296_ = _init_l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level___hyg_296_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level___hyg_296_);
l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level___hyg_296_ = _init_l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level___hyg_296_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level___hyg_296_);
l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level___hyg_296_ = _init_l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level___hyg_296_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level___hyg_296_);
l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level___hyg_296_ = _init_l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level___hyg_296_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level___hyg_296_);
if (builtin) {res = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_296_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Level_maxUniverseOffset = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Level_maxUniverseOffset);
lean_dec_ref(res);
}l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__3);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4);
l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0 = _init_l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0);
l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1 = _init_l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1);
l_Lean_Elab_Level_elabLevel___closed__0 = _init_l_Lean_Elab_Level_elabLevel___closed__0();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__0);
l_Lean_Elab_Level_elabLevel___closed__1 = _init_l_Lean_Elab_Level_elabLevel___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__1);
l_Lean_Elab_Level_elabLevel___closed__2 = _init_l_Lean_Elab_Level_elabLevel___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__2);
l_Lean_Elab_Level_elabLevel___closed__3 = _init_l_Lean_Elab_Level_elabLevel___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__3);
l_Lean_Elab_Level_elabLevel___closed__4 = _init_l_Lean_Elab_Level_elabLevel___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__4);
l_Lean_Elab_Level_elabLevel___closed__5 = _init_l_Lean_Elab_Level_elabLevel___closed__5();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__5);
l_Lean_Elab_Level_elabLevel___closed__6 = _init_l_Lean_Elab_Level_elabLevel___closed__6();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__6);
l_Lean_Elab_Level_elabLevel___closed__7 = _init_l_Lean_Elab_Level_elabLevel___closed__7();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__7);
l_Lean_Elab_Level_elabLevel___closed__8 = _init_l_Lean_Elab_Level_elabLevel___closed__8();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__8);
l_Lean_Elab_Level_elabLevel___closed__9 = _init_l_Lean_Elab_Level_elabLevel___closed__9();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__9);
l_Lean_Elab_Level_elabLevel___closed__10 = _init_l_Lean_Elab_Level_elabLevel___closed__10();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__10);
l_Lean_Elab_Level_elabLevel___closed__11 = _init_l_Lean_Elab_Level_elabLevel___closed__11();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__11);
l_Lean_Elab_Level_elabLevel___closed__12 = _init_l_Lean_Elab_Level_elabLevel___closed__12();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__12);
l_Lean_Elab_Level_elabLevel___closed__13 = _init_l_Lean_Elab_Level_elabLevel___closed__13();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__13);
l_Lean_Elab_Level_elabLevel___closed__14 = _init_l_Lean_Elab_Level_elabLevel___closed__14();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__14);
l_Lean_Elab_Level_elabLevel___closed__15 = _init_l_Lean_Elab_Level_elabLevel___closed__15();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__15);
l_Lean_Elab_Level_elabLevel___closed__16 = _init_l_Lean_Elab_Level_elabLevel___closed__16();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__16);
l_Lean_Elab_Level_elabLevel___closed__17 = _init_l_Lean_Elab_Level_elabLevel___closed__17();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__17);
l_Lean_Elab_Level_elabLevel___closed__18 = _init_l_Lean_Elab_Level_elabLevel___closed__18();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__18);
l_Lean_Elab_Level_elabLevel___closed__19 = _init_l_Lean_Elab_Level_elabLevel___closed__19();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__19);
l_Lean_Elab_Level_elabLevel___closed__20 = _init_l_Lean_Elab_Level_elabLevel___closed__20();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__20);
l_Lean_Elab_Level_elabLevel___closed__21 = _init_l_Lean_Elab_Level_elabLevel___closed__21();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__21);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
