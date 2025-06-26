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
lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_1);
x_27 = l_Lean_Syntax_getKind(x_1);
x_28 = l_Lean_Elab_Level_elabLevel___closed__6;
x_29 = lean_name_eq(x_27, x_28);
x_30 = l_Lean_replaceRef(x_1, x_25);
lean_dec(x_25);
lean_inc(x_24);
lean_ctor_set(x_2, 1, x_30);
if (x_29 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Elab_Level_elabLevel___closed__8;
x_32 = lean_name_eq(x_27, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Elab_Level_elabLevel___closed__10;
x_34 = lean_name_eq(x_27, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Elab_Level_elabLevel___closed__12;
x_36 = lean_name_eq(x_27, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Elab_Level_elabLevel___closed__14;
x_38 = lean_name_eq(x_27, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Elab_Level_elabLevel___closed__16;
x_40 = lean_name_eq(x_27, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
lean_dec(x_24);
x_41 = l_Lean_Elab_Level_elabLevel___closed__18;
x_42 = lean_name_eq(x_27, x_41);
lean_dec(x_27);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_43 = l_Lean_Elab_Level_elabLevel___closed__20;
x_44 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_43, x_2, x_3);
lean_dec(x_2);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Syntax_getArg(x_1, x_45);
lean_inc(x_2);
x_47 = l_Lean_Elab_Level_elabLevel(x_46, x_2, x_3);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_unsigned_to_nat(2u);
x_51 = l_Lean_Syntax_getArg(x_1, x_50);
lean_dec(x_1);
x_52 = l_Lean_Syntax_isNatLit_x3f(x_51);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
lean_dec(x_48);
x_53 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_2, x_49);
lean_dec(x_2);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_54, x_2, x_49);
lean_dec(x_2);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = l_Lean_Level_addOffsetAux(x_54, x_48);
lean_ctor_set(x_55, 0, x_58);
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_dec(x_55);
x_60 = l_Lean_Level_addOffsetAux(x_54, x_48);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_54);
lean_dec(x_48);
x_62 = !lean_is_exclusive(x_55);
if (x_62 == 0)
{
return x_55;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_55, 0);
x_64 = lean_ctor_get(x_55, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_55);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_47;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_27);
x_66 = lean_ctor_get(x_3, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_3, 2);
lean_inc(x_68);
x_69 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_70 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_69, x_68);
if (x_70 == 0)
{
if (x_26 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_24);
x_9 = x_69;
x_10 = x_2;
goto block_22;
}
else
{
lean_object* x_71; uint8_t x_72; uint8_t x_73; 
x_71 = l_Lean_Elab_Level_elabLevel___closed__21;
x_72 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_24, x_71);
lean_dec(x_24);
lean_inc(x_69);
x_73 = l_Lean_Elab_isValidAutoBoundLevelName(x_69, x_72);
if (x_73 == 0)
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
x_9 = x_69;
x_10 = x_2;
goto block_22;
}
else
{
uint8_t x_74; 
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_3);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_3, 2);
lean_dec(x_75);
x_76 = lean_ctor_get(x_3, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_3, 0);
lean_dec(x_77);
lean_inc(x_69);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_68);
lean_ctor_set(x_3, 2, x_78);
x_4 = x_69;
x_5 = x_3;
goto block_8;
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_3);
lean_inc(x_69);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_68);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_66);
lean_ctor_set(x_80, 1, x_67);
lean_ctor_set(x_80, 2, x_79);
x_4 = x_69;
x_5 = x_80;
goto block_8;
}
}
}
}
else
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_2);
lean_dec(x_24);
x_4 = x_69;
x_5 = x_3;
goto block_8;
}
}
}
else
{
lean_object* x_81; 
lean_dec(x_27);
lean_dec(x_24);
x_81 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_2, x_3);
lean_dec(x_2);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_83, x_2, x_3);
lean_dec(x_2);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
lean_dec(x_86);
x_87 = l_Lean_Level_ofNat(x_83);
lean_dec(x_83);
lean_ctor_set(x_84, 0, x_87);
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = l_Lean_Level_ofNat(x_83);
lean_dec(x_83);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_83);
x_91 = !lean_is_exclusive(x_84);
if (x_91 == 0)
{
return x_84;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_84, 0);
x_93 = lean_ctor_get(x_84, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_84);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
}
else
{
lean_object* x_95; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_1);
x_95 = l_Lean_Elab_Level_mkFreshLevelMVar(x_2, x_3);
lean_dec(x_2);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_27);
lean_dec(x_24);
x_96 = lean_unsigned_to_nat(1u);
x_97 = l_Lean_Syntax_getArg(x_1, x_96);
lean_dec(x_1);
x_98 = l_Lean_Syntax_getArgs(x_97);
lean_dec(x_97);
x_99 = lean_box(0);
x_100 = l_Array_back_x21___redArg(x_99, x_98);
lean_inc(x_2);
x_101 = l_Lean_Elab_Level_elabLevel(x_100, x_2, x_3);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
x_104 = lean_unsigned_to_nat(0u);
x_105 = lean_array_get_size(x_98);
x_106 = lean_nat_sub(x_105, x_96);
lean_dec(x_105);
x_107 = l_Array_toSubarray___redArg(x_98, x_104, x_106);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_107, 2);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_array_get_size(x_108);
x_112 = lean_nat_dec_le(x_110, x_111);
if (x_112 == 0)
{
uint8_t x_113; 
lean_dec(x_110);
x_113 = lean_nat_dec_lt(x_109, x_111);
if (x_113 == 0)
{
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_2);
return x_101;
}
else
{
size_t x_114; size_t x_115; lean_object* x_116; 
lean_dec(x_101);
x_114 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_115 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_116 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__3(x_108, x_114, x_115, x_102, x_2, x_103);
lean_dec(x_108);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_111);
x_117 = lean_nat_dec_lt(x_109, x_110);
if (x_117 == 0)
{
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_2);
return x_101;
}
else
{
size_t x_118; size_t x_119; lean_object* x_120; 
lean_dec(x_101);
x_118 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_119 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_120 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__3(x_108, x_118, x_119, x_102, x_2, x_103);
lean_dec(x_108);
return x_120;
}
}
}
else
{
lean_dec(x_98);
lean_dec(x_2);
return x_101;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_27);
lean_dec(x_24);
x_121 = lean_unsigned_to_nat(1u);
x_122 = l_Lean_Syntax_getArg(x_1, x_121);
lean_dec(x_1);
x_123 = l_Lean_Syntax_getArgs(x_122);
lean_dec(x_122);
x_124 = lean_box(0);
x_125 = l_Array_back_x21___redArg(x_124, x_123);
lean_inc(x_2);
x_126 = l_Lean_Elab_Level_elabLevel(x_125, x_2, x_3);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
x_129 = lean_unsigned_to_nat(0u);
x_130 = lean_array_get_size(x_123);
x_131 = lean_nat_sub(x_130, x_121);
lean_dec(x_130);
x_132 = l_Array_toSubarray___redArg(x_123, x_129, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 2);
lean_inc(x_135);
lean_dec(x_132);
x_136 = lean_array_get_size(x_133);
x_137 = lean_nat_dec_le(x_135, x_136);
if (x_137 == 0)
{
uint8_t x_138; 
lean_dec(x_135);
x_138 = lean_nat_dec_lt(x_134, x_136);
if (x_138 == 0)
{
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_2);
return x_126;
}
else
{
size_t x_139; size_t x_140; lean_object* x_141; 
lean_dec(x_126);
x_139 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_140 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_141 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__4(x_133, x_139, x_140, x_127, x_2, x_128);
lean_dec(x_133);
return x_141;
}
}
else
{
uint8_t x_142; 
lean_dec(x_136);
x_142 = lean_nat_dec_lt(x_134, x_135);
if (x_142 == 0)
{
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_2);
return x_126;
}
else
{
size_t x_143; size_t x_144; lean_object* x_145; 
lean_dec(x_126);
x_143 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_144 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_145 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__4(x_133, x_143, x_144, x_127, x_2, x_128);
lean_dec(x_133);
return x_145;
}
}
}
else
{
lean_dec(x_123);
lean_dec(x_2);
return x_126;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_27);
lean_dec(x_24);
x_146 = lean_unsigned_to_nat(1u);
x_147 = l_Lean_Syntax_getArg(x_1, x_146);
lean_dec(x_1);
x_1 = x_147;
goto _start;
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
x_149 = lean_ctor_get(x_2, 0);
x_150 = lean_ctor_get(x_2, 1);
x_151 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_2);
lean_inc(x_1);
x_152 = l_Lean_Syntax_getKind(x_1);
x_153 = l_Lean_Elab_Level_elabLevel___closed__6;
x_154 = lean_name_eq(x_152, x_153);
x_155 = l_Lean_replaceRef(x_1, x_150);
lean_dec(x_150);
lean_inc(x_149);
x_156 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_156, 0, x_149);
lean_ctor_set(x_156, 1, x_155);
lean_ctor_set_uint8(x_156, sizeof(void*)*2, x_151);
if (x_154 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = l_Lean_Elab_Level_elabLevel___closed__8;
x_158 = lean_name_eq(x_152, x_157);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = l_Lean_Elab_Level_elabLevel___closed__10;
x_160 = lean_name_eq(x_152, x_159);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = l_Lean_Elab_Level_elabLevel___closed__12;
x_162 = lean_name_eq(x_152, x_161);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = l_Lean_Elab_Level_elabLevel___closed__14;
x_164 = lean_name_eq(x_152, x_163);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = l_Lean_Elab_Level_elabLevel___closed__16;
x_166 = lean_name_eq(x_152, x_165);
if (x_166 == 0)
{
lean_object* x_167; uint8_t x_168; 
lean_dec(x_149);
x_167 = l_Lean_Elab_Level_elabLevel___closed__18;
x_168 = lean_name_eq(x_152, x_167);
lean_dec(x_152);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_1);
x_169 = l_Lean_Elab_Level_elabLevel___closed__20;
x_170 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_169, x_156, x_3);
lean_dec(x_156);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_unsigned_to_nat(0u);
x_172 = l_Lean_Syntax_getArg(x_1, x_171);
lean_inc(x_156);
x_173 = l_Lean_Elab_Level_elabLevel(x_172, x_156, x_3);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_unsigned_to_nat(2u);
x_177 = l_Lean_Syntax_getArg(x_1, x_176);
lean_dec(x_1);
x_178 = l_Lean_Syntax_isNatLit_x3f(x_177);
lean_dec(x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
lean_dec(x_174);
x_179 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_156, x_175);
lean_dec(x_156);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
lean_dec(x_178);
x_181 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_180, x_156, x_175);
lean_dec(x_156);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
x_184 = l_Lean_Level_addOffsetAux(x_180, x_174);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_182);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_180);
lean_dec(x_174);
x_186 = lean_ctor_get(x_181, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_181, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_188 = x_181;
} else {
 lean_dec_ref(x_181);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
}
else
{
lean_dec(x_156);
lean_dec(x_1);
return x_173;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
lean_dec(x_152);
x_190 = lean_ctor_get(x_3, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_3, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_3, 2);
lean_inc(x_192);
x_193 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_194 = l_List_elem___at___Lean_Environment_realizeConst_spec__4(x_193, x_192);
if (x_194 == 0)
{
if (x_151 == 0)
{
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_149);
x_9 = x_193;
x_10 = x_156;
goto block_22;
}
else
{
lean_object* x_195; uint8_t x_196; uint8_t x_197; 
x_195 = l_Lean_Elab_Level_elabLevel___closed__21;
x_196 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_149, x_195);
lean_dec(x_149);
lean_inc(x_193);
x_197 = l_Lean_Elab_isValidAutoBoundLevelName(x_193, x_196);
if (x_197 == 0)
{
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
x_9 = x_193;
x_10 = x_156;
goto block_22;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_156);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_198 = x_3;
} else {
 lean_dec_ref(x_3);
 x_198 = lean_box(0);
}
lean_inc(x_193);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_193);
lean_ctor_set(x_199, 1, x_192);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 3, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_190);
lean_ctor_set(x_200, 1, x_191);
lean_ctor_set(x_200, 2, x_199);
x_4 = x_193;
x_5 = x_200;
goto block_8;
}
}
}
else
{
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_156);
lean_dec(x_149);
x_4 = x_193;
x_5 = x_3;
goto block_8;
}
}
}
else
{
lean_object* x_201; 
lean_dec(x_152);
lean_dec(x_149);
x_201 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; 
x_202 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_156, x_3);
lean_dec(x_156);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_203, x_156, x_3);
lean_dec(x_156);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
x_207 = l_Lean_Level_ofNat(x_203);
lean_dec(x_203);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_203);
x_209 = lean_ctor_get(x_204, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_204, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_211 = x_204;
} else {
 lean_dec_ref(x_204);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
}
}
else
{
lean_object* x_213; 
lean_dec(x_152);
lean_dec(x_149);
lean_dec(x_1);
x_213 = l_Lean_Elab_Level_mkFreshLevelMVar(x_156, x_3);
lean_dec(x_156);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_152);
lean_dec(x_149);
x_214 = lean_unsigned_to_nat(1u);
x_215 = l_Lean_Syntax_getArg(x_1, x_214);
lean_dec(x_1);
x_216 = l_Lean_Syntax_getArgs(x_215);
lean_dec(x_215);
x_217 = lean_box(0);
x_218 = l_Array_back_x21___redArg(x_217, x_216);
lean_inc(x_156);
x_219 = l_Lean_Elab_Level_elabLevel(x_218, x_156, x_3);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
x_222 = lean_unsigned_to_nat(0u);
x_223 = lean_array_get_size(x_216);
x_224 = lean_nat_sub(x_223, x_214);
lean_dec(x_223);
x_225 = l_Array_toSubarray___redArg(x_216, x_222, x_224);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_225, 2);
lean_inc(x_228);
lean_dec(x_225);
x_229 = lean_array_get_size(x_226);
x_230 = lean_nat_dec_le(x_228, x_229);
if (x_230 == 0)
{
uint8_t x_231; 
lean_dec(x_228);
x_231 = lean_nat_dec_lt(x_227, x_229);
if (x_231 == 0)
{
lean_dec(x_229);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_156);
return x_219;
}
else
{
size_t x_232; size_t x_233; lean_object* x_234; 
lean_dec(x_219);
x_232 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_233 = lean_usize_of_nat(x_227);
lean_dec(x_227);
x_234 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__3(x_226, x_232, x_233, x_220, x_156, x_221);
lean_dec(x_226);
return x_234;
}
}
else
{
uint8_t x_235; 
lean_dec(x_229);
x_235 = lean_nat_dec_lt(x_227, x_228);
if (x_235 == 0)
{
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_156);
return x_219;
}
else
{
size_t x_236; size_t x_237; lean_object* x_238; 
lean_dec(x_219);
x_236 = lean_usize_of_nat(x_228);
lean_dec(x_228);
x_237 = lean_usize_of_nat(x_227);
lean_dec(x_227);
x_238 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__3(x_226, x_236, x_237, x_220, x_156, x_221);
lean_dec(x_226);
return x_238;
}
}
}
else
{
lean_dec(x_216);
lean_dec(x_156);
return x_219;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_152);
lean_dec(x_149);
x_239 = lean_unsigned_to_nat(1u);
x_240 = l_Lean_Syntax_getArg(x_1, x_239);
lean_dec(x_1);
x_241 = l_Lean_Syntax_getArgs(x_240);
lean_dec(x_240);
x_242 = lean_box(0);
x_243 = l_Array_back_x21___redArg(x_242, x_241);
lean_inc(x_156);
x_244 = l_Lean_Elab_Level_elabLevel(x_243, x_156, x_3);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
x_247 = lean_unsigned_to_nat(0u);
x_248 = lean_array_get_size(x_241);
x_249 = lean_nat_sub(x_248, x_239);
lean_dec(x_248);
x_250 = l_Array_toSubarray___redArg(x_241, x_247, x_249);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_250, 2);
lean_inc(x_253);
lean_dec(x_250);
x_254 = lean_array_get_size(x_251);
x_255 = lean_nat_dec_le(x_253, x_254);
if (x_255 == 0)
{
uint8_t x_256; 
lean_dec(x_253);
x_256 = lean_nat_dec_lt(x_252, x_254);
if (x_256 == 0)
{
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_156);
return x_244;
}
else
{
size_t x_257; size_t x_258; lean_object* x_259; 
lean_dec(x_244);
x_257 = lean_usize_of_nat(x_254);
lean_dec(x_254);
x_258 = lean_usize_of_nat(x_252);
lean_dec(x_252);
x_259 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__4(x_251, x_257, x_258, x_245, x_156, x_246);
lean_dec(x_251);
return x_259;
}
}
else
{
uint8_t x_260; 
lean_dec(x_254);
x_260 = lean_nat_dec_lt(x_252, x_253);
if (x_260 == 0)
{
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_246);
lean_dec(x_245);
lean_dec(x_156);
return x_244;
}
else
{
size_t x_261; size_t x_262; lean_object* x_263; 
lean_dec(x_244);
x_261 = lean_usize_of_nat(x_253);
lean_dec(x_253);
x_262 = lean_usize_of_nat(x_252);
lean_dec(x_252);
x_263 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__4(x_251, x_261, x_262, x_245, x_156, x_246);
lean_dec(x_251);
return x_263;
}
}
}
else
{
lean_dec(x_241);
lean_dec(x_156);
return x_244;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_152);
lean_dec(x_149);
x_264 = lean_unsigned_to_nat(1u);
x_265 = l_Lean_Syntax_getArg(x_1, x_264);
lean_dec(x_1);
x_1 = x_265;
x_2 = x_156;
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
x_12 = lean_mk_syntax_ident(x_9);
x_13 = l_Lean_MessageData_ofSyntax(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Elab_Level_elabLevel___closed__3;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_16, x_10, x_3);
lean_dec(x_10);
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
