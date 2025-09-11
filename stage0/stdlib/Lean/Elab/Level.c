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
static lean_object* l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10;
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Elab_Level_elabLevel_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__12;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_Elab_Level_elabLevel_spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1;
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_KVMap_find(lean_object*, lean_object*);
lean_object* l_Lean_Level_addOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2_spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___Lean_Elab_Level_elabLevel_spec__4(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_Context_ctorIdx(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__3;
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__5;
static lean_object* l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__17;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3;
static lean_object* l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM;
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__9;
uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__4;
static lean_object* l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_List_elem___at___Lean_Elab_Level_elabLevel_spec__4___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__0;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2_spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM;
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_maxUniverseOffset;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__2;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__16;
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__8;
lean_object* l_EStateM_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7;
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6;
extern lean_object* l_Lean_KVMap_instValueNat;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_State_ctorIdx___boxed(lean_object*);
static lean_object* l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__13;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_Context_ctorIdx___boxed(lean_object*);
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
static lean_object* l_Lean_Elab_Level_elabLevel___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__15;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Elab_Level_initFn____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM;
static lean_object* l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_State_ctorIdx(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__14;
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__8;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__6;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Elab_Level_initFn____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_Context_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_Context_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Level_Context_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_State_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_State_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Level_State_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_2);
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
lean_inc_ref(x_4);
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
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
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
x_10 = l_Lean_mkLevelMVar(x_7);
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
x_17 = l_Lean_mkLevelMVar(x_11);
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
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_21);
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
x_26 = l_Lean_mkLevelMVar(x_19);
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
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshLMVarId___at___Lean_Elab_Level_mkFreshLevelMVar_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Level_mkFreshLevelMVar(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Elab_Level_initFn____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_5);
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_inc(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxUniverseOffset", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum universe level offset", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_2 = l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Level", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_4 = l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_5 = l_Lean_Option_register___at___Lean_Elab_Level_initFn____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Lean_Elab_Level_initFn____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___Lean_Elab_Level_initFn____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
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
x_1 = lean_mk_string_unchecked("Universe level offset `", 23, 23);
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
x_1 = lean_mk_string_unchecked("` exceeds maximum offset `", 26, 26);
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
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("This code is probably misusing universe levels, since they are usually small natural numbers. If you are confident this is not the case, you can increase the limit using `set_option maxUniverseOffset <limit>`", 208, 208);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8;
x_2 = l_Lean_MessageData_note(x_1);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_5);
x_10 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2;
x_11 = l_Nat_reprFast(x_2);
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
x_17 = l_Nat_reprFast(x_8);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__9;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___redArg(x_3, x_4, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_dec_ref(x_5);
x_27 = lean_box(0);
x_28 = lean_apply_2(x_26, lean_box(0), x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_KVMap_instValueNat;
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
return x_7;
}
else
{
lean_dec(x_6);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0;
x_6 = l_Lean_Option_get___at_____private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2_spec__2(x_4, x_5);
x_7 = lean_nat_dec_le(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_8 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__2;
x_9 = l_Nat_reprFast(x_1);
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
x_15 = l_Nat_reprFast(x_6);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__9;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_22, x_2, x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___Lean_Elab_Level_elabLevel_spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_name_eq(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___Lean_Elab_Level_elabLevel_spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_find(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_7);
x_9 = lean_unbox(x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc_ref(x_5);
x_11 = l_Lean_Elab_Level_elabLevel(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
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
lean_dec_ref(x_11);
x_2 = x_9;
x_4 = x_16;
x_6 = x_17;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_11;
}
}
}
else
{
lean_object* x_19; 
lean_dec_ref(x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc_ref(x_5);
x_11 = l_Lean_Elab_Level_elabLevel(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
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
lean_dec_ref(x_11);
x_2 = x_9;
x_4 = x_16;
x_6 = x_17;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_11;
}
}
}
else
{
lean_object* x_19; 
lean_dec_ref(x_5);
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
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__1;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__0;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__3;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__0;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imax", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__5;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__0;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hole", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__7;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__0;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("num", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__11;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("addLit", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__13;
x_2 = l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__0;
x_4 = l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected universe level syntax kind", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown universe level `", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__19() {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_1);
x_8 = l_Lean_Syntax_getKind(x_1);
x_9 = l_Lean_Elab_Level_elabLevel___closed__2;
x_10 = lean_name_eq(x_8, x_9);
x_11 = l_Lean_replaceRef(x_1, x_6);
lean_dec(x_6);
lean_inc(x_5);
lean_ctor_set(x_2, 1, x_11);
if (x_10 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Level_elabLevel___closed__4;
x_13 = lean_name_eq(x_8, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Level_elabLevel___closed__6;
x_15 = lean_name_eq(x_8, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Elab_Level_elabLevel___closed__8;
x_17 = lean_name_eq(x_8, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Elab_Level_elabLevel___closed__10;
x_19 = lean_name_eq(x_8, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Elab_Level_elabLevel___closed__12;
x_21 = lean_name_eq(x_8, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_5);
x_22 = l_Lean_Elab_Level_elabLevel___closed__14;
x_23 = lean_name_eq(x_8, x_22);
lean_dec(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = l_Lean_Elab_Level_elabLevel___closed__16;
x_25 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_24, x_2, x_3);
lean_dec_ref(x_2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
lean_inc_ref(x_2);
x_28 = l_Lean_Elab_Level_elabLevel(x_27, x_2, x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_unsigned_to_nat(2u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
lean_dec(x_1);
x_33 = l_Lean_Syntax_isNatLit_x3f(x_32);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_29);
x_34 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_2, x_30);
lean_dec_ref(x_2);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec_ref(x_33);
lean_inc(x_35);
x_36 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_35, x_2, x_30);
lean_dec_ref(x_2);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = l_Lean_Level_addOffset(x_29, x_35);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = l_Lean_Level_addOffset(x_29, x_35);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_35);
lean_dec(x_29);
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_28;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_67; 
lean_dec(x_8);
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
x_49 = lean_ctor_get(x_3, 2);
x_50 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_67 = l_List_elem___at___Lean_Elab_Level_elabLevel_spec__4(x_50, x_49);
if (x_67 == 0)
{
if (x_7 == 0)
{
lean_dec(x_5);
goto block_66;
}
else
{
lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_68 = l_Lean_Elab_Level_elabLevel___closed__19;
x_69 = l_Lean_Option_get___at___Lean_Elab_Level_elabLevel_spec__5(x_5, x_68);
lean_dec(x_5);
lean_inc(x_50);
x_70 = l_Lean_Elab_isValidAutoBoundLevelName(x_50, x_69);
if (x_70 == 0)
{
goto block_66;
}
else
{
uint8_t x_71; 
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc_ref(x_47);
lean_dec_ref(x_2);
x_71 = !lean_is_exclusive(x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_3, 2);
lean_dec(x_72);
x_73 = lean_ctor_get(x_3, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_3, 0);
lean_dec(x_74);
lean_inc(x_50);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_50);
lean_ctor_set(x_75, 1, x_49);
lean_ctor_set(x_3, 2, x_75);
x_51 = x_3;
goto block_54;
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_3);
lean_inc(x_50);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_50);
lean_ctor_set(x_76, 1, x_49);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_47);
lean_ctor_set(x_77, 1, x_48);
lean_ctor_set(x_77, 2, x_76);
x_51 = x_77;
goto block_54;
}
}
}
}
else
{
lean_dec_ref(x_2);
lean_dec(x_5);
x_51 = x_3;
goto block_54;
}
block_54:
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_mkLevelParam(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
block_66:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_55 = l_Lean_Elab_Level_elabLevel___closed__18;
x_56 = lean_mk_syntax_ident(x_50);
x_57 = l_Lean_MessageData_ofSyntax(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_60, x_2, x_3);
lean_dec_ref(x_2);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
return x_61;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_61);
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
lean_object* x_78; 
lean_dec(x_8);
lean_dec(x_5);
x_78 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_2, x_3);
lean_dec_ref(x_2);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec_ref(x_78);
lean_inc(x_80);
x_81 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_80, x_2, x_3);
lean_dec_ref(x_2);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
x_84 = l_Lean_Level_ofNat(x_80);
lean_dec(x_80);
lean_ctor_set(x_81, 0, x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = l_Lean_Level_ofNat(x_80);
lean_dec(x_80);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_80);
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
return x_81;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_81, 0);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_81);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_92 = l_Lean_Elab_Level_mkFreshLevelMVar(x_2, x_3);
lean_dec_ref(x_2);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_8);
lean_dec(x_5);
x_93 = lean_unsigned_to_nat(1u);
x_94 = l_Lean_Syntax_getArg(x_1, x_93);
lean_dec(x_1);
x_95 = l_Lean_Syntax_getArgs(x_94);
lean_dec(x_94);
x_96 = lean_box(0);
x_97 = l_Array_back_x21___redArg(x_96, x_95);
lean_inc_ref(x_2);
x_98 = l_Lean_Elab_Level_elabLevel(x_97, x_2, x_3);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
x_118 = lean_array_get_size(x_95);
x_119 = lean_nat_sub(x_118, x_93);
x_120 = lean_unsigned_to_nat(0u);
x_121 = lean_nat_dec_le(x_119, x_118);
if (x_121 == 0)
{
lean_dec(x_119);
x_101 = x_120;
x_102 = x_118;
goto block_117;
}
else
{
lean_dec(x_118);
x_101 = x_120;
x_102 = x_119;
goto block_117;
}
block_117:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_103 = l_Array_toSubarray___redArg(x_95, x_101, x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc_ref(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_103, 2);
lean_inc(x_106);
lean_dec_ref(x_103);
x_107 = lean_array_get_size(x_104);
x_108 = lean_nat_dec_le(x_106, x_107);
if (x_108 == 0)
{
uint8_t x_109; 
lean_dec(x_106);
x_109 = lean_nat_dec_lt(x_105, x_107);
if (x_109 == 0)
{
lean_dec(x_107);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_2);
return x_98;
}
else
{
size_t x_110; size_t x_111; lean_object* x_112; 
lean_dec_ref(x_98);
x_110 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_111 = lean_usize_of_nat(x_105);
lean_dec(x_105);
x_112 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__6(x_104, x_110, x_111, x_99, x_2, x_100);
lean_dec_ref(x_104);
return x_112;
}
}
else
{
uint8_t x_113; 
lean_dec(x_107);
x_113 = lean_nat_dec_lt(x_105, x_106);
if (x_113 == 0)
{
lean_dec(x_106);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_2);
return x_98;
}
else
{
size_t x_114; size_t x_115; lean_object* x_116; 
lean_dec_ref(x_98);
x_114 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_115 = lean_usize_of_nat(x_105);
lean_dec(x_105);
x_116 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__6(x_104, x_114, x_115, x_99, x_2, x_100);
lean_dec_ref(x_104);
return x_116;
}
}
}
}
else
{
lean_dec_ref(x_95);
lean_dec_ref(x_2);
return x_98;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_8);
lean_dec(x_5);
x_122 = lean_unsigned_to_nat(1u);
x_123 = l_Lean_Syntax_getArg(x_1, x_122);
lean_dec(x_1);
x_124 = l_Lean_Syntax_getArgs(x_123);
lean_dec(x_123);
x_125 = lean_box(0);
x_126 = l_Array_back_x21___redArg(x_125, x_124);
lean_inc_ref(x_2);
x_127 = l_Lean_Elab_Level_elabLevel(x_126, x_2, x_3);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
x_147 = lean_array_get_size(x_124);
x_148 = lean_nat_sub(x_147, x_122);
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_nat_dec_le(x_148, x_147);
if (x_150 == 0)
{
lean_dec(x_148);
x_130 = x_149;
x_131 = x_147;
goto block_146;
}
else
{
lean_dec(x_147);
x_130 = x_149;
x_131 = x_148;
goto block_146;
}
block_146:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_132 = l_Array_toSubarray___redArg(x_124, x_130, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 2);
lean_inc(x_135);
lean_dec_ref(x_132);
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
lean_dec_ref(x_133);
lean_dec(x_129);
lean_dec(x_128);
lean_dec_ref(x_2);
return x_127;
}
else
{
size_t x_139; size_t x_140; lean_object* x_141; 
lean_dec_ref(x_127);
x_139 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_140 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_141 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__7(x_133, x_139, x_140, x_128, x_2, x_129);
lean_dec_ref(x_133);
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
lean_dec_ref(x_133);
lean_dec(x_129);
lean_dec(x_128);
lean_dec_ref(x_2);
return x_127;
}
else
{
size_t x_143; size_t x_144; lean_object* x_145; 
lean_dec_ref(x_127);
x_143 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_144 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_145 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__7(x_133, x_143, x_144, x_128, x_2, x_129);
lean_dec_ref(x_133);
return x_145;
}
}
}
}
else
{
lean_dec_ref(x_124);
lean_dec_ref(x_2);
return x_127;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_8);
lean_dec(x_5);
x_151 = lean_unsigned_to_nat(1u);
x_152 = l_Lean_Syntax_getArg(x_1, x_151);
lean_dec(x_1);
x_1 = x_152;
goto _start;
}
}
else
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; 
x_154 = lean_ctor_get(x_2, 0);
x_155 = lean_ctor_get(x_2, 1);
x_156 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_2);
lean_inc(x_1);
x_157 = l_Lean_Syntax_getKind(x_1);
x_158 = l_Lean_Elab_Level_elabLevel___closed__2;
x_159 = lean_name_eq(x_157, x_158);
x_160 = l_Lean_replaceRef(x_1, x_155);
lean_dec(x_155);
lean_inc(x_154);
x_161 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set_uint8(x_161, sizeof(void*)*2, x_156);
if (x_159 == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = l_Lean_Elab_Level_elabLevel___closed__4;
x_163 = lean_name_eq(x_157, x_162);
if (x_163 == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = l_Lean_Elab_Level_elabLevel___closed__6;
x_165 = lean_name_eq(x_157, x_164);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; 
x_166 = l_Lean_Elab_Level_elabLevel___closed__8;
x_167 = lean_name_eq(x_157, x_166);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = l_Lean_Elab_Level_elabLevel___closed__10;
x_169 = lean_name_eq(x_157, x_168);
if (x_169 == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = l_Lean_Elab_Level_elabLevel___closed__12;
x_171 = lean_name_eq(x_157, x_170);
if (x_171 == 0)
{
lean_object* x_172; uint8_t x_173; 
lean_dec(x_154);
x_172 = l_Lean_Elab_Level_elabLevel___closed__14;
x_173 = lean_name_eq(x_157, x_172);
lean_dec(x_157);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_1);
x_174 = l_Lean_Elab_Level_elabLevel___closed__16;
x_175 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_174, x_161, x_3);
lean_dec_ref(x_161);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_unsigned_to_nat(0u);
x_177 = l_Lean_Syntax_getArg(x_1, x_176);
lean_inc_ref(x_161);
x_178 = l_Lean_Elab_Level_elabLevel(x_177, x_161, x_3);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec_ref(x_178);
x_181 = lean_unsigned_to_nat(2u);
x_182 = l_Lean_Syntax_getArg(x_1, x_181);
lean_dec(x_1);
x_183 = l_Lean_Syntax_isNatLit_x3f(x_182);
lean_dec(x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; 
lean_dec(x_179);
x_184 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_161, x_180);
lean_dec_ref(x_161);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
lean_dec_ref(x_183);
lean_inc(x_185);
x_186 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_185, x_161, x_180);
lean_dec_ref(x_161);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_188 = x_186;
} else {
 lean_dec_ref(x_186);
 x_188 = lean_box(0);
}
x_189 = l_Lean_Level_addOffset(x_179, x_185);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_185);
lean_dec(x_179);
x_191 = lean_ctor_get(x_186, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_186, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_193 = x_186;
} else {
 lean_dec_ref(x_186);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
else
{
lean_dec_ref(x_161);
lean_dec(x_1);
return x_178;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_215; 
lean_dec(x_157);
x_195 = lean_ctor_get(x_3, 0);
x_196 = lean_ctor_get(x_3, 1);
x_197 = lean_ctor_get(x_3, 2);
x_198 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_215 = l_List_elem___at___Lean_Elab_Level_elabLevel_spec__4(x_198, x_197);
if (x_215 == 0)
{
if (x_156 == 0)
{
lean_dec(x_154);
goto block_214;
}
else
{
lean_object* x_216; uint8_t x_217; uint8_t x_218; 
x_216 = l_Lean_Elab_Level_elabLevel___closed__19;
x_217 = l_Lean_Option_get___at___Lean_Elab_Level_elabLevel_spec__5(x_154, x_216);
lean_dec(x_154);
lean_inc(x_198);
x_218 = l_Lean_Elab_isValidAutoBoundLevelName(x_198, x_217);
if (x_218 == 0)
{
goto block_214;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_inc(x_197);
lean_inc_ref(x_196);
lean_inc_ref(x_195);
lean_dec_ref(x_161);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_219 = x_3;
} else {
 lean_dec_ref(x_3);
 x_219 = lean_box(0);
}
lean_inc(x_198);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_198);
lean_ctor_set(x_220, 1, x_197);
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 3, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_195);
lean_ctor_set(x_221, 1, x_196);
lean_ctor_set(x_221, 2, x_220);
x_199 = x_221;
goto block_202;
}
}
}
else
{
lean_dec_ref(x_161);
lean_dec(x_154);
x_199 = x_3;
goto block_202;
}
block_202:
{
lean_object* x_200; lean_object* x_201; 
x_200 = l_Lean_mkLevelParam(x_198);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
block_214:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_203 = l_Lean_Elab_Level_elabLevel___closed__18;
x_204 = lean_mk_syntax_ident(x_198);
x_205 = l_Lean_MessageData_ofSyntax(x_204);
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_205);
x_207 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6;
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_208, x_161, x_3);
lean_dec_ref(x_161);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
else
{
lean_object* x_222; 
lean_dec(x_157);
lean_dec(x_154);
x_222 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_161, x_3);
lean_dec_ref(x_161);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
lean_dec_ref(x_222);
lean_inc(x_224);
x_225 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_224, x_161, x_3);
lean_dec_ref(x_161);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_227 = x_225;
} else {
 lean_dec_ref(x_225);
 x_227 = lean_box(0);
}
x_228 = l_Lean_Level_ofNat(x_224);
lean_dec(x_224);
if (lean_is_scalar(x_227)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_227;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_226);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_224);
x_230 = lean_ctor_get(x_225, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_225, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_232 = x_225;
} else {
 lean_dec_ref(x_225);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
}
}
else
{
lean_object* x_234; 
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_1);
x_234 = l_Lean_Elab_Level_mkFreshLevelMVar(x_161, x_3);
lean_dec_ref(x_161);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_157);
lean_dec(x_154);
x_235 = lean_unsigned_to_nat(1u);
x_236 = l_Lean_Syntax_getArg(x_1, x_235);
lean_dec(x_1);
x_237 = l_Lean_Syntax_getArgs(x_236);
lean_dec(x_236);
x_238 = lean_box(0);
x_239 = l_Array_back_x21___redArg(x_238, x_237);
lean_inc_ref(x_161);
x_240 = l_Lean_Elab_Level_elabLevel(x_239, x_161, x_3);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
x_260 = lean_array_get_size(x_237);
x_261 = lean_nat_sub(x_260, x_235);
x_262 = lean_unsigned_to_nat(0u);
x_263 = lean_nat_dec_le(x_261, x_260);
if (x_263 == 0)
{
lean_dec(x_261);
x_243 = x_262;
x_244 = x_260;
goto block_259;
}
else
{
lean_dec(x_260);
x_243 = x_262;
x_244 = x_261;
goto block_259;
}
block_259:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; 
x_245 = l_Array_toSubarray___redArg(x_237, x_243, x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc_ref(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_245, 2);
lean_inc(x_248);
lean_dec_ref(x_245);
x_249 = lean_array_get_size(x_246);
x_250 = lean_nat_dec_le(x_248, x_249);
if (x_250 == 0)
{
uint8_t x_251; 
lean_dec(x_248);
x_251 = lean_nat_dec_lt(x_247, x_249);
if (x_251 == 0)
{
lean_dec(x_249);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_161);
return x_240;
}
else
{
size_t x_252; size_t x_253; lean_object* x_254; 
lean_dec_ref(x_240);
x_252 = lean_usize_of_nat(x_249);
lean_dec(x_249);
x_253 = lean_usize_of_nat(x_247);
lean_dec(x_247);
x_254 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__6(x_246, x_252, x_253, x_241, x_161, x_242);
lean_dec_ref(x_246);
return x_254;
}
}
else
{
uint8_t x_255; 
lean_dec(x_249);
x_255 = lean_nat_dec_lt(x_247, x_248);
if (x_255 == 0)
{
lean_dec(x_248);
lean_dec(x_247);
lean_dec_ref(x_246);
lean_dec(x_242);
lean_dec(x_241);
lean_dec_ref(x_161);
return x_240;
}
else
{
size_t x_256; size_t x_257; lean_object* x_258; 
lean_dec_ref(x_240);
x_256 = lean_usize_of_nat(x_248);
lean_dec(x_248);
x_257 = lean_usize_of_nat(x_247);
lean_dec(x_247);
x_258 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__6(x_246, x_256, x_257, x_241, x_161, x_242);
lean_dec_ref(x_246);
return x_258;
}
}
}
}
else
{
lean_dec_ref(x_237);
lean_dec_ref(x_161);
return x_240;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_157);
lean_dec(x_154);
x_264 = lean_unsigned_to_nat(1u);
x_265 = l_Lean_Syntax_getArg(x_1, x_264);
lean_dec(x_1);
x_266 = l_Lean_Syntax_getArgs(x_265);
lean_dec(x_265);
x_267 = lean_box(0);
x_268 = l_Array_back_x21___redArg(x_267, x_266);
lean_inc_ref(x_161);
x_269 = l_Lean_Elab_Level_elabLevel(x_268, x_161, x_3);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
x_289 = lean_array_get_size(x_266);
x_290 = lean_nat_sub(x_289, x_264);
x_291 = lean_unsigned_to_nat(0u);
x_292 = lean_nat_dec_le(x_290, x_289);
if (x_292 == 0)
{
lean_dec(x_290);
x_272 = x_291;
x_273 = x_289;
goto block_288;
}
else
{
lean_dec(x_289);
x_272 = x_291;
x_273 = x_290;
goto block_288;
}
block_288:
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_274 = l_Array_toSubarray___redArg(x_266, x_272, x_273);
x_275 = lean_ctor_get(x_274, 0);
lean_inc_ref(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_274, 2);
lean_inc(x_277);
lean_dec_ref(x_274);
x_278 = lean_array_get_size(x_275);
x_279 = lean_nat_dec_le(x_277, x_278);
if (x_279 == 0)
{
uint8_t x_280; 
lean_dec(x_277);
x_280 = lean_nat_dec_lt(x_276, x_278);
if (x_280 == 0)
{
lean_dec(x_278);
lean_dec(x_276);
lean_dec_ref(x_275);
lean_dec(x_271);
lean_dec(x_270);
lean_dec_ref(x_161);
return x_269;
}
else
{
size_t x_281; size_t x_282; lean_object* x_283; 
lean_dec_ref(x_269);
x_281 = lean_usize_of_nat(x_278);
lean_dec(x_278);
x_282 = lean_usize_of_nat(x_276);
lean_dec(x_276);
x_283 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__7(x_275, x_281, x_282, x_270, x_161, x_271);
lean_dec_ref(x_275);
return x_283;
}
}
else
{
uint8_t x_284; 
lean_dec(x_278);
x_284 = lean_nat_dec_lt(x_276, x_277);
if (x_284 == 0)
{
lean_dec(x_277);
lean_dec(x_276);
lean_dec_ref(x_275);
lean_dec(x_271);
lean_dec(x_270);
lean_dec_ref(x_161);
return x_269;
}
else
{
size_t x_285; size_t x_286; lean_object* x_287; 
lean_dec_ref(x_269);
x_285 = lean_usize_of_nat(x_277);
lean_dec(x_277);
x_286 = lean_usize_of_nat(x_276);
lean_dec(x_276);
x_287 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__7(x_275, x_285, x_286, x_270, x_161, x_271);
lean_dec_ref(x_275);
return x_287;
}
}
}
}
else
{
lean_dec_ref(x_266);
lean_dec_ref(x_161);
return x_269;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_157);
lean_dec(x_154);
x_293 = lean_unsigned_to_nat(1u);
x_294 = l_Lean_Syntax_getArg(x_1, x_293);
lean_dec(x_1);
x_1 = x_294;
x_2 = x_161;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_Elab_Level_elabLevel_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwIllFormedSyntax___at___Lean_Elab_Level_elabLevel_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at_____private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at_____private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2_spec__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___Lean_Elab_Level_elabLevel_spec__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___Lean_Elab_Level_elabLevel_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___Lean_Elab_Level_elabLevel_spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Lean_Elab_Level_elabLevel_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___Lean_Elab_Level_elabLevel_spec__5(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__6(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___Lean_Elab_Level_elabLevel_spec__7(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
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
l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__0____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__1____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__2____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__3____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__4____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__5____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__6____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__7____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__8____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_(lean_io_mk_world());
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
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__7);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__9 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__9);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
