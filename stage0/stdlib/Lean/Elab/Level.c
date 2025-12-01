// Lean compiler output
// Module: Lean.Elab.Level
// Imports: public import Lean.Parser.Level public import Lean.Elab.AutoBound
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
static lean_object* l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
lean_object* l_EStateM_instMonad___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__10;
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__7;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__12;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__4;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__4;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
lean_object* l_EStateM_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__4(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4____boxed(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__3;
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__5;
static lean_object* l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
lean_object* l_Nat_reprFast(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__5;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__17;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3;
static lean_object* l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM;
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__9;
uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__9;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__4;
static lean_object* l_Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__4___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__0;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM;
lean_object* l_EStateM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_maxUniverseOffset;
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(lean_object*, lean_object*);
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
static lean_object* l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__1;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__13;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__6;
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2;
extern lean_object* l_Lean_Elab_relaxedAutoImplicit;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__1;
size_t lean_usize_sub(size_t, size_t);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__15;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM;
static lean_object* l_Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__14;
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__8;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__6;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instAddMessageContextLevelElabM___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___redArg(x_2);
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
x_3 = l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___00Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshLMVarId___at___00Lean_Elab_Level_mkFreshLevelMVar_spec__0(x_1, x_2);
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
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxUniverseOffset", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maximum universe level offset", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Level", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_2 = l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_4 = l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_6);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_17);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_18);
lean_inc(x_1);
x_21 = lean_register_option(x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_22 = x_21;
} else {
 lean_dec_ref(x_21);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_17);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_1);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_26 = x_21;
} else {
 lean_dec_ref(x_21);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_4 = l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_5 = l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
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
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed syntax", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1;
x_4 = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__5(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__4(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("paren", 5, 5);
return x_1;
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
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__1;
x_2 = l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__0;
x_4 = l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
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
x_2 = l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__0;
x_4 = l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
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
x_2 = l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__0;
x_4 = l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
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
x_2 = l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__0;
x_4 = l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
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
x_2 = l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
x_3 = l_Lean_Elab_Level_elabLevel___closed__0;
x_4 = l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__0;
x_6 = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(x_4, x_5);
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
x_23 = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(x_22, x_2, x_3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_25 = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(x_24, x_2, x_3);
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
x_34 = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(x_2, x_30);
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
x_36 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(x_35, x_2, x_30);
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
x_67 = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__4(x_50, x_49);
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
x_69 = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__5(x_5, x_68);
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
x_61 = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(x_60, x_2, x_3);
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
x_79 = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(x_2, x_3);
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
x_81 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(x_80, x_2, x_3);
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
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
x_101 = lean_array_get_size(x_95);
x_102 = lean_nat_sub(x_101, x_93);
lean_dec(x_101);
x_103 = lean_unsigned_to_nat(0u);
x_104 = l_Array_toSubarray___redArg(x_95, x_103, x_102);
x_105 = lean_ctor_get(x_104, 0);
lean_inc_ref(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 2);
lean_inc(x_107);
lean_dec_ref(x_104);
x_108 = lean_array_get_size(x_105);
x_109 = lean_nat_dec_le(x_107, x_108);
if (x_109 == 0)
{
uint8_t x_110; 
lean_dec(x_107);
x_110 = lean_nat_dec_lt(x_106, x_108);
if (x_110 == 0)
{
lean_dec(x_108);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_2);
return x_98;
}
else
{
size_t x_111; size_t x_112; lean_object* x_113; 
lean_dec_ref(x_98);
x_111 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_112 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_113 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(x_105, x_111, x_112, x_99, x_2, x_100);
lean_dec_ref(x_105);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_108);
x_114 = lean_nat_dec_lt(x_106, x_107);
if (x_114 == 0)
{
lean_dec(x_107);
lean_dec(x_106);
lean_dec_ref(x_105);
lean_dec(x_100);
lean_dec(x_99);
lean_dec_ref(x_2);
return x_98;
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; 
lean_dec_ref(x_98);
x_115 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_116 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_117 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(x_105, x_115, x_116, x_99, x_2, x_100);
lean_dec_ref(x_105);
return x_117;
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
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_8);
lean_dec(x_5);
x_118 = lean_unsigned_to_nat(1u);
x_119 = l_Lean_Syntax_getArg(x_1, x_118);
lean_dec(x_1);
x_120 = l_Lean_Syntax_getArgs(x_119);
lean_dec(x_119);
x_121 = lean_box(0);
x_122 = l_Array_back_x21___redArg(x_121, x_120);
lean_inc_ref(x_2);
x_123 = l_Lean_Elab_Level_elabLevel(x_122, x_2, x_3);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
x_126 = lean_array_get_size(x_120);
x_127 = lean_nat_sub(x_126, x_118);
lean_dec(x_126);
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Array_toSubarray___redArg(x_120, x_128, x_127);
x_130 = lean_ctor_get(x_129, 0);
lean_inc_ref(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 2);
lean_inc(x_132);
lean_dec_ref(x_129);
x_133 = lean_array_get_size(x_130);
x_134 = lean_nat_dec_le(x_132, x_133);
if (x_134 == 0)
{
uint8_t x_135; 
lean_dec(x_132);
x_135 = lean_nat_dec_lt(x_131, x_133);
if (x_135 == 0)
{
lean_dec(x_133);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_125);
lean_dec(x_124);
lean_dec_ref(x_2);
return x_123;
}
else
{
size_t x_136; size_t x_137; lean_object* x_138; 
lean_dec_ref(x_123);
x_136 = lean_usize_of_nat(x_133);
lean_dec(x_133);
x_137 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_138 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__7(x_130, x_136, x_137, x_124, x_2, x_125);
lean_dec_ref(x_130);
return x_138;
}
}
else
{
uint8_t x_139; 
lean_dec(x_133);
x_139 = lean_nat_dec_lt(x_131, x_132);
if (x_139 == 0)
{
lean_dec(x_132);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_125);
lean_dec(x_124);
lean_dec_ref(x_2);
return x_123;
}
else
{
size_t x_140; size_t x_141; lean_object* x_142; 
lean_dec_ref(x_123);
x_140 = lean_usize_of_nat(x_132);
lean_dec(x_132);
x_141 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_142 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__7(x_130, x_140, x_141, x_124, x_2, x_125);
lean_dec_ref(x_130);
return x_142;
}
}
}
else
{
lean_dec_ref(x_120);
lean_dec_ref(x_2);
return x_123;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_8);
lean_dec(x_5);
x_143 = lean_unsigned_to_nat(1u);
x_144 = l_Lean_Syntax_getArg(x_1, x_143);
lean_dec(x_1);
x_1 = x_144;
goto _start;
}
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_146 = lean_ctor_get(x_2, 0);
x_147 = lean_ctor_get(x_2, 1);
x_148 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_2);
lean_inc(x_1);
x_149 = l_Lean_Syntax_getKind(x_1);
x_150 = l_Lean_Elab_Level_elabLevel___closed__2;
x_151 = lean_name_eq(x_149, x_150);
x_152 = l_Lean_replaceRef(x_1, x_147);
lean_dec(x_147);
lean_inc(x_146);
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_146);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_148);
if (x_151 == 0)
{
lean_object* x_154; uint8_t x_155; 
x_154 = l_Lean_Elab_Level_elabLevel___closed__4;
x_155 = lean_name_eq(x_149, x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = l_Lean_Elab_Level_elabLevel___closed__6;
x_157 = lean_name_eq(x_149, x_156);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = l_Lean_Elab_Level_elabLevel___closed__8;
x_159 = lean_name_eq(x_149, x_158);
if (x_159 == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = l_Lean_Elab_Level_elabLevel___closed__10;
x_161 = lean_name_eq(x_149, x_160);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = l_Lean_Elab_Level_elabLevel___closed__12;
x_163 = lean_name_eq(x_149, x_162);
if (x_163 == 0)
{
lean_object* x_164; uint8_t x_165; 
lean_dec(x_146);
x_164 = l_Lean_Elab_Level_elabLevel___closed__14;
x_165 = lean_name_eq(x_149, x_164);
lean_dec(x_149);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_1);
x_166 = l_Lean_Elab_Level_elabLevel___closed__16;
x_167 = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(x_166, x_153, x_3);
lean_dec_ref(x_153);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_unsigned_to_nat(0u);
x_169 = l_Lean_Syntax_getArg(x_1, x_168);
lean_inc_ref(x_153);
x_170 = l_Lean_Elab_Level_elabLevel(x_169, x_153, x_3);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec_ref(x_170);
x_173 = lean_unsigned_to_nat(2u);
x_174 = l_Lean_Syntax_getArg(x_1, x_173);
lean_dec(x_1);
x_175 = l_Lean_Syntax_isNatLit_x3f(x_174);
lean_dec(x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
lean_dec(x_171);
x_176 = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(x_153, x_172);
lean_dec_ref(x_153);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
lean_dec_ref(x_175);
lean_inc(x_177);
x_178 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(x_177, x_153, x_172);
lean_dec_ref(x_153);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
x_181 = l_Lean_Level_addOffset(x_171, x_177);
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_180;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_179);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_177);
lean_dec(x_171);
x_183 = lean_ctor_get(x_178, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_178, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_185 = x_178;
} else {
 lean_dec_ref(x_178);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
else
{
lean_dec_ref(x_153);
lean_dec(x_1);
return x_170;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_207; 
lean_dec(x_149);
x_187 = lean_ctor_get(x_3, 0);
x_188 = lean_ctor_get(x_3, 1);
x_189 = lean_ctor_get(x_3, 2);
x_190 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_207 = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__4(x_190, x_189);
if (x_207 == 0)
{
if (x_148 == 0)
{
lean_dec(x_146);
goto block_206;
}
else
{
lean_object* x_208; uint8_t x_209; uint8_t x_210; 
x_208 = l_Lean_Elab_Level_elabLevel___closed__19;
x_209 = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__5(x_146, x_208);
lean_dec(x_146);
lean_inc(x_190);
x_210 = l_Lean_Elab_isValidAutoBoundLevelName(x_190, x_209);
if (x_210 == 0)
{
goto block_206;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_inc(x_189);
lean_inc_ref(x_188);
lean_inc_ref(x_187);
lean_dec_ref(x_153);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_211 = x_3;
} else {
 lean_dec_ref(x_3);
 x_211 = lean_box(0);
}
lean_inc(x_190);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_190);
lean_ctor_set(x_212, 1, x_189);
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(0, 3, 0);
} else {
 x_213 = x_211;
}
lean_ctor_set(x_213, 0, x_187);
lean_ctor_set(x_213, 1, x_188);
lean_ctor_set(x_213, 2, x_212);
x_191 = x_213;
goto block_194;
}
}
}
else
{
lean_dec_ref(x_153);
lean_dec(x_146);
x_191 = x_3;
goto block_194;
}
block_194:
{
lean_object* x_192; lean_object* x_193; 
x_192 = l_Lean_mkLevelParam(x_190);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
block_206:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_195 = l_Lean_Elab_Level_elabLevel___closed__18;
x_196 = lean_mk_syntax_ident(x_190);
x_197 = l_Lean_MessageData_ofSyntax(x_196);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
x_199 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___redArg___lam__0___closed__6;
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(x_200, x_153, x_3);
lean_dec_ref(x_153);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_204 = x_201;
} else {
 lean_dec_ref(x_201);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
else
{
lean_object* x_214; 
lean_dec(x_149);
lean_dec(x_146);
x_214 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
x_215 = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(x_153, x_3);
lean_dec_ref(x_153);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
lean_dec_ref(x_214);
lean_inc(x_216);
x_217 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(x_216, x_153, x_3);
lean_dec_ref(x_153);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
x_220 = l_Lean_Level_ofNat(x_216);
lean_dec(x_216);
if (lean_is_scalar(x_219)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_219;
}
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_218);
return x_221;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_216);
x_222 = lean_ctor_get(x_217, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_217, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_224 = x_217;
} else {
 lean_dec_ref(x_217);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
}
}
else
{
lean_object* x_226; 
lean_dec(x_149);
lean_dec(x_146);
lean_dec(x_1);
x_226 = l_Lean_Elab_Level_mkFreshLevelMVar(x_153, x_3);
lean_dec_ref(x_153);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_149);
lean_dec(x_146);
x_227 = lean_unsigned_to_nat(1u);
x_228 = l_Lean_Syntax_getArg(x_1, x_227);
lean_dec(x_1);
x_229 = l_Lean_Syntax_getArgs(x_228);
lean_dec(x_228);
x_230 = lean_box(0);
x_231 = l_Array_back_x21___redArg(x_230, x_229);
lean_inc_ref(x_153);
x_232 = l_Lean_Elab_Level_elabLevel(x_231, x_153, x_3);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
x_235 = lean_array_get_size(x_229);
x_236 = lean_nat_sub(x_235, x_227);
lean_dec(x_235);
x_237 = lean_unsigned_to_nat(0u);
x_238 = l_Array_toSubarray___redArg(x_229, x_237, x_236);
x_239 = lean_ctor_get(x_238, 0);
lean_inc_ref(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_238, 2);
lean_inc(x_241);
lean_dec_ref(x_238);
x_242 = lean_array_get_size(x_239);
x_243 = lean_nat_dec_le(x_241, x_242);
if (x_243 == 0)
{
uint8_t x_244; 
lean_dec(x_241);
x_244 = lean_nat_dec_lt(x_240, x_242);
if (x_244 == 0)
{
lean_dec(x_242);
lean_dec(x_240);
lean_dec_ref(x_239);
lean_dec(x_234);
lean_dec(x_233);
lean_dec_ref(x_153);
return x_232;
}
else
{
size_t x_245; size_t x_246; lean_object* x_247; 
lean_dec_ref(x_232);
x_245 = lean_usize_of_nat(x_242);
lean_dec(x_242);
x_246 = lean_usize_of_nat(x_240);
lean_dec(x_240);
x_247 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(x_239, x_245, x_246, x_233, x_153, x_234);
lean_dec_ref(x_239);
return x_247;
}
}
else
{
uint8_t x_248; 
lean_dec(x_242);
x_248 = lean_nat_dec_lt(x_240, x_241);
if (x_248 == 0)
{
lean_dec(x_241);
lean_dec(x_240);
lean_dec_ref(x_239);
lean_dec(x_234);
lean_dec(x_233);
lean_dec_ref(x_153);
return x_232;
}
else
{
size_t x_249; size_t x_250; lean_object* x_251; 
lean_dec_ref(x_232);
x_249 = lean_usize_of_nat(x_241);
lean_dec(x_241);
x_250 = lean_usize_of_nat(x_240);
lean_dec(x_240);
x_251 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(x_239, x_249, x_250, x_233, x_153, x_234);
lean_dec_ref(x_239);
return x_251;
}
}
}
else
{
lean_dec_ref(x_229);
lean_dec_ref(x_153);
return x_232;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_149);
lean_dec(x_146);
x_252 = lean_unsigned_to_nat(1u);
x_253 = l_Lean_Syntax_getArg(x_1, x_252);
lean_dec(x_1);
x_254 = l_Lean_Syntax_getArgs(x_253);
lean_dec(x_253);
x_255 = lean_box(0);
x_256 = l_Array_back_x21___redArg(x_255, x_254);
lean_inc_ref(x_153);
x_257 = l_Lean_Elab_Level_elabLevel(x_256, x_153, x_3);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
x_260 = lean_array_get_size(x_254);
x_261 = lean_nat_sub(x_260, x_252);
lean_dec(x_260);
x_262 = lean_unsigned_to_nat(0u);
x_263 = l_Array_toSubarray___redArg(x_254, x_262, x_261);
x_264 = lean_ctor_get(x_263, 0);
lean_inc_ref(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_263, 2);
lean_inc(x_266);
lean_dec_ref(x_263);
x_267 = lean_array_get_size(x_264);
x_268 = lean_nat_dec_le(x_266, x_267);
if (x_268 == 0)
{
uint8_t x_269; 
lean_dec(x_266);
x_269 = lean_nat_dec_lt(x_265, x_267);
if (x_269 == 0)
{
lean_dec(x_267);
lean_dec(x_265);
lean_dec_ref(x_264);
lean_dec(x_259);
lean_dec(x_258);
lean_dec_ref(x_153);
return x_257;
}
else
{
size_t x_270; size_t x_271; lean_object* x_272; 
lean_dec_ref(x_257);
x_270 = lean_usize_of_nat(x_267);
lean_dec(x_267);
x_271 = lean_usize_of_nat(x_265);
lean_dec(x_265);
x_272 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__7(x_264, x_270, x_271, x_258, x_153, x_259);
lean_dec_ref(x_264);
return x_272;
}
}
else
{
uint8_t x_273; 
lean_dec(x_267);
x_273 = lean_nat_dec_lt(x_265, x_266);
if (x_273 == 0)
{
lean_dec(x_266);
lean_dec(x_265);
lean_dec_ref(x_264);
lean_dec(x_259);
lean_dec(x_258);
lean_dec_ref(x_153);
return x_257;
}
else
{
size_t x_274; size_t x_275; lean_object* x_276; 
lean_dec_ref(x_257);
x_274 = lean_usize_of_nat(x_266);
lean_dec(x_266);
x_275 = lean_usize_of_nat(x_265);
lean_dec(x_265);
x_276 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__7(x_264, x_274, x_275, x_258, x_153, x_259);
lean_dec_ref(x_264);
return x_276;
}
}
}
else
{
lean_dec_ref(x_254);
lean_dec_ref(x_153);
return x_257;
}
}
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_149);
lean_dec(x_146);
x_277 = lean_unsigned_to_nat(1u);
x_278 = l_Lean_Syntax_getArg(x_1, x_277);
lean_dec(x_1);
x_1 = x_278;
x_2 = x_153;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at___00Lean_Elab_Level_elabLevel_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_Level_elabLevel_spec__5(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2_spec__2(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___00Lean_Elab_Level_elabLevel_spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__6(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_Level_elabLevel_spec__7(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at___00Lean_Elab_Level_elabLevel_spec__2(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Lean_Parser_Level(uint8_t builtin);
lean_object* initialize_Lean_Elab_AutoBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Level(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AutoBound(builtin);
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
l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__0_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__1_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__2_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__3_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__4_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__5_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__6_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_ = _init_l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_Elab_Level_initFn___closed__7_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_Elab_Level_initFn_00___x40_Lean_Elab_Level_2963254870____hygCtx___hyg_4_();
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
l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0 = _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__0);
l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1 = _init_l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___at___00Lean_Elab_Level_elabLevel_spec__1___redArg___closed__1);
l_Lean_Elab_Level_elabLevel___closed__1 = _init_l_Lean_Elab_Level_elabLevel___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__1);
l_Lean_Elab_Level_elabLevel___closed__0 = _init_l_Lean_Elab_Level_elabLevel___closed__0();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__0);
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
