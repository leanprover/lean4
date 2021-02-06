// Lean compiler output
// Module: Lean.Elab.Level
// Imports: Init Lean.Meta.LevelDefEq Lean.Elab.Exception Lean.Elab.Log Lean.Elab.AutoBound
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
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3;
lean_object* l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__7;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4;
size_t l_USize_sub(size_t, size_t);
lean_object* l_Lean_Elab_Level_elabLevel___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_foldrMUnsafe___at_Lean_Elab_Level_elabLevel___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__4;
lean_object* l_Array_foldrMUnsafe___at_Lean_Elab_Level_elabLevel___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__6;
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__3;
lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2;
lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1;
lean_object* l_Lean_Elab_Level_maxUniverseOffset;
lean_object* lean_level_mk_max_simp(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_level_mk_imax_simp(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168_(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__1(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__2(lean_object*);
extern lean_object* l_Lean_Level_PP_Result_quote___lambda__4___closed__1;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Lean_Core_getMaxHeartbeats___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__2;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3;
lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__1;
lean_object* l_Lean_Elab_Level_elabLevel_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__2;
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1;
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__4;
lean_object* l_Lean_Elab_Level_elabLevel___closed__1;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_4____spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4;
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM;
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__31;
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2;
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object*);
extern lean_object* l_Lean_Level_PP_Result_quote___lambda__6___closed__1;
lean_object* l_Lean_Elab_Level_elabLevel___closed__3;
extern lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__2;
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2;
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__5;
lean_object* l_Lean_Elab_Level_elabLevel___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2;
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1;
lean_object* l_Subarray_foldrM___at_Lean_Elab_Level_elabLevel___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth___closed__1;
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_PP_Result_quote___lambda__5___closed__1;
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3;
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM;
lean_object* l_Subarray_foldrM___at_Lean_Elab_Level_elabLevel___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1;
x_2 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3;
return x_1;
}
}
lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static lean_object* _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1;
x_2 = l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2;
x_2 = l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadRefLevelElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4;
return x_1;
}
}
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instAddMessageContextLevelElabM(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_1);
x_6 = lean_box(0);
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
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1;
x_2 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3;
x_2 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__5;
return x_1;
}
}
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg(lean_object* x_1) {
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
x_7 = lean_name_mk_numeral(x_5, x_6);
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
x_13 = lean_name_mk_numeral(x_11, x_12);
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
x_24 = lean_name_mk_numeral(x_21, x_22);
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
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg(x_2);
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
x_26 = l_Lean_mkLevelMVar(x_19);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Level_mkFreshLevelMVar(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maxUniverseOffset");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum universe level offset");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = l_Lean_instInhabitedParserDescr___closed__1;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__2;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum universe level offset threshold (");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(") has been reached, you can increase the limit using option `set_option maxUniverseOffset <limit>`, but you are probably misusing universe levels since offsets are usually small natural numbers");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Elab_Level_maxUniverseOffset;
x_6 = l_Lean_Option_get___at_Lean_Core_getMaxHeartbeats___spec__1(x_4, x_5);
x_7 = lean_nat_dec_le(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___rarg(x_2, x_3, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_3);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_16, lean_box(0), x_17);
return x_18;
}
}
}
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_3, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Level_elabLevel_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Level_elabLevel_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Level_elabLevel_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_elabLevel_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Level_elabLevel_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Level_elabLevel_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Elab_Level_maxUniverseOffset;
x_6 = l_Lean_Option_get___at_Lean_Core_getMaxHeartbeats___spec__1(x_4, x_5);
x_7 = lean_nat_dec_le(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4(x_13, x_2, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
return x_16;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_3 == x_4;
if (x_8 == 0)
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 1;
x_10 = x_3 - x_9;
x_11 = lean_array_uget(x_2, x_10);
lean_inc(x_1);
lean_inc(x_6);
x_12 = lean_apply_4(x_1, x_11, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_3 = x_10;
x_5 = x_13;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_3 == x_4;
if (x_8 == 0)
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 1;
x_10 = x_3 - x_9;
x_11 = lean_array_uget(x_2, x_10);
lean_inc(x_1);
lean_inc(x_6);
x_12 = lean_apply_4(x_1, x_11, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_3 = x_10;
x_5 = x_13;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
}
}
lean_object* l_Array_foldrMUnsafe___at_Lean_Elab_Level_elabLevel___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_le(x_4, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_5, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_13 = lean_usize_of_nat(x_5);
x_14 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__8(x_1, x_3, x_12, x_13, x_2, x_6, x_7);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = lean_nat_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_usize_of_nat(x_4);
x_18 = lean_usize_of_nat(x_5);
x_19 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__9(x_1, x_3, x_17, x_18, x_2, x_6, x_7);
return x_19;
}
}
}
}
lean_object* l_Subarray_foldrM___at_Lean_Elab_Level_elabLevel___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Array_foldrMUnsafe___at_Lean_Elab_Level_elabLevel___spec__7(x_1, x_2, x_6, x_7, x_8, x_4, x_5);
return x_9;
}
}
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_mkLevelParam(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Level_elabLevel___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Level_elabLevel(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_level_mk_imax_simp(x_7, x_2);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_level_mk_imax_simp(x_9, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Elab_Level_elabLevel___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Level_elabLevel(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_level_mk_max_simp(x_7, x_2);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_level_mk_max_simp(x_9, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected universe level syntax kind");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown universe level '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_elabLevel___lambda__2), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_elabLevel___lambda__3), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Level_elabLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
lean_inc(x_1);
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Lean_Level_PP_Result_quote___lambda__4___closed__1;
x_6 = lean_name_eq(x_4, x_5);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_10 = l_Lean_replaceRef(x_1, x_8);
lean_dec(x_8);
lean_ctor_set(x_2, 1, x_10);
if (x_6 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Level_PP_Result_quote___lambda__5___closed__1;
x_12 = lean_name_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Level_PP_Result_quote___lambda__6___closed__1;
x_14 = lean_name_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__31;
x_16 = lean_name_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_numLitKind;
x_18 = lean_name_eq(x_4, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_identKind;
x_20 = lean_name_eq(x_4, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_Level_PP_Result_quote___lambda__3___closed__2;
x_22 = lean_name_eq(x_4, x_21);
lean_dec(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = l_Lean_Elab_Level_elabLevel___closed__3;
x_24 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(x_23, x_2, x_3);
lean_dec(x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
lean_inc(x_2);
x_27 = l_Lean_Elab_Level_elabLevel(x_26, x_2, x_3);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_unsigned_to_nat(2u);
x_31 = l_Lean_Syntax_getArg(x_1, x_30);
lean_dec(x_1);
x_32 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_17, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_28);
x_33 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_2, x_29);
lean_dec(x_2);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_34, x_2, x_29);
lean_dec(x_2);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = l_Lean_Level_addOffsetAux(x_34, x_28);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = l_Lean_Level_addOffsetAux(x_34, x_28);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_34);
lean_dec(x_28);
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
return x_27;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_27, 0);
x_48 = lean_ctor_get(x_27, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_27);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_4);
x_50 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
x_54 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_50, x_53);
if (x_54 == 0)
{
if (x_9 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_55 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_56 = l_Lean_Elab_Level_elabLevel___closed__5;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_KernelException_toMessageData___closed__3;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(x_59, x_2, x_3);
lean_dec(x_2);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_inc(x_50);
x_65 = l_Lean_Elab_isValidAutoBoundLevelName(x_50);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_66 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_66, 0, x_50);
x_67 = l_Lean_Elab_Level_elabLevel___closed__5;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_KernelException_toMessageData___closed__3;
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(x_70, x_2, x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
return x_71;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_71);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_3);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_3, 2);
lean_dec(x_77);
x_78 = lean_ctor_get(x_3, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_3, 0);
lean_dec(x_79);
lean_inc(x_50);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_50);
lean_ctor_set(x_80, 1, x_53);
lean_ctor_set(x_3, 2, x_80);
x_81 = lean_box(0);
x_82 = l_Lean_Elab_Level_elabLevel___lambda__1(x_50, x_81, x_2, x_3);
lean_dec(x_2);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_3);
lean_inc(x_50);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_50);
lean_ctor_set(x_83, 1, x_53);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_51);
lean_ctor_set(x_84, 1, x_52);
lean_ctor_set(x_84, 2, x_83);
x_85 = lean_box(0);
x_86 = l_Lean_Elab_Level_elabLevel___lambda__1(x_50, x_85, x_2, x_84);
lean_dec(x_2);
return x_86;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_87 = lean_box(0);
x_88 = l_Lean_Elab_Level_elabLevel___lambda__1(x_50, x_87, x_2, x_3);
lean_dec(x_2);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_4);
x_89 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_17, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_2, x_3);
lean_dec(x_2);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_91, x_2, x_3);
lean_dec(x_2);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
x_95 = l_Lean_Level_ofNat(x_91);
lean_dec(x_91);
lean_ctor_set(x_92, 0, x_95);
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = l_Lean_Level_ofNat(x_91);
lean_dec(x_91);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_91);
x_99 = !lean_is_exclusive(x_92);
if (x_99 == 0)
{
return x_92;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_92, 0);
x_101 = lean_ctor_get(x_92, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_92);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_4);
lean_dec(x_1);
x_103 = l_Lean_Elab_Level_mkFreshLevelMVar(x_2, x_3);
lean_dec(x_2);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_4);
x_104 = lean_unsigned_to_nat(1u);
x_105 = l_Lean_Syntax_getArg(x_1, x_104);
lean_dec(x_1);
x_106 = l_Lean_Syntax_getArgs(x_105);
lean_dec(x_105);
x_107 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_106);
lean_inc(x_2);
x_108 = l_Lean_Elab_Level_elabLevel(x_107, x_2, x_3);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_array_get_size(x_106);
x_112 = lean_nat_sub(x_111, x_104);
lean_dec(x_111);
x_113 = lean_unsigned_to_nat(0u);
x_114 = l_Array_toSubarray___rarg(x_106, x_113, x_112);
x_115 = l_Lean_Elab_Level_elabLevel___closed__6;
x_116 = l_Subarray_foldrM___at_Lean_Elab_Level_elabLevel___spec__6(x_115, x_109, x_114, x_2, x_110);
lean_dec(x_114);
return x_116;
}
else
{
uint8_t x_117; 
lean_dec(x_106);
lean_dec(x_2);
x_117 = !lean_is_exclusive(x_108);
if (x_117 == 0)
{
return x_108;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_108, 0);
x_119 = lean_ctor_get(x_108, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_108);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_4);
x_121 = lean_unsigned_to_nat(1u);
x_122 = l_Lean_Syntax_getArg(x_1, x_121);
lean_dec(x_1);
x_123 = l_Lean_Syntax_getArgs(x_122);
lean_dec(x_122);
x_124 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_123);
lean_inc(x_2);
x_125 = l_Lean_Elab_Level_elabLevel(x_124, x_2, x_3);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_array_get_size(x_123);
x_129 = lean_nat_sub(x_128, x_121);
lean_dec(x_128);
x_130 = lean_unsigned_to_nat(0u);
x_131 = l_Array_toSubarray___rarg(x_123, x_130, x_129);
x_132 = l_Lean_Elab_Level_elabLevel___closed__7;
x_133 = l_Subarray_foldrM___at_Lean_Elab_Level_elabLevel___spec__6(x_132, x_126, x_131, x_2, x_127);
lean_dec(x_131);
return x_133;
}
else
{
uint8_t x_134; 
lean_dec(x_123);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_125);
if (x_134 == 0)
{
return x_125;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_125, 0);
x_136 = lean_ctor_get(x_125, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_125);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_4);
x_138 = lean_unsigned_to_nat(1u);
x_139 = l_Lean_Syntax_getArg(x_1, x_138);
lean_dec(x_1);
x_1 = x_139;
goto _start;
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; 
x_141 = lean_ctor_get(x_2, 0);
x_142 = lean_ctor_get(x_2, 1);
x_143 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_2);
x_144 = l_Lean_replaceRef(x_1, x_142);
lean_dec(x_142);
x_145 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_145, 0, x_141);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*2, x_143);
if (x_6 == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = l_Lean_Level_PP_Result_quote___lambda__5___closed__1;
x_147 = lean_name_eq(x_4, x_146);
if (x_147 == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = l_Lean_Level_PP_Result_quote___lambda__6___closed__1;
x_149 = lean_name_eq(x_4, x_148);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1136____closed__31;
x_151 = lean_name_eq(x_4, x_150);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = l_Lean_numLitKind;
x_153 = lean_name_eq(x_4, x_152);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; 
x_154 = l_Lean_identKind;
x_155 = lean_name_eq(x_4, x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = l_Lean_Level_PP_Result_quote___lambda__3___closed__2;
x_157 = lean_name_eq(x_4, x_156);
lean_dec(x_4);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_1);
x_158 = l_Lean_Elab_Level_elabLevel___closed__3;
x_159 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(x_158, x_145, x_3);
lean_dec(x_145);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_unsigned_to_nat(0u);
x_161 = l_Lean_Syntax_getArg(x_1, x_160);
lean_inc(x_145);
x_162 = l_Lean_Elab_Level_elabLevel(x_161, x_145, x_3);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_unsigned_to_nat(2u);
x_166 = l_Lean_Syntax_getArg(x_1, x_165);
lean_dec(x_1);
x_167 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_152, x_166);
lean_dec(x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
lean_dec(x_163);
x_168 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_145, x_164);
lean_dec(x_145);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
lean_dec(x_167);
x_170 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_169, x_145, x_164);
lean_dec(x_145);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
x_173 = l_Lean_Level_addOffsetAux(x_169, x_163);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_169);
lean_dec(x_163);
x_175 = lean_ctor_get(x_170, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_170, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_177 = x_170;
} else {
 lean_dec_ref(x_170);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_145);
lean_dec(x_1);
x_179 = lean_ctor_get(x_162, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_162, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_181 = x_162;
} else {
 lean_dec_ref(x_162);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_dec(x_4);
x_183 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_184 = lean_ctor_get(x_3, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_3, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_3, 2);
lean_inc(x_186);
x_187 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_183, x_186);
if (x_187 == 0)
{
if (x_143 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
x_188 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_188, 0, x_183);
x_189 = l_Lean_Elab_Level_elabLevel___closed__5;
x_190 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = l_Lean_KernelException_toMessageData___closed__3;
x_192 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(x_192, x_145, x_3);
lean_dec(x_145);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
else
{
uint8_t x_198; 
lean_inc(x_183);
x_198 = l_Lean_Elab_isValidAutoBoundLevelName(x_183);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
x_199 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_199, 0, x_183);
x_200 = l_Lean_Elab_Level_elabLevel___closed__5;
x_201 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_202 = l_Lean_KernelException_toMessageData___closed__3;
x_203 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(x_203, x_145, x_3);
lean_dec(x_145);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_209 = x_3;
} else {
 lean_dec_ref(x_3);
 x_209 = lean_box(0);
}
lean_inc(x_183);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_183);
lean_ctor_set(x_210, 1, x_186);
if (lean_is_scalar(x_209)) {
 x_211 = lean_alloc_ctor(0, 3, 0);
} else {
 x_211 = x_209;
}
lean_ctor_set(x_211, 0, x_184);
lean_ctor_set(x_211, 1, x_185);
lean_ctor_set(x_211, 2, x_210);
x_212 = lean_box(0);
x_213 = l_Lean_Elab_Level_elabLevel___lambda__1(x_183, x_212, x_145, x_211);
lean_dec(x_145);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
x_214 = lean_box(0);
x_215 = l_Lean_Elab_Level_elabLevel___lambda__1(x_183, x_214, x_145, x_3);
lean_dec(x_145);
return x_215;
}
}
}
else
{
lean_object* x_216; 
lean_dec(x_4);
x_216 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_152, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; 
x_217 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_145, x_3);
lean_dec(x_145);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
lean_dec(x_216);
x_219 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_218, x_145, x_3);
lean_dec(x_145);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_221 = x_219;
} else {
 lean_dec_ref(x_219);
 x_221 = lean_box(0);
}
x_222 = l_Lean_Level_ofNat(x_218);
lean_dec(x_218);
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_221;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_220);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_218);
x_224 = lean_ctor_get(x_219, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_219, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_226 = x_219;
} else {
 lean_dec_ref(x_219);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
}
}
else
{
lean_object* x_228; 
lean_dec(x_4);
lean_dec(x_1);
x_228 = l_Lean_Elab_Level_mkFreshLevelMVar(x_145, x_3);
lean_dec(x_145);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_4);
x_229 = lean_unsigned_to_nat(1u);
x_230 = l_Lean_Syntax_getArg(x_1, x_229);
lean_dec(x_1);
x_231 = l_Lean_Syntax_getArgs(x_230);
lean_dec(x_230);
x_232 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_231);
lean_inc(x_145);
x_233 = l_Lean_Elab_Level_elabLevel(x_232, x_145, x_3);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_array_get_size(x_231);
x_237 = lean_nat_sub(x_236, x_229);
lean_dec(x_236);
x_238 = lean_unsigned_to_nat(0u);
x_239 = l_Array_toSubarray___rarg(x_231, x_238, x_237);
x_240 = l_Lean_Elab_Level_elabLevel___closed__6;
x_241 = l_Subarray_foldrM___at_Lean_Elab_Level_elabLevel___spec__6(x_240, x_234, x_239, x_145, x_235);
lean_dec(x_239);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_231);
lean_dec(x_145);
x_242 = lean_ctor_get(x_233, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_233, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_244 = x_233;
} else {
 lean_dec_ref(x_233);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_4);
x_246 = lean_unsigned_to_nat(1u);
x_247 = l_Lean_Syntax_getArg(x_1, x_246);
lean_dec(x_1);
x_248 = l_Lean_Syntax_getArgs(x_247);
lean_dec(x_247);
x_249 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_248);
lean_inc(x_145);
x_250 = l_Lean_Elab_Level_elabLevel(x_249, x_145, x_3);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = lean_array_get_size(x_248);
x_254 = lean_nat_sub(x_253, x_246);
lean_dec(x_253);
x_255 = lean_unsigned_to_nat(0u);
x_256 = l_Array_toSubarray___rarg(x_248, x_255, x_254);
x_257 = l_Lean_Elab_Level_elabLevel___closed__7;
x_258 = l_Subarray_foldrM___at_Lean_Elab_Level_elabLevel___spec__6(x_257, x_251, x_256, x_145, x_252);
lean_dec(x_256);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_248);
lean_dec(x_145);
x_259 = lean_ctor_get(x_250, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_250, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_261 = x_250;
} else {
 lean_dec_ref(x_250);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_4);
x_263 = lean_unsigned_to_nat(1u);
x_264 = l_Lean_Syntax_getArg(x_1, x_263);
lean_dec(x_1);
x_1 = x_264;
x_2 = x_145;
goto _start;
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__8(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__9(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_foldrMUnsafe___at_Lean_Elab_Level_elabLevel___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldrMUnsafe___at_Lean_Elab_Level_elabLevel___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Subarray_foldrM___at_Lean_Elab_Level_elabLevel___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Subarray_foldrM___at_Lean_Elab_Level_elabLevel___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Level_elabLevel___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Lean_Elab_Exception(lean_object*);
lean_object* initialize_Lean_Elab_Log(lean_object*);
lean_object* initialize_Lean_Elab_AutoBound(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Level(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LevelDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Log(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AutoBound(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3);
l_Lean_Elab_Level_instMonadOptionsLevelElabM = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM);
l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1 = _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1);
l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2 = _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2);
l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3 = _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3);
l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4 = _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4);
l_Lean_Elab_Level_instMonadRefLevelElabM = _init_l_Lean_Elab_Level_instMonadRefLevelElabM();
lean_mark_persistent(l_Lean_Elab_Level_instMonadRefLevelElabM);
l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1 = _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1);
l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2 = _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2);
l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3 = _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3);
l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4 = _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4);
l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__5 = _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__5();
lean_mark_persistent(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__5);
l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM = _init_l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM();
lean_mark_persistent(l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__1 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__1();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__1);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__2 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__2();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__2);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__3 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__3();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__3);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__4 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__4();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168____closed__4);
res = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_168_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Level_maxUniverseOffset = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Level_maxUniverseOffset);
lean_dec_ref(res);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
