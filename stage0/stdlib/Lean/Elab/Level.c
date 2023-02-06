// Lean compiler output
// Module: Lean.Elab.Level
// Imports: Init Lean.Log Lean.Parser.Level Lean.Elab.Exception Lean.Elab.AutoBound
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
static lean_object* l_Lean_Elab_Level_elabLevel___closed__18;
uint8_t l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1;
lean_object* l_Lean_Level_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__12;
static lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__5;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__8;
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__1;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__2;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__5;
static lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2;
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440_(lean_object*);
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM;
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__1;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__22;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__10;
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__4;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1;
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__20;
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_maxUniverseOffset;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__21;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__16;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__9;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__13;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2;
extern lean_object* l_Lean_Elab_relaxedAutoImplicit;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2___rarg(lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__1;
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__19;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__5;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__15;
extern lean_object* l_Lean_instInhabitedSyntax;
static lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM;
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__7;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__11;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__14;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__8;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM() {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instAddMessageContextLevelElabM(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2___rarg(x_2);
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
x_3 = l_Lean_mkFreshLMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshLMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshLMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(x_1, x_2);
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
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maxUniverseOffset", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maximum universe level offset", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__3;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Level", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__6;
x_2 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__7;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__8;
x_4 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__2;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__5;
x_4 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__9;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Level_maxUniverseOffset;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maximum universe level offset threshold (", 41);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(") has been reached, you can increase the limit using option `set_option maxUniverseOffset <limit>`, but you are probably misusing universe levels since offsets are usually small natural numbers", 193);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1;
x_6 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_4, x_5);
x_7 = lean_nat_dec_le(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Nat_repr(x_6);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__5;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___rarg(x_2, x_3, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_3);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ill-formed syntax", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__2;
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(x_3, x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1;
x_6 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_4, x_5);
x_7 = lean_nat_dec_le(x_1, x_6);
lean_dec(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Nat_repr(x_6);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__5;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4(x_14, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
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
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
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
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_6);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Level_param___override(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("paren", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__6;
x_2 = l_Lean_Elab_Level_elabLevel___closed__1;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__8;
x_4 = l_Lean_Elab_Level_elabLevel___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("max", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__6;
x_2 = l_Lean_Elab_Level_elabLevel___closed__1;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__8;
x_4 = l_Lean_Elab_Level_elabLevel___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("imax", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__6;
x_2 = l_Lean_Elab_Level_elabLevel___closed__1;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__8;
x_4 = l_Lean_Elab_Level_elabLevel___closed__6;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__6;
x_2 = l_Lean_Elab_Level_elabLevel___closed__1;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__8;
x_4 = l_Lean_Elab_Level_elabLevel___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("num", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Level_elabLevel___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Level_elabLevel___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("addLit", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__6;
x_2 = l_Lean_Elab_Level_elabLevel___closed__1;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__8;
x_4 = l_Lean_Elab_Level_elabLevel___closed__14;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected universe level syntax kind", 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown universe level '", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__18;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__20;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__22() {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
lean_inc(x_1);
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Lean_Elab_Level_elabLevel___closed__3;
x_6 = lean_name_eq(x_4, x_5);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_11 = l_Lean_replaceRef(x_1, x_9);
lean_dec(x_9);
lean_inc(x_8);
lean_ctor_set(x_2, 1, x_11);
if (x_6 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Elab_Level_elabLevel___closed__5;
x_13 = lean_name_eq(x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Level_elabLevel___closed__7;
x_15 = lean_name_eq(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_Elab_Level_elabLevel___closed__9;
x_17 = lean_name_eq(x_4, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Elab_Level_elabLevel___closed__11;
x_19 = lean_name_eq(x_4, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Elab_Level_elabLevel___closed__13;
x_21 = lean_name_eq(x_4, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_8);
x_22 = l_Lean_Elab_Level_elabLevel___closed__15;
x_23 = lean_name_eq(x_4, x_22);
lean_dec(x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = l_Lean_Elab_Level_elabLevel___closed__17;
x_25 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(x_24, x_2, x_3);
lean_dec(x_2);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Syntax_getArg(x_1, x_26);
lean_inc(x_2);
x_28 = l_Lean_Elab_Level_elabLevel(x_27, x_2, x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(2u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
lean_dec(x_1);
x_33 = l_Lean_Syntax_isNatLit_x3f(x_32);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_29);
x_34 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_2, x_30);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_35);
x_36 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_35, x_2, x_30);
lean_dec(x_2);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = l_Lean_Level_addOffsetAux(x_35, x_29);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = l_Lean_Level_addOffsetAux(x_35, x_29);
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
uint8_t x_47; 
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_28);
if (x_47 == 0)
{
return x_28;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_28, 0);
x_49 = lean_ctor_get(x_28, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_28);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_4);
x_51 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 2);
lean_inc(x_54);
x_55 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_51, x_54);
if (x_55 == 0)
{
uint8_t x_56; 
if (x_10 == 0)
{
uint8_t x_79; 
lean_dec(x_8);
x_79 = 0;
x_56 = x_79;
goto block_78;
}
else
{
lean_object* x_80; uint8_t x_81; uint8_t x_82; 
x_80 = l_Lean_Elab_Level_elabLevel___closed__22;
x_81 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_8, x_80);
lean_dec(x_8);
lean_inc(x_51);
x_82 = l_Lean_Elab_isValidAutoBoundLevelName(x_51, x_81);
x_56 = x_82;
goto block_78;
}
block_78:
{
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_57 = l_Lean_MessageData_ofName(x_51);
x_58 = l_Lean_Elab_Level_elabLevel___closed__19;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Elab_Level_elabLevel___closed__21;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(x_61, x_2, x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_62);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_3);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_3, 2);
lean_dec(x_68);
x_69 = lean_ctor_get(x_3, 1);
lean_dec(x_69);
x_70 = lean_ctor_get(x_3, 0);
lean_dec(x_70);
lean_inc(x_51);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_51);
lean_ctor_set(x_71, 1, x_54);
lean_ctor_set(x_3, 2, x_71);
x_72 = lean_box(0);
x_73 = l_Lean_Elab_Level_elabLevel___lambda__1(x_51, x_72, x_2, x_3);
lean_dec(x_2);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_3);
lean_inc(x_51);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_51);
lean_ctor_set(x_74, 1, x_54);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_52);
lean_ctor_set(x_75, 1, x_53);
lean_ctor_set(x_75, 2, x_74);
x_76 = lean_box(0);
x_77 = l_Lean_Elab_Level_elabLevel___lambda__1(x_51, x_76, x_2, x_75);
lean_dec(x_2);
return x_77;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_8);
x_83 = lean_box(0);
x_84 = l_Lean_Elab_Level_elabLevel___lambda__1(x_51, x_83, x_2, x_3);
lean_dec(x_2);
return x_84;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_8);
lean_dec(x_4);
x_85 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_2, x_3);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_87);
x_88 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_87, x_2, x_3);
lean_dec(x_2);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
lean_dec(x_90);
x_91 = l_Lean_Level_ofNat(x_87);
lean_dec(x_87);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = l_Lean_Level_ofNat(x_87);
lean_dec(x_87);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
uint8_t x_95; 
lean_dec(x_87);
x_95 = !lean_is_exclusive(x_88);
if (x_95 == 0)
{
return x_88;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_88, 0);
x_97 = lean_ctor_get(x_88, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_88);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_99 = l_Lean_Elab_Level_mkFreshLevelMVar(x_2, x_3);
lean_dec(x_2);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_8);
lean_dec(x_4);
x_100 = lean_unsigned_to_nat(1u);
x_101 = l_Lean_Syntax_getArg(x_1, x_100);
lean_dec(x_1);
x_102 = l_Lean_Syntax_getArgs(x_101);
lean_dec(x_101);
x_103 = l_Lean_instInhabitedSyntax;
x_104 = l_Array_back___rarg(x_103, x_102);
lean_inc(x_2);
x_105 = l_Lean_Elab_Level_elabLevel(x_104, x_2, x_3);
if (lean_obj_tag(x_105) == 0)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
x_109 = lean_array_get_size(x_102);
x_110 = lean_nat_sub(x_109, x_100);
lean_dec(x_109);
x_111 = lean_unsigned_to_nat(0u);
x_112 = l_Array_toSubarray___rarg(x_102, x_111, x_110);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_array_get_size(x_113);
x_117 = lean_nat_dec_le(x_114, x_116);
if (x_117 == 0)
{
uint8_t x_118; 
lean_dec(x_114);
x_118 = lean_nat_dec_lt(x_115, x_116);
if (x_118 == 0)
{
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_113);
lean_dec(x_2);
return x_105;
}
else
{
size_t x_119; size_t x_120; lean_object* x_121; 
lean_free_object(x_105);
x_119 = lean_usize_of_nat(x_116);
lean_dec(x_116);
x_120 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_121 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_113, x_119, x_120, x_107, x_2, x_108);
lean_dec(x_113);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_dec(x_116);
x_122 = lean_nat_dec_lt(x_115, x_114);
if (x_122 == 0)
{
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_2);
return x_105;
}
else
{
size_t x_123; size_t x_124; lean_object* x_125; 
lean_free_object(x_105);
x_123 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_124 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_125 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_113, x_123, x_124, x_107, x_2, x_108);
lean_dec(x_113);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_126 = lean_ctor_get(x_105, 0);
x_127 = lean_ctor_get(x_105, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_105);
x_128 = lean_array_get_size(x_102);
x_129 = lean_nat_sub(x_128, x_100);
lean_dec(x_128);
x_130 = lean_unsigned_to_nat(0u);
x_131 = l_Array_toSubarray___rarg(x_102, x_130, x_129);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 2);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_array_get_size(x_132);
x_136 = lean_nat_dec_le(x_133, x_135);
if (x_136 == 0)
{
uint8_t x_137; 
lean_dec(x_133);
x_137 = lean_nat_dec_lt(x_134, x_135);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_2);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_126);
lean_ctor_set(x_138, 1, x_127);
return x_138;
}
else
{
size_t x_139; size_t x_140; lean_object* x_141; 
x_139 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_140 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_141 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_132, x_139, x_140, x_126, x_2, x_127);
lean_dec(x_132);
return x_141;
}
}
else
{
uint8_t x_142; 
lean_dec(x_135);
x_142 = lean_nat_dec_lt(x_134, x_133);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_2);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_126);
lean_ctor_set(x_143, 1, x_127);
return x_143;
}
else
{
size_t x_144; size_t x_145; lean_object* x_146; 
x_144 = lean_usize_of_nat(x_133);
lean_dec(x_133);
x_145 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_146 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_132, x_144, x_145, x_126, x_2, x_127);
lean_dec(x_132);
return x_146;
}
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_102);
lean_dec(x_2);
x_147 = !lean_is_exclusive(x_105);
if (x_147 == 0)
{
return x_105;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_105, 0);
x_149 = lean_ctor_get(x_105, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_105);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_8);
lean_dec(x_4);
x_151 = lean_unsigned_to_nat(1u);
x_152 = l_Lean_Syntax_getArg(x_1, x_151);
lean_dec(x_1);
x_153 = l_Lean_Syntax_getArgs(x_152);
lean_dec(x_152);
x_154 = l_Lean_instInhabitedSyntax;
x_155 = l_Array_back___rarg(x_154, x_153);
lean_inc(x_2);
x_156 = l_Lean_Elab_Level_elabLevel(x_155, x_2, x_3);
if (lean_obj_tag(x_156) == 0)
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_ctor_get(x_156, 1);
x_160 = lean_array_get_size(x_153);
x_161 = lean_nat_sub(x_160, x_151);
lean_dec(x_160);
x_162 = lean_unsigned_to_nat(0u);
x_163 = l_Array_toSubarray___rarg(x_153, x_162, x_161);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 2);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = lean_array_get_size(x_164);
x_168 = lean_nat_dec_le(x_165, x_167);
if (x_168 == 0)
{
uint8_t x_169; 
lean_dec(x_165);
x_169 = lean_nat_dec_lt(x_166, x_167);
if (x_169 == 0)
{
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_2);
return x_156;
}
else
{
size_t x_170; size_t x_171; lean_object* x_172; 
lean_free_object(x_156);
x_170 = lean_usize_of_nat(x_167);
lean_dec(x_167);
x_171 = lean_usize_of_nat(x_166);
lean_dec(x_166);
x_172 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_164, x_170, x_171, x_158, x_2, x_159);
lean_dec(x_164);
return x_172;
}
}
else
{
uint8_t x_173; 
lean_dec(x_167);
x_173 = lean_nat_dec_lt(x_166, x_165);
if (x_173 == 0)
{
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_2);
return x_156;
}
else
{
size_t x_174; size_t x_175; lean_object* x_176; 
lean_free_object(x_156);
x_174 = lean_usize_of_nat(x_165);
lean_dec(x_165);
x_175 = lean_usize_of_nat(x_166);
lean_dec(x_166);
x_176 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_164, x_174, x_175, x_158, x_2, x_159);
lean_dec(x_164);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_177 = lean_ctor_get(x_156, 0);
x_178 = lean_ctor_get(x_156, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_156);
x_179 = lean_array_get_size(x_153);
x_180 = lean_nat_sub(x_179, x_151);
lean_dec(x_179);
x_181 = lean_unsigned_to_nat(0u);
x_182 = l_Array_toSubarray___rarg(x_153, x_181, x_180);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec(x_182);
x_186 = lean_array_get_size(x_183);
x_187 = lean_nat_dec_le(x_184, x_186);
if (x_187 == 0)
{
uint8_t x_188; 
lean_dec(x_184);
x_188 = lean_nat_dec_lt(x_185, x_186);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_2);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_177);
lean_ctor_set(x_189, 1, x_178);
return x_189;
}
else
{
size_t x_190; size_t x_191; lean_object* x_192; 
x_190 = lean_usize_of_nat(x_186);
lean_dec(x_186);
x_191 = lean_usize_of_nat(x_185);
lean_dec(x_185);
x_192 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_183, x_190, x_191, x_177, x_2, x_178);
lean_dec(x_183);
return x_192;
}
}
else
{
uint8_t x_193; 
lean_dec(x_186);
x_193 = lean_nat_dec_lt(x_185, x_184);
if (x_193 == 0)
{
lean_object* x_194; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_2);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_177);
lean_ctor_set(x_194, 1, x_178);
return x_194;
}
else
{
size_t x_195; size_t x_196; lean_object* x_197; 
x_195 = lean_usize_of_nat(x_184);
lean_dec(x_184);
x_196 = lean_usize_of_nat(x_185);
lean_dec(x_185);
x_197 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_183, x_195, x_196, x_177, x_2, x_178);
lean_dec(x_183);
return x_197;
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_153);
lean_dec(x_2);
x_198 = !lean_is_exclusive(x_156);
if (x_198 == 0)
{
return x_156;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_156, 0);
x_200 = lean_ctor_get(x_156, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_156);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_8);
lean_dec(x_4);
x_202 = lean_unsigned_to_nat(1u);
x_203 = l_Lean_Syntax_getArg(x_1, x_202);
lean_dec(x_1);
x_1 = x_203;
goto _start;
}
}
else
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_2, 0);
x_206 = lean_ctor_get(x_2, 1);
x_207 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_2);
x_208 = l_Lean_replaceRef(x_1, x_206);
lean_dec(x_206);
lean_inc(x_205);
x_209 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_209, 0, x_205);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set_uint8(x_209, sizeof(void*)*2, x_207);
if (x_6 == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = l_Lean_Elab_Level_elabLevel___closed__5;
x_211 = lean_name_eq(x_4, x_210);
if (x_211 == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = l_Lean_Elab_Level_elabLevel___closed__7;
x_213 = lean_name_eq(x_4, x_212);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = l_Lean_Elab_Level_elabLevel___closed__9;
x_215 = lean_name_eq(x_4, x_214);
if (x_215 == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = l_Lean_Elab_Level_elabLevel___closed__11;
x_217 = lean_name_eq(x_4, x_216);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = l_Lean_Elab_Level_elabLevel___closed__13;
x_219 = lean_name_eq(x_4, x_218);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
lean_dec(x_205);
x_220 = l_Lean_Elab_Level_elabLevel___closed__15;
x_221 = lean_name_eq(x_4, x_220);
lean_dec(x_4);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_1);
x_222 = l_Lean_Elab_Level_elabLevel___closed__17;
x_223 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(x_222, x_209, x_3);
lean_dec(x_209);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_unsigned_to_nat(0u);
x_225 = l_Lean_Syntax_getArg(x_1, x_224);
lean_inc(x_209);
x_226 = l_Lean_Elab_Level_elabLevel(x_225, x_209, x_3);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_unsigned_to_nat(2u);
x_230 = l_Lean_Syntax_getArg(x_1, x_229);
lean_dec(x_1);
x_231 = l_Lean_Syntax_isNatLit_x3f(x_230);
lean_dec(x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; 
lean_dec(x_227);
x_232 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_209, x_228);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
lean_dec(x_231);
lean_inc(x_233);
x_234 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_233, x_209, x_228);
lean_dec(x_209);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_236 = x_234;
} else {
 lean_dec_ref(x_234);
 x_236 = lean_box(0);
}
x_237 = l_Lean_Level_addOffsetAux(x_233, x_227);
if (lean_is_scalar(x_236)) {
 x_238 = lean_alloc_ctor(0, 2, 0);
} else {
 x_238 = x_236;
}
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_235);
return x_238;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_233);
lean_dec(x_227);
x_239 = lean_ctor_get(x_234, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_234, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_241 = x_234;
} else {
 lean_dec_ref(x_234);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_209);
lean_dec(x_1);
x_243 = lean_ctor_get(x_226, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_226, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_245 = x_226;
} else {
 lean_dec_ref(x_226);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
lean_dec(x_4);
x_247 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_248 = lean_ctor_get(x_3, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_3, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_3, 2);
lean_inc(x_250);
x_251 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_247, x_250);
if (x_251 == 0)
{
uint8_t x_252; 
if (x_207 == 0)
{
uint8_t x_269; 
lean_dec(x_205);
x_269 = 0;
x_252 = x_269;
goto block_268;
}
else
{
lean_object* x_270; uint8_t x_271; uint8_t x_272; 
x_270 = l_Lean_Elab_Level_elabLevel___closed__22;
x_271 = l_Lean_Option_get___at_Lean_getSanitizeNames___spec__1(x_205, x_270);
lean_dec(x_205);
lean_inc(x_247);
x_272 = l_Lean_Elab_isValidAutoBoundLevelName(x_247, x_271);
x_252 = x_272;
goto block_268;
}
block_268:
{
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
x_253 = l_Lean_MessageData_ofName(x_247);
x_254 = l_Lean_Elab_Level_elabLevel___closed__19;
x_255 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
x_256 = l_Lean_Elab_Level_elabLevel___closed__21;
x_257 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(x_257, x_209, x_3);
lean_dec(x_209);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_261 = x_258;
} else {
 lean_dec_ref(x_258);
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
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_263 = x_3;
} else {
 lean_dec_ref(x_3);
 x_263 = lean_box(0);
}
lean_inc(x_247);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_247);
lean_ctor_set(x_264, 1, x_250);
if (lean_is_scalar(x_263)) {
 x_265 = lean_alloc_ctor(0, 3, 0);
} else {
 x_265 = x_263;
}
lean_ctor_set(x_265, 0, x_248);
lean_ctor_set(x_265, 1, x_249);
lean_ctor_set(x_265, 2, x_264);
x_266 = lean_box(0);
x_267 = l_Lean_Elab_Level_elabLevel___lambda__1(x_247, x_266, x_209, x_265);
lean_dec(x_209);
return x_267;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
lean_dec(x_205);
x_273 = lean_box(0);
x_274 = l_Lean_Elab_Level_elabLevel___lambda__1(x_247, x_273, x_209, x_3);
lean_dec(x_209);
return x_274;
}
}
}
else
{
lean_object* x_275; 
lean_dec(x_205);
lean_dec(x_4);
x_275 = l_Lean_Syntax_isNatLit_x3f(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; 
x_276 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_209, x_3);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_275, 0);
lean_inc(x_277);
lean_dec(x_275);
lean_inc(x_277);
x_278 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_277, x_209, x_3);
lean_dec(x_209);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_280 = x_278;
} else {
 lean_dec_ref(x_278);
 x_280 = lean_box(0);
}
x_281 = l_Lean_Level_ofNat(x_277);
lean_dec(x_277);
if (lean_is_scalar(x_280)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_280;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_279);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_277);
x_283 = lean_ctor_get(x_278, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_278, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 lean_ctor_release(x_278, 1);
 x_285 = x_278;
} else {
 lean_dec_ref(x_278);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
}
}
else
{
lean_object* x_287; 
lean_dec(x_205);
lean_dec(x_4);
lean_dec(x_1);
x_287 = l_Lean_Elab_Level_mkFreshLevelMVar(x_209, x_3);
lean_dec(x_209);
return x_287;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_205);
lean_dec(x_4);
x_288 = lean_unsigned_to_nat(1u);
x_289 = l_Lean_Syntax_getArg(x_1, x_288);
lean_dec(x_1);
x_290 = l_Lean_Syntax_getArgs(x_289);
lean_dec(x_289);
x_291 = l_Lean_instInhabitedSyntax;
x_292 = l_Array_back___rarg(x_291, x_290);
lean_inc(x_209);
x_293 = l_Lean_Elab_Level_elabLevel(x_292, x_209, x_3);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_296 = x_293;
} else {
 lean_dec_ref(x_293);
 x_296 = lean_box(0);
}
x_297 = lean_array_get_size(x_290);
x_298 = lean_nat_sub(x_297, x_288);
lean_dec(x_297);
x_299 = lean_unsigned_to_nat(0u);
x_300 = l_Array_toSubarray___rarg(x_290, x_299, x_298);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 2);
lean_inc(x_302);
x_303 = lean_ctor_get(x_300, 1);
lean_inc(x_303);
lean_dec(x_300);
x_304 = lean_array_get_size(x_301);
x_305 = lean_nat_dec_le(x_302, x_304);
if (x_305 == 0)
{
uint8_t x_306; 
lean_dec(x_302);
x_306 = lean_nat_dec_lt(x_303, x_304);
if (x_306 == 0)
{
lean_object* x_307; 
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_301);
lean_dec(x_209);
if (lean_is_scalar(x_296)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_296;
}
lean_ctor_set(x_307, 0, x_294);
lean_ctor_set(x_307, 1, x_295);
return x_307;
}
else
{
size_t x_308; size_t x_309; lean_object* x_310; 
lean_dec(x_296);
x_308 = lean_usize_of_nat(x_304);
lean_dec(x_304);
x_309 = lean_usize_of_nat(x_303);
lean_dec(x_303);
x_310 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_301, x_308, x_309, x_294, x_209, x_295);
lean_dec(x_301);
return x_310;
}
}
else
{
uint8_t x_311; 
lean_dec(x_304);
x_311 = lean_nat_dec_lt(x_303, x_302);
if (x_311 == 0)
{
lean_object* x_312; 
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_209);
if (lean_is_scalar(x_296)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_296;
}
lean_ctor_set(x_312, 0, x_294);
lean_ctor_set(x_312, 1, x_295);
return x_312;
}
else
{
size_t x_313; size_t x_314; lean_object* x_315; 
lean_dec(x_296);
x_313 = lean_usize_of_nat(x_302);
lean_dec(x_302);
x_314 = lean_usize_of_nat(x_303);
lean_dec(x_303);
x_315 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_301, x_313, x_314, x_294, x_209, x_295);
lean_dec(x_301);
return x_315;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_290);
lean_dec(x_209);
x_316 = lean_ctor_get(x_293, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_293, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_318 = x_293;
} else {
 lean_dec_ref(x_293);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_205);
lean_dec(x_4);
x_320 = lean_unsigned_to_nat(1u);
x_321 = l_Lean_Syntax_getArg(x_1, x_320);
lean_dec(x_1);
x_322 = l_Lean_Syntax_getArgs(x_321);
lean_dec(x_321);
x_323 = l_Lean_instInhabitedSyntax;
x_324 = l_Array_back___rarg(x_323, x_322);
lean_inc(x_209);
x_325 = l_Lean_Elab_Level_elabLevel(x_324, x_209, x_3);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
x_329 = lean_array_get_size(x_322);
x_330 = lean_nat_sub(x_329, x_320);
lean_dec(x_329);
x_331 = lean_unsigned_to_nat(0u);
x_332 = l_Array_toSubarray___rarg(x_322, x_331, x_330);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 2);
lean_inc(x_334);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
lean_dec(x_332);
x_336 = lean_array_get_size(x_333);
x_337 = lean_nat_dec_le(x_334, x_336);
if (x_337 == 0)
{
uint8_t x_338; 
lean_dec(x_334);
x_338 = lean_nat_dec_lt(x_335, x_336);
if (x_338 == 0)
{
lean_object* x_339; 
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_333);
lean_dec(x_209);
if (lean_is_scalar(x_328)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_328;
}
lean_ctor_set(x_339, 0, x_326);
lean_ctor_set(x_339, 1, x_327);
return x_339;
}
else
{
size_t x_340; size_t x_341; lean_object* x_342; 
lean_dec(x_328);
x_340 = lean_usize_of_nat(x_336);
lean_dec(x_336);
x_341 = lean_usize_of_nat(x_335);
lean_dec(x_335);
x_342 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_333, x_340, x_341, x_326, x_209, x_327);
lean_dec(x_333);
return x_342;
}
}
else
{
uint8_t x_343; 
lean_dec(x_336);
x_343 = lean_nat_dec_lt(x_335, x_334);
if (x_343 == 0)
{
lean_object* x_344; 
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_209);
if (lean_is_scalar(x_328)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_328;
}
lean_ctor_set(x_344, 0, x_326);
lean_ctor_set(x_344, 1, x_327);
return x_344;
}
else
{
size_t x_345; size_t x_346; lean_object* x_347; 
lean_dec(x_328);
x_345 = lean_usize_of_nat(x_334);
lean_dec(x_334);
x_346 = lean_usize_of_nat(x_335);
lean_dec(x_335);
x_347 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_333, x_345, x_346, x_326, x_209, x_327);
lean_dec(x_333);
return x_347;
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_322);
lean_dec(x_209);
x_348 = lean_ctor_get(x_325, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_325, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_350 = x_325;
} else {
 lean_dec_ref(x_325);
 x_350 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_351 = x_350;
}
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_349);
return x_351;
}
}
}
else
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_205);
lean_dec(x_4);
x_352 = lean_unsigned_to_nat(1u);
x_353 = l_Lean_Syntax_getArg(x_1, x_352);
lean_dec(x_1);
x_1 = x_353;
x_2 = x_209;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Level_elabLevel___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Level(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_AutoBound(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Level(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1);
l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2 = _init_l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2);
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
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__1 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__1();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__1);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__2 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__2();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__2);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__3 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__3();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__3);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__4 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__4();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__4);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__5 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__5();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__5);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__6 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__6();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__6);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__7 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__7();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__7);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__8 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__8();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__8);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__9 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__9();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440____closed__9);
if (builtin) {res = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_440_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Level_maxUniverseOffset = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Level_maxUniverseOffset);
lean_dec_ref(res);
}l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4);
l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__5 = _init_l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__5);
l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__1 = _init_l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__1();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__1);
l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__2 = _init_l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__2();
lean_mark_persistent(l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__2);
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
l_Lean_Elab_Level_elabLevel___closed__22 = _init_l_Lean_Elab_Level_elabLevel___closed__22();
lean_mark_persistent(l_Lean_Elab_Level_elabLevel___closed__22);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
