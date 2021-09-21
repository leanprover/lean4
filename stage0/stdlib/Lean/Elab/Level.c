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
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__20;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__7;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__2;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__16;
static lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4;
size_t l_USize_sub(size_t, size_t);
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__9;
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__22;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__1;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__6;
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__2;
lean_object* l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_218____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_maxUniverseOffset;
lean_object* lean_level_mk_max_simp(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__1;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2___boxed(lean_object*);
lean_object* lean_level_mk_imax_simp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203_(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__12;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_maxUniverseOffset___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__1;
lean_object* l_Lean_mkLevelMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__8;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__4;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__17;
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2___rarg(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__1;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_4____spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadOptionsLevelElabM;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l_Lean_Elab_Level_elabLevel___closed__14;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__3;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__15;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__18;
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__5;
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2;
static lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__5;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1;
static lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__4;
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadOptionsLevelElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
static lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4;
static lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__13;
static lean_object* l_Lean_Elab_Level_elabLevel___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_3 = l_Lean_mkFreshMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshMVarId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(x_1, x_2);
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
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maxUniverseOffset");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum universe level offset");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__3;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__2;
x_3 = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__5;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Level_maxUniverseOffset___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Elab_Level_maxUniverseOffset;
x_6 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_218____spec__1(x_4, x_5);
x_7 = lean_nat_dec_le(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Nat_repr(x_6);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
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
x_1 = lean_mk_string("ill-formed syntax");
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
x_5 = l_Lean_Elab_Level_maxUniverseOffset;
x_6 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_218____spec__1(x_4, x_5);
x_7 = lean_nat_dec_le(x_1, x_6);
lean_dec(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Nat_repr(x_6);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___rarg___lambda__1___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
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
x_7 = x_2 == x_3;
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 1;
x_9 = x_2 - x_8;
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
x_14 = lean_level_mk_imax_simp(x_12, x_4);
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
x_7 = x_2 == x_3;
if (x_7 == 0)
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 1;
x_9 = x_2 - x_8;
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
x_14 = lean_level_mk_max_simp(x_12, x_4);
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
x_5 = l_Lean_mkLevelParam(x_1);
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
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Level_elabLevel___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__2;
x_2 = l_Lean_Elab_Level_elabLevel___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Level");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__4;
x_2 = l_Lean_Elab_Level_elabLevel___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__6;
x_2 = l_Lean_Elab_Level_elabLevel___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("max");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__6;
x_2 = l_Lean_Elab_Level_elabLevel___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("imax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__6;
x_2 = l_Lean_Elab_Level_elabLevel___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hole");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__6;
x_2 = l_Lean_Elab_Level_elabLevel___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__6;
x_2 = l_Lean_Elab_Level_elabLevel___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected universe level syntax kind");
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
x_1 = lean_mk_string("unknown universe level '");
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
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Level_elabLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
lean_inc(x_1);
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Lean_Elab_Level_elabLevel___closed__8;
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
x_11 = l_Lean_Elab_Level_elabLevel___closed__10;
x_12 = lean_name_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Level_elabLevel___closed__12;
x_14 = lean_name_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Elab_Level_elabLevel___closed__14;
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
x_21 = l_Lean_Elab_Level_elabLevel___closed__16;
x_22 = lean_name_eq(x_4, x_21);
lean_dec(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = l_Lean_Elab_Level_elabLevel___closed__18;
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
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_34);
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
x_56 = l_Lean_Elab_Level_elabLevel___closed__20;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Elab_Level_elabLevel___closed__22;
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
x_67 = l_Lean_Elab_Level_elabLevel___closed__20;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_Elab_Level_elabLevel___closed__22;
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
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_91);
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
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
x_112 = lean_array_get_size(x_106);
x_113 = lean_nat_sub(x_112, x_104);
lean_dec(x_112);
x_114 = lean_unsigned_to_nat(0u);
x_115 = l_Array_toSubarray___rarg(x_106, x_114, x_113);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_array_get_size(x_116);
x_120 = lean_nat_dec_le(x_117, x_119);
if (x_120 == 0)
{
uint8_t x_121; 
lean_dec(x_117);
x_121 = lean_nat_dec_lt(x_118, x_119);
if (x_121 == 0)
{
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_116);
lean_dec(x_2);
return x_108;
}
else
{
size_t x_122; size_t x_123; lean_object* x_124; 
lean_free_object(x_108);
x_122 = lean_usize_of_nat(x_119);
lean_dec(x_119);
x_123 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_124 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_116, x_122, x_123, x_110, x_2, x_111);
lean_dec(x_116);
return x_124;
}
}
else
{
uint8_t x_125; 
lean_dec(x_119);
x_125 = lean_nat_dec_lt(x_118, x_117);
if (x_125 == 0)
{
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_116);
lean_dec(x_2);
return x_108;
}
else
{
size_t x_126; size_t x_127; lean_object* x_128; 
lean_free_object(x_108);
x_126 = lean_usize_of_nat(x_117);
lean_dec(x_117);
x_127 = lean_usize_of_nat(x_118);
lean_dec(x_118);
x_128 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_116, x_126, x_127, x_110, x_2, x_111);
lean_dec(x_116);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_129 = lean_ctor_get(x_108, 0);
x_130 = lean_ctor_get(x_108, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_108);
x_131 = lean_array_get_size(x_106);
x_132 = lean_nat_sub(x_131, x_104);
lean_dec(x_131);
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Array_toSubarray___rarg(x_106, x_133, x_132);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_array_get_size(x_135);
x_139 = lean_nat_dec_le(x_136, x_138);
if (x_139 == 0)
{
uint8_t x_140; 
lean_dec(x_136);
x_140 = lean_nat_dec_lt(x_137, x_138);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_2);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_129);
lean_ctor_set(x_141, 1, x_130);
return x_141;
}
else
{
size_t x_142; size_t x_143; lean_object* x_144; 
x_142 = lean_usize_of_nat(x_138);
lean_dec(x_138);
x_143 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_144 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_135, x_142, x_143, x_129, x_2, x_130);
lean_dec(x_135);
return x_144;
}
}
else
{
uint8_t x_145; 
lean_dec(x_138);
x_145 = lean_nat_dec_lt(x_137, x_136);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_2);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_129);
lean_ctor_set(x_146, 1, x_130);
return x_146;
}
else
{
size_t x_147; size_t x_148; lean_object* x_149; 
x_147 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_148 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_149 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_135, x_147, x_148, x_129, x_2, x_130);
lean_dec(x_135);
return x_149;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_106);
lean_dec(x_2);
x_150 = !lean_is_exclusive(x_108);
if (x_150 == 0)
{
return x_108;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_108, 0);
x_152 = lean_ctor_get(x_108, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_108);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_4);
x_154 = lean_unsigned_to_nat(1u);
x_155 = l_Lean_Syntax_getArg(x_1, x_154);
lean_dec(x_1);
x_156 = l_Lean_Syntax_getArgs(x_155);
lean_dec(x_155);
x_157 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_156);
lean_inc(x_2);
x_158 = l_Lean_Elab_Level_elabLevel(x_157, x_2, x_3);
if (lean_obj_tag(x_158) == 0)
{
uint8_t x_159; 
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ctor_get(x_158, 1);
x_162 = lean_array_get_size(x_156);
x_163 = lean_nat_sub(x_162, x_154);
lean_dec(x_162);
x_164 = lean_unsigned_to_nat(0u);
x_165 = l_Array_toSubarray___rarg(x_156, x_164, x_163);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 2);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_169 = lean_array_get_size(x_166);
x_170 = lean_nat_dec_le(x_167, x_169);
if (x_170 == 0)
{
uint8_t x_171; 
lean_dec(x_167);
x_171 = lean_nat_dec_lt(x_168, x_169);
if (x_171 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_166);
lean_dec(x_2);
return x_158;
}
else
{
size_t x_172; size_t x_173; lean_object* x_174; 
lean_free_object(x_158);
x_172 = lean_usize_of_nat(x_169);
lean_dec(x_169);
x_173 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_174 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_166, x_172, x_173, x_160, x_2, x_161);
lean_dec(x_166);
return x_174;
}
}
else
{
uint8_t x_175; 
lean_dec(x_169);
x_175 = lean_nat_dec_lt(x_168, x_167);
if (x_175 == 0)
{
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_2);
return x_158;
}
else
{
size_t x_176; size_t x_177; lean_object* x_178; 
lean_free_object(x_158);
x_176 = lean_usize_of_nat(x_167);
lean_dec(x_167);
x_177 = lean_usize_of_nat(x_168);
lean_dec(x_168);
x_178 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_166, x_176, x_177, x_160, x_2, x_161);
lean_dec(x_166);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_179 = lean_ctor_get(x_158, 0);
x_180 = lean_ctor_get(x_158, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_158);
x_181 = lean_array_get_size(x_156);
x_182 = lean_nat_sub(x_181, x_154);
lean_dec(x_181);
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Array_toSubarray___rarg(x_156, x_183, x_182);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
lean_dec(x_184);
x_188 = lean_array_get_size(x_185);
x_189 = lean_nat_dec_le(x_186, x_188);
if (x_189 == 0)
{
uint8_t x_190; 
lean_dec(x_186);
x_190 = lean_nat_dec_lt(x_187, x_188);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_2);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_179);
lean_ctor_set(x_191, 1, x_180);
return x_191;
}
else
{
size_t x_192; size_t x_193; lean_object* x_194; 
x_192 = lean_usize_of_nat(x_188);
lean_dec(x_188);
x_193 = lean_usize_of_nat(x_187);
lean_dec(x_187);
x_194 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_185, x_192, x_193, x_179, x_2, x_180);
lean_dec(x_185);
return x_194;
}
}
else
{
uint8_t x_195; 
lean_dec(x_188);
x_195 = lean_nat_dec_lt(x_187, x_186);
if (x_195 == 0)
{
lean_object* x_196; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_2);
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_179);
lean_ctor_set(x_196, 1, x_180);
return x_196;
}
else
{
size_t x_197; size_t x_198; lean_object* x_199; 
x_197 = lean_usize_of_nat(x_186);
lean_dec(x_186);
x_198 = lean_usize_of_nat(x_187);
lean_dec(x_187);
x_199 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_185, x_197, x_198, x_179, x_2, x_180);
lean_dec(x_185);
return x_199;
}
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_156);
lean_dec(x_2);
x_200 = !lean_is_exclusive(x_158);
if (x_200 == 0)
{
return x_158;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_158, 0);
x_202 = lean_ctor_get(x_158, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_158);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_4);
x_204 = lean_unsigned_to_nat(1u);
x_205 = l_Lean_Syntax_getArg(x_1, x_204);
lean_dec(x_1);
x_1 = x_205;
goto _start;
}
}
else
{
lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; 
x_207 = lean_ctor_get(x_2, 0);
x_208 = lean_ctor_get(x_2, 1);
x_209 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_2);
x_210 = l_Lean_replaceRef(x_1, x_208);
lean_dec(x_208);
x_211 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_211, 0, x_207);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set_uint8(x_211, sizeof(void*)*2, x_209);
if (x_6 == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = l_Lean_Elab_Level_elabLevel___closed__10;
x_213 = lean_name_eq(x_4, x_212);
if (x_213 == 0)
{
lean_object* x_214; uint8_t x_215; 
x_214 = l_Lean_Elab_Level_elabLevel___closed__12;
x_215 = lean_name_eq(x_4, x_214);
if (x_215 == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = l_Lean_Elab_Level_elabLevel___closed__14;
x_217 = lean_name_eq(x_4, x_216);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = l_Lean_numLitKind;
x_219 = lean_name_eq(x_4, x_218);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = l_Lean_identKind;
x_221 = lean_name_eq(x_4, x_220);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = l_Lean_Elab_Level_elabLevel___closed__16;
x_223 = lean_name_eq(x_4, x_222);
lean_dec(x_4);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_1);
x_224 = l_Lean_Elab_Level_elabLevel___closed__18;
x_225 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(x_224, x_211, x_3);
lean_dec(x_211);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_unsigned_to_nat(0u);
x_227 = l_Lean_Syntax_getArg(x_1, x_226);
lean_inc(x_211);
x_228 = l_Lean_Elab_Level_elabLevel(x_227, x_211, x_3);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_unsigned_to_nat(2u);
x_232 = l_Lean_Syntax_getArg(x_1, x_231);
lean_dec(x_1);
x_233 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_218, x_232);
lean_dec(x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; 
lean_dec(x_229);
x_234 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_211, x_230);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
lean_dec(x_233);
lean_inc(x_235);
x_236 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_235, x_211, x_230);
lean_dec(x_211);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_238 = x_236;
} else {
 lean_dec_ref(x_236);
 x_238 = lean_box(0);
}
x_239 = l_Lean_Level_addOffsetAux(x_235, x_229);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_235);
lean_dec(x_229);
x_241 = lean_ctor_get(x_236, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_236, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 lean_ctor_release(x_236, 1);
 x_243 = x_236;
} else {
 lean_dec_ref(x_236);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_211);
lean_dec(x_1);
x_245 = lean_ctor_get(x_228, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_228, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_247 = x_228;
} else {
 lean_dec_ref(x_228);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
lean_dec(x_4);
x_249 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_250 = lean_ctor_get(x_3, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_3, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_3, 2);
lean_inc(x_252);
x_253 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_249, x_252);
if (x_253 == 0)
{
if (x_209 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
x_254 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_254, 0, x_249);
x_255 = l_Lean_Elab_Level_elabLevel___closed__20;
x_256 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
x_257 = l_Lean_Elab_Level_elabLevel___closed__22;
x_258 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(x_258, x_211, x_3);
lean_dec(x_211);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_262 = x_259;
} else {
 lean_dec_ref(x_259);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
else
{
uint8_t x_264; 
lean_inc(x_249);
x_264 = l_Lean_Elab_isValidAutoBoundLevelName(x_249);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
x_265 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_265, 0, x_249);
x_266 = l_Lean_Elab_Level_elabLevel___closed__20;
x_267 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_265);
x_268 = l_Lean_Elab_Level_elabLevel___closed__22;
x_269 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__5(x_269, x_211, x_3);
lean_dec(x_211);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_273 = x_270;
} else {
 lean_dec_ref(x_270);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_275 = x_3;
} else {
 lean_dec_ref(x_3);
 x_275 = lean_box(0);
}
lean_inc(x_249);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_249);
lean_ctor_set(x_276, 1, x_252);
if (lean_is_scalar(x_275)) {
 x_277 = lean_alloc_ctor(0, 3, 0);
} else {
 x_277 = x_275;
}
lean_ctor_set(x_277, 0, x_250);
lean_ctor_set(x_277, 1, x_251);
lean_ctor_set(x_277, 2, x_276);
x_278 = lean_box(0);
x_279 = l_Lean_Elab_Level_elabLevel___lambda__1(x_249, x_278, x_211, x_277);
lean_dec(x_211);
return x_279;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; 
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_250);
x_280 = lean_box(0);
x_281 = l_Lean_Elab_Level_elabLevel___lambda__1(x_249, x_280, x_211, x_3);
lean_dec(x_211);
return x_281;
}
}
}
else
{
lean_object* x_282; 
lean_dec(x_4);
x_282 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_218, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; 
x_283 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_211, x_3);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
lean_dec(x_282);
lean_inc(x_284);
x_285 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_checkUniverseOffset___at_Lean_Elab_Level_elabLevel___spec__3(x_284, x_211, x_3);
lean_dec(x_211);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_287 = x_285;
} else {
 lean_dec_ref(x_285);
 x_287 = lean_box(0);
}
x_288 = l_Lean_Level_ofNat(x_284);
lean_dec(x_284);
if (lean_is_scalar(x_287)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_287;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_286);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_284);
x_290 = lean_ctor_get(x_285, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_285, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_292 = x_285;
} else {
 lean_dec_ref(x_285);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
}
}
else
{
lean_object* x_294; 
lean_dec(x_4);
lean_dec(x_1);
x_294 = l_Lean_Elab_Level_mkFreshLevelMVar(x_211, x_3);
lean_dec(x_211);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_4);
x_295 = lean_unsigned_to_nat(1u);
x_296 = l_Lean_Syntax_getArg(x_1, x_295);
lean_dec(x_1);
x_297 = l_Lean_Syntax_getArgs(x_296);
lean_dec(x_296);
x_298 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_297);
lean_inc(x_211);
x_299 = l_Lean_Elab_Level_elabLevel(x_298, x_211, x_3);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_302 = x_299;
} else {
 lean_dec_ref(x_299);
 x_302 = lean_box(0);
}
x_303 = lean_array_get_size(x_297);
x_304 = lean_nat_sub(x_303, x_295);
lean_dec(x_303);
x_305 = lean_unsigned_to_nat(0u);
x_306 = l_Array_toSubarray___rarg(x_297, x_305, x_304);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 2);
lean_inc(x_308);
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_dec(x_306);
x_310 = lean_array_get_size(x_307);
x_311 = lean_nat_dec_le(x_308, x_310);
if (x_311 == 0)
{
uint8_t x_312; 
lean_dec(x_308);
x_312 = lean_nat_dec_lt(x_309, x_310);
if (x_312 == 0)
{
lean_object* x_313; 
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_307);
lean_dec(x_211);
if (lean_is_scalar(x_302)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_302;
}
lean_ctor_set(x_313, 0, x_300);
lean_ctor_set(x_313, 1, x_301);
return x_313;
}
else
{
size_t x_314; size_t x_315; lean_object* x_316; 
lean_dec(x_302);
x_314 = lean_usize_of_nat(x_310);
lean_dec(x_310);
x_315 = lean_usize_of_nat(x_309);
lean_dec(x_309);
x_316 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_307, x_314, x_315, x_300, x_211, x_301);
lean_dec(x_307);
return x_316;
}
}
else
{
uint8_t x_317; 
lean_dec(x_310);
x_317 = lean_nat_dec_lt(x_309, x_308);
if (x_317 == 0)
{
lean_object* x_318; 
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_307);
lean_dec(x_211);
if (lean_is_scalar(x_302)) {
 x_318 = lean_alloc_ctor(0, 2, 0);
} else {
 x_318 = x_302;
}
lean_ctor_set(x_318, 0, x_300);
lean_ctor_set(x_318, 1, x_301);
return x_318;
}
else
{
size_t x_319; size_t x_320; lean_object* x_321; 
lean_dec(x_302);
x_319 = lean_usize_of_nat(x_308);
lean_dec(x_308);
x_320 = lean_usize_of_nat(x_309);
lean_dec(x_309);
x_321 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__6(x_307, x_319, x_320, x_300, x_211, x_301);
lean_dec(x_307);
return x_321;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_297);
lean_dec(x_211);
x_322 = lean_ctor_get(x_299, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_299, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_324 = x_299;
} else {
 lean_dec_ref(x_299);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 2, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_323);
return x_325;
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_4);
x_326 = lean_unsigned_to_nat(1u);
x_327 = l_Lean_Syntax_getArg(x_1, x_326);
lean_dec(x_1);
x_328 = l_Lean_Syntax_getArgs(x_327);
lean_dec(x_327);
x_329 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_328);
lean_inc(x_211);
x_330 = l_Lean_Elab_Level_elabLevel(x_329, x_211, x_3);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_333 = x_330;
} else {
 lean_dec_ref(x_330);
 x_333 = lean_box(0);
}
x_334 = lean_array_get_size(x_328);
x_335 = lean_nat_sub(x_334, x_326);
lean_dec(x_334);
x_336 = lean_unsigned_to_nat(0u);
x_337 = l_Array_toSubarray___rarg(x_328, x_336, x_335);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 2);
lean_inc(x_339);
x_340 = lean_ctor_get(x_337, 1);
lean_inc(x_340);
lean_dec(x_337);
x_341 = lean_array_get_size(x_338);
x_342 = lean_nat_dec_le(x_339, x_341);
if (x_342 == 0)
{
uint8_t x_343; 
lean_dec(x_339);
x_343 = lean_nat_dec_lt(x_340, x_341);
if (x_343 == 0)
{
lean_object* x_344; 
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_338);
lean_dec(x_211);
if (lean_is_scalar(x_333)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_333;
}
lean_ctor_set(x_344, 0, x_331);
lean_ctor_set(x_344, 1, x_332);
return x_344;
}
else
{
size_t x_345; size_t x_346; lean_object* x_347; 
lean_dec(x_333);
x_345 = lean_usize_of_nat(x_341);
lean_dec(x_341);
x_346 = lean_usize_of_nat(x_340);
lean_dec(x_340);
x_347 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_338, x_345, x_346, x_331, x_211, x_332);
lean_dec(x_338);
return x_347;
}
}
else
{
uint8_t x_348; 
lean_dec(x_341);
x_348 = lean_nat_dec_lt(x_340, x_339);
if (x_348 == 0)
{
lean_object* x_349; 
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_211);
if (lean_is_scalar(x_333)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_333;
}
lean_ctor_set(x_349, 0, x_331);
lean_ctor_set(x_349, 1, x_332);
return x_349;
}
else
{
size_t x_350; size_t x_351; lean_object* x_352; 
lean_dec(x_333);
x_350 = lean_usize_of_nat(x_339);
lean_dec(x_339);
x_351 = lean_usize_of_nat(x_340);
lean_dec(x_340);
x_352 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__7(x_338, x_350, x_351, x_331, x_211, x_332);
lean_dec(x_338);
return x_352;
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_328);
lean_dec(x_211);
x_353 = lean_ctor_get(x_330, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_330, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_355 = x_330;
} else {
 lean_dec_ref(x_330);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 2, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_354);
return x_356;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; 
lean_dec(x_4);
x_357 = lean_unsigned_to_nat(1u);
x_358 = l_Lean_Syntax_getArg(x_1, x_357);
lean_dec(x_1);
x_1 = x_358;
x_2 = x_211;
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_LevelDefEq(lean_object*);
lean_object* initialize_Lean_Elab_Exception(lean_object*);
lean_object* initialize_Lean_Elab_Log(lean_object*);
lean_object* initialize_Lean_Elab_AutoBound(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Level(lean_object* w) {
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
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__1 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__1();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__1);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__2 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__2();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__2);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__3 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__3();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__3);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__4 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__4();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__4);
l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__5 = _init_l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__5();
lean_mark_persistent(l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203____closed__5);
l_Lean_Elab_Level_maxUniverseOffset___closed__1 = _init_l_Lean_Elab_Level_maxUniverseOffset___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_maxUniverseOffset___closed__1);
res = l_Lean_Elab_Level_initFn____x40_Lean_Elab_Level___hyg_203_(lean_io_mk_world());
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
