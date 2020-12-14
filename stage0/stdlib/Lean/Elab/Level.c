// Lean compiler output
// Module: Lean.Elab.Level
// Imports: Init Lean.Meta.LevelDefEq Lean.Elab.Exception Lean.Elab.Log
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
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3___boxed(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM;
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__10;
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3;
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__7;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_10913____closed__7;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4;
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__9;
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__6;
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___closed__2;
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_level_mk_max_simp(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName___boxed(lean_object*);
lean_object* lean_level_mk_imax_simp(lean_object*, lean_object*);
uint8_t l_Char_isLower(uint32_t);
lean_object* l_Lean_Elab_Level_elabLevel_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__1(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__2(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__2;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName_match__1(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___closed__4;
lean_object* l_Lean_Elab_Level_elabLevel___closed__8;
lean_object* l_Lean_Elab_Level_elabLevel___closed__4;
lean_object* l_Lean_Elab_Level_elabLevel___closed__1;
extern lean_object* l_Lean_identKind;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__34;
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__3;
lean_object* l_ReaderT_read___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__1(lean_object*, lean_object*);
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName(lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2;
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__5;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2;
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1;
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1;
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3;
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM;
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__35;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__5;
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__2___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_2);
x_8 = lean_apply_2(x_3, x_4, x_5);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
x_11 = lean_apply_2(x_3, x_10, x_5);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1;
x_2 = l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__2___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3;
x_2 = l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4;
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
x_1 = l_Lean_Elab_Level_instMonadRefLevelElabM___closed__5;
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
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__2___rarg), 4, 2);
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
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_7 = lean_box_usize(x_6);
x_8 = lean_apply_2(x_2, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_erase_macro_scopes(x_1);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_string_length(x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_string_utf8_get(x_4, x_9);
lean_dec(x_4);
x_11 = l_Char_isLower(x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = 0;
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = 0;
return x_13;
}
}
}
lean_object* l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName(x_1);
x_3 = lean_box(x_2);
return x_3;
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
x_4 = lean_ctor_get(x_2, 0);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
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
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_3 < x_2;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_array_uget(x_9, x_3);
lean_inc(x_5);
x_11 = l_Lean_Elab_Level_elabLevel(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_level_mk_imax_simp(x_4, x_12);
x_15 = 1;
x_16 = x_3 + x_15;
x_3 = x_16;
x_4 = x_14;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_3 < x_2;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_array_uget(x_9, x_3);
lean_inc(x_5);
x_11 = l_Lean_Elab_Level_elabLevel(x_10, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_level_mk_max_simp(x_4, x_12);
x_15 = 1;
x_16 = x_3 + x_15;
x_3 = x_16;
x_4 = x_14;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
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
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__34;
x_2 = l_myMacro____x40_Init_Notation___hyg_10913____closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__34;
x_2 = l_Lean_Level_LevelToFormat_Result_format___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__34;
x_2 = l_Lean_Level_LevelToFormat_Result_format___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("addLit");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__34;
x_2 = l_Lean_Elab_Level_elabLevel___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected universe level syntax kind");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unknown universe level '");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Level_elabLevel___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Level_elabLevel___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Level_elabLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
lean_inc(x_1);
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Lean_Elab_Level_elabLevel___closed__1;
x_6 = lean_name_eq(x_4, x_5);
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_10 = l_Lean_replaceRef(x_1, x_8);
lean_dec(x_8);
lean_ctor_set(x_2, 0, x_10);
if (x_6 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Elab_Level_elabLevel___closed__2;
x_12 = lean_name_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_Level_elabLevel___closed__3;
x_14 = lean_name_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__35;
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
x_21 = l_Lean_Elab_Level_elabLevel___closed__5;
x_22 = lean_name_eq(x_4, x_21);
lean_dec(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = l_Lean_Elab_Level_elabLevel___closed__8;
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
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_unsigned_to_nat(2u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
lean_dec(x_1);
x_33 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_17, x_32);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_free_object(x_27);
lean_dec(x_29);
x_34 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_2, x_30);
lean_dec(x_2);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_2);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Level_addOffsetAux(x_35, x_29);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = lean_unsigned_to_nat(2u);
x_40 = l_Lean_Syntax_getArg(x_1, x_39);
lean_dec(x_1);
x_41 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_17, x_40);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
lean_dec(x_37);
x_42 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_2, x_38);
lean_dec(x_2);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Level_addOffsetAux(x_43, x_37);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
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
x_56 = l_Lean_Elab_Level_elabLevel___closed__10;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_KernelException_toMessageData___closed__3;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3(x_59, x_2, x_3);
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
x_65 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName(x_50);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_66 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_66, 0, x_50);
x_67 = l_Lean_Elab_Level_elabLevel___closed__10;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Lean_KernelException_toMessageData___closed__3;
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3(x_70, x_2, x_3);
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
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_2);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Level_ofNat(x_91);
lean_dec(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_3);
return x_93;
}
}
}
else
{
lean_object* x_94; 
lean_dec(x_4);
lean_dec(x_1);
x_94 = l_Lean_Elab_Level_mkFreshLevelMVar(x_2, x_3);
lean_dec(x_2);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_4);
x_95 = lean_unsigned_to_nat(1u);
x_96 = l_Lean_Syntax_getArg(x_1, x_95);
lean_dec(x_1);
x_97 = l_Lean_Syntax_getArgs(x_96);
lean_dec(x_96);
x_98 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_97);
lean_inc(x_2);
x_99 = l_Lean_Elab_Level_elabLevel(x_98, x_2, x_3);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; lean_object* x_108; size_t x_109; lean_object* x_110; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_array_get_size(x_97);
x_103 = lean_nat_sub(x_102, x_95);
lean_dec(x_102);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Array_toSubarray___rarg(x_97, x_104, x_103);
x_106 = lean_ctor_get(x_105, 2);
lean_inc(x_106);
x_107 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
x_109 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_110 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4(x_105, x_107, x_109, x_100, x_2, x_101);
lean_dec(x_105);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
return x_110;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_110);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_110);
if (x_115 == 0)
{
return x_110;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_110, 0);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_110);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_97);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_99);
if (x_119 == 0)
{
return x_99;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_99, 0);
x_121 = lean_ctor_get(x_99, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_99);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_4);
x_123 = lean_unsigned_to_nat(1u);
x_124 = l_Lean_Syntax_getArg(x_1, x_123);
lean_dec(x_1);
x_125 = l_Lean_Syntax_getArgs(x_124);
lean_dec(x_124);
x_126 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_125);
lean_inc(x_2);
x_127 = l_Lean_Elab_Level_elabLevel(x_126, x_2, x_3);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; size_t x_135; lean_object* x_136; size_t x_137; lean_object* x_138; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_array_get_size(x_125);
x_131 = lean_nat_sub(x_130, x_123);
lean_dec(x_130);
x_132 = lean_unsigned_to_nat(0u);
x_133 = l_Array_toSubarray___rarg(x_125, x_132, x_131);
x_134 = lean_ctor_get(x_133, 2);
lean_inc(x_134);
x_135 = lean_usize_of_nat(x_134);
lean_dec(x_134);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
x_137 = lean_usize_of_nat(x_136);
lean_dec(x_136);
x_138 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__5(x_133, x_135, x_137, x_128, x_2, x_129);
lean_dec(x_133);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
return x_138;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_138);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_138);
if (x_143 == 0)
{
return x_138;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_138, 0);
x_145 = lean_ctor_get(x_138, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_138);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_125);
lean_dec(x_2);
x_147 = !lean_is_exclusive(x_127);
if (x_147 == 0)
{
return x_127;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_127, 0);
x_149 = lean_ctor_get(x_127, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_127);
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
lean_object* x_151; lean_object* x_152; 
lean_dec(x_4);
x_151 = lean_unsigned_to_nat(1u);
x_152 = l_Lean_Syntax_getArg(x_1, x_151);
lean_dec(x_1);
x_1 = x_152;
goto _start;
}
}
else
{
lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_2, 0);
x_155 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_154);
lean_dec(x_2);
x_156 = l_Lean_replaceRef(x_1, x_154);
lean_dec(x_154);
x_157 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_155);
if (x_6 == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = l_Lean_Elab_Level_elabLevel___closed__2;
x_159 = lean_name_eq(x_4, x_158);
if (x_159 == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = l_Lean_Elab_Level_elabLevel___closed__3;
x_161 = lean_name_eq(x_4, x_160);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__35;
x_163 = lean_name_eq(x_4, x_162);
if (x_163 == 0)
{
lean_object* x_164; uint8_t x_165; 
x_164 = l_Lean_numLitKind;
x_165 = lean_name_eq(x_4, x_164);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; 
x_166 = l_Lean_identKind;
x_167 = lean_name_eq(x_4, x_166);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = l_Lean_Elab_Level_elabLevel___closed__5;
x_169 = lean_name_eq(x_4, x_168);
lean_dec(x_4);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_1);
x_170 = l_Lean_Elab_Level_elabLevel___closed__8;
x_171 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(x_170, x_157, x_3);
lean_dec(x_157);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_unsigned_to_nat(0u);
x_173 = l_Lean_Syntax_getArg(x_1, x_172);
lean_inc(x_157);
x_174 = l_Lean_Elab_Level_elabLevel(x_173, x_157, x_3);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
x_178 = lean_unsigned_to_nat(2u);
x_179 = l_Lean_Syntax_getArg(x_1, x_178);
lean_dec(x_1);
x_180 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_164, x_179);
lean_dec(x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
lean_dec(x_177);
lean_dec(x_175);
x_181 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_157, x_176);
lean_dec(x_157);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_157);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_Level_addOffsetAux(x_182, x_175);
if (lean_is_scalar(x_177)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_177;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_176);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_157);
lean_dec(x_1);
x_185 = lean_ctor_get(x_174, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_187 = x_174;
} else {
 lean_dec_ref(x_174);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_dec(x_4);
x_189 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_190 = lean_ctor_get(x_3, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_3, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_3, 2);
lean_inc(x_192);
x_193 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_189, x_192);
if (x_193 == 0)
{
if (x_155 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
x_194 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_194, 0, x_189);
x_195 = l_Lean_Elab_Level_elabLevel___closed__10;
x_196 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = l_Lean_KernelException_toMessageData___closed__3;
x_198 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3(x_198, x_157, x_3);
lean_dec(x_157);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_202 = x_199;
} else {
 lean_dec_ref(x_199);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
else
{
uint8_t x_204; 
lean_inc(x_189);
x_204 = l___private_Lean_Elab_Level_0__Lean_Elab_Level_isValidAutoBoundLevelName(x_189);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
x_205 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_205, 0, x_189);
x_206 = l_Lean_Elab_Level_elabLevel___closed__10;
x_207 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = l_Lean_KernelException_toMessageData___closed__3;
x_209 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3(x_209, x_157, x_3);
lean_dec(x_157);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_215 = x_3;
} else {
 lean_dec_ref(x_3);
 x_215 = lean_box(0);
}
lean_inc(x_189);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_189);
lean_ctor_set(x_216, 1, x_192);
if (lean_is_scalar(x_215)) {
 x_217 = lean_alloc_ctor(0, 3, 0);
} else {
 x_217 = x_215;
}
lean_ctor_set(x_217, 0, x_190);
lean_ctor_set(x_217, 1, x_191);
lean_ctor_set(x_217, 2, x_216);
x_218 = lean_box(0);
x_219 = l_Lean_Elab_Level_elabLevel___lambda__1(x_189, x_218, x_157, x_217);
lean_dec(x_157);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
x_220 = lean_box(0);
x_221 = l_Lean_Elab_Level_elabLevel___lambda__1(x_189, x_220, x_157, x_3);
lean_dec(x_157);
return x_221;
}
}
}
else
{
lean_object* x_222; 
lean_dec(x_4);
x_222 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_164, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_157, x_3);
lean_dec(x_157);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_157);
x_224 = lean_ctor_get(x_222, 0);
lean_inc(x_224);
lean_dec(x_222);
x_225 = l_Lean_Level_ofNat(x_224);
lean_dec(x_224);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_3);
return x_226;
}
}
}
else
{
lean_object* x_227; 
lean_dec(x_4);
lean_dec(x_1);
x_227 = l_Lean_Elab_Level_mkFreshLevelMVar(x_157, x_3);
lean_dec(x_157);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_4);
x_228 = lean_unsigned_to_nat(1u);
x_229 = l_Lean_Syntax_getArg(x_1, x_228);
lean_dec(x_1);
x_230 = l_Lean_Syntax_getArgs(x_229);
lean_dec(x_229);
x_231 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_230);
lean_inc(x_157);
x_232 = l_Lean_Elab_Level_elabLevel(x_231, x_157, x_3);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; size_t x_240; lean_object* x_241; size_t x_242; lean_object* x_243; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_array_get_size(x_230);
x_236 = lean_nat_sub(x_235, x_228);
lean_dec(x_235);
x_237 = lean_unsigned_to_nat(0u);
x_238 = l_Array_toSubarray___rarg(x_230, x_237, x_236);
x_239 = lean_ctor_get(x_238, 2);
lean_inc(x_239);
x_240 = lean_usize_of_nat(x_239);
lean_dec(x_239);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
x_242 = lean_usize_of_nat(x_241);
lean_dec(x_241);
x_243 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4(x_238, x_240, x_242, x_233, x_157, x_234);
lean_dec(x_238);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_246 = x_243;
} else {
 lean_dec_ref(x_243);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get(x_243, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_243, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_250 = x_243;
} else {
 lean_dec_ref(x_243);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_230);
lean_dec(x_157);
x_252 = lean_ctor_get(x_232, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_232, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_254 = x_232;
} else {
 lean_dec_ref(x_232);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_4);
x_256 = lean_unsigned_to_nat(1u);
x_257 = l_Lean_Syntax_getArg(x_1, x_256);
lean_dec(x_1);
x_258 = l_Lean_Syntax_getArgs(x_257);
lean_dec(x_257);
x_259 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_258);
lean_inc(x_157);
x_260 = l_Lean_Elab_Level_elabLevel(x_259, x_157, x_3);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; size_t x_268; lean_object* x_269; size_t x_270; lean_object* x_271; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_array_get_size(x_258);
x_264 = lean_nat_sub(x_263, x_256);
lean_dec(x_263);
x_265 = lean_unsigned_to_nat(0u);
x_266 = l_Array_toSubarray___rarg(x_258, x_265, x_264);
x_267 = lean_ctor_get(x_266, 2);
lean_inc(x_267);
x_268 = lean_usize_of_nat(x_267);
lean_dec(x_267);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
x_270 = lean_usize_of_nat(x_269);
lean_dec(x_269);
x_271 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__5(x_266, x_268, x_270, x_261, x_157, x_262);
lean_dec(x_266);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_274 = x_271;
} else {
 lean_dec_ref(x_271);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_271, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_271, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_278 = x_271;
} else {
 lean_dec_ref(x_271);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_258);
lean_dec(x_157);
x_280 = lean_ctor_get(x_260, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_260, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_282 = x_260;
} else {
 lean_dec_ref(x_260);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_4);
x_284 = lean_unsigned_to_nat(1u);
x_285 = l_Lean_Syntax_getArg(x_1, x_284);
lean_dec(x_1);
x_1 = x_285;
x_2 = x_157;
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
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__4(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_Level_elabLevel___spec__5(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
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
l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1 = _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1();
lean_mark_persistent(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1);
l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2 = _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2();
lean_mark_persistent(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2);
l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3 = _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3();
lean_mark_persistent(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3);
l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4 = _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4();
lean_mark_persistent(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4);
l_Lean_Elab_Level_instMonadRefLevelElabM___closed__5 = _init_l_Lean_Elab_Level_instMonadRefLevelElabM___closed__5();
lean_mark_persistent(l_Lean_Elab_Level_instMonadRefLevelElabM___closed__5);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
