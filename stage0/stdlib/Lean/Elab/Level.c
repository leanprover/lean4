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
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwIllFormedSyntax___rarg___closed__3;
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__3;
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MetavarContext_addLevelMVarDecl(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__4;
size_t l_USize_sub(size_t, size_t);
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1128____closed__31;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_mkFreshLevelMVar(lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_level_mk_max_simp(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_level_mk_imax_simp(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__1(lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__2(lean_object*);
extern lean_object* l_Lean_Level_PP_Result_quote___lambda__4___closed__1;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Level_addOffsetAux(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__2;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_mkLevelMVar(lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__4;
lean_object* l_Lean_Elab_Level_elabLevel___closed__1;
extern lean_object* l_Lean_identKind;
uint8_t l_List_elem___at_Lean_NameHashSet_insert___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Elab_isValidAutoBoundLevelName(lean_object*);
lean_object* l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___boxed(lean_object*);
extern lean_object* l_Lean_Level_PP_Result_quote___lambda__6___closed__1;
lean_object* l_Lean_Elab_Level_elabLevel___closed__3;
lean_object* l_ReaderT_read___at_Lean_Elab_Level_instMonadRefLevelElabM___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Level_PP_Result_quote___lambda__3___closed__2;
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__2;
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__5;
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__2;
lean_object* l_Lean_mkFreshId___at_Lean_Elab_Level_mkFreshLevelMVar___spec__1___rarg(lean_object*);
lean_object* l_Lean_Elab_Level_instAddMessageContextLevelElabM___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__1;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__1;
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_PP_Result_quote___lambda__5___closed__1;
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___closed__4;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__3;
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Level_instMonadNameGeneratorLevelElabM;
lean_object* l_Lean_Elab_Level_instMonadRefLevelElabM___closed__5;
lean_object* l_Lean_Elab_Level_elabLevel___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_10 = l_Lean_replaceRef(x_1, x_8);
lean_dec(x_8);
lean_ctor_set(x_2, 0, x_10);
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
x_15 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1128____closed__31;
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
x_56 = l_Lean_Elab_Level_elabLevel___closed__5;
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
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_101 = lean_ctor_get(x_99, 0);
x_102 = lean_ctor_get(x_99, 1);
x_103 = lean_array_get_size(x_97);
x_104 = lean_nat_sub(x_103, x_95);
lean_dec(x_103);
x_105 = lean_unsigned_to_nat(0u);
x_106 = l_Array_toSubarray___rarg(x_97, x_105, x_104);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 2);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_array_get_size(x_107);
x_111 = lean_nat_dec_le(x_108, x_110);
if (x_111 == 0)
{
uint8_t x_112; 
lean_dec(x_108);
x_112 = lean_nat_dec_lt(x_109, x_110);
if (x_112 == 0)
{
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_2);
return x_99;
}
else
{
size_t x_113; size_t x_114; lean_object* x_115; 
lean_free_object(x_99);
x_113 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_114 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_115 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__4(x_107, x_113, x_114, x_101, x_2, x_102);
lean_dec(x_107);
return x_115;
}
}
else
{
uint8_t x_116; 
lean_dec(x_110);
x_116 = lean_nat_dec_lt(x_109, x_108);
if (x_116 == 0)
{
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_2);
return x_99;
}
else
{
size_t x_117; size_t x_118; lean_object* x_119; 
lean_free_object(x_99);
x_117 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_118 = lean_usize_of_nat(x_109);
lean_dec(x_109);
x_119 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__4(x_107, x_117, x_118, x_101, x_2, x_102);
lean_dec(x_107);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_120 = lean_ctor_get(x_99, 0);
x_121 = lean_ctor_get(x_99, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_99);
x_122 = lean_array_get_size(x_97);
x_123 = lean_nat_sub(x_122, x_95);
lean_dec(x_122);
x_124 = lean_unsigned_to_nat(0u);
x_125 = l_Array_toSubarray___rarg(x_97, x_124, x_123);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = lean_array_get_size(x_126);
x_130 = lean_nat_dec_le(x_127, x_129);
if (x_130 == 0)
{
uint8_t x_131; 
lean_dec(x_127);
x_131 = lean_nat_dec_lt(x_128, x_129);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_126);
lean_dec(x_2);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_120);
lean_ctor_set(x_132, 1, x_121);
return x_132;
}
else
{
size_t x_133; size_t x_134; lean_object* x_135; 
x_133 = lean_usize_of_nat(x_129);
lean_dec(x_129);
x_134 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_135 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__4(x_126, x_133, x_134, x_120, x_2, x_121);
lean_dec(x_126);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_129);
x_136 = lean_nat_dec_lt(x_128, x_127);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_2);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_120);
lean_ctor_set(x_137, 1, x_121);
return x_137;
}
else
{
size_t x_138; size_t x_139; lean_object* x_140; 
x_138 = lean_usize_of_nat(x_127);
lean_dec(x_127);
x_139 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_140 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__4(x_126, x_138, x_139, x_120, x_2, x_121);
lean_dec(x_126);
return x_140;
}
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_97);
lean_dec(x_2);
x_141 = !lean_is_exclusive(x_99);
if (x_141 == 0)
{
return x_99;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_99, 0);
x_143 = lean_ctor_get(x_99, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_99);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_4);
x_145 = lean_unsigned_to_nat(1u);
x_146 = l_Lean_Syntax_getArg(x_1, x_145);
lean_dec(x_1);
x_147 = l_Lean_Syntax_getArgs(x_146);
lean_dec(x_146);
x_148 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_147);
lean_inc(x_2);
x_149 = l_Lean_Elab_Level_elabLevel(x_148, x_2, x_3);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_151 = lean_ctor_get(x_149, 0);
x_152 = lean_ctor_get(x_149, 1);
x_153 = lean_array_get_size(x_147);
x_154 = lean_nat_sub(x_153, x_145);
lean_dec(x_153);
x_155 = lean_unsigned_to_nat(0u);
x_156 = l_Array_toSubarray___rarg(x_147, x_155, x_154);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
x_160 = lean_array_get_size(x_157);
x_161 = lean_nat_dec_le(x_158, x_160);
if (x_161 == 0)
{
uint8_t x_162; 
lean_dec(x_158);
x_162 = lean_nat_dec_lt(x_159, x_160);
if (x_162 == 0)
{
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_2);
return x_149;
}
else
{
size_t x_163; size_t x_164; lean_object* x_165; 
lean_free_object(x_149);
x_163 = lean_usize_of_nat(x_160);
lean_dec(x_160);
x_164 = lean_usize_of_nat(x_159);
lean_dec(x_159);
x_165 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__5(x_157, x_163, x_164, x_151, x_2, x_152);
lean_dec(x_157);
return x_165;
}
}
else
{
uint8_t x_166; 
lean_dec(x_160);
x_166 = lean_nat_dec_lt(x_159, x_158);
if (x_166 == 0)
{
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_2);
return x_149;
}
else
{
size_t x_167; size_t x_168; lean_object* x_169; 
lean_free_object(x_149);
x_167 = lean_usize_of_nat(x_158);
lean_dec(x_158);
x_168 = lean_usize_of_nat(x_159);
lean_dec(x_159);
x_169 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__5(x_157, x_167, x_168, x_151, x_2, x_152);
lean_dec(x_157);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_170 = lean_ctor_get(x_149, 0);
x_171 = lean_ctor_get(x_149, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_149);
x_172 = lean_array_get_size(x_147);
x_173 = lean_nat_sub(x_172, x_145);
lean_dec(x_172);
x_174 = lean_unsigned_to_nat(0u);
x_175 = l_Array_toSubarray___rarg(x_147, x_174, x_173);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 2);
lean_inc(x_177);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
x_179 = lean_array_get_size(x_176);
x_180 = lean_nat_dec_le(x_177, x_179);
if (x_180 == 0)
{
uint8_t x_181; 
lean_dec(x_177);
x_181 = lean_nat_dec_lt(x_178, x_179);
if (x_181 == 0)
{
lean_object* x_182; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_2);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_170);
lean_ctor_set(x_182, 1, x_171);
return x_182;
}
else
{
size_t x_183; size_t x_184; lean_object* x_185; 
x_183 = lean_usize_of_nat(x_179);
lean_dec(x_179);
x_184 = lean_usize_of_nat(x_178);
lean_dec(x_178);
x_185 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__5(x_176, x_183, x_184, x_170, x_2, x_171);
lean_dec(x_176);
return x_185;
}
}
else
{
uint8_t x_186; 
lean_dec(x_179);
x_186 = lean_nat_dec_lt(x_178, x_177);
if (x_186 == 0)
{
lean_object* x_187; 
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_2);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_170);
lean_ctor_set(x_187, 1, x_171);
return x_187;
}
else
{
size_t x_188; size_t x_189; lean_object* x_190; 
x_188 = lean_usize_of_nat(x_177);
lean_dec(x_177);
x_189 = lean_usize_of_nat(x_178);
lean_dec(x_178);
x_190 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__5(x_176, x_188, x_189, x_170, x_2, x_171);
lean_dec(x_176);
return x_190;
}
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_147);
lean_dec(x_2);
x_191 = !lean_is_exclusive(x_149);
if (x_191 == 0)
{
return x_149;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_149, 0);
x_193 = lean_ctor_get(x_149, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_149);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
}
else
{
lean_object* x_195; lean_object* x_196; 
lean_dec(x_4);
x_195 = lean_unsigned_to_nat(1u);
x_196 = l_Lean_Syntax_getArg(x_1, x_195);
lean_dec(x_1);
x_1 = x_196;
goto _start;
}
}
else
{
lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_2, 0);
x_199 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_inc(x_198);
lean_dec(x_2);
x_200 = l_Lean_replaceRef(x_1, x_198);
lean_dec(x_198);
x_201 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_199);
if (x_6 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = l_Lean_Level_PP_Result_quote___lambda__5___closed__1;
x_203 = lean_name_eq(x_4, x_202);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Lean_Level_PP_Result_quote___lambda__6___closed__1;
x_205 = lean_name_eq(x_4, x_204);
if (x_205 == 0)
{
lean_object* x_206; uint8_t x_207; 
x_206 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1128____closed__31;
x_207 = lean_name_eq(x_4, x_206);
if (x_207 == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = l_Lean_numLitKind;
x_209 = lean_name_eq(x_4, x_208);
if (x_209 == 0)
{
lean_object* x_210; uint8_t x_211; 
x_210 = l_Lean_identKind;
x_211 = lean_name_eq(x_4, x_210);
if (x_211 == 0)
{
lean_object* x_212; uint8_t x_213; 
x_212 = l_Lean_Level_PP_Result_quote___lambda__3___closed__2;
x_213 = lean_name_eq(x_4, x_212);
lean_dec(x_4);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_1);
x_214 = l_Lean_Elab_Level_elabLevel___closed__3;
x_215 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__1(x_214, x_201, x_3);
lean_dec(x_201);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_unsigned_to_nat(0u);
x_217 = l_Lean_Syntax_getArg(x_1, x_216);
lean_inc(x_201);
x_218 = l_Lean_Elab_Level_elabLevel(x_217, x_201, x_3);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
x_222 = lean_unsigned_to_nat(2u);
x_223 = l_Lean_Syntax_getArg(x_1, x_222);
lean_dec(x_1);
x_224 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_208, x_223);
lean_dec(x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; 
lean_dec(x_221);
lean_dec(x_219);
x_225 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_201, x_220);
lean_dec(x_201);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_201);
x_226 = lean_ctor_get(x_224, 0);
lean_inc(x_226);
lean_dec(x_224);
x_227 = l_Lean_Level_addOffsetAux(x_226, x_219);
if (lean_is_scalar(x_221)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_221;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_220);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_201);
lean_dec(x_1);
x_229 = lean_ctor_get(x_218, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_218, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_231 = x_218;
} else {
 lean_dec_ref(x_218);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
lean_dec(x_4);
x_233 = l_Lean_Syntax_getId(x_1);
lean_dec(x_1);
x_234 = lean_ctor_get(x_3, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_3, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_3, 2);
lean_inc(x_236);
x_237 = l_List_elem___at_Lean_NameHashSet_insert___spec__2(x_233, x_236);
if (x_237 == 0)
{
if (x_199 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
x_238 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_238, 0, x_233);
x_239 = l_Lean_Elab_Level_elabLevel___closed__5;
x_240 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
x_241 = l_Lean_KernelException_toMessageData___closed__3;
x_242 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3(x_242, x_201, x_3);
lean_dec(x_201);
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
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_244);
lean_ctor_set(x_247, 1, x_245);
return x_247;
}
else
{
uint8_t x_248; 
lean_inc(x_233);
x_248 = l_Lean_Elab_isValidAutoBoundLevelName(x_233);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
x_249 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_249, 0, x_233);
x_250 = l_Lean_Elab_Level_elabLevel___closed__5;
x_251 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_249);
x_252 = l_Lean_KernelException_toMessageData___closed__3;
x_253 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = l_Lean_throwError___at_Lean_Elab_Level_elabLevel___spec__3(x_253, x_201, x_3);
lean_dec(x_201);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_257 = x_254;
} else {
 lean_dec_ref(x_254);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_259 = x_3;
} else {
 lean_dec_ref(x_3);
 x_259 = lean_box(0);
}
lean_inc(x_233);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_233);
lean_ctor_set(x_260, 1, x_236);
if (lean_is_scalar(x_259)) {
 x_261 = lean_alloc_ctor(0, 3, 0);
} else {
 x_261 = x_259;
}
lean_ctor_set(x_261, 0, x_234);
lean_ctor_set(x_261, 1, x_235);
lean_ctor_set(x_261, 2, x_260);
x_262 = lean_box(0);
x_263 = l_Lean_Elab_Level_elabLevel___lambda__1(x_233, x_262, x_201, x_261);
lean_dec(x_201);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
x_264 = lean_box(0);
x_265 = l_Lean_Elab_Level_elabLevel___lambda__1(x_233, x_264, x_201, x_3);
lean_dec(x_201);
return x_265;
}
}
}
else
{
lean_object* x_266; 
lean_dec(x_4);
x_266 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_208, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; 
x_267 = l_Lean_Elab_throwIllFormedSyntax___at_Lean_Elab_Level_elabLevel___spec__2(x_201, x_3);
lean_dec(x_201);
return x_267;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_201);
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
lean_dec(x_266);
x_269 = l_Lean_Level_ofNat(x_268);
lean_dec(x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_3);
return x_270;
}
}
}
else
{
lean_object* x_271; 
lean_dec(x_4);
lean_dec(x_1);
x_271 = l_Lean_Elab_Level_mkFreshLevelMVar(x_201, x_3);
lean_dec(x_201);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_4);
x_272 = lean_unsigned_to_nat(1u);
x_273 = l_Lean_Syntax_getArg(x_1, x_272);
lean_dec(x_1);
x_274 = l_Lean_Syntax_getArgs(x_273);
lean_dec(x_273);
x_275 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_274);
lean_inc(x_201);
x_276 = l_Lean_Elab_Level_elabLevel(x_275, x_201, x_3);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_279 = x_276;
} else {
 lean_dec_ref(x_276);
 x_279 = lean_box(0);
}
x_280 = lean_array_get_size(x_274);
x_281 = lean_nat_sub(x_280, x_272);
lean_dec(x_280);
x_282 = lean_unsigned_to_nat(0u);
x_283 = l_Array_toSubarray___rarg(x_274, x_282, x_281);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_283, 1);
lean_inc(x_286);
lean_dec(x_283);
x_287 = lean_array_get_size(x_284);
x_288 = lean_nat_dec_le(x_285, x_287);
if (x_288 == 0)
{
uint8_t x_289; 
lean_dec(x_285);
x_289 = lean_nat_dec_lt(x_286, x_287);
if (x_289 == 0)
{
lean_object* x_290; 
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_284);
lean_dec(x_201);
if (lean_is_scalar(x_279)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_279;
}
lean_ctor_set(x_290, 0, x_277);
lean_ctor_set(x_290, 1, x_278);
return x_290;
}
else
{
size_t x_291; size_t x_292; lean_object* x_293; 
lean_dec(x_279);
x_291 = lean_usize_of_nat(x_287);
lean_dec(x_287);
x_292 = lean_usize_of_nat(x_286);
lean_dec(x_286);
x_293 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__4(x_284, x_291, x_292, x_277, x_201, x_278);
lean_dec(x_284);
return x_293;
}
}
else
{
uint8_t x_294; 
lean_dec(x_287);
x_294 = lean_nat_dec_lt(x_286, x_285);
if (x_294 == 0)
{
lean_object* x_295; 
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_201);
if (lean_is_scalar(x_279)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_279;
}
lean_ctor_set(x_295, 0, x_277);
lean_ctor_set(x_295, 1, x_278);
return x_295;
}
else
{
size_t x_296; size_t x_297; lean_object* x_298; 
lean_dec(x_279);
x_296 = lean_usize_of_nat(x_285);
lean_dec(x_285);
x_297 = lean_usize_of_nat(x_286);
lean_dec(x_286);
x_298 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__4(x_284, x_296, x_297, x_277, x_201, x_278);
lean_dec(x_284);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_274);
lean_dec(x_201);
x_299 = lean_ctor_get(x_276, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_276, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_301 = x_276;
} else {
 lean_dec_ref(x_276);
 x_301 = lean_box(0);
}
if (lean_is_scalar(x_301)) {
 x_302 = lean_alloc_ctor(1, 2, 0);
} else {
 x_302 = x_301;
}
lean_ctor_set(x_302, 0, x_299);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_4);
x_303 = lean_unsigned_to_nat(1u);
x_304 = l_Lean_Syntax_getArg(x_1, x_303);
lean_dec(x_1);
x_305 = l_Lean_Syntax_getArgs(x_304);
lean_dec(x_304);
x_306 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_305);
lean_inc(x_201);
x_307 = l_Lean_Elab_Level_elabLevel(x_306, x_201, x_3);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_310 = x_307;
} else {
 lean_dec_ref(x_307);
 x_310 = lean_box(0);
}
x_311 = lean_array_get_size(x_305);
x_312 = lean_nat_sub(x_311, x_303);
lean_dec(x_311);
x_313 = lean_unsigned_to_nat(0u);
x_314 = l_Array_toSubarray___rarg(x_305, x_313, x_312);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 2);
lean_inc(x_316);
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec(x_314);
x_318 = lean_array_get_size(x_315);
x_319 = lean_nat_dec_le(x_316, x_318);
if (x_319 == 0)
{
uint8_t x_320; 
lean_dec(x_316);
x_320 = lean_nat_dec_lt(x_317, x_318);
if (x_320 == 0)
{
lean_object* x_321; 
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_315);
lean_dec(x_201);
if (lean_is_scalar(x_310)) {
 x_321 = lean_alloc_ctor(0, 2, 0);
} else {
 x_321 = x_310;
}
lean_ctor_set(x_321, 0, x_308);
lean_ctor_set(x_321, 1, x_309);
return x_321;
}
else
{
size_t x_322; size_t x_323; lean_object* x_324; 
lean_dec(x_310);
x_322 = lean_usize_of_nat(x_318);
lean_dec(x_318);
x_323 = lean_usize_of_nat(x_317);
lean_dec(x_317);
x_324 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__5(x_315, x_322, x_323, x_308, x_201, x_309);
lean_dec(x_315);
return x_324;
}
}
else
{
uint8_t x_325; 
lean_dec(x_318);
x_325 = lean_nat_dec_lt(x_317, x_316);
if (x_325 == 0)
{
lean_object* x_326; 
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_201);
if (lean_is_scalar(x_310)) {
 x_326 = lean_alloc_ctor(0, 2, 0);
} else {
 x_326 = x_310;
}
lean_ctor_set(x_326, 0, x_308);
lean_ctor_set(x_326, 1, x_309);
return x_326;
}
else
{
size_t x_327; size_t x_328; lean_object* x_329; 
lean_dec(x_310);
x_327 = lean_usize_of_nat(x_316);
lean_dec(x_316);
x_328 = lean_usize_of_nat(x_317);
lean_dec(x_317);
x_329 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__5(x_315, x_327, x_328, x_308, x_201, x_309);
lean_dec(x_315);
return x_329;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_305);
lean_dec(x_201);
x_330 = lean_ctor_get(x_307, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_307, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 x_332 = x_307;
} else {
 lean_dec_ref(x_307);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 2, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_4);
x_334 = lean_unsigned_to_nat(1u);
x_335 = l_Lean_Syntax_getArg(x_1, x_334);
lean_dec(x_1);
x_1 = x_335;
x_2 = x_201;
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
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__4(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldrMUnsafe_fold___at_Lean_Elab_Level_elabLevel___spec__5(x_1, x_7, x_8, x_4, x_5, x_6);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
