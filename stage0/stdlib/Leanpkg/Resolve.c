// Lean compiler output
// Module: Leanpkg.Resolve
// Imports: Init Leanpkg.Manifest Leanpkg.Proc Leanpkg.Git
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
lean_object* l_List_reverse___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Leanpkg_gitParseOriginRevision(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_resolveDir___boxed(lean_object*, lean_object*);
lean_object* l_Leanpkg_resolvedPath_match__1(lean_object*);
extern lean_object* l_Lean_Syntax_strLitToAtom___closed__3;
lean_object* l_Leanpkg_resolvedPath(lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedString;
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_3356____closed__35;
lean_object* l_Leanpkg_solveDepsCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Leanpkg_Assignment_contains(lean_object*, lean_object*);
lean_object* l_Leanpkg_materialize_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_resolveDir___closed__1;
lean_object* l_List_lookup___at_Leanpkg_Assignment_contains___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_is_dir(lean_object*, lean_object*);
lean_object* l_Leanpkg_materialize(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_resolveDir(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Leanpkg_solveDepsCore_match__1(lean_object*);
lean_object* l_Leanpkg_solveDepsCore_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_solveDeps_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Leanpkg_materialize___closed__7;
lean_object* l_Leanpkg_execCmd(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Leanpkg_constructPath_match__1(lean_object*);
lean_object* l_Leanpkg_constructPath_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Leanpkg_notYetAssigned___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_Assignment_fold_match__1(lean_object*);
lean_object* l_Leanpkg_Assignment_fold_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Leanpkg_materialize___lambda__1___closed__4;
uint8_t l_Leanpkg_notYetAssigned___closed__1;
extern lean_object* l_Leanpkg_gitParseRevision___closed__1;
extern lean_object* l_Leanpkg_gitLatestOriginRevision___closed__2;
lean_object* l_Leanpkg_materialize_match__2(lean_object*);
lean_object* l_Leanpkg_resolvedPath___closed__4;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_mapM___at_Leanpkg_constructPath___spec__1(lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__3;
lean_object* l_Leanpkg_materialize___closed__6;
lean_object* l_IO_print___at_IO_println___spec__1(lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Leanpkg_constructPathCore___rarg(lean_object*, lean_object*);
lean_object* l_List_foldl___at_Leanpkg_Assignment_fold___spec__1(lean_object*);
lean_object* l_Leanpkg_solveDeps(lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_object* l_Leanpkg_solveDepsCore___closed__2;
lean_object* l_Leanpkg_solveDeps_match__1(lean_object*);
lean_object* l_Leanpkg_solveDepsCore___closed__1;
lean_object* l_Leanpkg_Assignment_insert(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Leanpkg_leanpkgTomlFn;
lean_object* l_List_lookup___at_Leanpkg_Assignment_contains___spec__1(lean_object*, lean_object*);
lean_object* l_Leanpkg_gitRevisionExists(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
extern lean_object* l_instMonadEST___closed__1;
lean_object* l_Leanpkg_constructPathCore___boxed(lean_object*);
lean_object* l_Leanpkg_notYetAssigned(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_Assignment_fold___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_materialize___closed__5;
lean_object* l_Leanpkg_Manifest_fromFile(lean_object*, lean_object*);
lean_object* l_Leanpkg_constructPathCore(lean_object*);
lean_object* l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_mkAntiquotNode___closed__9;
lean_object* l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_materialize___lambda__1___closed__2;
lean_object* l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__2;
lean_object* l_IO_isDir___at_Leanpkg_materialize___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_constructPath(lean_object*, lean_object*);
lean_object* l_Leanpkg_materialize___closed__8;
lean_object* l_Leanpkg_solveDepsCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_resolvedPath___closed__5;
uint8_t l_UInt32_decEq(uint32_t, uint32_t);
lean_object* l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterAuxM___at_Leanpkg_solveDepsCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_resolvedPath___closed__3;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Leanpkg_materialize_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_resolvedPath___closed__2;
lean_object* l_Leanpkg_resolvedPath___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_resolvedPath___closed__1;
lean_object* l_List_forM___at_Leanpkg_solveDepsCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_resolvedPath_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_materialize___closed__3;
lean_object* l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__1;
lean_object* l_Leanpkg_solveDepsCore_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Leanpkg_Assignment_fold___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_materialize___lambda__1___closed__3;
lean_object* l_Leanpkg_Assignment_empty;
lean_object* l_Leanpkg_Assignment_contains___boxed(lean_object*, lean_object*);
lean_object* l_Leanpkg_materialize___closed__2;
lean_object* l_StateT_instMonadStateT___rarg(lean_object*);
uint8_t l_Leanpkg_notYetAssigned___closed__2;
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
lean_object* l_IO_isDir___at_Leanpkg_materialize___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Leanpkg_leanpkgTomlFn___closed__1;
lean_object* l_Leanpkg_materialize___closed__4;
lean_object* l_Leanpkg_Manifest_effectivePath(lean_object*);
lean_object* l_Leanpkg_materialize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Leanpkg_gitParseRevision___closed__9;
lean_object* l_Leanpkg_materialize_match__1(lean_object*);
lean_object* l_Leanpkg_materialize___lambda__1___closed__1;
lean_object* l_Leanpkg_materialize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Leanpkg_materialize___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Leanpkg_Assignment_fold(lean_object*);
static lean_object* _init_l_Leanpkg_Assignment_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_List_lookup___at_Leanpkg_Assignment_contains___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_dec_eq(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
}
}
}
uint8_t l_Leanpkg_Assignment_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at_Leanpkg_Assignment_contains___spec__1(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
lean_object* l_List_lookup___at_Leanpkg_Assignment_contains___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at_Leanpkg_Assignment_contains___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Leanpkg_Assignment_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Leanpkg_Assignment_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Leanpkg_Assignment_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Leanpkg_Assignment_contains(x_1, x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Leanpkg_Assignment_fold_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Leanpkg_Assignment_fold_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_Assignment_fold_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_foldl___at_Leanpkg_Assignment_fold___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_1);
x_8 = lean_apply_3(x_1, x_2, x_6, x_7);
x_2 = x_8;
x_3 = x_5;
goto _start;
}
}
}
lean_object* l_List_foldl___at_Leanpkg_Assignment_fold___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_Leanpkg_Assignment_fold___spec__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Leanpkg_Assignment_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at_Leanpkg_Assignment_fold___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Leanpkg_Assignment_fold(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_Assignment_fold___rarg), 3, 0);
return x_2;
}
}
static uint8_t _init_l_Leanpkg_notYetAssigned___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static uint8_t _init_l_Leanpkg_notYetAssigned___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
lean_object* l_Leanpkg_notYetAssigned(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Leanpkg_Assignment_contains(x_2, x_1);
if (x_4 == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Leanpkg_notYetAssigned___closed__1;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Leanpkg_notYetAssigned___closed__2;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
lean_object* l_Leanpkg_notYetAssigned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Leanpkg_notYetAssigned(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Leanpkg_resolvedPath_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Leanpkg_resolvedPath_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_resolvedPath_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Leanpkg_resolvedPath___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_instMonadEST___closed__1;
x_2 = l_StateT_instMonadStateT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Leanpkg_resolvedPath___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_resolvedPath___closed__1;
x_2 = l_String_instInhabitedString;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_resolvedPath___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Leanpkg.Resolve");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_resolvedPath___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Leanpkg.resolvedPath");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_resolvedPath___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Leanpkg_resolvedPath___closed__3;
x_2 = l_Leanpkg_resolvedPath___closed__4;
x_3 = lean_unsigned_to_nat(34u);
x_4 = lean_unsigned_to_nat(44u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Leanpkg_resolvedPath(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___at_Leanpkg_Assignment_contains___spec__1(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Leanpkg_resolvedPath___closed__2;
x_6 = l_Leanpkg_resolvedPath___closed__5;
x_7 = lean_panic_fn(x_5, x_6);
x_8 = lean_apply_2(x_7, x_2, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
lean_object* l_Leanpkg_resolvedPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Leanpkg_resolvedPath(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Leanpkg_resolveDir___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("/");
return x_1;
}
}
lean_object* l_Leanpkg_resolveDir(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; uint32_t x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_get(x_1, x_3);
x_5 = 47;
x_6 = x_4 == x_5;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Leanpkg_resolveDir___closed__1;
x_8 = lean_string_append(x_2, x_7);
x_9 = lean_string_append(x_8, x_1);
return x_9;
}
else
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
}
}
lean_object* l_Leanpkg_resolveDir___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Leanpkg_resolveDir(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Leanpkg_materialize_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_3(x_3, x_6, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Leanpkg_materialize_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_materialize_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Leanpkg_materialize_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Leanpkg_materialize_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_materialize_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_isDir___at_Leanpkg_materialize___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_io_is_dir(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
static lean_object* _init_l_Leanpkg_materialize___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("checkout");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_materialize___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkAntiquotNode___closed__9;
x_2 = l_Leanpkg_materialize___lambda__1___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_materialize___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("--detach");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_materialize___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Leanpkg_materialize___lambda__1___closed__2;
x_2 = l_Leanpkg_materialize___lambda__1___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Leanpkg_materialize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Leanpkg_gitParseOriginRevision(x_1, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Leanpkg_materialize___lambda__1___closed__4;
x_11 = lean_array_push(x_10, x_8);
lean_inc(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = l_Leanpkg_gitParseRevision___closed__1;
x_14 = l_Leanpkg_gitParseRevision___closed__9;
x_15 = l_Array_empty___closed__1;
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
lean_ctor_set(x_16, 4, x_15);
x_17 = l_Leanpkg_execCmd(x_16, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Leanpkg_Assignment_insert(x_5, x_3, x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l_Leanpkg_Assignment_insert(x_5, x_3, x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
return x_7;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
static lean_object* _init_l_Leanpkg_materialize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(": using local path ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_materialize___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("build/deps/");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_materialize___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(": cloning ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_materialize___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" to ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_materialize___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("clone");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_materialize___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_mkAntiquotNode___closed__9;
x_2 = l_Leanpkg_materialize___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Leanpkg_materialize___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(": trying to update ");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_materialize___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" to revision ");
return x_1;
}
}
lean_object* l_Leanpkg_materialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Leanpkg_resolveDir(x_6, x_1);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_instInhabitedParserDescr___closed__1;
x_10 = lean_string_append(x_9, x_8);
x_11 = l_Leanpkg_materialize___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_7);
x_14 = lean_string_append(x_13, x_9);
x_15 = l_IO_println___at_Lean_instEval___spec__1(x_14, x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = l_Leanpkg_Assignment_insert(x_3, x_8, x_7);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l_Leanpkg_Assignment_insert(x_3, x_8, x_7);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_5, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_5, 2);
lean_inc(x_32);
lean_dec(x_5);
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_dec(x_2);
x_34 = l_Leanpkg_materialize___closed__2;
x_35 = lean_string_append(x_34, x_33);
x_36 = l_IO_isDir___at_Leanpkg_materialize___spec__1(x_35, x_3, x_4);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_32);
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = l_Lean_instInhabitedParserDescr___closed__1;
x_43 = lean_string_append(x_42, x_33);
x_44 = l_Leanpkg_materialize___closed__3;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_string_append(x_45, x_30);
x_47 = l_Leanpkg_materialize___closed__4;
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_35);
x_50 = lean_string_append(x_49, x_42);
x_51 = l_IO_println___at_Lean_instEval___spec__1(x_50, x_40);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Leanpkg_materialize___closed__6;
x_54 = lean_array_push(x_53, x_30);
lean_inc(x_35);
x_55 = lean_array_push(x_54, x_35);
x_56 = lean_box(0);
x_57 = l_Leanpkg_gitParseRevision___closed__1;
x_58 = l_Leanpkg_gitParseRevision___closed__9;
x_59 = l_Array_empty___closed__1;
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_56);
lean_ctor_set(x_60, 4, x_59);
x_61 = l_Leanpkg_execCmd(x_60, x_52);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Leanpkg_materialize___lambda__1(x_35, x_31, x_33, x_62, x_41, x_63);
lean_dec(x_62);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_41);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
x_69 = !lean_is_exclusive(x_51);
if (x_69 == 0)
{
return x_51;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_51, 0);
x_71 = lean_ctor_get(x_51, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_51);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_30);
x_73 = lean_ctor_get(x_36, 1);
lean_inc(x_73);
lean_dec(x_36);
x_74 = lean_ctor_get(x_37, 1);
lean_inc(x_74);
lean_dec(x_37);
x_75 = l_Lean_instInhabitedParserDescr___closed__1;
x_76 = lean_string_append(x_75, x_33);
x_77 = l_Leanpkg_materialize___closed__7;
x_78 = lean_string_append(x_76, x_77);
x_79 = lean_string_append(x_78, x_35);
x_80 = l_Leanpkg_materialize___closed__8;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_string_append(x_81, x_31);
x_83 = lean_string_append(x_82, x_75);
x_84 = l_IO_print___at_IO_println___spec__1(x_83, x_73);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
if (lean_obj_tag(x_32) == 0)
{
x_86 = x_75;
goto block_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_32, 0);
lean_inc(x_122);
lean_dec(x_32);
x_123 = l_myMacro____x40_Init_NotationExtra___hyg_3356____closed__35;
x_124 = lean_string_append(x_123, x_122);
lean_dec(x_122);
x_86 = x_124;
goto block_121;
}
block_121:
{
lean_object* x_87; 
x_87 = l_IO_println___at_Lean_instEval___spec__1(x_86, x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
lean_inc(x_31);
lean_inc(x_35);
x_89 = l_Leanpkg_gitParseOriginRevision(x_35, x_31, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_35);
x_92 = l_Leanpkg_gitRevisionExists(x_35, x_90, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
lean_inc(x_35);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_35);
x_97 = l_Leanpkg_gitParseRevision___closed__1;
x_98 = l_Leanpkg_gitParseRevision___closed__9;
x_99 = l_Leanpkg_gitLatestOriginRevision___closed__2;
x_100 = l_Array_empty___closed__1;
x_101 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_99);
lean_ctor_set(x_101, 3, x_96);
lean_ctor_set(x_101, 4, x_100);
x_102 = l_Leanpkg_execCmd(x_101, x_95);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Leanpkg_materialize___lambda__1(x_35, x_31, x_33, x_103, x_74, x_104);
lean_dec(x_103);
return x_105;
}
else
{
uint8_t x_106; 
lean_dec(x_74);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
x_106 = !lean_is_exclusive(x_102);
if (x_106 == 0)
{
return x_102;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_102, 0);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_102);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_92, 1);
lean_inc(x_110);
lean_dec(x_92);
x_111 = lean_box(0);
x_112 = l_Leanpkg_materialize___lambda__1(x_35, x_31, x_33, x_111, x_74, x_110);
return x_112;
}
}
else
{
uint8_t x_113; 
lean_dec(x_74);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
x_113 = !lean_is_exclusive(x_89);
if (x_113 == 0)
{
return x_89;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_89, 0);
x_115 = lean_ctor_get(x_89, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_89);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_74);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
x_117 = !lean_is_exclusive(x_87);
if (x_117 == 0)
{
return x_87;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_87, 0);
x_119 = lean_ctor_get(x_87, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_87);
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
uint8_t x_125; 
lean_dec(x_74);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_125 = !lean_is_exclusive(x_84);
if (x_125 == 0)
{
return x_84;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_84, 0);
x_127 = lean_ctor_get(x_84, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_84);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
x_129 = !lean_is_exclusive(x_36);
if (x_129 == 0)
{
return x_36;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_36, 0);
x_131 = lean_ctor_get(x_36, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_36);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
}
lean_object* l_IO_isDir___at_Leanpkg_materialize___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_isDir___at_Leanpkg_materialize___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Leanpkg_materialize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Leanpkg_materialize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Leanpkg_solveDepsCore_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
lean_object* l_Leanpkg_solveDepsCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_solveDepsCore_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Leanpkg_solveDepsCore_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Leanpkg_solveDepsCore_match__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_filterAuxM___at_Leanpkg_solveDepsCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = l_Leanpkg_notYetAssigned(x_10, x_3, x_4);
lean_dec(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_1);
lean_dec(x_8);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_1 = x_9;
x_3 = x_16;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_9;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_2 = x_19;
lean_object* _tmp_3 = x_18;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = l_Leanpkg_notYetAssigned(x_23, x_3, x_4);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_1 = x_22;
x_3 = x_29;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_2);
x_1 = x_22;
x_2 = x_33;
x_3 = x_32;
x_4 = x_31;
goto _start;
}
}
}
}
}
lean_object* l_List_forM___at_Leanpkg_solveDepsCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_10 = l_Leanpkg_materialize(x_1, x_8, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_2 = x_9;
x_3 = x_13;
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
lean_object* l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Leanpkg_solveDepsCore(x_1, x_2, x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_9, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (in ");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(") depends on ");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", but resolved dependency has name ");
return x_1;
}
}
lean_object* l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Leanpkg_resolvedPath(x_12, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Leanpkg_resolveDir___closed__1;
lean_inc(x_16);
x_19 = lean_string_append(x_16, x_18);
x_20 = l_Leanpkg_leanpkgTomlFn___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_Leanpkg_Manifest_fromFile(x_21, x_15);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_string_dec_eq(x_26, x_12);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_5);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
x_29 = l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_string_append(x_30, x_1);
x_32 = l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__2;
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_26);
lean_dec(x_26);
x_35 = l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__3;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_string_append(x_36, x_12);
x_38 = lean_string_append(x_37, x_29);
x_39 = lean_string_append(x_38, x_16);
lean_dec(x_16);
x_40 = l_prec_x28___x29___closed__7;
x_41 = lean_string_append(x_39, x_40);
x_42 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_42);
return x_22;
}
else
{
lean_object* x_43; 
lean_dec(x_26);
lean_free_object(x_22);
x_43 = l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___lambda__1(x_16, x_24, x_3, x_5, x_17, x_25);
lean_dec(x_5);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_44, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
lean_dec(x_45);
lean_ctor_set(x_44, 0, x_50);
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec(x_44);
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_43, 0, x_53);
return x_43;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_43, 1);
lean_inc(x_54);
lean_dec(x_43);
x_55 = lean_ctor_get(x_44, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_56 = x_44;
} else {
 lean_dec_ref(x_44);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_45, 0);
lean_inc(x_57);
lean_dec(x_45);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_54);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_43, 1);
lean_inc(x_60);
lean_dec(x_43);
x_61 = lean_ctor_get(x_44, 1);
lean_inc(x_61);
lean_dec(x_44);
x_62 = lean_ctor_get(x_45, 0);
lean_inc(x_62);
lean_dec(x_45);
x_4 = x_11;
x_5 = x_62;
x_6 = x_61;
x_7 = x_60;
goto _start;
}
}
else
{
uint8_t x_64; 
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_43);
if (x_64 == 0)
{
return x_43;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_43, 0);
x_66 = lean_ctor_get(x_43, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_43);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_22, 0);
x_69 = lean_ctor_get(x_22, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_22);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_string_dec_eq(x_70, x_12);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_68);
lean_dec(x_17);
lean_dec(x_5);
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
lean_dec(x_2);
x_73 = l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__1;
x_74 = lean_string_append(x_72, x_73);
x_75 = lean_string_append(x_74, x_1);
x_76 = l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__2;
x_77 = lean_string_append(x_75, x_76);
x_78 = lean_string_append(x_77, x_70);
lean_dec(x_70);
x_79 = l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__3;
x_80 = lean_string_append(x_78, x_79);
x_81 = lean_string_append(x_80, x_12);
x_82 = lean_string_append(x_81, x_73);
x_83 = lean_string_append(x_82, x_16);
lean_dec(x_16);
x_84 = l_prec_x28___x29___closed__7;
x_85 = lean_string_append(x_83, x_84);
x_86 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_69);
return x_87;
}
else
{
lean_object* x_88; 
lean_dec(x_70);
x_88 = l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___lambda__1(x_16, x_68, x_3, x_5, x_17, x_69);
lean_dec(x_5);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_2);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_92 = x_88;
} else {
 lean_dec_ref(x_88);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_94 = x_89;
} else {
 lean_dec_ref(x_89);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
if (lean_is_scalar(x_92)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_92;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_91);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_dec(x_88);
x_99 = lean_ctor_get(x_89, 1);
lean_inc(x_99);
lean_dec(x_89);
x_100 = lean_ctor_get(x_90, 0);
lean_inc(x_100);
lean_dec(x_90);
x_4 = x_11;
x_5 = x_100;
x_6 = x_99;
x_7 = x_98;
goto _start;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_2);
x_102 = lean_ctor_get(x_88, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_88, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_104 = x_88;
} else {
 lean_dec_ref(x_88);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_22);
if (x_106 == 0)
{
return x_22;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_22, 0);
x_108 = lean_ctor_get(x_22, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_22);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_5);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_13);
if (x_110 == 0)
{
return x_13;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_13, 0);
x_112 = lean_ctor_get(x_13, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_13);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
}
static lean_object* _init_l_Leanpkg_solveDepsCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maximum dependency resolution depth reached");
return x_1;
}
}
static lean_object* _init_l_Leanpkg_solveDepsCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Leanpkg_solveDepsCore___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Leanpkg_solveDepsCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_3, x_8);
x_10 = lean_ctor_get(x_2, 5);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = l_List_filterAuxM___at_Leanpkg_solveDepsCore___spec__1(x_10, x_11, x_4, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_List_reverse___rarg(x_15);
lean_inc(x_17);
lean_inc(x_1);
x_18 = l_List_forM___at_Leanpkg_solveDepsCore___spec__2(x_1, x_17, x_16, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3(x_1, x_2, x_9, x_17, x_22, x_21, x_20);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_18);
if (x_41 == 0)
{
return x_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_18, 0);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_18);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_45 = l_Leanpkg_solveDepsCore___closed__2;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_5);
return x_46;
}
}
}
lean_object* l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Leanpkg_solveDepsCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Leanpkg_solveDepsCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Leanpkg_solveDeps_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Leanpkg_solveDeps_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_solveDeps_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Leanpkg_solveDeps(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l_Leanpkg_Assignment_empty;
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Leanpkg_Assignment_insert(x_4, x_3, x_5);
x_7 = lean_unsigned_to_nat(1024u);
x_8 = l_Leanpkg_solveDepsCore(x_5, x_1, x_7, x_6, x_2);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Leanpkg_constructPathCore___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Leanpkg_resolveDir___closed__1;
x_4 = lean_string_append(x_1, x_3);
x_5 = l_Leanpkg_leanpkgTomlFn;
lean_inc(x_4);
x_6 = lean_string_append(x_4, x_5);
x_7 = l_Leanpkg_Manifest_fromFile(x_6, x_2);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Leanpkg_Manifest_effectivePath(x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_4, x_10);
lean_dec(x_10);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = l_Leanpkg_Manifest_effectivePath(x_12);
lean_dec(x_12);
x_15 = lean_string_append(x_4, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Leanpkg_constructPathCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_constructPathCore___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Leanpkg_constructPathCore___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Leanpkg_constructPathCore(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Leanpkg_constructPath_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Leanpkg_constructPath_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Leanpkg_constructPath_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_mapM___at_Leanpkg_constructPath___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Leanpkg_constructPathCore___rarg(x_8, x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___at_Leanpkg_constructPath___spec__1(x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_free_object(x_1);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_free_object(x_1);
lean_dec(x_7);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Leanpkg_constructPathCore___rarg(x_28, x_2);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_List_mapM___at_Leanpkg_constructPath___spec__1(x_27, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_30);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_27);
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_44 = x_29;
} else {
 lean_dec_ref(x_29);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
}
lean_object* l_Leanpkg_constructPath(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_reverse___rarg(x_1);
x_4 = l_List_mapM___at_Leanpkg_constructPath___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Leanpkg_Manifest(lean_object*);
lean_object* initialize_Leanpkg_Proc(lean_object*);
lean_object* initialize_Leanpkg_Git(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Leanpkg_Resolve(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Leanpkg_Manifest(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Leanpkg_Proc(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Leanpkg_Git(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Leanpkg_Assignment_empty = _init_l_Leanpkg_Assignment_empty();
lean_mark_persistent(l_Leanpkg_Assignment_empty);
l_Leanpkg_notYetAssigned___closed__1 = _init_l_Leanpkg_notYetAssigned___closed__1();
l_Leanpkg_notYetAssigned___closed__2 = _init_l_Leanpkg_notYetAssigned___closed__2();
l_Leanpkg_resolvedPath___closed__1 = _init_l_Leanpkg_resolvedPath___closed__1();
lean_mark_persistent(l_Leanpkg_resolvedPath___closed__1);
l_Leanpkg_resolvedPath___closed__2 = _init_l_Leanpkg_resolvedPath___closed__2();
lean_mark_persistent(l_Leanpkg_resolvedPath___closed__2);
l_Leanpkg_resolvedPath___closed__3 = _init_l_Leanpkg_resolvedPath___closed__3();
lean_mark_persistent(l_Leanpkg_resolvedPath___closed__3);
l_Leanpkg_resolvedPath___closed__4 = _init_l_Leanpkg_resolvedPath___closed__4();
lean_mark_persistent(l_Leanpkg_resolvedPath___closed__4);
l_Leanpkg_resolvedPath___closed__5 = _init_l_Leanpkg_resolvedPath___closed__5();
lean_mark_persistent(l_Leanpkg_resolvedPath___closed__5);
l_Leanpkg_resolveDir___closed__1 = _init_l_Leanpkg_resolveDir___closed__1();
lean_mark_persistent(l_Leanpkg_resolveDir___closed__1);
l_Leanpkg_materialize___lambda__1___closed__1 = _init_l_Leanpkg_materialize___lambda__1___closed__1();
lean_mark_persistent(l_Leanpkg_materialize___lambda__1___closed__1);
l_Leanpkg_materialize___lambda__1___closed__2 = _init_l_Leanpkg_materialize___lambda__1___closed__2();
lean_mark_persistent(l_Leanpkg_materialize___lambda__1___closed__2);
l_Leanpkg_materialize___lambda__1___closed__3 = _init_l_Leanpkg_materialize___lambda__1___closed__3();
lean_mark_persistent(l_Leanpkg_materialize___lambda__1___closed__3);
l_Leanpkg_materialize___lambda__1___closed__4 = _init_l_Leanpkg_materialize___lambda__1___closed__4();
lean_mark_persistent(l_Leanpkg_materialize___lambda__1___closed__4);
l_Leanpkg_materialize___closed__1 = _init_l_Leanpkg_materialize___closed__1();
lean_mark_persistent(l_Leanpkg_materialize___closed__1);
l_Leanpkg_materialize___closed__2 = _init_l_Leanpkg_materialize___closed__2();
lean_mark_persistent(l_Leanpkg_materialize___closed__2);
l_Leanpkg_materialize___closed__3 = _init_l_Leanpkg_materialize___closed__3();
lean_mark_persistent(l_Leanpkg_materialize___closed__3);
l_Leanpkg_materialize___closed__4 = _init_l_Leanpkg_materialize___closed__4();
lean_mark_persistent(l_Leanpkg_materialize___closed__4);
l_Leanpkg_materialize___closed__5 = _init_l_Leanpkg_materialize___closed__5();
lean_mark_persistent(l_Leanpkg_materialize___closed__5);
l_Leanpkg_materialize___closed__6 = _init_l_Leanpkg_materialize___closed__6();
lean_mark_persistent(l_Leanpkg_materialize___closed__6);
l_Leanpkg_materialize___closed__7 = _init_l_Leanpkg_materialize___closed__7();
lean_mark_persistent(l_Leanpkg_materialize___closed__7);
l_Leanpkg_materialize___closed__8 = _init_l_Leanpkg_materialize___closed__8();
lean_mark_persistent(l_Leanpkg_materialize___closed__8);
l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__1 = _init_l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__1);
l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__2 = _init_l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__2);
l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__3 = _init_l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Leanpkg_solveDepsCore___spec__3___closed__3);
l_Leanpkg_solveDepsCore___closed__1 = _init_l_Leanpkg_solveDepsCore___closed__1();
lean_mark_persistent(l_Leanpkg_solveDepsCore___closed__1);
l_Leanpkg_solveDepsCore___closed__2 = _init_l_Leanpkg_solveDepsCore___closed__2();
lean_mark_persistent(l_Leanpkg_solveDepsCore___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
